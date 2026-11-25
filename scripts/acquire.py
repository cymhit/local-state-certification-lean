#!/usr/bin/env python3
"""Acquire exact public revisions and official Mathlib cache; build required QIT sources."""
import argparse, datetime, json, os, re, shutil, subprocess, sys
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parent))
from verify import (VerificationError,TOOLCHAIN,sha,read_json,imports,load_modules,load_checks,require_project_files,source_identity,artifact_inventory,
                    new_output,find_lean,validate_lean_version,lean_slot,run_logged,sandbox_command,clean_env)

def source_closure(index,seeds,core):
    order=[];seen=set();active=set()
    def visit(name):
        if name in seen:return
        candidates=index.get(name,[])
        if not candidates:
            if name in {'Init','Lean','Lake','Std'} or (core/(name.replace('.','/')+'.olean')).is_file():
                seen.add(name);return
            raise VerificationError('Missing external source/import: '+name,'dependencies',6)
        if len(candidates)!=1:raise VerificationError('Ambiguous external source: '+name,'dependencies',6)
        if name in active:raise VerificationError('External import cycle: '+name,'dependencies',6)
        active.add(name)
        for dep in imports(candidates[0].read_text(encoding='utf-8-sig')):visit(dep)
        active.remove(name);seen.add(name);order.append(name)
    for name in seeds:visit(name)
    return order

def git_output(path,*args):
    return subprocess.check_output(['git','-C',str(path),*args],text=True).strip()

def acquire_sources(packages,output,pool):
    result=[]
    env={'PATH':'/usr/bin:/bin','HOME':str(output/'home'),'GIT_CONFIG_GLOBAL':'/dev/null',
         'GIT_CONFIG_NOSYSTEM':'1','GIT_TERMINAL_PROMPT':'0','LC_ALL':'C.UTF-8'}
    for p in packages:
        if not re.fullmatch(r'[A-Za-z0-9_-]+',p['name']) or not re.fullmatch(r'[0-9a-f]{40}',p['rev']):
            raise VerificationError('Dependency name/revision is not pinned','dependencies',6)
        if not p['url'].startswith('https://') or p.get('subDir'):
            raise VerificationError('Only pinned complete HTTPS repositories are supported','dependencies',6)
        dst=output/'packages'/p['name']; dst.parent.mkdir(exist_ok=True)
        log=output/'logs'/('fetch-'+p['name']+'.log')
        if pool:
            src=pool/p['name']
            if git_output(src,'rev-parse','HEAD')!=p['rev'] or git_output(src,'remote','get-url','origin')!=p['url']:
                raise VerificationError('Source pool revision/URL mismatch: '+p['name'],'dependencies',6)
            if subprocess.run(['git','-C',str(src),'diff','--quiet','HEAD','--']).returncode:
                raise VerificationError('Source pool has modified tracked files','dependencies',6)
            others=git_output(src,'ls-files','--others','-z').split('\0')
            for rel in filter(None,others):
                untracked_path=Path(rel)
                if '.lake' in untracked_path.parts or '__pycache__' in untracked_path.parts or untracked_path.suffix in {'.olean','.ilean','.ir'}:continue
                raise VerificationError('Source pool contains untracked content: '+rel,'dependencies',6)
            for link in src.rglob('*'):
                if link.is_symlink() and (Path(os.readlink(link)).is_absolute() or src.resolve() not in link.resolve().parents):
                    raise VerificationError('Source pool symlink leaves its repository: '+str(link),'dependencies',6)
            # Copy public source and Git identity only; never carry any .lake or compiled file.
            shutil.copytree(src,dst,symlinks=True,ignore=shutil.ignore_patterns('.lake','*.olean','*.ilean','*.ir','__pycache__'))
            log.parent.mkdir(exist_ok=True);log.write_text('Copied verified public source pool; all .lake/build artifacts excluded.\n')
            source='explicit_pristine_public_source_pool_no_build_artifacts'
        else:
            commands=[['git','init','--quiet',dst],['git','-C',dst,'remote','add','origin',p['url']],
                      ['git','-C',dst,'-c','credential.helper=','fetch','--depth','1','origin',p['rev']],
                      ['git','-C',dst,'checkout','--quiet','--detach','FETCH_HEAD']]
            for n,cmd in enumerate(commands):run_logged(cmd,output,log.with_name(log.stem+f'-{n}.log'),env)
            source='public_https_fetch'
        if git_output(dst,'rev-parse','HEAD')!=p['rev']:raise VerificationError('Fetched revision mismatch','dependencies',6)
        if subprocess.run(['git','-C',str(dst),'diff','--quiet','HEAD','--']).returncode:
            raise VerificationError('Copied/fetched tracked source differs from pinned revision: '+p['name'],'dependencies',6)
        result.append({'name':p['name'],'url':p['url'],'rev':p['rev'],'path':dst.relative_to(output).as_posix(),'source':source})
        print('Source ready:',p['name'],flush=True)
    return result

def prepare(root,output,lean,locks,packages,pool,seeds):
    result=acquire_sources(packages,output,pool)
    package_roots={p['name']:output/p['path'] for p in result}
    libpaths=[p/'.lake/build/lib/lean' for p in package_roots.values()]
    for p in libpaths:p.mkdir(parents=True,exist_ok=True)
    core=lean.parent.parent/'lib/lean'
    env=clean_env(lean,output,libpaths)
    env.update(LEAN_SRC_PATH=':'.join(map(str,package_roots.values())),
               MATHLIB_CACHE_DIR=str(output/'cache-downloads'),XDG_CACHE_HOME=str(output/'xdg-cache'),
               GIT_CONFIG_GLOBAL='/dev/null',GIT_CONFIG_NOSYSTEM='1',GIT_TERMINAL_PROMPT='0')
    index={};owners={}
    for owner,pkg in package_roots.items():
        for p in pkg.rglob('*.lean'):
            rel=p.relative_to(pkg)
            if any(x in {'.git','.lake'} for x in rel.parts):continue
            name=rel.as_posix()[:-5].replace('/','.')
            index.setdefault(name,[]).append(p);owners[p]=owner
    closure=source_closure(index,seeds,core)
    bootstrap=source_closure(index,['Cache.Main'],core)
    compiled=[]
    def compile_module(name,kind):
        src=index[name][0];owner=owners[src];pkg=package_roots[owner]
        target=pkg/'.lake/build/lib/lean'/(name.replace('.','/')+'.olean')
        target.parent.mkdir(parents=True,exist_ok=True)
        command=[lean,'-j1','-s65536']
        if owner=='QIT':command+=['-DautoImplicit=false']
        command+=['-o',target,'-i',target.with_suffix('.ilean'),src]
        with lean_slot(locks):
            run_logged(sandbox_command(command,output,pkg,env),pkg,output/'logs'/kind/(name+'.log'))
        compiled.append({'module':name,'package':owner,'source_sha256':sha(src),'kind':kind})
        print('Compiled:',name,flush=True)
    for name in bootstrap:compile_module(name,'cache-bootstrap')
    mathlib=package_roots['mathlib']
    # Execute the unchanged official Cache.Main entry point. Serial bootstrap above
    # avoids Lake spawning an unbounded number of Lean compiler subprocesses.
    cached=[name for name in closure if owners[index[name][0]]!='QIT']
    if not cached:raise VerificationError('No Mathlib-family imports selected','dependencies',6)
    command=[lean,'-j1','-s65536','--run',mathlib/'Cache/Main.lean','get',*cached]
    with lean_slot(locks):
        run_logged(sandbox_command(command,output,mathlib,env,network=True),mathlib,output/'logs/mathlib-cache-get.log')
    # Official .ltar archives retain mathlib's standard nested package layout.
    # Copy those freshly fetched artifacts to the independently tracked source
    # package locations used by this script; do not touch any original checkout.
    for owner,pkg in package_roots.items():
        nested=mathlib/'.lake/packages'/owner/'.lake/build'
        if owner!='mathlib' and nested.is_dir():
            shutil.copytree(nested,pkg/'.lake/build',dirs_exist_ok=True)
    for name in cached:
        src=index[name][0];pkg=package_roots[owners[src]]
        artifact=pkg/'.lake/build/lib/lean'/(name.replace('.','/')+'.olean')
        if not artifact.is_file():raise VerificationError('Official cache did not supply '+name,'dependencies',6)
    for name in closure:
        if owners[index[name][0]]=='QIT':compile_module(name,'qit')
    state={'schema':1,'status':'DEPENDENCIES_READY','toolchain':TOOLCHAIN,'packages':result,
           'artifacts':artifact_inventory(libpaths,output),
           'cache_implementation':{'commit':next(p['rev'] for p in result if p['name']=='mathlib'),
              'main_sha256':sha(mathlib/'Cache/Main.lean'),'command':list(map(str,command)),
              'cwd':str(mathlib),'LEAN_SRC_PATH':env['LEAN_SRC_PATH'],'MATHLIB_CACHE_DIR':env['MATHLIB_CACHE_DIR'],
              'policy':'Default official get endpoint and trust scope; no unsafe lookup, author cache or package update.'},
           'external_import_seeds':seeds,'external_closure':[
              {'module':n,'package':owners[index[n][0]],'source_sha256':sha(index[n][0])} for n in closure],
           'compiled_from_source':compiled,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    return state

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent.parent)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--lean')
    ap.add_argument('--slots',type=Path,default=os.environ.get('LOCAL_CERTIFICATION_SLOTS'))
    ap.add_argument('--source-pool',type=Path,help='Optional explicit pristine HTTPS source clones; no .lake artifacts copied')
    ap.add_argument('--imports-json',type=Path,help='Optional list of external module imports for dependency-only preparation')
    ap.add_argument('--cache-downloads',type=Path,help='Optional explicit prior official .ltar downloads; copied to the new output, never used as own artifacts')
    a=ap.parse_args();root=a.root.resolve();output=None
    try:
        output=new_output(root,a.output);(output/'home').mkdir()
        source_before=source_identity(root)
        require_project_files(root)
        if a.cache_downloads:
            downloads=output/'cache-downloads';downloads.mkdir()
            for p in a.cache_downloads.resolve().glob('*.ltar'):
                if p.is_symlink():raise VerificationError('Symlink in supplied cache downloads')
                shutil.copy2(p,downloads/p.name)
            (output/'cache-reuse.json').write_text(json.dumps({'explicit_source':str(a.cache_downloads.resolve()),'copied_ltar_files':len(list(downloads.iterdir())),'scope':'Optional official third-party cache archives only; no first-party oleans.'},indent=2))
        lean=find_lean(root,a.lean);locks=(a.slots or output/'slots').resolve()
        with lean_slot(locks):version=subprocess.check_output([lean,'--version'],text=True).strip()
        validate_lean_version(version)
        packages=[x for x in read_json(root/'lake-manifest.json')['packages'] if x['type']=='git']
        if a.imports_json:seeds=read_json(a.imports_json)
        else:
            modules=load_modules(root);seeds=sorted({dep for r in modules.values() for dep in r['imports'] if dep not in modules})
            checks=load_checks(root)
            seeds=sorted(set(seeds)|{dep for c in checks for dep in imports((root/c['path']).read_text()) if dep not in modules})
        if not isinstance(seeds,list) or not all(isinstance(x,str) for x in seeds):raise VerificationError('Imports must be a JSON string list')
        state=prepare(root,output,lean,locks,packages,a.source_pool.resolve() if a.source_pool else None,seeds)
        if source_identity(root)!=source_before:
            raise VerificationError('Source tree changed during dependency acquisition')
        (output/'state.json').write_text(json.dumps(state,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
        print(json.dumps({'status':state['status'],'state':str(output/'state.json'),'external_modules':len(state['external_closure'])}))
        return 0
    except (VerificationError,OSError,ValueError,KeyError,subprocess.SubprocessError) as e:
        failure={'status':'FAILED','error':str(e),'exit_code':getattr(e,'code',6),'category':getattr(e,'category','dependencies')}
        if output:(output/'failure.json').write_text(json.dumps(failure,indent=2)+'\n')
        print(json.dumps(failure));return failure['exit_code']
if __name__=='__main__':raise SystemExit(main())
