#!/usr/bin/env python3
"""Build and check LocalCertification in a read-only Linux or WSL source tree."""
import argparse, contextlib, datetime, fcntl, hashlib, json, os, pathlib, re, shutil, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor

Path=pathlib.Path
TOOLCHAIN='leanprover/lean4:v4.34.0'
ALLOWED_AXIOMS={'propext','Classical.choice','Quot.sound'}
EXPECTED_CHECK_NAMES={
    'EulerCertificatesRoutes','UniformConfidenceRoutes','UniformBasisComparisonRoutes','FiniteDensityReadoutRoutes',
    'EulerMomentBoundaries','TerminalInformationBoundaries','FinitePrefixBoundaries','IncidentHolderBoundaries',
    'GeometricDecayRegression','GlobalProjectorRegression','CanonicalCertificateRuntime','StagedSearchRuntime',
    'AxiomAudit','MappingStatements','FixedBlockSameEventRegression','FixedBlockSameEventConsequences',
    'GaussianBridgeReplacement',
    'ToleranceHierarchyStatements','HaarStatements','NearCriticalStatements','FixedBlockStatements',
    'MeasurementModelRegression','ExecutionRegression','UniverseRegression','CommonEventRegression',
    'ProjectAxioms','PaperMapping','ProofRoutes',
    'DimensionCriticalValues','WienerInterpolation',
    'AlternatingBinomial','PaperNotation',
}
REQUIRED_CHECK_CONTRACTS={
    'AxiomAudit':('axioms',False),
    'MappingStatements':('mapping',False),
    'ProjectAxioms':('axioms',True),
    'PaperMapping':('mapping',True),
    'ProofRoutes':('routes',False),
    'EulerCertificatesRoutes':('routes',False),
    'UniformConfidenceRoutes':('routes',False),
    'UniformBasisComparisonRoutes':('routes',False),
    'FiniteDensityReadoutRoutes':('routes',False),
}
PROJECT_FILES = (
    '.gitattributes', '.gitignore', 'README.md', 'LICENSE', 'THIRD_PARTY_NOTICES.md',
    'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'docs/paper-map.tsv',
    'support/gaussian/lean-toolchain', 'support/gaussian/lakefile.toml', 'support/gaussian/lake-manifest.json',
    'scripts/verify.py', 'scripts/verify.ps1', 'scripts/acquire.py', 'scripts/inspect_paper_row.py',
)

class VerificationError(Exception):
    def __init__(self,message,category='integrity',code=3):
        super().__init__(message); self.category=category; self.code=code

def read_json(path):
    try: return json.loads(Path(path).read_text(encoding='utf-8-sig'))
    except (ValueError,OSError) as e: raise VerificationError(f'Cannot read JSON {path}: {e}') from e

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''): h.update(b)
    return h.hexdigest()

def safe_path(root,name):
    p=pathlib.PurePosixPath(name)
    if p.is_absolute() or '..' in p.parts or '\\' in name or not name:
        raise VerificationError(f'Unsafe relative path: {name}')
    result=root.joinpath(*p.parts)
    if any(x.is_symlink() for x in [result,*result.parents] if x!=root.parent):
        raise VerificationError(f'Symlink in input path: {name}')
    if root.resolve() not in result.resolve().parents:
        raise VerificationError(f'Escaping input path: {name}')
    return result

def imports(text):
    # Nested block comments are legal Lean syntax. Preserve newlines while removing them.
    out=[]; i=0; depth=0; in_string=False
    while i<len(text):
        if depth:
            if text.startswith('/-',i): depth+=1; i+=2
            elif text.startswith('-/',i): depth-=1; i+=2
            else:
                if text[i]=='\n': out.append('\n')
                i+=1
        elif not in_string and text.startswith('/-',i): depth=1; i+=2
        elif not in_string and text.startswith('--',i):
            end=text.find('\n',i); i=len(text) if end<0 else end
        else:
            c=text[i]; out.append(c)
            if c=='"' and (i==0 or text[i-1]!='\\'): in_string=not in_string
            i+=1
    clean=''.join(out)
    result=[]
    for line in clean.splitlines():
        if not line.strip() or line.strip() in {'module','prelude'}:continue
        m=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.*)$',line)
        if m:
            result.extend(x for x in m[1].split() if x!='all')
        else:break  # Lean imports belong to the header, never to widget/string bodies.
    return result

def source_files(root):
    """Walk the source tree without entering Git metadata or Lake build trees."""
    artifacts = {'.git', '.lake', 'support/gaussian/.lake'}
    for base, dirs, files in os.walk(root, followlinks=False, onerror=raise_walk_error):
        base = Path(base)
        for name in dirs.copy():
            path = base / name
            rel = path.relative_to(root).as_posix()
            if rel in artifacts or name == '__pycache__' and 'scripts' == path.relative_to(root).parts[0]:
                dirs.remove(name)
            elif path.is_symlink():
                raise VerificationError(f'Source directory is a symbolic link: {rel}')
        for name in files:
            path = base / name
            rel = path.relative_to(root).as_posix()
            if rel == '.git':  # Linked Git worktrees store a file here.
                continue
            if path.is_symlink() or not path.is_file():
                raise VerificationError(f'Expected a regular source file: {rel}')
            yield rel, path

def raise_walk_error(error):
    raise error

def source_identity(root):
    """Bind each relative path to its bytes, with unambiguous record boundaries."""
    files = sorted((rel, sha(path)) for rel, path in source_files(root))
    return hashlib.sha256(json.dumps(files, ensure_ascii=False, separators=(',', ':')).encode()).hexdigest()

def require_project_files(root):
    for name in PROJECT_FILES:
        if not safe_path(root, name).is_file():
            raise VerificationError(f'Missing project file: {name}')
    for name in ('lean-toolchain', 'support/gaussian/lean-toolchain'):
        if (root/name).read_text(encoding='utf-8').strip() != TOOLCHAIN:
            raise VerificationError(f'Unexpected toolchain in {name}')

def load_modules(root):
    data=read_json(root/'checks/module-manifest.json')
    if data.get('schema')!=2 or not isinstance(data.get('modules'),list):
        raise VerificationError('Unsupported module manifest schema')
    if len(data['modules'])!=data.get('expected_count') or not data['modules']:
        raise VerificationError('Module count does not match required inventory')
    records={}; paths=set()
    for rec in data['modules']:
        if not all(k in rec for k in ['module','path','project']):
            raise VerificationError('Incomplete module record')
        name=rec['module']; rel=rec['path']; project=rec['project']
        if project not in ['main','adapter']: raise VerificationError('Unknown module project')
        expected=('support/gaussian/' if project=='adapter' else '')+name.replace('.','/')+'.lean'
        if expected!=rel or name in records or rel in paths:
            raise VerificationError(f'Duplicate or inconsistent module/path: {name}')
        p=safe_path(root,rel)
        if not p.is_file():
            raise VerificationError(f'Missing module: {rel}')
        records[name]={**rec,'sha256':sha(p),'imports':imports(p.read_text(encoding='utf-8-sig'))}
        paths.add(rel)
    discovered=set()
    for rel, p in source_files(root):
        if p.suffix=='.lean' and not rel.startswith('checks/'):
            discovered.add(rel)
    if discovered!=paths:
        raise VerificationError(f'Module inventory mismatch; unlisted={sorted(discovered-paths)}, missing={sorted(paths-discovered)}')
    return records

def order_modules(records,seeds=None):
    ordered=[]; seen=set(); active=set()
    def visit(name):
        if name in seen:return
        if name in active:raise VerificationError(f'Import cycle at {name}')
        if name not in records:raise VerificationError(f'Missing selected module: {name}')
        active.add(name)
        for dependency in records[name]['imports']:
            if dependency in records:visit(dependency)
        active.remove(name); seen.add(name); ordered.append(name)
    for name in sorted(seeds if seeds is not None else records):visit(name)
    return ordered

def contract_digest(rows):
    """Hash the canonical, order-independent statement/route contract."""
    encoded = json.dumps(sorted(rows, key=lambda row: row[0]), ensure_ascii=False, separators=(',', ':'))
    return hashlib.sha256(encoded.encode('utf-8')).hexdigest()


def load_checks(root):
    data = read_json(root / 'checks/checks-manifest.json')
    checks = data.get('checks')
    if data.get('schema') != 2 or not isinstance(checks, list) or not checks:
        raise VerificationError('Missing check inventory')
    names = set()
    paths = set()
    for check in checks:
        name = check.get('name')
        kind = check.get('kind')
        if kind not in {'axioms', 'routes', 'mapping', 'regression'} or not isinstance(name, str):
            raise VerificationError('Unknown check')
        if name in names or not re.fullmatch(r'[A-Za-z0-9_.-]+', name):
            raise VerificationError(f'Duplicate or invalid check name: {name}')
        rel = check.get('path')
        if rel != f'checks/{name}.lean' or not safe_path(root, rel).is_file():
            raise VerificationError(f'Missing or inconsistent check path for {name}: {rel}')
        check['sha256'] = sha(root / rel)
        required_kind, complete = REQUIRED_CHECK_CONTRACTS.get(name, ('regression', False))
        if kind != required_kind or complete and check.get('complete_types') is not True:
            raise VerificationError(f'Required check contract cannot be downgraded: {name}')
        if kind != 'regression':
            count = check.get('expected_records')
            digest = check.get('contract_sha256')
            if type(count) is not int or count < 1 or not isinstance(digest, str) or not re.fullmatch('[a-f0-9]{64}', digest):
                raise VerificationError(f'Expected a positive record count and a statement contract for {name}')
        markers = check.get('expected_output_substrings')
        if not isinstance(markers, list) or not markers or not all(isinstance(s, str) and s for s in markers):
            raise VerificationError(f'Expected explicit output markers for {name}')
        names.add(name)
        paths.add(rel)
    actual = {p.relative_to(root).as_posix() for p in (root / 'checks').rglob('*.lean')}
    if actual != paths:
        raise VerificationError('Unlisted or missing Lean check modules')
    if names != EXPECTED_CHECK_NAMES:
        raise VerificationError(f'Check inventory mismatch: missing={sorted(EXPECTED_CHECK_NAMES-names)}, unexpected={sorted(names-EXPECTED_CHECK_NAMES)}')
    return checks


def string_list(row, field):
    items = row.get(field)
    if not isinstance(items, list) or any(not isinstance(s, str) or not s for s in items):
        raise VerificationError(f'Invalid string list in check record: {field}', 'check', 5)
    if len(items) != len(set(items)):
        raise VerificationError(f'Duplicate entries in check record: {field}', 'check', 5)
    return items


def check_projection(check, row):
    kind = check['kind']
    name = row.get('id' if kind == 'routes' else 'declaration')
    if not isinstance(name, str) or not name:
        raise VerificationError('Missing check identity', kind, 5)
    projection = [name]
    if kind == 'routes':
        if row.get('passed') is not True:
            raise VerificationError(f'Failed proof route: {name}', kind, 5)
        if check['name'] == 'ProofRoutes':
            projection.extend([sorted(string_list(row, 'required')), sorted(string_list(row, 'forbidden'))])
        return projection
    if kind == 'axioms':
        axioms = string_list(row, 'axioms')
        if set(axioms) - ALLOWED_AXIOMS:
            raise VerificationError(f'Disallowed axioms on {name}: {sorted(set(axioms)-ALLOWED_AXIOMS)}', kind, 5)
    if kind == 'mapping' or check.get('complete_types'):
        ty = row.get('type')
        if not isinstance(ty, str) or not ty.strip():
            raise VerificationError(f'Missing type: {name}', kind, 5)
        levels = string_list(row, 'level_parameters')
        if check.get('complete_types'):
            if any(mark in ty for mark in ('⋯', '…', '...')):
                raise VerificationError(f'Abbreviated type: {name}', kind, 5)
            projection.extend([hashlib.sha256(ty.encode()).hexdigest(), levels])
            field = 'module' if kind == 'axioms' else 'target'
            reference = row.get(field)
            if not isinstance(reference, str) or not reference:
                raise VerificationError(f'Missing {field}: {name}', kind, 5)
            projection.append(reference)
            if kind == 'axioms':
                projection.append(sorted(axioms))
    return projection


def validate_check_output(check, text):
    for expected in check.get('expected_output_substrings', []):
        if expected not in text:
            raise VerificationError(f'Missing expected output: {expected}', 'check', 5)
    kind = check['kind']
    if kind == 'regression':
        return
    marker = {'axioms': 'AXIOM_AUDIT', 'routes': 'ROUTE_CHECK', 'mapping': 'MAPPING_CHECK'}[kind] + '\t'
    rows = []
    for line in text.splitlines():
        if line.startswith(marker):
            try:
                row = json.loads(line[len(marker):])
            except ValueError as e:
                raise VerificationError('Malformed check record', kind, 5) from e
            if not isinstance(row, dict):
                raise VerificationError('Expected a check object', kind, 5)
            rows.append(check_projection(check, row))
    if len(rows) != check['expected_records'] or len({r[0] for r in rows}) != len(rows):
        raise VerificationError(f'Incomplete or duplicate {kind} records', kind, 5)
    if contract_digest(rows) != check['contract_sha256']:
        raise VerificationError(f'{kind} contract differs in {check["name"]}', kind, 5)


def new_output(root,output):
    output=output.expanduser().absolute()
    if output.exists() or root.resolve()==output.resolve() or root.resolve() in output.resolve().parents:
        raise VerificationError('Output must be a NEW directory outside the source bundle','environment',2)
    output.mkdir(parents=True)
    return output.resolve()

@contextlib.contextmanager
def lean_slot(directory):
    directory.mkdir(parents=True,exist_ok=True)
    handles=[(directory/f'{n}.lock').open('a+') for n in range(2)]
    selected=None
    try:
        while selected is None:
            for h in handles:
                try:fcntl.flock(h,fcntl.LOCK_EX|fcntl.LOCK_NB); selected=h; break
                except BlockingIOError:pass
            if selected is None:time.sleep(.2)
        yield
    finally:
        for h in handles:h.close()

def run_logged(command,cwd,log,env=None):
    log.parent.mkdir(parents=True,exist_ok=True)
    command=list(map(str,command))
    metadata={'command':command,'cwd':str(cwd),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    with log.open('w',encoding='utf-8') as stream:
        result=subprocess.run(command,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT)
    metadata.update(exit_code=result.returncode,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    log.with_suffix('.command.json').write_text(json.dumps(metadata,ensure_ascii=False,indent=2)+'\n')
    if result.returncode:raise VerificationError(f'Command failed ({result.returncode}); see {log}','build',4)
    return result.returncode

def find_lean(root,explicit=None):
    if (root/'lean-toolchain').read_text().strip()!=TOOLCHAIN:raise VerificationError('Unexpected Lean toolchain')
    lean=Path(explicit).expanduser().resolve() if explicit else None
    if not lean:
        elan=shutil.which('elan')
        if not elan:
            candidate=Path.home()/'.elan/bin/elan'
            if candidate.is_file():elan=str(candidate)
        if elan:
            result=subprocess.run([elan,'which','lean'],env={**os.environ,'ELAN_TOOLCHAIN':TOOLCHAIN},capture_output=True,text=True)
            if result.returncode==0:lean=Path(result.stdout.strip()).resolve()
    if not lean or not lean.is_file():raise VerificationError(f'Install {TOOLCHAIN} using Elan before verification','environment',2)
    # Version inspection itself also participates in the shared process bound.
    return lean

def validate_lean_version(version):
    if not re.search(r'\bversion 4\.34\.0(?=[,)\s]|$)',version):
        raise VerificationError('Installed Lean is not release 4.34.0','environment',2)

def sandbox_command(command,output,cwd,env,network=False):
    if not shutil.which('bwrap'):raise VerificationError('bubblewrap (bwrap) is required on Linux/WSL','environment',2)
    cmd=['bwrap','--die-with-parent','--ro-bind','/','/','--bind',str(output),str(output),
         '--proc','/proc','--dev','/dev','--chdir',str(cwd),'--clearenv']
    if not network:cmd+=['--unshare-net']
    for k,v in env.items():cmd+=['--setenv',k,str(v)]
    return cmd+list(map(str,command))

def clean_env(lean,output,paths):
    (output/'tmp').mkdir(exist_ok=True)
    return {'PATH':str(lean.parent)+':/usr/bin:/bin','HOME':str(output/'home'),
            'LEAN_PATH':':'.join(map(str,paths)),'TMPDIR':str(output/'tmp'),'LC_ALL':'C.UTF-8','TZ':'UTC'}

def artifact_inventory(paths,base):
    inventory={}
    for library in paths:
        for p in sorted(library.rglob('*')):
            if p.is_symlink():raise VerificationError('Symlink in prepared dependency artifacts: '+str(p))
            if p.is_file():inventory[p.relative_to(base).as_posix()]=sha(p)
    return inventory

def validate_artifacts(expected,paths,base):
    if not isinstance(expected,dict) or artifact_inventory(paths,base)!=expected:
        raise VerificationError('Prepared dependency artifacts are missing, changed or unlisted')

def dependency_paths(state_path,root):
    state=read_json(state_path); base=state_path.resolve().parent
    if state.get('status')!='DEPENDENCIES_READY' or state.get('toolchain')!=TOOLCHAIN:
        raise VerificationError('Dependency preparation has not passed','environment',2)
    wanted={x['name']:(x['url'],x['rev']) for x in read_json(root/'lake-manifest.json')['packages'] if x['type']=='git'}
    actual={x['name']:(x['url'],x['rev']) for x in state['packages']}
    if actual!=wanted:raise VerificationError('Dependency revisions differ from frozen Lake manifest')
    paths=[]
    for package in state['packages']:
        p=safe_path(base,package['path'])
        head=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
        if head!=package['rev']:raise VerificationError('Dependency HEAD changed: '+package['name'])
        if subprocess.run(['git','-C',str(p),'diff','--quiet','HEAD','--']).returncode:
            raise VerificationError('Tracked dependency source changed: '+package['name'])
        lib=p/'.lake/build/lib/lean'
        if not lib.is_dir():raise VerificationError('Missing dependency artifacts: '+str(lib),'environment',2)
        if any(lib.rglob('LocalCertification*.olean')) or (lib/'CertificationGaussian').exists():
            raise VerificationError('Dependency cache contains first-party artifacts')
        paths.append(lib)
    validate_artifacts(state.get('artifacts'),paths,base)
    return paths,state

def build(root,output,lean,paths,records,selected,checks,jobs,locks):
    own=output/'lib/lean'; own.mkdir(parents=True)
    env=clean_env(lean,output,[own,*paths]); (output/'home').mkdir()
    receipt=[]
    def compile_one(name):
        rec=records[name]; src=root/rec['path']; target=own/(name.replace('.','/')+'.olean')
        target.parent.mkdir(parents=True,exist_ok=True)
        cwd=root/('support/gaussian' if rec['project']=='adapter' else '.')
        command=[lean,'-j1','-s65536','-o',target,'-i',target.with_suffix('.ilean'),src]
        log=output/'logs/modules'/(name+'.log')
        with lean_slot(locks):run_logged(sandbox_command(command,output,cwd,env),cwd,log)
        if not target.is_file():raise VerificationError('Compiler did not produce '+str(target),'build',4)
        return {'module':name,'source_sha256':rec['sha256'],'olean_sha256':sha(target),'log':str(log.relative_to(output))}
    pending=set(selected); complete=set()
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending:
            ready=sorted(n for n in pending if not (set(records[n]['imports']) & pending))
            if not ready:raise VerificationError('Import graph contains a cycle')
            # Small bounded batches ensure a failing process cannot launch the rest of a large layer.
            for i in range(0,len(ready),jobs):
                for item in pool.map(compile_one,ready[i:i+jobs]):receipt.append(item)
            complete.update(ready); pending.difference_update(ready)
            (output/'build-progress.json').write_text(json.dumps({'completed':len(complete),'total':len(selected),'modules':receipt},indent=2))
    check_results=[]
    for c in checks:
        log=output/'logs/checks'/(c['name']+'.log')
        command=[lean,'-j1','-s65536',root/c['path']]
        with lean_slot(locks):run_logged(sandbox_command(command,output,root,env),root,log)
        validate_check_output(c,log.read_text(encoding='utf-8'))
        check_results.append({'name':c['name'],'kind':c['kind'],'exit_code':0,'log':str(log.relative_to(output)),'sha256':sha(log)})
    return receipt,check_results

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent.parent)
    ap.add_argument('--mode',choices=['quick','full','inspect'],default='full')
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--dependencies',type=Path,help='state.json produced by acquire.py')
    ap.add_argument('--lean',help='Explicit installed Lean executable; version still checked')
    ap.add_argument('--jobs',type=int,choices=[1,2],default=2)
    ap.add_argument('--slots',type=Path,default=os.environ.get('LOCAL_CERTIFICATION_SLOTS'))
    a=ap.parse_args(); root=a.root.resolve(); output=None
    receipt = {'mode': a.mode, 'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'status': 'FAILED', 'source_unchanged': False}
    try:
        output = new_output(root, a.output)
        receipt['source_sha256'] = source_identity(root)
        require_project_files(root)
        records = load_modules(root)
        checks = load_checks(root)
        receipt.update(module_count=len(records),check_count=len(checks))
        if a.mode=='inspect':receipt['status']='INTEGRITY_CHECKED_ONLY'
        else:
            if not a.dependencies:raise VerificationError('--dependencies is required for compilation','environment',2)
            paths,state=dependency_paths(a.dependencies,root)
            for name in records:
                relative=name.replace('.','/')+'.olean'
                if any((p/relative).exists() for p in paths):
                    raise VerificationError('Dependency path contains a delivered production module: '+name)
            lean=find_lean(root,a.lean); locks=(a.slots or output/'slots').resolve()
            with lean_slot(locks):
                version=subprocess.check_output([str(lean),'--version'],text=True).strip()
            validate_lean_version(version)
            receipt['lean_version']=version;receipt['dependency_state_sha256']=sha(a.dependencies)
            manifest=read_json(root/'checks/module-manifest.json')
            selected=order_modules(records,manifest.get('quick_modules',['LocalCertification.Paper']) if a.mode=='quick' else None)
            modules,results=build(root,output,lean,paths,records,selected,checks if a.mode=='full' else [],a.jobs,locks)
            validate_artifacts(state['artifacts'],paths,a.dependencies.resolve().parent)
            receipt.update(compiled_modules=modules,checks=results,selected_module_count=len(selected),dependency_lean_paths=list(map(str,paths)))
            receipt['status']='TECHNICALLY_VERIFIED' if a.mode=='full' else 'QUICK_CHECK_ONLY'
        if source_identity(root) != receipt['source_sha256']:
            raise VerificationError('Source tree changed during verification')
        receipt['source_unchanged']=True
        receipt['exit_code']=0
    except (VerificationError,OSError,KeyError,TypeError,ValueError,subprocess.SubprocessError) as e:
        receipt.update(status='FAILED',error=str(e),category=getattr(e,'category','environment'),exit_code=getattr(e,'code',2))
    receipt['technical_verification']=receipt['status']
    receipt['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    if output:(output/'receipt.json').write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in {'compiled_modules','checks'}},ensure_ascii=False,indent=2))
    return receipt['exit_code']

if __name__=='__main__':sys.dont_write_bytecode=True;raise SystemExit(main())
