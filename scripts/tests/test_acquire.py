import importlib.util, pathlib, subprocess, tempfile, unittest
SCRIPT=pathlib.Path(__file__).resolve().parents[1]/'acquire.py'
class AcquisitionTests(unittest.TestCase):
    def setUp(self):
        self.assertTrue(SCRIPT.is_file(),'Pinned dependency acquisition is missing')
        spec=importlib.util.spec_from_file_location('acquire',SCRIPT)
        self.a=importlib.util.module_from_spec(spec);spec.loader.exec_module(self.a)
        self.tmp=tempfile.TemporaryDirectory(prefix='deps \u4e2d\u6587 ');self.root=pathlib.Path(self.tmp.name)
    def tearDown(self):
        if hasattr(self,'tmp'):self.tmp.cleanup()
    def test_minimal_qit_closure_excludes_unused_source(self):
        files={'QIT/Used.lean':'import QIT.Base\nimport Mathlib.X\n',
               'QIT/Base.lean':'import Init\n','QIT/Unused.lean':'import QIT.DoesNotExist\n',
               'Mathlib/X.lean':'import Init\n'}
        index={}
        for path,text in files.items():
            p=self.root/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
            index[path[:-5].replace('/','.')]=[p]
        order=self.a.source_closure(index,['QIT.Used'],self.root/'core')
        self.assertEqual(order,['QIT.Base','Mathlib.X','QIT.Used'])
    def test_unknown_external_import_fails(self):
        with self.assertRaises(self.a.VerificationError):
            self.a.source_closure({},['Missing.Package'],self.root/'core')
    def test_ambiguous_external_import_fails(self):
        with self.assertRaises(self.a.VerificationError):
            self.a.source_closure({'Duplicate':[self.root/'a',self.root/'b']},['Duplicate'],self.root/'core')

    def test_public_source_pool_preserves_git_tracked_symlinks(self):
        pool=self.root/'pool';src=pool/'sample';src.mkdir(parents=True)
        subprocess.run(['git','init','--quiet',str(src)],check=True)
        (src/'target.py').write_text('print("fixture")\n')
        (src/'linked.py').symlink_to('target.py')
        subprocess.run(['git','-C',str(src),'add','.'],check=True)
        subprocess.run(['git','-C',str(src),'-c','user.name=Fixture','-c','user.email=fixture@example.invalid','commit','--quiet','-m','test fixture'],check=True)
        url='https://example.invalid/sample.git'
        subprocess.run(['git','-C',str(src),'remote','add','origin',url],check=True)
        revision=self.a.git_output(src,'rev-parse','HEAD')
        output=self.root/'out';output.mkdir();(output/'home').mkdir()
        self.a.acquire_sources([{'name':'sample','url':url,'rev':revision}],output,pool)
        copied=output/'packages/sample'
        self.assertTrue((copied/'linked.py').is_symlink())
        self.assertEqual(subprocess.run(['git','-C',str(copied),'diff','--quiet','HEAD','--']).returncode,0)

    def test_source_pool_rejects_untracked_lean_source(self):
        pool=self.root/'pool';src=pool/'sample';src.mkdir(parents=True)
        subprocess.run(['git','init','--quiet',str(src)],check=True)
        (src/'tracked').write_text('fixture')
        subprocess.run(['git','-C',str(src),'add','.'],check=True)
        subprocess.run(['git','-C',str(src),'-c','user.name=Fixture','-c','user.email=fixture@example.invalid','commit','--quiet','-m','test fixture'],check=True)
        url='https://example.invalid/sample.git';subprocess.run(['git','-C',str(src),'remote','add','origin',url],check=True)
        (src/'Injected.lean').write_text('axiom injected : False\n')
        output=self.root/'out';output.mkdir();(output/'home').mkdir()
        with self.assertRaises(self.a.VerificationError):
            self.a.acquire_sources([{'name':'sample','url':url,'rev':self.a.git_output(src,'rev-parse','HEAD')}],output,pool)

    def test_source_pool_allows_but_does_not_copy_build_cache(self):
        pool=self.root/'pool';src=pool/'sample';src.mkdir(parents=True)
        subprocess.run(['git','init','--quiet',str(src)],check=True)
        (src/'tracked').write_text('fixture')
        subprocess.run(['git','-C',str(src),'add','.'],check=True)
        subprocess.run(['git','-C',str(src),'-c','user.name=Fixture','-c','user.email=fixture@example.invalid','commit','--quiet','-m','test fixture'],check=True)
        url='https://example.invalid/sample.git';subprocess.run(['git','-C',str(src),'remote','add','origin',url],check=True)
        (src/'.lake/build').mkdir(parents=True);(src/'.lake/build/Unused.olean').write_bytes(b'not copied')
        output=self.root/'out';output.mkdir();(output/'home').mkdir()
        self.a.acquire_sources([{'name':'sample','url':url,'rev':self.a.git_output(src,'rev-parse','HEAD')}],output,pool)
        self.assertTrue((output/'packages/sample/tracked').is_file())
        self.assertFalse((output/'packages/sample/.lake').exists())
if __name__=='__main__':unittest.main(verbosity=2)
