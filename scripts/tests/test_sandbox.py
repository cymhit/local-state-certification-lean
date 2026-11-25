"""Integration tests run real Lean against disposable files; never production proofs."""
import importlib.util, json, os, pathlib, sys, tempfile, unittest
sys.dont_write_bytecode=True
SCRIPT=pathlib.Path(__file__).resolve().parents[1]/'verify.py'
spec=importlib.util.spec_from_file_location('verify',SCRIPT)
v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)

class SandboxTests(unittest.TestCase):
    def test_real_lean_build_and_rejected_source_write(self):
        with tempfile.TemporaryDirectory(prefix='lean \u4e2d\u6587 ') as tmp:
            base=pathlib.Path(tmp);root=base/'proofs';root.mkdir()
            (root/'lean-toolchain').write_text(v.TOOLCHAIN+'\n')
            (root/'LocalCertification').mkdir()
            (root/'LocalCertification.lean').write_text('import LocalCertification.Basic\n')
            basic=root/'LocalCertification/Basic.lean';basic.write_text('theorem good : True := True.intro\n')
            records={name:{'module':name,'path':p,'project':'main','sha256':v.sha(root/p),'imports':v.imports((root/p).read_text())}
                     for name,p in [('LocalCertification','LocalCertification.lean'),('LocalCertification.Basic','LocalCertification/Basic.lean')]}
            out=v.new_output(root,base/'output');lean=v.find_lean(root)
            locks=pathlib.Path(os.environ.get('LOCAL_CERTIFICATION_SLOTS',str(out/'slots')))
            built,checks=v.build(root,out,lean,[],records,v.order_modules(records),[],2,locks)
            self.assertEqual({x['module'] for x in built},{'LocalCertification','LocalCertification.Basic'})
            before=basic.read_bytes()
            cmd=v.sandbox_command([sys.executable,'-c','from pathlib import Path; Path(__import__("sys").argv[1]).write_text("changed")',str(basic)],out,root,v.clean_env(lean,out,[]))
            with self.assertRaises(v.VerificationError):v.run_logged(cmd,root,out/'write-denied.log')
            self.assertEqual(basic.read_bytes(),before)

if __name__=='__main__':unittest.main(verbosity=2)
