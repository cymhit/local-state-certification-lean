"""Behavior tests: every fixture lives outside production proofs."""
import contextlib, hashlib, importlib.util, io, json, os, pathlib, shutil, subprocess, sys, tempfile, unittest, zipfile
from unittest.mock import patch

SCRIPT=pathlib.Path(__file__).resolve().parents[1]/'verify.py'

def expected(kind, names, name='Example', **fields):
    rows = [[n] for n in names]
    encoded = json.dumps(sorted(rows), ensure_ascii=False, separators=(',', ':')).encode()
    return dict(name=name, kind=kind, expected_records=len(rows),
                contract_sha256=hashlib.sha256(encoded).hexdigest(), **fields)


def contract_row(row):
    """Independent encoding of the expected one-row fixture contract."""
    encoded = json.dumps([row], ensure_ascii=False, separators=(',', ':')).encode()
    return hashlib.sha256(encoded).hexdigest()


def fixture_checks(root):
    checks = []
    for name, kind in CHECK_KINDS.items():
        path = f'checks/{name}.lean'
        (root/path).write_text('-- fixture\n')
        c = dict(name=name, path=path, kind=kind, expected_output_substrings=['PASS'])
        if kind != 'regression':
            c.update(expected_records=1, contract_sha256=contract_row(['example']))
        if name in {'PaperMapping', 'ProjectAxioms'}:
            c['complete_types'] = True
        checks.append(c)
    (root/'checks/checks-manifest.json').write_text(json.dumps(dict(schema=2, checks=checks)))
    return checks


class PortableVerificationTests(unittest.TestCase):
    def setUp(self):
        self.assertTrue(SCRIPT.is_file(), 'Portable verifier implementation is missing')
        spec=importlib.util.spec_from_file_location('verify', SCRIPT)
        self.v=importlib.util.module_from_spec(spec); spec.loader.exec_module(self.v)
        self.tmp=tempfile.TemporaryDirectory(prefix='verify \u4e2d\u6587 ')
        self.root=pathlib.Path(self.tmp.name)
        (self.root/'checks').mkdir()
        (self.root/'LocalCertification').mkdir()
        files={'LocalCertification.lean':'import LocalCertification.Basic\n',
               'LocalCertification/Basic.lean':'theorem good : True := True.intro\n'}
        records=[]
        for p,text in files.items():
            (self.root/p).write_text(text)
            records.append({'module':p[:-5].replace('/','.'),'path':p,'project':'main'})
        self.manifest={'schema':2,'expected_count':2,'quick_modules':['LocalCertification'],'modules':records}
        self.write_manifest()

    def tearDown(self):
        if hasattr(self,'tmp'): self.tmp.cleanup()

    def write_manifest(self):
        (self.root/'checks/module-manifest.json').write_text(json.dumps(self.manifest))

    def test_topological_order_builds_import_before_consumer(self):
        records=self.v.load_modules(self.root)
        self.assertEqual(self.v.order_modules(records), ['LocalCertification.Basic','LocalCertification'])

    def test_inconsistent_module_path_fails(self):
        self.manifest['modules'][0]['path']='LocalCertification/Other.lean'
        self.write_manifest()
        with self.assertRaises(self.v.VerificationError):
            self.v.load_modules(self.root)

    def test_editing_proof_source_updates_its_identity(self):
        previous=self.v.source_identity(self.root)
        p=self.root/'LocalCertification/Basic.lean'
        p.write_text('theorem good : True := by trivial\n')
        records=self.v.load_modules(self.root)
        self.assertEqual(records['LocalCertification.Basic']['sha256'],self.v.sha(p))
        self.assertNotEqual(previous,self.v.source_identity(self.root))

    def test_missing_module_fails(self):
        (self.root/'LocalCertification/Basic.lean').unlink()
        with self.assertRaises(self.v.VerificationError): self.v.load_modules(self.root)

    def test_unlisted_module_fails(self):
        (self.root/'LocalCertification/Hidden.lean').write_text('def hidden := 1\n')
        with self.assertRaises(self.v.VerificationError): self.v.load_modules(self.root)

    def test_omitted_manifest_record_fails(self):
        self.manifest['modules'].pop(); self.write_manifest()
        with self.assertRaises(self.v.VerificationError): self.v.load_modules(self.root)

    def test_disallowed_axiom_fails(self):
        text='AXIOM_AUDIT\t'+json.dumps({'declaration':'bad','axioms':['sorryAx']})
        with self.assertRaises(self.v.VerificationError):
            self.v.validate_check_output(expected('axioms',['bad']),text)

    def test_allowed_axioms_pass(self):
        text='AXIOM_AUDIT\t'+json.dumps({'declaration':'good','axioms':['propext','Classical.choice','Quot.sound']})
        self.v.validate_check_output(expected('axioms',['good']),text)

    def complete_type_fixture(self):
        row={'declaration':'AuditFixture.good','module':'AuditFixture.Module','axioms':['propext'],
             'type':'forall {a : Type u}, a = a','level_parameters':['u']}
        expected_row=['AuditFixture.good', hashlib.sha256(row['type'].encode()).hexdigest(),
                      ['u'], 'AuditFixture.Module', ['propext']]
        check=dict(name='ProjectAxioms',kind='axioms',expected_records=1,complete_types=True,
                   contract_sha256=contract_row(expected_row))
        return check,row

    def test_complete_type_and_exact_owner_pass(self):
        check,row=self.complete_type_fixture()
        self.v.validate_check_output(check,'AXIOM_AUDIT\t'+json.dumps(row))

    def test_complete_type_cannot_change_with_same_identity(self):
        check,row=self.complete_type_fixture(); row['type']='True'
        with self.assertRaises(self.v.VerificationError):
            self.v.validate_check_output(check,'AXIOM_AUDIT\t'+json.dumps(row))

    def test_abbreviated_type_is_rejected_even_if_hash_matches(self):
        for omitted in ['⋯','…','...','']:
            check,row=self.complete_type_fixture();row['type']=omitted
            check['contract_sha256']=contract_row(['AuditFixture.good',hashlib.sha256(omitted.encode()).hexdigest(),
                                                  ['u'],'AuditFixture.Module',['propext']])
            with self.subTest(omitted=omitted),self.assertRaises(self.v.VerificationError):
                self.v.validate_check_output(check,'AXIOM_AUDIT\t'+json.dumps(row))

    def test_exact_owner_cannot_be_reassigned(self):
        check,row=self.complete_type_fixture();row['module']='Different.Owner'
        with self.assertRaises(self.v.VerificationError):
            self.v.validate_check_output(check,'AXIOM_AUDIT\t'+json.dumps(row))

    def test_universe_parameters_cannot_be_dropped_or_reordered(self):
        for levels in [[],['v'],['u','v'],None]:
            check,row=self.complete_type_fixture();row['level_parameters']=levels
            with self.subTest(levels=levels),self.assertRaises(self.v.VerificationError):
                self.v.validate_check_output(check,'AXIOM_AUDIT\t'+json.dumps(row))

    def check_manifest_fixture(self):
        checks=fixture_checks(self.root)
        self.v.load_checks(self.root)
        return checks

    def test_required_project_checks_cannot_be_downgraded(self):
        checks=self.check_manifest_fixture()
        for name in ['AxiomAudit','MappingStatements','ProjectAxioms','PaperMapping','ProofRoutes',
                     'EulerCertificatesRoutes','UniformConfidenceRoutes','UniformBasisComparisonRoutes',
                     'FiniteDensityReadoutRoutes']:
            mutations=[('kind','regression')]
            if name in {'ProjectAxioms','PaperMapping'}:mutations += [('complete_types',None),('complete_types',False)]
            for key,value in mutations:
                changed=json.loads(json.dumps(checks));entry=next(c for c in changed if c['name']==name)
                if value is None:entry.pop(key)
                else:entry[key]=value
                (self.root/'checks/checks-manifest.json').write_text(json.dumps({'schema':2,'checks':changed}))
                with self.subTest(name=name,key=key,value=value),self.assertRaises(self.v.VerificationError):
                    self.v.load_checks(self.root)

    def test_complete_check_cannot_omit_exact_contract(self):
        checks=self.check_manifest_fixture()
        for key in ['expected_records','contract_sha256']:
            changed=json.loads(json.dumps(checks))
            next(c for c in changed if c['name']=='ProjectAxioms').pop(key)
            (self.root/'checks/checks-manifest.json').write_text(json.dumps({'schema':2,'checks':changed}))
            with self.subTest(key=key),self.assertRaises(self.v.VerificationError):
                self.v.load_checks(self.root)

    def test_allowed_axiom_change_is_detected_in_complete_contract(self):
        check,row=self.complete_type_fixture()
        row['axioms']=['Classical.choice']
        with self.assertRaises(self.v.VerificationError):
            self.v.validate_check_output(check,'AXIOM_AUDIT\t'+json.dumps(row))

    def test_public_alias_target_change_is_detected(self):
        check=dict(name='PaperMapping',kind='mapping',expected_records=1,complete_types=True,
                   contract_sha256=contract_row(['Sample',hashlib.sha256(b'True').hexdigest(),[],'Expected']))
        row=dict(declaration='Sample',type='True',level_parameters=[],target='Other')
        with self.assertRaises(self.v.VerificationError):
            self.v.validate_check_output(check,'MAPPING_CHECK\t'+json.dumps(row))

    def test_proof_route_cannot_drop_required_or_forbidden_edge(self):
        check=dict(name='ProofRoutes',kind='routes',expected_records=1,
                   contract_sha256=contract_row(['sample',['Lemma'],['Unrelated']]))
        for required,forbidden in [([],['Unrelated']),(['Lemma'],[])]:
            with self.subTest(required=required,forbidden=forbidden),self.assertRaises(self.v.VerificationError):
                row=dict(id='sample',required=required,forbidden=forbidden,passed=True)
                self.v.validate_check_output(check,'ROUTE_CHECK\t'+json.dumps(row))

    def test_missing_route_fails(self):
        with self.assertRaises(self.v.VerificationError):
            self.v.validate_check_output(expected('routes',['route1']),'unrelated success')

    def test_false_route_fails(self):
        with self.assertRaises(self.v.VerificationError):
            self.v.validate_check_output(expected('routes',['route1']),'ROUTE_CHECK\t{"id":"route1","passed":false}')

    def test_failing_child_exit_is_not_pass(self):
        log=self.root/'child.log'
        with self.assertRaises(self.v.VerificationError):
            self.v.run_logged([sys.executable,'-c','print("OK"); raise SystemExit(7)'],self.root,log)
        self.assertIn('OK',log.read_text())

    def test_nested_comment_fake_import_is_ignored(self):
        source='/- import Bad\n /- nested -/\n-/\npublic import Good.One\nimport Good.Two -- comment\ndef s := "import Bad"\n'
        self.assertEqual(self.v.imports(source),['Good.One','Good.Two'])

    def test_javascript_import_inside_lean_string_is_not_dependency(self):
        source='import Lean\ndef widget := "\nimport * as React from react\n"\n'
        self.assertEqual(self.v.imports(source),['Lean'])

    def test_output_cannot_be_inside_proofs(self):
        with self.assertRaises(self.v.VerificationError):
            self.v.new_output(self.root,self.root/'output')

    def test_existing_output_cannot_be_reused(self):
        with tempfile.TemporaryDirectory() as previous:
            with self.assertRaises(self.v.VerificationError):
                self.v.new_output(self.root,pathlib.Path(previous))

    def test_installed_elan_toolchain_is_found_without_installation(self):
        if not (pathlib.Path.home()/'.elan/bin/elan').is_file():self.skipTest('Elan not installed')
        (self.root/'lean-toolchain').write_text('leanprover/lean4:v4.34.0\n')
        self.assertTrue(self.v.find_lean(self.root).is_file())

    def test_added_nonmodule_file_changes_tree_identity(self):
        old=self.v.source_identity(self.root)
        (self.root/'LocalCertification/notes.txt').write_text('new')
        self.assertNotEqual(old,self.v.source_identity(self.root))

    def test_git_metadata_and_lake_build_cache_do_not_change_identity(self):
        old=self.v.source_identity(self.root)
        (self.root/'.git').write_text('gitdir: elsewhere\n')
        self.assertEqual(old,self.v.source_identity(self.root))
        (self.root/'.git').unlink()
        for name in ['.git','.lake','support/gaussian/.lake']:
            d=self.root/name/'nested'
            d.mkdir(parents=True)
            (d/'Ignored.lean').write_text('-- generated\n')
        self.assertEqual(old,self.v.source_identity(self.root))
        self.assertEqual(len(self.v.load_modules(self.root)),2)

    def test_unrelated_nested_cache_named_directory_cannot_hide_proof_source(self):
        d=self.root/'LocalCertification/.lake'
        d.mkdir()
        (d/'Unexpected.lean').write_text('def unexpected := 1\n')
        with self.assertRaises(self.v.VerificationError):
            self.v.load_modules(self.root)

    def test_git_checkout_and_source_zip_share_the_same_identity(self):
        shutil.copyfile(SCRIPT.parents[1]/'.gitattributes',self.root/'.gitattributes')
        env=dict(os.environ,GIT_CONFIG_NOSYSTEM='1',GIT_CONFIG_GLOBAL=os.devnull)
        def git(cwd,*args):
            subprocess.run(['git',*args],cwd=cwd,env=env,check=True,capture_output=True)
        with tempfile.TemporaryDirectory() as tmp:
            base=pathlib.Path(tmp)
            archive=base/'source.zip'
            with zipfile.ZipFile(archive,'w') as z:
                for name,path in self.v.source_files(self.root):
                    z.write(path,name)
            extracted=base/'source zip'
            with zipfile.ZipFile(archive) as z:
                z.extractall(extracted)
            identity=self.v.source_identity(extracted)
            git(self.root,'init','--quiet')
            git(self.root,'-c','core.autocrlf=false','add','.')
            git(self.root,'-c','user.name=Fixture','-c','user.email=fixture@example.invalid',
                '-c','commit.gpgsign=false','commit','--quiet','-m','fixture')
            for setting in ['false','true']:
                target=base/setting
                git(base,'clone','--quiet','--no-local','--config','core.autocrlf='+setting,str(self.root),str(target))
                self.assertEqual(identity,self.v.source_identity(target))
                self.assertEqual(set(self.v.load_modules(target)),set(self.v.load_modules(extracted)))

    def test_source_symlink_is_rejected(self):
        p=self.root/'linked'
        p.symlink_to('LocalCertification',target_is_directory=True)
        with self.assertRaises(self.v.VerificationError):
            self.v.source_identity(self.root)

    def test_mapping_count_cannot_silently_drop_declarations(self):
        with self.assertRaises(self.v.VerificationError):
            self.v.validate_check_output(expected('mapping',['one','two']),'MAPPING_CHECK\t{"declaration":"one","type":"True","level_parameters":[]}')

    def test_mapping_complete_records_pass(self):
        self.v.validate_check_output(expected('mapping',['one']),'MAPPING_CHECK\t{"declaration":"one","type":"True","level_parameters":[]}')

    def test_right_count_wrong_identity_fails_for_each_audit_kind(self):
        examples=[('axioms','AXIOM_AUDIT\t',{'declaration':'wrong','axioms':[]}),
                  ('mapping','MAPPING_CHECK\t',{'declaration':'wrong','type':'True','level_parameters':[]}),
                  ('routes','ROUTE_CHECK\t',{'id':'wrong','passed':True})]
        for kind,marker,row in examples:
            with self.subTest(kind=kind),self.assertRaises(self.v.VerificationError):
                self.v.validate_check_output(expected(kind,['required']),marker+json.dumps(row))

    def test_matching_identity_set_can_be_reported_in_different_order(self):
        text='ROUTE_CHECK\t{"id":"second","passed":true}\nROUTE_CHECK\t{"id":"first","passed":true}'
        self.v.validate_check_output(expected('routes',['first','second']),text)

    def test_load_checks_rejects_missing_malformed_or_empty_contract(self):
        checks=self.check_manifest_fixture()
        for kind in ['axioms','routes','mapping']:
            for count,digest in [(1,None),(1,''),(1,'xyz'),(1,'0'*63),(0,'0'*64),(True,'0'*64)]:
                with self.subTest(kind=kind,count=count,digest=digest):
                    candidate=json.loads(json.dumps(checks))
                    target=next(c for c in candidate if c['kind']==kind)
                    target.update(expected_records=count,contract_sha256=digest)
                    (self.root/'checks/checks-manifest.json').write_text(json.dumps({'schema':2,'checks':candidate}))
                    with self.assertRaises(self.v.VerificationError):
                        self.v.load_checks(self.root)

    def test_duplicate_identities_rejected_with_matching_count(self):
        row='ROUTE_CHECK\t'+json.dumps(dict(id='first',passed=True))
        with self.assertRaises(self.v.VerificationError):
            self.v.validate_check_output(expected('routes',['first','second']),row+'\n'+row)

    def test_changed_dependency_artifact_is_rejected(self):
        library=self.root/'package/lib';library.mkdir(parents=True)
        (library/'Example.olean').write_bytes(b'original')
        inventory=self.v.artifact_inventory([library],self.root)
        (library/'Example.olean').write_bytes(b'changed')
        with self.assertRaises(self.v.VerificationError):self.v.validate_artifacts(inventory,[library],self.root)

    def test_extra_dependency_artifact_is_rejected(self):
        library=self.root/'package/lib';library.mkdir(parents=True)
        inventory=self.v.artifact_inventory([library],self.root)
        (library/'Unexpected.olean').write_bytes(b'new')
        with self.assertRaises(self.v.VerificationError):self.v.validate_artifacts(inventory,[library],self.root)

    def test_missing_dependency_artifact_is_rejected(self):
        library=self.root/'package/lib';library.mkdir(parents=True)
        artifact=library/'Example.olean';artifact.write_bytes(b'original')
        inventory=self.v.artifact_inventory([library],self.root)
        artifact.unlink()
        with self.assertRaises(self.v.VerificationError):self.v.validate_artifacts(inventory,[library],self.root)

    def test_release_lean_version_is_accepted(self):
        self.v.validate_lean_version('Lean (version 4.34.0, x86_64-unknown-linux-gnu, commit example, Release)')

    def test_release_candidate_lean_version_is_rejected(self):
        with self.assertRaises(self.v.VerificationError):self.v.validate_lean_version('Lean (version 4.34.0-rc1, Release)')

    def test_nightly_lean_version_is_rejected(self):
        with self.assertRaises(self.v.VerificationError):self.v.validate_lean_version('Lean (version 4.34.0-nightly, Release)')

CHECK_KINDS = {
    'EulerCertificatesRoutes': 'routes', 'UniformConfidenceRoutes': 'routes',
    'UniformBasisComparisonRoutes': 'routes', 'FiniteDensityReadoutRoutes': 'routes',
    'EulerMomentBoundaries': 'regression', 'TerminalInformationBoundaries': 'regression',
    'FinitePrefixBoundaries': 'regression', 'IncidentHolderBoundaries': 'regression',
    'GeometricDecayRegression': 'regression', 'GlobalProjectorRegression': 'regression',
    'CanonicalCertificateRuntime': 'regression', 'StagedSearchRuntime': 'regression',
    'AxiomAudit': 'axioms', 'MappingStatements': 'mapping',
    'FixedBlockSameEventRegression': 'regression', 'FixedBlockSameEventConsequences': 'regression',
    'ToleranceHierarchyStatements': 'regression', 'HaarStatements': 'regression',
    'NearCriticalStatements': 'regression', 'FixedBlockStatements': 'regression',
    'MeasurementModelRegression': 'regression', 'ExecutionRegression': 'regression',
    'UniverseRegression': 'regression', 'CommonEventRegression': 'regression',
    'ProjectAxioms': 'axioms', 'PaperMapping': 'mapping', 'ProofRoutes': 'routes',
    'GaussianBridgeReplacement': 'regression',
    'DimensionCriticalValues': 'regression', 'WienerInterpolation': 'regression',
    'AlternatingBinomial': 'regression', 'PaperNotation': 'regression',
}


class ReceiptStatusTests(unittest.TestCase):
    def setUp(self):
        spec = importlib.util.spec_from_file_location('receipt_verifier', SCRIPT)
        self.v = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.v)
        self.temp = tempfile.TemporaryDirectory(prefix='receipt \u4e2d\u6587 ')
        self.base = pathlib.Path(self.temp.name)
        self.root = self.base / 'source'
        (self.root / 'checks').mkdir(parents=True)
        (self.root / 'LocalCertification').mkdir()
        for name in self.v.PROJECT_FILES:
            path=self.root/name
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text(self.v.TOOLCHAIN+'\n' if path.name=='lean-toolchain' else 'fixture\n')
        modules = []
        for i in range(3):
            rel = 'LocalCertification/Paper.lean' if i == 0 else f'LocalCertification/Fixture{i}.lean'
            p = self.root / rel
            p.write_text('-- isolated test fixture\n')
            modules.append({'module': rel[:-5].replace('/', '.'), 'path': rel,
                            'project': 'main'})
        (self.root / 'checks/module-manifest.json').write_text(json.dumps({
            'schema': 2, 'expected_count': 3, 'quick_modules': ['LocalCertification.Paper'],
            'modules': modules}))
        fixture_checks(self.root)
        (self.root / 'lake-manifest.json').write_text('{"packages": []}\n')
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.0\n')
        self.lean = self.base / 'lean'
        self.lean.write_text('#!/bin/sh\nprintf "Lean (version 4.34.0, Release)\\n"\n')
        self.lean.chmod(0o755)
        self.dependencies = self.base / 'state.json'
        self.dependencies.write_text(json.dumps({'status': 'DEPENDENCIES_READY',
            'toolchain': 'leanprover/lean4:v4.34.0', 'packages': [], 'artifacts': {}}))

    def tearDown(self):
        self.temp.cleanup()

    def run_mode(self, mode, build_failure=None):
        output = self.base / ('output-' + mode)
        argv = ['verify.py', '--root', str(self.root), '--mode', mode, '--output', str(output),
                '--dependencies', str(self.dependencies), '--lean', str(self.lean)]
        # Replace the compiler boundary only. Input validation and receipts remain active.
        def completed_build(root, out, lean, paths, records, selected, checks, jobs, locks):
            if build_failure:
                raise self.v.VerificationError(build_failure, 'build', 4)
            return ([{'module': name} for name in selected],
                    [{'name': c['name'], 'kind': c['kind'], 'exit_code': 0} for c in checks])
        with patch.object(sys, 'argv', argv), patch.object(self.v, 'build', side_effect=completed_build), contextlib.redirect_stdout(io.StringIO()):
            code = self.v.main()
        return code, json.loads((output / 'receipt.json').read_text())

    def test_full_success_records_the_verified_scope(self):
        code, receipt = self.run_mode('full')
        self.assertEqual(code, 0)
        self.assertEqual(receipt['status'], 'TECHNICALLY_VERIFIED')
        self.assertEqual(receipt.get('technical_verification'), 'TECHNICALLY_VERIFIED')
        self.assertEqual(receipt['selected_module_count'], 3)
        self.assertEqual({c['name'] for c in receipt['checks']}, set(CHECK_KINDS))

    def test_module_inventory_can_include_additional_modules(self):
        path = self.root / 'checks/module-manifest.json'
        manifest = json.loads(path.read_text())
        source = self.root / 'LocalCertification/Additional.lean'
        source.write_text('-- another module\n')
        manifest['modules'].append({'module': 'LocalCertification.Additional',
            'path': 'LocalCertification/Additional.lean', 'project': 'main'})
        manifest['expected_count'] = len(manifest['modules'])
        path.write_text(json.dumps(manifest))
        code, receipt = self.run_mode('inspect')
        self.assertEqual(code, 0, receipt.get('error'))
        self.assertEqual(receipt['module_count'], manifest['expected_count'])
        self.assertEqual(receipt['status'], 'INTEGRITY_CHECKED_ONLY')

    def test_wrong_expected_module_count_is_rejected(self):
        path=self.root/'checks/module-manifest.json'
        manifest=json.loads(path.read_text())
        for count in [None,2]:
            with self.subTest(count=count):
                manifest['expected_count']=count
                path.write_text(json.dumps(manifest))
                with self.assertRaises(self.v.VerificationError):
                    self.v.load_modules(self.root)

    def test_unlisted_source_is_rejected(self):
        (self.root / 'LocalCertification/Unlisted.lean').write_text('-- unlisted source\n')
        code, receipt = self.run_mode('inspect')
        self.assertEqual(code, 3)
        self.assertEqual(receipt['status'], 'FAILED')
        self.assertIn('Module inventory mismatch', receipt['error'])

    def test_missing_public_correspondence_table_is_detected(self):
        (self.root/'docs/paper-map.tsv').unlink()
        code,receipt=self.run_mode('inspect')
        self.assertEqual(code,3)
        self.assertIn('docs/paper-map.tsv',receipt['error'])

    def test_missing_source_is_rejected(self):
        (self.root / 'LocalCertification/Fixture1.lean').unlink()
        code, receipt = self.run_mode('inspect')
        self.assertEqual(code, 3)
        self.assertEqual(receipt['status'], 'FAILED')
        self.assertIn('Missing module', receipt['error'])

    def test_partial_scopes_cannot_report_full_technical_acceptance(self):
        for mode, expected in [('quick', 'QUICK_CHECK_ONLY'), ('inspect', 'INTEGRITY_CHECKED_ONLY')]:
            with self.subTest(mode=mode):
                code, receipt = self.run_mode(mode)
                self.assertEqual(code, 0)
                self.assertEqual(receipt.get('technical_verification'), expected)
                self.assertEqual(receipt['status'], expected)
        
    def test_compiler_failure_keeps_failed_exit(self):
        code, receipt = self.run_mode('full', build_failure='fixture compiler rejected source')
        self.assertEqual(code, 4)
        self.assertEqual(receipt['status'], 'FAILED')
        self.assertEqual(receipt.get('technical_verification'), 'FAILED')

    def test_integrity_failure_keeps_failed_exit(self):
        (self.root / 'LocalCertification/Paper.lean').unlink()
        code, receipt = self.run_mode('inspect')
        self.assertEqual(code, 3)
        self.assertEqual(receipt['status'], 'FAILED')
        self.assertEqual(receipt.get('technical_verification'), 'FAILED')

    def test_concurrent_source_change_is_detected(self):
        original=self.v.load_checks
        def mutate_source(root):
            checks=original(root)
            (root/'LocalCertification/Paper.lean').write_text('-- concurrent host edit\n')
            return checks
        with patch.object(self.v,'load_checks',side_effect=mutate_source):
            code,receipt=self.run_mode('inspect')
        self.assertEqual(code,3)
        self.assertEqual(receipt['status'],'FAILED')
        self.assertFalse(receipt['source_unchanged'])
        self.assertIn('Source tree changed during verification',receipt['error'])

    def test_missing_check_file_is_rejected_before_acceptance(self):
        (self.root / 'checks/GaussianBridgeReplacement.lean').unlink()
        code, receipt = self.run_mode('full')
        self.assertEqual(code, 3)
        self.assertEqual(receipt['status'], 'FAILED')
        self.assertIn('Missing or inconsistent check', receipt['error'])

    def test_reduced_check_inventory_is_rejected(self):
        path = self.root / 'checks/checks-manifest.json'
        manifest = json.loads(path.read_text())
        removed = manifest['checks'].pop()
        (self.root / removed['path']).unlink()
        path.write_text(json.dumps(manifest))
        code, receipt = self.run_mode('full')
        self.assertEqual(code, 3)
        self.assertEqual(receipt['status'], 'FAILED')
        self.assertEqual(receipt.get('technical_verification'), 'FAILED')
        self.assertIn('Check inventory mismatch', receipt['error'])

    def test_renamed_check_is_rejected(self):
        path = self.root / 'checks/checks-manifest.json'
        manifest = json.loads(path.read_text())
        entry = next(c for c in manifest['checks'] if c['name'] == 'GaussianBridgeReplacement')
        entry['name'] = 'RenamedCheck'
        path.write_text(json.dumps(manifest))
        code, receipt = self.run_mode('full')
        self.assertEqual(code, 3)
        self.assertEqual(receipt['status'], 'FAILED')
        self.assertIn('GaussianBridgeReplacement', receipt['error'])

    def test_same_count_substitution_cannot_drop_s22_regression(self):
        path = self.root / 'checks/checks-manifest.json'
        manifest = json.loads(path.read_text())
        entry = next(c for c in manifest['checks'] if c['name'] == 'FixedBlockSameEventRegression')
        (self.root / entry['path']).unlink()
        entry.update(name='UnrelatedRegression', path='checks/UnrelatedRegression.lean')
        replacement = self.root / entry['path']
        replacement.write_text('-- different isolated test fixture\n')
        path.write_text(json.dumps(manifest))
        code, receipt = self.run_mode('full')
        self.assertEqual(code, 3)
        self.assertEqual(receipt['status'], 'FAILED')
        self.assertIn('FixedBlockSameEventRegression', receipt['error'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
