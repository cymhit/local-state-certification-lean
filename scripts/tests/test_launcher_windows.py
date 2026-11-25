"""Native Windows launcher behavior; all WSL responses are mocked, no WSL launches."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / 'verify.ps1'
WRAPPER = r'''
function Get-Command {
    param($Name, $ErrorAction)
    if ($env:MOCK_SCENARIO -eq 'missing_wsl') { return $null }
    Microsoft.PowerShell.Core\Get-Command $Name -ErrorAction SilentlyContinue
}
function wsl.exe {
    $a = @($args)
    $global:LASTEXITCODE = 0
    if ($a[0] -eq '--list') {
        if ($env:MOCK_SCENARIO -eq 'service') {
            $global:LASTEXITCODE = -1
            'W' + [char]0 + 'S' + [char]0 + 'L/Service/ExampleDiagnostic'
        } elseif ($env:MOCK_SCENARIO -ne 'no_distro') { 'Test Linux' }
        return
    }
    if ($env:MOCK_SCENARIO -eq 'missing_tools') { $global:LASTEXITCODE = 1; 'python3 unavailable'; return }
    if ($env:MOCK_SCENARIO -eq 'path_failure') { $global:LASTEXITCODE = 7; 'conversion failed'; return }
    if ($env:MOCK_SCENARIO -eq 'launch_failure') { $global:LASTEXITCODE = 19; 'WSL service timed out'; return }
    if ($env:MOCK_SCENARIO -eq 'real_python_bootstrap') {
        $ci = [array]::IndexOf($a, '-c')
        $a[$ci + 3] = '//?/' + $env:MOCK_ENTRY.Replace('\','/')
        for ($i = $ci + 4; $i -lt $a.Count; $i++) {
            if ($a[$i] -match '^[A-Z]:') { $a[$i] = '/mock/' + $a[$i].Replace('\','/') }
        }
        $pi = [array]::IndexOf($a, 'python3')
        $pythonArgs = @($a[($pi + 1)..($a.Count - 1)])
        & $env:MOCK_PYTHON @pythonArgs
        return
    }
    $ci = [array]::IndexOf($a, '-c')
    if ($ci -ge 0) { [string]$a[$ci + 2] }
    if ($env:MOCK_SCENARIO -eq 'python_failure') { $global:LASTEXITCODE = 5 }
    '{"status":"PYTHON_RESULT","exit_code":' + $global:LASTEXITCODE + '}'
    if ($env:MOCK_SCENARIO -eq 'success') {
        if (-not (($a -join ' ') -match '\u4e2d\u6587 space')) { $global:LASTEXITCODE = 91 }
    }
}
$params = @{ Output = 'C:\test\\u4e2d\u6587 space\out'; Root = 'C:\test\\u4e2d\u6587 space\bundle'; Dependencies = '/deps/state.json' }
if ($env:MOCK_SCENARIO -eq 'unknown_distro') { $params.Distribution = 'Missing Linux' }
& $env:LAUNCHER_SCRIPT @params
exit $LASTEXITCODE
'''.replace(r'\u4e2d\u6587', '\u4e2d\u6587')


@unittest.skipUnless(os.name == 'nt', 'Windows-native PowerShell launcher tests')
class LauncherTests(unittest.TestCase):
    def run_case(self, scenario):
        temporary = tempfile.TemporaryDirectory(prefix='launcher mock ')
        self.addCleanup(temporary.cleanup)
        td = Path(temporary.name)
        wrapper = td / 'mock.ps1'
        wrapper.write_text(WRAPPER, encoding='utf-8-sig')
        entry = td / 'entry \u4e2d\u6587 space.py'
        entry.write_text("import json,sys\nassert __name__ == '__main__'\nassert any('\u4e2d\u6587 space' in arg for arg in sys.argv)\nprint(json.dumps({'status':'PYTHON_RESULT','exit_code':5}))\nraise SystemExit(5)\n", encoding='utf-8')
        (td / 'bwrap.cmd').write_text('@exit /b 0')
        env = dict(os.environ, PATH=str(td)+os.pathsep+os.environ['PATH'],
                   MOCK_SCENARIO=scenario, LAUNCHER_SCRIPT=str(SCRIPT),
                   MOCK_PYTHON=sys.executable, MOCK_ENTRY=str(entry))
        # Process-only policy for this local mock fixture; no registry/global policy change.
        result = subprocess.run(['powershell.exe', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', str(wrapper)],
                                env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
        (td / 'stdout.raw').write_bytes(result.stdout)
        (td / 'stderr.raw').write_bytes(result.stderr)
        (td / 'exit.json').write_text(json.dumps({'scenario': scenario, 'exit_code': result.returncode}))
        output = result.stdout.decode('utf-8', errors='replace')
        records = [json.loads(line) for line in output.splitlines() if line.startswith('{')]
        return result, records

    def test_environment_failures_are_structured_exit_two(self):
        for scenario in ['missing_wsl', 'no_distro', 'unknown_distro', 'service', 'missing_tools', 'path_failure', 'launch_failure']:
            with self.subTest(scenario=scenario):
                result, records = self.run_case(scenario)
                self.assertEqual(result.returncode, 2, (scenario, result.stdout, result.stderr))
                self.assertEqual(len(records), 1)
                self.assertEqual(records[0]['status'], 'FAILED')
                self.assertEqual(records[0]['phase'], 'launcher/environment')
                self.assertEqual(records[0]['category'], 'environment')
                self.assertEqual(records[0]['exit_code'], 2)
                self.assertIn('diagnostic', records[0])
                self.assertIn('native_exit_code', records[0])
                if scenario == 'service':
                    self.assertIn('ExampleDiagnostic', records[0]['diagnostic'])
                    self.assertIn('\0', records[0]['diagnostic'])
                if scenario == 'launch_failure':
                    self.assertEqual(records[0]['native_exit_code'], 19)

    def test_started_python_exit_is_preserved(self):
        result, records = self.run_case('python_failure')
        self.assertEqual(result.returncode, 5)
        self.assertEqual(records, [{'status': 'PYTHON_RESULT', 'exit_code': 5}])

    def test_automatic_selection_and_chinese_space_paths(self):
        result, records = self.run_case('success')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(records, [{'status': 'PYTHON_RESULT', 'exit_code': 0}])

    def test_native_python_bootstrap_quoting_and_exit(self):
        result, records = self.run_case('real_python_bootstrap')
        self.assertEqual(result.returncode, 5, (result.stdout, result.stderr))
        self.assertEqual(records, [{'status': 'PYTHON_RESULT', 'exit_code': 5}])


if __name__ == '__main__':
    unittest.main()
