[CmdletBinding()]
param(
    [ValidateSet('quick','full','inspect')][string]$Mode = 'full',
    [string]$Root = (Split-Path -Parent $PSScriptRoot),
    [Parameter(Mandatory=$true)][string]$Output,
    [string]$Dependencies,
    [string]$Distribution,
    [ValidateRange(1,2)][int]$Jobs = 2,
    [switch]$Acquire,
    [string]$Slots
)
$ErrorActionPreference = 'Stop'
$script:NativeExitCode = $null
$script:Diagnostics = New-Object 'System.Collections.Generic.List[string]'
$script:PythonStarted = $false
$script:StartMarker = 'LOCAL_CERTIFICATION_PYTHON_STARTED_' + [guid]::NewGuid().ToString('N')

function Invoke-Wsl([string[]]$Arguments, [switch]$StreamPython) {
    $lines = New-Object 'System.Collections.Generic.List[string]'
    # Native stderr is evidence, not a PowerShell terminating error. Keep the
    # original decoded strings (including NULs) in diagnostics; normalize only
    # when interpreting WSL's occasionally UTF-16-style list/path output.
    $savedPreference = $ErrorActionPreference
    $ErrorActionPreference = 'Continue'
    try {
        & wsl.exe @Arguments 2>&1 | ForEach-Object {
            $line = [string]$_
            $lines.Add($line)
            if ($StreamPython) {
                if ($line -eq $script:StartMarker) { $script:PythonStarted = $true }
                else { [Console]::Out.WriteLine($line) }
            }
        }
        $code = $LASTEXITCODE
    } finally { $ErrorActionPreference = $savedPreference }
    $script:NativeExitCode = $code
    foreach ($line in $lines) { $script:Diagnostics.Add($line) }
    return [pscustomobject]@{ Code = $code; Lines = @($lines.ToArray()) }
}

function Get-SourcePath([string]$Value) {
    if ($Value.StartsWith('/')) { return $Value }
    return $ExecutionContext.SessionState.Path.GetUnresolvedProviderPathFromPSPath($Value)
}

try {
    if (-not (Get-Command wsl.exe -ErrorAction SilentlyContinue)) {
        throw 'WSL is not installed. Install a Linux WSL distribution, Python 3, bubblewrap and the pinned Lean toolchain first.'
    }
    $inventory = Invoke-Wsl @('--list', '--quiet')
    if ($inventory.Code -ne 0) { throw 'WSL distribution inventory failed; consult the native diagnostic.' }
    $available = @($inventory.Lines | ForEach-Object { ($_ -replace "`0", '').Trim() } | Where-Object { $_ })
    if ($available.Count -eq 0) { throw 'No WSL distribution is available.' }
    if ($Distribution) {
        if ($Distribution -notin $available) { throw "Unknown WSL distribution: $Distribution" }
        $candidates = @($Distribution)
    } else { $candidates = $available }
    $scriptName = if ($Acquire) { 'acquire.py' } else { 'verify.py' }
    # Convert paths in the same WSL process that invokes the verifier. The marker
    # separates discovery/conversion errors from the verifier's own exit code.
    $bootstrap = @'
import runpy, shutil, subprocess, sys
if shutil.which('bwrap') is None:
    sys.exit('bubblewrap is unavailable in this distribution')
def convert(value):
    if value.startswith('/'):
        return value
    result = subprocess.run(['wslpath', '-a', '-u', value], capture_output=True)
    if result.returncode:
        sys.stderr.buffer.write(result.stderr)
        sys.exit(result.returncode)
    path = result.stdout.decode('utf-8').rstrip('\r\n')
    if not path.startswith('/'):
        sys.exit('wslpath returned a nonabsolute path')
    return path
args = sys.argv[2:]
for i, value in enumerate(args):
    if i == 0 or args[i-1] in ('--root', '--output', '--dependencies', '--slots'):
        args[i] = convert(value)
print(sys.argv[1], flush=True)
sys.argv = args
runpy.run_path(args[0], run_name='__main__')
'@
    $entry = @((Join-Path $PSScriptRoot $scriptName), '--root', (Get-SourcePath $Root),
               '--output', (Get-SourcePath $Output))
    if (-not $Acquire) {
        $entry += @('--mode', $Mode, '--jobs', [string]$Jobs)
        if ($Dependencies) { $entry += @('--dependencies', (Get-SourcePath $Dependencies)) }
    }
    if ($Slots) { $entry += @('--slots', (Get-SourcePath $Slots)) }
    foreach ($candidate in $candidates) {
        $arguments = @('--distribution', $candidate, '--cd', '/', '--exec', 'python3', '-B', '-c',
                       $bootstrap, $script:StartMarker) + $entry
        $result = Invoke-Wsl $arguments -StreamPython
        if ($script:PythonStarted) { exit $result.Code }
    }
    throw 'No selected WSL distribution started the verifier; consult the native diagnostic.'
} catch {
    # Never invent or replace a Python verification receipt. This is a separate
    # launcher/environment summary, including the native exit code when known.
    [ordered]@{
        status = 'FAILED'; phase = 'launcher/environment'; category = 'environment'
        exit_code = 2; native_exit_code = $script:NativeExitCode
        error = $_.Exception.Message; diagnostic = ($script:Diagnostics -join "`n")
        python_started = $script:PythonStarted; distribution = $Distribution
    } | ConvertTo-Json -Compress -Depth 5
    exit 2
}
