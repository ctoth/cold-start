# The routine full repository gate: tests, static analysis, corpus, and Lean.
# Mutation is intentionally separate: CI and explicit assurance runs invoke the
# named logical and portable campaigns in tools/mutate.py.
#
# Every native command is followed by an explicit $LASTEXITCODE test.
# $ErrorActionPreference='Stop' alone does NOT stop on a native command's
# nonzero exit (it only governs cmdlet errors); a red Ruff once slipped
# through a compound gate exactly that way. Hence the belt and suspenders.

$ErrorActionPreference = 'Stop'

function Invoke-Gate {
    param(
        [Parameter(Mandatory)] [string] $Label,
        [Parameter(Mandatory)] [string[]] $Command
    )
    Write-Host "== $Label ==" -ForegroundColor Cyan
    & $Command[0] @($Command[1..($Command.Length - 1)])
    if ($LASTEXITCODE -ne 0) {
        Write-Host "GATE FAILED at ${Label} (exit $LASTEXITCODE)" -ForegroundColor Red
        exit $LASTEXITCODE
    }
}

Invoke-Gate -Label 'pytest'  -Command @('uv', 'run', 'pytest', '-n', 'auto')
Invoke-Gate -Label 'ruff'    -Command @('uv', 'run', 'ruff', 'check', '.')
Invoke-Gate -Label 'pyright (strict)' -Command @('uv', 'run', 'pyright')
Invoke-Gate -Label 'Lean corpus generation' -Command @('uv', 'run', 'python', '-m', 'cold_start.lean')
Invoke-Gate -Label 'Lean corpus freshness' -Command @('git', 'diff', '--exit-code', '--', 'lean_export/ColdStart.lean')

$LeanToolchain = (Get-Content -LiteralPath 'lean-toolchain' -Raw).Trim()
Invoke-Gate -Label 'Lean 4 compilation' -Command @(
    'elan', 'run', $LeanToolchain, 'lean', 'lean_export/ColdStart.lean'
)

Write-Host 'GATE GREEN' -ForegroundColor Green
