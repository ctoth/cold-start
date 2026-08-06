# The full repository gate: pytest, Ruff, strict Pyright -- in that order.
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
# The mutation campaign's verdict depends only on the trusted base, the
# focused tests tools/mutate.py runs per mutant, and the tool itself. When
# the change set (working tree, index, untracked, and the last commit)
# touches none of those, the previous campaign's kill remains valid and the
# stage is skipped -- LOUDLY, never silently. GATE_FULL=1 forces it.
$MutationScope = @(
    'cold_start/checker.py'; 'cold_start/proof.py'; 'cold_start/sequent.py'
    'cold_start/syntax.py'; 'cold_start/theory.py'; 'tools/mutate.py'
    'tests/test_checker.py'; 'tests/test_kernel_boundaries.py'
    'tests/test_theory.py'; 'tests/test_quantifiers.py'
    'tests/test_quant_soundness.py'; 'tests/test_logic.py'
    'tests/test_sorts.py'; 'tests/test_relations.py'
    'tests/test_properties.py'; 'tests/test_rings.py'
)
$Changed = @(git diff --name-only HEAD) + @(git ls-files --others --exclude-standard)
if (git rev-parse --verify -q 'HEAD~1') {
    $Changed += @(git diff --name-only 'HEAD~1..HEAD')
}
$InScope = @($Changed | Where-Object { $MutationScope -contains $_ })
if ($env:GATE_FULL -eq '1' -or $InScope.Count -gt 0) {
    Invoke-Gate -Label 'trusted-base mutation campaign' -Command @(
        'uv', 'run', 'python', 'tools/mutate.py'
    )
} else {
    Write-Host 'trusted-base mutation campaign SKIPPED (change set outside trusted base; GATE_FULL=1 forces it)' -ForegroundColor Yellow
}

Write-Host 'GATE GREEN' -ForegroundColor Green
