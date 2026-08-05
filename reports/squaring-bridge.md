# The squaring seed: multiplication inside addition plus square

Scope: B1 of the decidability-boundary program, implemented by
`cold_start/squaring.py`, `cold_start/squaring_proofs.py`, and
`cold_start/squaring_bridges.py`. Every payment described here is rechecked by
`checker.check`; the Lean corpus independently replays both payments and
instantiates the target theory at the standard naturals.

## Target theory

`SQUARE_ARITHMETIC` extends PRESBURGER by one unary symbol and two recursions:

```text
sq(0)    = 0
sq(S(x)) = sq(x) + S(x+x)
```

The language contains only `0`, `S`, `+`, and `sq`. The second axiom is the
subtraction-free recurrence `(x+1)^2 = x^2 + 2x + 1`.

## Bridge

Multiplication is translated to the graph

```text
2z + sq(x) + sq(y) = sq(x+y)
```

where `2z` is literally `z+z`. No subtraction operation appears. In the bounded
standard model the graph holds exactly when `z = x*y`; the test checks every
`x,y < 5` and every candidate `z < 17`.

## Paid obligations

| obligation | proof | toll |
|---|---|---:|
| `totality:*` | induction on `y`; witness `0` at the base and `z+x` at the step | 15,186 |
| `uniqueness:*` | cancel the common square terms, then use addition-only injectivity of `z -> z+z` | 5,044 |

The bridge is 14 nodes; total toll is 20,230 proof nodes; no obligation remains
open. `double_injective` is proved by induction and a zero/successor split, not
by importing multiplication cancellation.

The tests walk every graph and payment node. Their complete function vocabulary
is a subset of `{0, S, +, sq}`; neither `*` nor `-` occurs in the artifact.

## Lean cash-out

The exact model registry interprets `sq` as `(fun n => Nat.mul n n)`. Lean core
pays the successor recursion with `Nat.succ_mul`, `Nat.mul_succ`, and
`Nat.add_assoc`, so the two checked bridge payments become unconditional
theorems about standard `Nat` and its actual multiplication-based square.
Canonical interpretation variables such as `x!1` also exposed and permanently
regressed a double-quoting bug in the Lean exporter.

## Reproduce

```powershell
uv run pytest tests/test_squaring_bridges.py tests/test_lean.py -q
uv run python -m cold_start.ledger
uv run python -m cold_start.lean
```

Promotion evidence on 2026-08-05: the full owned gate passed 1,337 tests; Ruff
passed; Pyright basic reported 0 errors and 0 warnings; the generated Lean corpus
compiled and its corrupted-proof negative control was rejected.
