# lean.py export — working notes

## State
- Step 1 DONE + committed (01b825e): `cold_start/lean.py` renders terms/formulas/statements
  to Lean 4 text. `render_statement` ∀-closes free vars in **lexicographic** order, keeping
  the original variable names (readability + lets the proof body use σ = identity).
- Step 2 DONE (green, 25 tests; ruff+pyright clean; about to commit): iterative Pratt parser
  for the emitted statement fragment (mirrors `notation._Parser`), round-trip tests incl. a
  hypothesis property test. Gotchas hit and fixed:
  * application must bind tighter than `=`: `_P_APP` had to be 4 (above `_P_EQ`+1=3), else
    `zero = succ zero` parsed `succ` with no argument.
  * a shadowing binder (`∀ x, ∀ x, ...`) would make `forall()` steal the outer binder's
    occurrences -> rejected explicitly (we never emit shadowing names).
- Step 3 GREEN (37 tests pass, ruff clean); eyeballed the four exported theorems and they
  look right. Remaining before commit: 11 pyright errors, all "substitute() returns Node,
  Formula expected" -> fix by making `substitute` generic (TypeVar bound=Node).
- Step 3 detail: proof export written (`export_theorem`, `_Export` dataclass with one
  handler method per rule, dispatched through a dict — presentation stays out of proof.py,
  mirroring notation.py's `_emit`). Tests written (red), implementation just typed in,
  not yet run. Coordinator confirmed the Lean 3.4.2-only finding.
- Step 3 COMMITTED as 1f07e98 (full suite green, ruff+pyright clean). Fixed pyright by making
  `substitute` generic over a `_N = TypeVar(bound=Node)`.
- Step 4 GREEN: 42 tests in tests/test_lean.py (41 pass, 1 skip = the Lean compile probe,
  whose skip message reads "no Lean 4 toolchain on PATH (found: Lean (version 3.4.2, ...))").
  `lean_export/ColdStart.lean` generated via `uv run python -m cold_start.lean`; a test
  asserts the committed file equals `export_corpus()`. ruff + pyright clean.
  NOTE for the report: the corpus was NOT kernel-checked here (Lean 3 only, no elan).
- Step 4 implementation typed in (`_Style` for the Nat re-render, `export_corpus`,
  `write_corpus`, `nat_example`, header/epilogue text); about to run the tests and add the
  `__main__` block. Not yet green.
- Step 4 earlier (red): corpus tests written (incl. an "is the committed file up to date"
  test and the Lean-4-only compile probe). Implementation next: `export_corpus`,
  `write_corpus`, `CORPUS_PATH`, `CORPUS_NAMES`, `__main__`, and a `_Style` (symbol map +
  carrier name) so the Nat epilogue can re-render the same statements with Nat.add/Nat.succ.
- Step 4 was: corpus emitter + `python -m cold_start.lean` + golden tests + Lean compile test.

## Key design decisions (settled)
- Proof rendering threads a **substitution env σ: name -> Term** downward. `Inst(sub, var, t)`
  = re-render `sub` under σ[var := t[σ]]. That makes `Axiom f` render as
  `ax_name σ(v1) ... σ(vk)` with v1..vk = sorted free vars of the axiom — instantiation order
  therefore must match `render_statement`'s lexicographic ∀-closure. Pin with a test.
- `Induct(var, pred, base, step)` -> `ind (fun n => pred[var:=n]) <base@σ[var:=zero]>
  (fun n ih => <step@σ[var:=n]> ih) σ(var)`.
- Cong: 1 arg -> `congrArg f h`; n args -> `congr (congrArg f h1) h2 ...`.
- Hypothesis env keyed by the σ-substituted Formula -> Lean binder name (Assume/ImpIntro).
- Everything iterative: emitters push `("emit", node, prec, scope)` items, scope carried
  by value, fresh names from a monotonic supply so no scope ever needs restoring.
- Robinson theorems stay conditional: A1 (`S a ≠ 1`) is FALSE over Nat at a := 0
  (Robinson's domain is the positive integers), so only Presburger/Peano get the ℕ epilogue.

## Environment finding (important for the final report)
- `lean --version` => **Lean (version 3.4.2)** at /c/ProgramData/chocolatey/bin/lean.
  `elan` is NOT installed. That is Lean **3**, which cannot compile a Lean 4 file.
  => The compile test must detect the major version and `pytest.skip` unless Lean 4.
  => Final report must say: Lean 4 NOT available; the corpus was NOT kernel-checked here.

## LEAN 4 VERDICT (supersedes the Lean 3 note above)
Coordinator installed Lean 4 mid-task. Probe now prefers `elan which lean` and
`%LOCALAPPDATA%\Microsoft\WinGet\Links\lean.exe` over bare `lean` (still Lean 3.4.2 on PATH).
**`lean_export/ColdStart.lean` COMPILES: Lean 4.32.2, exit code 0, no warnings** (warnings
were unused-binder ones; silenced with `set_option linter.unusedVariables false` + comment,
because every theorem takes its theory's whole axiom set). Added a negative control test:
corrupting an induction base makes Lean exit non-zero, so the passing compile has teeth.
Committed 50d0115. Full suite 395 passed, ruff + pyright clean.

## Remaining
REFACTOR pass (mandatory third TDD step): drop the duplicated `symbol_name` in favour of
`_Style.symbol`, replace the magic `params[:4]` slice, drop redundant theory imports.

## Blockers
None.
