# Notation Formatter Deletion-First Workstream - 2026-06-16

## Literal Outcome

Remove human-notation formatting ownership from `cold_start/syntax.py`.
`cold_start/notation.py` must be the only production owner of parse/print surface
notation. `syntax.py` keeps object-language data, structural operations, exact-type
validation hooks, equality/hash, substitution, sort checking, and serialization.

This workstream is complete only when the old production formatting path is gone,
the replacement path is proven by search gates and runtime gates, and old and new
formatting implementations do not coexist.

## Target Architecture

- `syntax.py` owns object-language structure and structural operations.
- `notation.py` owns human notation parsing and formatting.
- `format_term()` and `format_formula()` remain the public notation entrypoints.
- Formatting remains iterative and stack-safe.
- The parser may keep local conditionals and exact-type checks inside `notation.py`;
  this is an untrusted surface layer, not the checker trust gate.

## Forbidden Surfaces

Production code must not retain:

- `Node.format(...)`
- any `_format_push(...)` method on syntax nodes
- `_binder_format_push(...)` in `syntax.py`
- notation printer context passed into syntax nodes
- `ctx.bound`, `ctx.used`, `ctx.infix`, `ctx.name`, or `ctx.fresh` references in
  `syntax.py`
- syntax-owned infix, precedence, parenthesization, fresh-name, or surface-name
  quoting behavior
- a visitor, adapter, sender, printer protocol, compatibility wrapper, facade, or
  renamed copy of the deleted syntax formatter path

Allowed to remain in `syntax.py`:

- structural `symbol` constants on formula classes if they still simplify parser
  spelling and tests
- `__repr__` / `_repr_with`, because those are structural debug representations,
  not human notation formatting

## Slice Boundary

Single target family:

- production: `cold_start/syntax.py`, `cold_start/notation.py`
- tests/docs touched only as needed: `tests/test_notation.py`,
  `cold_start/CLAUDE.md`, `ARCHITECTURE.md`, `notes-cold-start.md`

Do not widen into proof checking, serialization, theories, package exports, or
public `__init__` surfaces.

## Search Gates

Run these before the slice starts and after each kept reduction:

```powershell
rg -n "def format|_format_push|_binder_format_push|node\.format|\.format\(" cold_start tests
rg -n "ctx\.|_Printer|infix|fresh|surface notation|human notation" cold_start\syntax.py
rg -n "adapter|visitor|protocol|compat|legacy|fallback|shim|facade" cold_start\syntax.py cold_start\notation.py
```

Completion expectations:

- `syntax.py` has zero hits for notation formatter ownership terms.
- `notation.py` may have formatter implementation hits.
- Tests may reference `format_term` / `format_formula`.
- No production compatibility layer is introduced under another name.

## Runtime Gates

Use `uv`, not bare Python or pytest:

```powershell
uv run pytest tests\test_notation.py
uv run pytest
uv run ruff check cold_start tests
uv run pyright
```

If the first full-suite run exposes unrelated failure, record it plainly and keep
the target-slice gates (`tests\test_notation.py`, ruff on touched files, pyright)
separate from unrelated repo state.

## Iteration 1 - Delete The Wrong Owner

Slice read:

- `cold_start/syntax.py`
- `cold_start/notation.py`
- `tests/test_notation.py`

Disposition:

- `Node.format`: delete.
- all concrete `_format_push` methods: delete.
- `_binder_format_push`: delete.
- `_Printer` in `notation.py`: keep only if it remains useful to the new
  notation-owned implementation; otherwise delete or shrink it.

Action:

1. Delete the syntax-owned formatter path first.
2. Run the smallest search gate to expose every remaining caller:

   ```powershell
   rg -n "def format|_format_push|_binder_format_push|node\.format|\.format\(" cold_start tests
   ```

3. Treat each failure as an ownership question, not an import-repair queue.

Breakage review:

- `format_term()` and `format_formula()` still need to exist.
- Their owner is `notation.py`.
- No syntax node should receive a notation printer context.

## Iteration 2 - Recreate Formatting In The Real Owner

Owner after cleanup:

- `cold_start/notation.py`

Disposition:

- `format_term`: rewrite to call a module-local iterative formatter.
- `format_formula`: rewrite to call the same module-local iterative formatter.
- parser code: keep unless directly affected.
- `_format_name`, `_fresh_name`, constants, and precedence tables: keep in
  `notation.py` if the formatter still uses them.

Implementation constraints:

- Keep formatting stack-safe for deeply nested implications.
- Use direct local exact-type handling in `notation.py`; do not create a generic
  visitor/protocol layer.
- Preserve output accepted by `parse_term()` and `parse_formula()`.
- Preserve binder fresh-name behavior and bound-sort suppression.
- Preserve infix precedence and parenthesization behavior.
- Keep `BVar` formatting failure behavior for dangling bound variables.

Suggested shape:

- A small explicit work stack in `notation.py`.
- Work items can be local tuples or a private dataclass if that makes the code
  clearer.
- Combine steps build strings from already-rendered child strings.
- Binder handling opens the binder with `instantiate(...)`, pushes the fresh
  surface name into the notation-owned context for the body, and restores it in
  the combine step.

Forbidden implementation moves:

- adding `format()` back under another name on `Node`, `Term`, `Formula`, or
  concrete syntax classes
- adding a formatter protocol that syntax nodes implement
- adding a syntax-side helper that receives notation state
- preserving `node.format(_Printer(...))` as a compatibility path

## Iteration 3 - Tighten Tests Around The Ownership Boundary

Keep or add focused tests in `tests/test_notation.py`:

- term round-trip property: `parse_term(format_term(term)) == term`
- formula round-trip property: `parse_formula(format_formula(formula)) == formula`
- binder sort suppression: `forall("x", "N", ...)` prints body variables without
  repeating `:N`
- quoted-name round trip
- deep formatting remains non-recursive
- direct syntax nodes do not expose a public notation formatting method

The last test should assert the architectural boundary without baking in private
formatter names. Example intent:

```python
assert not hasattr(Eq(Var("x"), Var("x")), "format")
```

Only add this if it does not conflict with another non-notation `format` need.

## Iteration 4 - Documentation Cleanup

Update docs only after production and tests pass.

Expected docs changes:

- `cold_start/CLAUDE.md`: remove or rewrite the claim that printing is a syntax
  node method.
- `ARCHITECTURE.md`: remove or rewrite the `format` item from the list of syntax
  node methods.
- `notes-cold-start.md`: append a short completion note instead of rewriting
  history.

Do not edit package exports.

## Completion Checklist

- [x] `syntax.py` has no human-notation formatter ownership.
- [x] `notation.py` owns both parse and print.
- [x] No compatibility wrapper, visitor, adapter, protocol, fallback, or renamed
  syntax formatter path exists.
- [x] `format_term()` and `format_formula()` preserve current behavior.
- [x] Deep notation formatting stays stack-safe.
- [x] Search gates pass with only expected hits.
- [x] `uv run pytest tests\test_notation.py` passes.
- [x] `uv run pytest` passes or unrelated failures are recorded separately.
- [x] `uv run ruff check cold_start tests` passes.
- [x] `uv run pyright` passes.
- [x] The kept reduction is committed before switching to a different target
  family.

## Fixed-Point Log Template

Record each kept iteration below while executing.

### Iteration 1 - `syntax.py formatter ownership`

Surfaces:

- `Node.format`
  - Disposition: delete
  - Owner after cleanup: `cold_start/notation.py`
  - Action: removed the public syntax-node notation formatting method.
  - Evidence: search gate has no `Node.format` / `node.format` production hits.
- concrete node `_format_push` methods
  - Disposition: delete
  - Owner after cleanup: `cold_start/notation.py`
  - Action: removed formatter push methods from `Var`, `Fun`, `BVar`, `Eq`,
    `Implies`, `Bottom`, `Forall`, and `Exists`.
  - Evidence: search gate has no `_format_push` hits in `syntax.py`.
- `_binder_format_push`
  - Disposition: delete
  - Owner after cleanup: `cold_start/notation.py`
  - Action: removed binder formatting helper from `syntax.py`.
  - Evidence: search gate has no `_binder_format_push` hits.

Gate results:

- Pass: `rg -n "def format|_format_push|_binder_format_push|node\.format|\.format\(" cold_start tests`
  - remaining hits are in `cold_start/notation.py` only.
- Pass: `rg -n "ctx\.|_Printer|infix|fresh|surface notation|human notation" cold_start\syntax.py`
  - zero hits.
- Pass: `rg -n "adapter|visitor|protocol|compat|legacy|fallback|shim|facade" cold_start\syntax.py cold_start\notation.py`
  - zero hits.

Commit:

- this workstream commit

Next slice:

- `cold_start/notation.py`

### Iteration 2 - `notation.py formatter owner`

Surfaces:

- `format_term`
  - Disposition: rewrite
  - Owner after cleanup: `cold_start/notation.py`
  - Action: rewired to notation-local `_format_node(...)`.
  - Evidence: `uv run pytest tests\test_notation.py` passed with term round-trip
    property coverage.
- `format_formula`
  - Disposition: rewrite
  - Owner after cleanup: `cold_start/notation.py`
  - Action: rewired to notation-local `_format_node(...)`.
  - Evidence: `uv run pytest tests\test_notation.py` passed with formula
    round-trip and deep-format coverage.
- `_Printer`, `_format_name`, `_fresh_name`, precedence/constants tables
  - Disposition: keep
  - Owner after cleanup: `cold_start/notation.py`
  - Action: kept as notation-owned lexical state and helpers.
  - Evidence: no notation state crosses into `syntax.py`.
- notation formatter work stack
  - Disposition: rewrite
  - Owner after cleanup: `cold_start/notation.py`
  - Action: rebuilt formatting as a module-local iterative stack with exact-type
    handling.
  - Evidence: deep formatting test passed under low recursion limit.

Gate results:

- Pass: `uv run pytest tests\test_notation.py` - `11 passed in 1.00s`.
- Pass: `uv run pytest` - `316 passed in 58.99s`.
- Pass: `uv run ruff check cold_start tests` - all checks passed.
- Pass: `uv run pyright` - `0 errors, 0 warnings, 0 informations`.

Commit:

- this workstream commit

Next slice:

- `tests/test_notation.py`

### Iteration 3 - `notation boundary tests`

Surfaces:

- direct syntax-node `.format` exposure
  - Disposition: delete/reject
  - Owner after cleanup: `cold_start/notation.py`
  - Action: added a regression test asserting syntax nodes do not expose a public
    human-notation formatting method.
  - Evidence: `uv run pytest tests\test_notation.py` passed.

Gate results:

- Pass: `uv run pytest tests\test_notation.py` - `11 passed in 1.00s`.

Commit:

- this workstream commit

Next slice:

- docs

### Iteration 4 - `docs`

Surfaces:

- `cold_start/CLAUDE.md`
  - Disposition: rewrite
  - Owner after cleanup: docs describe `notation.py` as human notation owner.
  - Action: removed the claim that `node.format(ctx)` prints syntax nodes.
  - Evidence: search gate has no `node.format` hit.
- `ARCHITECTURE.md`
  - Disposition: rewrite
  - Owner after cleanup: docs describe syntax methods as structural and notation
    parse/print as `notation.py` ownership.
  - Action: removed `format` from the syntax method list.
  - Evidence: search gate has no old formatter ownership hit.
- `notes-cold-start.md`
  - Disposition: keep history, append current note
  - Owner after cleanup: running notes record the workstream and gates.
  - Action: appended a 2026-06-16 completion note.
  - Evidence: docs now point future work at this workstream.

Gate results:

- Pass: all search and runtime gates listed above.

Commit:

- this workstream commit

Next slice:

- none; requested target family is at fixed point after commit.
