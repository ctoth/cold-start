# Certified Algebra Phase 0 Evidence and Frozen Contracts

Date: 2026-08-08

Status: accepted baseline for `certified-algebra-certificate-program.md`.

The program and its insertion before certifying Cooper are authorized by the
2026-08-08 instruction to fully execute the workstream. This record freezes the
pre-implementation measurements, inventories, and version-1 contracts. Phase 0
changes documentation only; no implementation file is changed.

## Preserved worktree state

Before implementation, `main` was six commits ahead of `origin/main` at
`bfd0b24`. The following unrelated untracked material was present and is outside
this program:

```text
.package-smoke/
notes-breakthrough-interp.md
notes-breakthrough.md
notes-cleanup-evaluation.md
notes-cleanup-plan.md
notes-code-review.md
notes-decidability-a1-b1.md
notes-fundamental-cas-next.md
notes-open-obligations.md
notes-project-thread.md
```

`workstreams/certified-algebra-certificate-program.md` itself was the untracked
design supplied for execution. It enters version control with this record.

## Reproduced baselines

The exact determinant traversal from the program reproduced:

```text
tree_nodes=47147
unique_objects=13682
hamblin_bytes=2094481
```

`uv run python -m cold_start.jacobian2_proofs` reported 74,739 total proof-node
occurrences across the suite, including a 47,147-node determinant proof, and
took 18.407 seconds on the baseline machine.

A deliberately shared valid proof used one `Refl(Var("x"))` object as both
children of `Trans`. Its proof tree has three occurrences and two distinct proof
objects. `export_theorem("shared_baseline", proof, PEANO)` emitted 558 UTF-8
bytes and expanded the shared `Eq.refl x` twice. Lean proof emission therefore
starts as explicitly tree-shaped presentation output.

`uv run python -m cold_start.ledger` took 58.786 seconds and reported all six
completed interpretation artifacts fully paid. The largest was the 51-node
ring-of-integers bridge with an 876,035-node toll. Its three explicitly open
Robinson rows remained unchanged: `uniqueness:+` for the partial S2 artifact,
`totality:*`/`uniqueness:*` for Theorem 1.2, and those same two multiplication
debts for the positive-Peano bridge.

The forced full gate baseline completed in 1,129.023 seconds:

```text
1411 passed in 533.10s (0:08:53)
Ruff: all checks passed
Pyright strict: 0 errors, 0 warnings, 0 informations
Lean coverage: 16 proof rules, 16 feature families, 15 official theories
Lean corpus freshness: clean
Lean 4 compilation: passed
Trusted-base mutations: 177/177 killed, 0 survived
GATE GREEN
```

## Current caller inventory

Raw proof bytes have one production decoder caller, `cold_start/verify.py`, and
are directly exercised by `tests/test_checker.py`, `tests/test_codec.py`,
`tests/test_jacobian2.py`, `tests/test_properties.py`, and
`tests/test_relations.py`. The owner definitions are `encode_proof` and
`decode_proof` in `cold_start/codec.py`. No other production module calls them.

The polynomial surfaces to delete are:

- `cold_start/jacobian2_proofs.py`: `normal_form_rules`, used by derivative and
  determinant normalization in the same module;
- `cold_start/peano_proofs.py`: `ring_kit`, consumed by `ring_z.py` and tests;
- `cold_start/combination.py`: `by_combination`, consumed by
  `integer_pairs.py`, `ring_z.py`, and `squaring_proofs.py`.

Non-checker production consumers of canonical owner inventories or generic
proof/syntax traversal are:

- `codec.py`: both inventories and `children`, for the current external bytes;
- `notation.py`: the syntax inventory for exhaustive presentation dispatch;
- `lean/proof.py`: the proof inventory plus generic traversal for export
  discovery and tree-shaped emission;
- `lean/syntax.py`: the syntax inventory plus traversal for rendering;
- `lean/models.py`: generic syntax traversal for model symbol discovery;
- `lean/coverage.py`: the proof inventory plus generic traversal for semantic
  coverage.

`lean/coverage.py` and the inspection traversals in `lean/models.py` and
`lean/proof.py` will deduplicate by object identity when repeated visits add no
semantics. Lean proof text remains tree-shaped presentation output and receives
explicit byte and expansion-work limits. It is not a certificate verifier.

The completed cleanup workstream's early proposal to put trusted proof
derivation methods on proof classes is superseded. Current production is the
authority: proof dataclasses are inert and `checker.py` owns the exhaustive
trusted rule semantics. `cold_start/CLAUDE.md` is corrected in this Phase 0
commit so the two workstreams cannot be executed as conflicting instructions.

## Version-1 certificate byte grammar

All multibyte text is strict UTF-8. `uvarint` is unsigned LEB128 with the
shortest possible representation; redundant high zero groups are invalid.
`string` is `uvarint(byte_length) || utf8_bytes`. There are no implicit native
integers, native byte orders, or optional trailing fields.

```text
certificate := "CSPC" || uvarint(1)
               || string(theory_key) || 32-byte theory_fingerprint
               || uvarint(syntax_count) || syntax_entry * syntax_count
               || uvarint(proof_count)  || proof_entry  * proof_count
               || uvarint(hyp_count) || syntax_ref * hyp_count
               || syntax_ref(claim_conclusion)
               || proof_ref(root)

syntax_entry := string(exact_class_name) || uvarint(field_count)
                || encoded_field * field_count
proof_entry  := string(exact_class_name) || uvarint(field_count)
                || encoded_field * field_count

encoded_field := 0x00 || uvarint(nonnegative_integer)
               | 0x01 || string
               | 0x02 || syntax_ref
               | 0x03 || uvarint(arity) || syntax_ref * arity
               | 0x04 || proof_ref
               | 0x05 || uvarint(arity) || proof_ref * arity

syntax_ref := uvarint(table_index)
proof_ref  := uvarint(table_index)
```

Each entry's exact class name must resolve through the closed registry derived
from `CANONICAL_NODE_TYPES` or `CANONICAL_PROOF_TYPES`. Field count, order, and
field marker must match that class's dataclass fields and supported annotations
exactly. A syntax reference in a syntax entry and a proof reference in a proof
entry must be strictly lower than the containing entry index. Proof entries may
refer to any syntax entry. Claim references may refer to any syntax entry and
the root may refer to any proof entry.

The tables are the canonical structural postorders specified by the program.
Exact class name, primitive values, tuple order, and child structural keys form
the structural key. The decoder rejects duplicate structural keys, forward or
out-of-range references, unsorted or duplicate claim hypotheses, empty proof or
syntax tables, unsupported field annotations, malformed UTF-8, nonminimal
varints, and trailing bytes. Re-encoding an accepted value must be byte-for-byte
identical.

This grammar deliberately uses owner-derived class names and dataclass metadata
rather than a separately maintained numeric rule-schema inventory. Changing a
canonical class name or fields requires a new certificate version.

## Version-1 theory fingerprint preimage

The digest is SHA-256 over the following length-framed records. `frame(x)` is
`uvarint(len(x)) || x`. Every record is prefixed by one byte identifying its
kind, so concatenations are unambiguous.

```text
frame("cold-start-theory-v1")
0x01 || uvarint(sort_count) || frame(sort_utf8) * sort_count
0x02 || uvarint(function_count)
     || (frame(name) || uvarint(arg_count) || frame(arg_sort) * arg_count
         || frame(result_sort)) * function_count
0x03 || uvarint(relation_count)
     || (frame(name) || uvarint(arg_count) || frame(arg_sort) * arg_count)
        * relation_count
0x04 || uvarint(axiom_count) || frame(canonical_formula_bytes) * axiom_count
0x05 || absent_or_present_zero
0x06 || absent_or_present_successor
```

Sorts are sorted by UTF-8 bytes. Function and relation ranks are sorted by
symbol-name UTF-8 bytes. Axioms are sorted by their standalone canonical
formula bytes. `absent` is `0x00`; present zero is `0x01 ||
frame(canonical_term_bytes)`; present successor is `0x01 || frame(symbol_utf8)`.
The theory slug is intentionally absent from this semantic digest.

## Deterministic trusted work units

Checker limits count operations at named admission points, never elapsed time:

- `proof_nodes`: increment once when a unique proof object changes unseen to
  active;
- `proof_edges`: increment once for every immediate proof-child edge returned by
  local validation, including edges to already complete nodes;
- `syntax_nodes` and `syntax_edges`: increment once per unique input syntax
  object and immediate syntax edge across proof fields, claim, and theory data;
- `hypothesis_elements`: increment for every element inspected while validating,
  unioning, subtracting, scanning, sorting, or comparing hypothesis sets;
- `syntax_visits`: increment for every syntax node inspected by validation,
  free-variable/sort discovery, equality-side inspection, or formula/term size
  measurement;
- `syntax_rebuilds`: increment for every syntax node constructed by substitution,
  binder instantiation, quantifier construction, and checker-derived formulas;
- `sort_steps`: increment for every syntax node or declared rank inspected by
  sort checking;
- `sequent_steps`: increment once for each derived sequent plus every conclusion
  and hypothesis syntax node measured for its size.

The meter also tracks maxima rather than cumulative units for
`single_term_nodes`, `single_formula_nodes`, `derived_hypotheses`, and
`derived_sequent_nodes`. A limit is checked before the operation or allocation
that would exceed it. Rejection identifies the exact named limit. Counts use
exact object identity only for per-call deduplication; no cache or meter state
survives `check()`.

Certificate IO limits separately count input bytes, syntax/proof table entries
and edges, tuple/set arity, string bytes, and claim hypotheses before allocation.
The artifact contains no limit fields. Repository defaults accept all official
artifacts with recorded headroom; callers may only lower them.
