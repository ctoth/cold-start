# Certified Algebra Phase 5 Evidence

Date: 2026-08-08

Status: implemented; both mutation boundaries and the full repository gate are
green.

## Red contracts

`tests/test_work_limits.py` was introduced before the meter and initially failed
during collection because `check_with_usage` did not exist. The contract covers
small-proof/large-substitution amplification, excessive hypotheses, hostile
strings, large derived formulas, each cumulative graph/operation budget,
derived-size maxima, deterministic usage, official-theory defaults, and
verifier overrides that may only lower repository ceilings.

The first green attempt exposed three incorrect test assumptions and one shared
DAG defect: inserting a large replacement does not rebuild it, one edge does not
exceed a limit of one, and reversing preorder is not a valid child-first order
when syntax identities are shared. The repaired tests construct a deep source
that substitution must rebuild and graphs with two edges. Syntax measurement now
uses iterative tri-color postorder and rejects identity cycles.

## Deterministic work boundary

`work.py` owns exact frozen `WorkLimits` and `WorkUsage` values plus one mutable
per-invocation `WorkMeter`. Counters and ceilings are explicit typed attributes;
`Literal` names and exhaustive `match` dispatch replace string-indexed maps or
reflective `getattr` coupling. No counter identity or usage survives a check.

The checker accounts for unique proof nodes/edges, unique validated input syntax
nodes/edges, hypothesis elements, syntax visits/rebuilds, sort steps, sequent
steps, UTF-8 string bytes, and maximum term, formula, hypothesis-set, and derived
sequent sizes. Syntax validation, substitution, abstraction, binder
instantiation, free-variable scans, sorting, rule construction, set operations,
sequent observation, and exact claim comparison all execute under the same
meter. Per-invocation identity caches retain immutable syntax sizes,
free-variable sets, and term sorts keyed by signature and binder scope. Persistent
substructure is checked once; no cache survives the call. Wall time is not a
semantic budget.

The verifier reads at most the decoder ceiling plus one sentinel byte, accepts
only exact repository limit values, and rejects any override that raises either
an I/O or checker ceiling. Certificate bytes contain no policy fields.
`cold-start-verify --report-work` reports artifact bytes, deterministic usage,
and both repository ceiling sets.

## Measurements and headroom

The decoded canonical determinant certificate remains 39,605 bytes and reports:

```text
proof nodes/edges: 2,633 / 4,556
unique input syntax nodes/edges: 275 / 443
hypothesis elements: 0
syntax visits/rebuilds: 35,151 / 9,258
sort/sequent steps: 14,231 / 2,634
UTF-8 string bytes: 2,532
maximum term/formula nodes: 308 / 617
maximum hypotheses/derived sequent nodes: 0 / 617
```

The independently generated ideal-membership consequence reports 4,295 proof
nodes, 4,796 proof edges, 2,120 input syntax nodes, 124,020 syntax visits,
28,855 rebuilds, 44,418 sort steps, 4,311 sequent steps, and at most two
hypotheses and 367 derived sequent nodes. The in-memory determinant, before
portable structural sharing, reports 5,813 proof nodes and 84,148 visits.

The first serial deep-proof run exposed repeated full traversal of persistent
derived syntax and free-variable data. It was stopped after 659.8173577 seconds.
After the per-invocation caches, the 6,000-deep proof regression plus the complete
work-limit, checker, certificate, and tool suites pass together in 5.9887734
seconds. A 1,000-deep `Cong` check fell from 2.2030673 to 0.0597951 seconds;
the corresponding instantiation check fell from 3.4148777 to 0.0952528 seconds.

Repository defaults retain explicit expansion headroom over these observed
official artifacts: 1,000,000 proof nodes, 4,000,000 proof edges, 2,000,000
input syntax nodes, 8,000,000 syntax edges, 20,000,000 hypothesis elements,
100,000,000 syntax visits, 20,000,000 rebuilds, 100,000,000 sort and sequent
steps, 1,000,000 string bytes, 2,000,000/4,000,000 term/formula nodes,
100,000 hypotheses, and 10,000,000 derived sequent nodes. These are ceilings,
not target artifact sizes; the CLI makes the actual margin visible per artifact.

## Assurance integration

The logical mutation boundary now includes `work.py` and the work-limit tests.
The portable campaign also runs the work-limit tests against verifier and codec
lowering behavior. The kernel CI slice includes the same suite. Routine
`tools/gate.ps1` remains mutation-free; both named campaigns remain explicit CI
assurance jobs.

The first post-commit portable campaign failed closed with 30/115 codec and 2/8
verifier survivors. Isolation checks confirmed that mutants were imported from
their disposable worktrees. The gaps were exact-boundary acceptance, malformed
scalar types, frozen schema branches, semantic fingerprint components, and file
diagnostic labeling. Focused adversarial tests now pin each of those contracts;
the redundant reference-range predicate and combined nonempty-table guard were
also split into independently meaningful fail-closed checks. A repeat campaign
against the amended commit reduced the result to 4/112 codec survivors and 0/8
verifier survivors. The last four were an unpinned nonempty relation fingerprint,
one equivalent reference predicate, and an unreachable proof-schema
syntax-tuple branch. A Robinson fingerprint vector, adversarial syntax-tuple
references, and an explicit frozen-schema assertion now cover those contracts;
the next repeat killed all but the relation-fingerprint mutation because every
registered theory currently has an empty relation signature. A direct semantic
comparison between otherwise identical zero-relation and one-relation theories
now pins that fingerprint component. The final complete portable campaign killed
111/111 codec and 8/8 verifier mutations (certificate has no sites) in
206.2699174 seconds.

Focused work-limit, certificate, checker, deep-proof, and tool tests pass. The
mutation-free repository gate is green in 72.5501717 seconds: 1,480 tests are
collected and pass, Ruff is clean, strict Pyright reports 0 errors, 0 warnings,
and 0 informations, the generated Lean corpus is fresh, and pinned Lean 4
compilation passes.

The first final-HEAD logical campaign took 1,954.1509092 seconds. Checker killed
81/81, sequent 5/5, theory 44/44, and work 27/27; proof had no mutation sites.
Syntax left 4/94 survivors: three operation-kind accounting branches and one
duplicate unmetered equality sort implementation. Exact free-variable, function
sort, and relation sort usage assertions now pin the three counters. The
unreachable `Eq`/`Rel` `_sort_check_step` duplicates were deleted so the exact
special cases in `Formula.sort_check` remain the only owners. A focused syntax
repeat killed 90/90 sites in 490.7723777 seconds. The resulting logical boundary
has 247 sites: checker 81, proof 0, sequent 5, syntax 90, theory 44, and work 27.
Every site was killed across the complete campaign plus the focused repair run.
A redundant whole-campaign pass then took 1,680.8078453 seconds and killed every
checker, sequent, syntax, and theory site, but exposed two work-meter survivors:
acceptance exactly at a cumulative ceiling and rejection of a negative maximum.
Exact direct `WorkMeter` contracts now pin both boundaries; a focused work-source
campaign killed those original survivors but exposed four more boundaries that
the whole run had classified as killed only through unrelated test timeouts:
exact string-byte acceptance, zero cached syntax size, and exact types for both
work-limit lowering arguments. Direct cache consistency and exact-input tests now
pin the complete meter helper surface; a second focused work-source campaign
killed all 27/27 sites in 674.0446197 seconds. The complete final logical
inventory is therefore 247/247 killed: checker 81, proof 0, sequent 5, syntax
90, theory 44, and work 27. The whole campaign established the unchanged
checker/sequent/syntax/theory boundary; the exact-HEAD focused repeat established
the final amended work source and tests without rerunning those unchanged slices.
