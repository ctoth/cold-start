# notes — cold-start proof checker

Project lives in this git repo. Full design notes in `NOTES.md`; this file is
the running scratch log. (Moved into the repo at Q's request; was at the parent.)

## 2026-08-03: orchestration — prover layer + Robinson derivation (IN PROGRESS)

Session assessment concluded: the checker is a cathedral with one theorem in it
(`0+n=n`), because there is no untrusted prover — the missing half of the De
Bruijn split. Also: ARCHITECTURE overclaimed the Robinson bridge as a "checked
theorem" (it was only model-checked), and verify.py knew only the peano theory.
Q approved: "drive Opus subagents and get it done."

Two Opus coder agents dispatched:
1. fixes-coder (main repo) — DONE, verified independently:
   - 62e1d72 verify.py registers peano/presburger/robinson
   - 52eeaf8 proofs.robinson_add_proof(a,b): bridge(a,b,a+b) DERIVED from
     Robinson's A4'/A5' via Inst+MP chain; 1..5 sweep in test_robinson.py
   - cddd630 ARCHITECTURE.md now claims exactly what is true (instances
     derived; general definability NOT derived)
   - 6a273a7 notes entry. Gates: 352 passed (was 322), ruff+pyright clean.
   - I re-ran pytest myself (green) and cross-process-verified
     robinson_add_proof(2,3) via `verify.py --theory robinson` -> VERIFIED,
     hypothesis-free, no `+` symbol in the sequent.
2. tactics-coder (worktree .claude/worktrees/agent-a92fb955711a2172f) — RUNNING.
   Building cold_start/tactics.py (untrusted: matching, proof-producing
   rewriting, normalize/prove_eq, by_induction) + tests/test_tactics.py.
   Targets: 0+n=n, S(x)+y=S(x+y), x+y=y+x, (x+y)+z=x+(y+z), all through
   check(_, PRESBURGER), plus a Hypothesis numeral-addition property test.
   Diagnostics show left_identity/succ_add/add_comm/add_assoc in flight.

Known cosmetic issue: repo-root `ruff check .` sees F401s inside the agent
worktree under .claude/ — goes away when the worktree is cleaned up post-merge.

UPDATE (later same session):
- tactics-coder DONE: 9 commits on worktree branch. tactics.py API: match /
  Rule(.fire/.instance/.flipped) / axiom_rule / lemma_rule / hypothesis_rule /
  rewrite_step (leftmost-outermost) / normalize / prove_eq / by_induction.
  Theorems by tactics, all check() with empty hyps: LEFT_IDENTITY, SUCC_ADD
  (S(x)+y=S(x+y)), ADD_COMM, ADD_ASSOC. Its gates: 356 passed, ruff+pyright 0.
  Two pinned API facts: (1) sequential Inst captures — Rule.instance renames
  holes to fresh x! names before substituting (simultaneous subst spelled in
  sequential primitive); (2) IH is a ground rule + ImpIntro discharge is what
  satisfies Induct's eigenvariable condition.
- Q asked for a Lean compat layer -> lean-coder (Opus, own worktree) RUNNING:
  cold_start/lean.py, conditional-theorem export (axioms as ∀-hypotheses, no
  `axiom` keyword; ind hypothesis for Induct), ℕ instantiation epilogue,
  statement-level from-Lean parser, lean_export/ColdStart.lean corpus.
  Q says lean IS installed (choco) — must tell lean-coder to actually compile.
- MERGE DONE (9e7f225): tactics branch into main. proofs.py conflict
  (robinson_add_proof vs tactics section) resolved as clean union. Gates on
  merged main: 389 passed in 66s, ruff clean, pyright 0/0/0.
  Gotcha learned: pyproject addopts already has -q, so `pytest -q` goes
  double-quiet and SUPPRESSES the summary line — run plain `uv run pytest`.
- Lean toolchain: `lean --version` on PATH -> 3.4.2 (choco package is Lean 3,
  2018). Export targets Lean 4 -> told lean-coder to version-gate the compile
  test (skip with message on <4, probe `elan which lean`), keep targeting
  Lean 4, and report honestly that the export is NOT compile-checked here
  unless a Lean 4 is found. Q may want elan installed for a real Lean 4.
- tactics-analyst (Opus) dispatched on merged main: probing exact-conclusion
  claims, Rule.instance "x!" renaming collisions, by_induction eigenvariable
  edge, normalize budget enforcement, robinson_add_proof(1,500) recursion
  depth, top-3 test gaps. Read-only, no fixes.
NEXT: (1) lean-coder report -> review, merge worktree, gates; (2) analyst
report -> triage findings, dispatch fixes if MAJOR+; (3) final docs pass
(README/NOTES already updated for tactics by its coder; add lean layer),
(4) done-check against Q's goal. Blockers: none, two agents in flight.

LEAN 4 TOOLCHAIN SAGA (Q asked "should I just get 4?" -> yes, doing it):
- choco `lean` = 3.4.2 only (package dead). winget has official Lean.Elan
  4.2.3 -> installed OK; exes land in %LOCALAPPDATA%\Microsoft\WinGet\Links
  (NOT ~\.elan\bin). choco lean 3.4.2 still shadows `lean` on PATH — Q can
  `choco uninstall lean`; any compile test must use elan's shim explicitly.
- elan's own downloader FAILS instantly against release.lean-lang.org
  ([7] connect fail in 7-37ms, sandboxed AND unsandboxed) while curl.exe
  and Test-NetConnection to the same host succeed — looks like a libcurl/
  IPv6 quirk in elan, not a network block. `leanprover/lean4:stable` spec
  still resolves via release.lean-lang.org, same failure.
- Workaround IN FLIGHT: downloading lean-4.32.2-windows.zip (794MB) from
  GitHub releases to ~\Downloads (background job). Then: extract +
  `elan toolchain link stable-manual <dir>` + `elan default stable-manual`,
  verify `lean --version` via the Links shim, then compile
  lean_export/ColdStart.lean for the real independent-kernel check.
- tactics-analyst: idle-pinged once, report still owed. lean-coder: active
  (corpus emitter + parser visible in worktree diagnostics).

Workstream: `workstreams/notation-formatter-deletion-first.md`. Target is exact:
`notation.py` owns human parse/print notation; `syntax.py` owns object-language
structure and structural operations only. Deleted the syntax-owned formatter
surface (`Node.format`, node `_format_push` methods, `_binder_format_push`) and
rebuilt formatting as a notation-local iterative work stack. Added a notation
boundary test so syntax nodes do not grow a public `.format` method again. Search
gates and full runtime gates are recorded in the workstream log.

## 2026-06-15 pt3: Q ALSO caught the bigger thing -- "shims are fucking everywhere",
## quoted `_vp_assume(pf): validate(pf.formula)`. The dict-of-tiny-functions
## (_vp_*/_d_*/_ff_*) IS the shim pile -- I dodged methods-on-Pf with a manual
## dispatch table. PLAN: after sort migration green+committed, convert _d_* (derive)
## and the validators to METHODS on the classes. derive runs POST-validate so it can
## be a method (no subclass attack). validate_proof is the trust GATE -> exact-type
## gate + per-type method (gate rejects hostile subclass BEFORE its method runs).
## Circular-import note: derive methods need Sequent -> move Sequent into proof.py
## (it's about formulas); Theory stays a duck-typed param; sort-check -> Sequent method.
## syntax `validate` (_v_*) likewise -> exact-type gate + node._check() method.
## STATUS: COMMIT A DONE = 5c437ea sort-checking polymorphic, no elif type. 310
## passed, ruff clean, pyright 0. test_sort_of_is_memoized -> test_repeated_subterms.
## NOW COMMIT B: convert _vp_* (16 validators) + _d_* (derive handlers) + _VALIDATE_PROOF
## + _DERIVE dicts -> METHODS on Pf classes. Design:
##   - proof.py: each Pf gets `derive(self, theory) -> Sequent` (the _d_* logic) and
##     `_validate(self)` (the _vp_* logic). Sequent MOVES to proof.py (about formulas).
##     Sequent gets `sort_check(sig)` method (the _sort_check_sequent body).
##   - validate_proof stays a GATE: `if type(pf) not in _PROOF_TYPES: raise; pf._validate()`
##     -- exact-type gate BEFORE method (hostile subclass rejected pre-method). Lives in
##     proof.py so Pf._validate can recurse via it (no circular w/ checker).
##   - derive: gate runs first (validate_proof), so derive can be a plain method;
##     recursion sub.derive(theory) then seq.sort_check(theory.signature). The
##     _derive wrapper (derive+sortcheck) -> a method too, or derive does both.
##   - checker.py keeps: Theory, Signature, check() (orchestration: type(theory) check,
##     validate_proof, top derive, RecursionError guard), sort_check_formula (public).
##     Imports Sequent + validate_proof from proof.
## RISK: trusted-core reshuffle. Keep behaviour byte-identical, run full suite. If a
## module won't go green, revert + log. Theory is duck-typed param to derive (no import).
## COMMIT B DONE = a4fc4dc. proof.py: _validate/_derive_rule/derive methods on each Pf;
## validate_proof = exact-type gate + pf._validate(). sequent.py new (Sequent + sort_check
## method). checker.py thin (Theory/Signature/check/sort_check_formula). 310 pass, ruff
## clean, pyright 0. NEXT TWO PILES (Q: "shims everywhere"): (1) syntax.py _v_* validators
## + _VALIDATORS dict -> exact-type gate + node._validate(depth) methods (parallel to
## validate_proof). (2) notation.py _ff_*/_ft_* formatter + _FORMAT_* dicts -> polymorphic
## format() methods (plan: "Refactor the formatter to polymorphic format() methods").
## Each its own green+commit. validate gate+method preserves security (gate rejects hostile
## subclass BEFORE method). PENDING after: iterative check (Q rejects RecursionError guard).
## COMMIT C DONE = 0b71867. syntax.py validate -> exact-type gate (_CANONICAL) + node._validate
## (depth) methods on Node base + 8 nodes. 310 pass, ruff clean, pyright 0.
## REMAINING SHIM PILE: notation.py _ff_*/_ft_* formatter + _FORMAT_FORMULA/_FORMAT_TERM dicts.
## -> polymorphic format() methods. NOTE coupling: formatter needs constants/bound/precedence
## context -> format(self, ctx) method on nodes (presentation on syntax nodes; plan sanctions
## "polymorphic format() methods"). Parser STAYS (local conditionals OK per CLAUDE.md). Then
## update CLAUDE.md (gate+method pattern, trust spans modules). Then iterative check.
## IN PROGRESS: formatter -> format(self, ctx, parent_prec) methods on nodes. ctx (notation
## side) carries LEXICAL concerns (name quoting, infix table, constants, fresh names, bound
## stack); nodes own STRUCTURAL precedence (40 Eq, 10/35 Implies, 5 quant, 50 Bottom). Added
## format to Node base + Var/Fun/BVar/Eq/Implies/Bottom/Forall. Forall/Exists share
## _format_binder(self,ctx,pp) module helper (TODO: define it + Exists.format). THEN rewrite
## notation.py: delete _ff_*/_ft_*/_FORMAT_* dicts/_format_formula/_format_term; add _Printer
## ctx (constants/bound/used + .name/.fresh/.infix); format_term/format_formula call node.format.
## Round-trip tests are the safety net.
## ALL FOUR PILES NOW METHODS. Commits: 5c437ea sort walkers; a4fc4dc proof derive/validate;
## 0b71867 syntax validate gate+method; 18f5256 formatter format(). Each 310 pass/ruff/pyright0.
## Updated cold_start/CLAUDE.md (gate-guards-methods, derive/format are methods, trust spans
## modules). TODO: update ARCHITECTURE.md to match. THEN the LAST pending item Q rejected:
## make check() truly ITERATIVE (explicit stacks), not the RecursionError->ValueError guard.
## test_check_is_total_on_pathologically_deep_input (numeral 5000) is the spec. Recursion is
## in: validate (depth recursion), derive (sub.derive), sort_of/sort_check, free_vars/subst/
## free_var_sorts/abstract/instantiate (Node child-recursion), format. Deep term = numeral(5000)
## = Fun nests. The guard currently catches RecursionError at check() top. Q wants iterative.
## ===
## ITERATIVE WORK IN PROGRESS. Q called out: iterative is the clean worklist/generator idiom,
## not "ugly stacks everywhere" -- I overstated the cost. Approach:
## - DONE: subnodes(node) generator (iterative preorder, heap stack). free_vars/free_var_sorts
##   = comprehensions over subnodes (locally-nameless: every Var is free). Removed Var overrides.
## - IN PROGRESS: validate gate iterative. _validate(self,depth) now RETURNS (child,depth) agenda
##   instead of recursing; driver = while stack: pop, gate exact-type, extend(n._validate(d)).
##   Base done; 8 concrete _validate still return None (pyright flags) -> convert each to return
##   tuple agenda: Var/BVar/Bottom -> (); Fun -> ((a,depth)...); Eq/Implies -> 2 children at depth;
##   Forall/Exists -> ((body, depth+1),). Then rewrite validate() driver.
## - TODO after: subst/abstract/instantiate (rebuild -> iterative post-order), sort_of/sort_check
##   (deep term/formula), derive (deep proof chain). THEN delete RecursionError guard in check().
## - Verify with test_check_is_total_on_pathologically_deep_input (numeral 5000) sans guard.
## ===
## STEP 1 DONE (committing): subnodes generator; free_vars/free_var_sorts comprehensions;
## validate driver iterative (agenda of (node,depth), each _validate returns child agenda).
## 310 pass, pyright 0. The deep-term test triggers validate(deep term) -> now iterative.
## REMAINING recursion reachable from check(): subst/abstract/instantiate (rebuild), sort_of,
## sort_check, derive (proof chain). Must make iterative too before deleting the guard, else
## removing it leaves uncaught RecursionError holes for deep proofs/formula-subst (dishonest
## totality). Plan: rebuilds via iterative post-order; sort_of term-fold; sort_check formula
## scope-stack; derive proof post-order fold. THEN delete check() guard, prove deep test green.
## ===
## STEP 2 IN PROGRESS: validate_proof iterative (proof gate). Driver done (worklist over Pf,
## gate exact-type, extend(_validate())). Converting 16 Pf._validate: -> tuple, return sub-Pf
## agenda instead of validate_proof(sub). DONE: base, Axiom, Assume, Refl, Sym, Trans, Cong.
## TODO: MP, ImpIntro, Inst, Induct, ExFalso, RAA, ForallElim, ForallIntro, ExistsIntro,
## ExistsElim. Then green+commit. THEN derive iterative (post-order fold; refactor 16 rules to
## take child sequents) -- the big one. THEN rebuilds + sort_of/sort_check iterative. THEN drop
## guard + add deep-proof totality test [see STEP 3+ below]. PEANO.signature is None (confirmed). Deep-term test
## already passes via iterative validate; deep PROOF (Sym^4000) currently caught by guard only.
## ===
## STEP 2 DONE (committing): validate_proof iterative (all 16 _validate return sub-Pf agenda,
## driver worklist). 310 pass/ruff/pyright0. NEXT = STEP 3 derive iterative (the hard one):
## post-order over proof tree, each rule reads child Sequents from a map instead of
## self.sub.derive(theory). Refactor _derive_rule(self, theory) -> _derive_rule(self, theory,
## subseqs) where subseqs maps child-Pf id -> Sequent. Driver does post-order, applies sort_check
## per node. Then rebuilds (subst/abstract/instantiate) + sort_of/sort_check iterative. Then drop
## guard + add deep-proof totality test.
## ===
## STEP 3 DONE (committing): derive iterative. Pf.derive = post-order driver (worklist +
## reversed order), each _derive_rule(self, theory, derived) reads child sequents via
## derived(child) lookup instead of .derive(theory). 310 pass/ruff/pyright0. PROBED: Sym^6000,
## Cong^6000, Refl(numeral 6000) all -> Sequent iteratively (guard never fires). REMAINING
## recursion (confirmed by probe): subst on deep formula (Inst over deep concl) -> guard catches.
## So STEP 4 = subst/abstract/instantiate iterative via generic _rebuild((id,depth)-keyed,
## leaf hooks Var/BVar, map_children reassembly, depth+1 under binders) -- removes Var/BVar/
## Forall/Exists rebuild overrides. STEP 5 = sort_of (term fold) + sort_check (formula scope
## stack) iterative. THEN delete guard in check(), add deep-proof + deep-subst totality tests.
## ===
## STEP 4 IN PROGRESS: subst/abstract/instantiate iterative via _rebuild((id,depth)-keyed,
## on_var/on_bvar leaf hooks, map_children reassembly, depth+1 under binders). Node.subst/
## abstract/instantiate rewritten to call _rebuild. REMOVED overrides: Var.subst, Var.abstract,
## BVar.instantiate, Forall/Exists.abstract+instantiate. Kept Term.subst/Formula.subst covariant
## casts. NEXT: run tests (subst/alpha/roundtrip property tests are the net). Then STEP 5 sort_of/
## sort_check iterative, then drop guard.
## ===
## STEP 4 DONE = 7046d2d (rebuilds iterative). STEP 5 IN PROGRESS: sort_of/sort_check iterative.
## sort_of = post-order driver on Term + _sort_step(sig,scope,sorts) per Var/Fun/BVar (Fun reads
## sorts[id(arg)]). sort_check = agenda driver on Formula + _sort_check_step(sig,scope) per
## Eq/Implies/Bottom/Forall/Exists (returns (subformula,scope) agenda; Eq does sort_of checks).
## DONE: Term.sort_of driver + Var/Fun/BVar _sort_step; Formula.sort_check driver. TODO: Eq/
## Implies/Bottom/Forall/Exists _sort_check_step (replace their sort_check overrides). Then test
## (test_sorts is the net). Then STEP 6: delete check() guard, add deep-proof+deep-subst totality
## tests, prove green. NOTE check() still has RecursionError guard until all iterative confirmed.
## ===
## STEP 5 DONE = 732311d. ALL 8 explicit tree-walks now iterative (validate, validate_proof,
## derive, free_vars, free_var_sorts, subst/abstract/instantiate, sort_of, sort_check). BUT
## found the FLOOR: Python's dataclass-generated __eq__ AND __hash__ RECURSE on deep nested
## terms (numeral(6000) == numeral(6000) -> RecursionError). Used in derive (Trans rhs!=lhs,
## MP, Induct concl==, ExistsIntro) and frozenset/dict (hyps, theory.accepts via hash). So the
## guard STILL needed for ==/hash depth -- can't drop it honestly yet.
## OPTION to finish: custom iterative Node.__eq__ + __hash__ (reflective over fields(), one impl
## for all nodes, @dataclass(eq=False)). Removes last recursion. RISK: == IS alpha-equivalence /
## soundness-critical; a bug -> unsound checker. Tests (alpha-equiv, hostile-subclass, soundness)
## are the net but this touches the crux. PAUSED to confirm with Q before reimplementing ==/hash.
## Guard NOT removed. State: 310 pass, ruff clean, pyright 0, 8 ops iterative, committed.
## ===
## STEP 6 DONE = 2405417: Node.__eq__/__hash__ iterative (eq=False on 8 node dataclasses;
## reflective over node_fields() helper). Deep ==/hash/set-membership work at 8000 deep. 310
## pass, ruff clean, pyright 0. Alpha/hostile-subclass/soundness tests confirm semantics.
## NOW STEP 7 (final): remove the RecursionError guard in check() (checker.py ~line 102-106),
## rewrite the check() docstring (no more "convert RecursionError"), add deep-proof totality
## tests (deep Trans over deep terms = the == case; deep proof chain; deep subst) to
## tests/test_properties.py. Then full verify (pytest+ruff+pyright+verify CLI) and commit. ALL
## check-reachable recursion now iterative: validate, validate_proof, derive, free_vars,
## free_var_sorts, subst/abstract/instantiate, sort_of, sort_check, ==, hash.
## ===
## STEP 7 DONE: removed RecursionError guard from check() (now just validate_proof + derive,
## docstring rewritten). Added test_check_handles_arbitrarily_deep_proofs_without_recursion
## (Sym^6000, Cong^6000, Trans deep== distinct objects, Inst deep subst). 311 pass, ruff clean,
## pyright 0, verify CLI VERIFIES 2+3=5. ITERATIVE WORK COMPLETE. The whole iterative chain is
## genuinely iterative end-to-end; the guard is gone. Commits e350525..(this).

## FIXING (2026-06-15 pt2): Q caught `elif type` in checker.py sort walkers -- NOT
## polymorphism. Real failure: I left sort_of/_sort_structure/_collect_consistent/
## _sorts_of_var as type-switches while free_vars/subst became methods. Converting
## sort-checking to POLYMORPHIC METHODS on nodes (no elif type):
## - syntax.py DONE: Node.free_var_sorts() + Var override; Term.sort_of base +
##   Var/Fun/BVar overrides; Formula.sort_check base + Eq/Implies/Bottom/Forall
##   (+Exists TODO). No lru_cache (B019 forbids method-cache + circular import) ->
##   dropping sort_of memoization, will update test_sort_of_is_memoized.
## - TODO: Exists.sort_check; rewrite checker.py (delete sort_of fn + 3 walkers;
##   add _check_var_sort_consistency; rewrite _sort_check_sequent + sort_check_formula
##   to use methods; update _d_inst/_d_forallelim/_d_existsintro to term.sort_of(sig);
##   fix imports); update test_sorts (sort_of import + memoization test -> Fun? no,
##   dropped -> correctness test). Then pytest+ruff+pyright green, COMMIT.
## - ALSO PENDING (Q wants): iterative (not the RecursionError guard). After elif fix.

## REBUILD COMPLETE (2026-06-15). 310 passed · ruff clean · pyright 0 · verify CLI ok.
Commits: 9e64ff8 baseline · b61d6af CLAUDE+ARCH · 49b0439 syntax (Node + methods +
exact-type validate) · 4108fe9 checker (validate_proof + _derive_rule dispatch
tables) · e46a52e notation (formatter table) · df5f132 sorts×quantifiers coexist ·
f4d80a9 check total on deep input · 61ac4ad Robinson (1,S,·) experiment. proof/
presburger/peano/algebra/proofs/verify recovered clean (no type-switch). Every core
op is a polymorphic method or an exact-type table; trust stays in checker.py.

## AUTONOMOUS REBUILD IN PROGRESS (2026-06-15) — plan: ~/.claude/plans/sprightly-watching-fiddle.md
Goal (/goal): fully execute the plan, rebuild cold_start beautiful & principled.
Polymorphic redesign: one Node root, operations as methods (not elif type-switch),
scope carries bound-var SORTS through binders so sorts+quantifiers coexist; trust
gate (validate/validate_proof) stays exact-type dict dispatch (can't be a method
the attacker overrides). Recover-from-green, commit EVERY green step, quote every
run. Robinson/Skolem experiment is the stretch finale (Phase 4).
- Phase 0 DONE: recovered cold_start from e23ad18, 125 passed, committed 9e64ff8.
  Removed stray VISITOR.md; gitignored papers/ pdfs+pngs. (Robinson 1949 paper read
  + saved at papers/Robinson_1949_DefinabilityArithmetic/.)
- Phase 1 DONE: CLAUDE.md + ARCHITECTURE.md written, committed b61d6af.
- Phase 2 IN PROGRESS (task #13, syntax.py):
  * syntax.py REWRITTEN to Node design: one Node root (Term/Formula under it);
    free_vars/subst/abstract/instantiate are METHODS (Var overrides free_vars/
    subst/abstract; BVar overrides instantiate; Forall/Exists override abstract/
    instantiate with depth+1, methods duplicated on each to keep Formula.__subclasses__
    = [Eq,Implies,Bottom,Forall,Exists] for the coverage test). validate = exact-type
    dict dispatch _VALIDATORS (the trust gate, NOT a method). Kept children/
    map_children/encode_node/decode_node/SYNTAX_REGISTRY/term&formula_to/from_dict.
    Dropped is_a (dead) + the 4 _abstract/_instantiate functions.
  * CALL SITES being migrated (free_vars/subst now methods): checker.py import
    dropped free_vars/subst; free_vars(h)->h.free_vars() done (4x); free_vars(phi)
    ->phi.free_vars() done. STILL TODO: 3 subst() in checker.py (lines ~392,409,410)
    -> .subst(); notation.py free_vars(formula.body)->.free_vars(); tests
    (test_properties free_vars/subst, test_quantifiers free_vars/subst, test_model
    subst). Then run full suite + ruff + pyright, fix, COMMIT syntax phase.
- Defaults locked (no forks): see plan. notation parser = recover working logic
  from git, only refactor the formatter; revert-and-log if a module won't go green.
- evaluate (tests/semantics.py) left as test-helper for now (clean fold, test infra).
- COMMITS so far: 9e64ff8 baseline, b61d6af CLAUDE+ARCH, 49b0439 syntax.py
  polymorphic. proof.py (#14) already clean (inert Pf data + generic serialize) -
  NO derive methods on it (would spread trust to untrusted layer); DECISION:
  derivation stays in checker as exact-type dict dispatch.
- checker.py (#15): validate_proof elif -> exact-type dict _VALIDATE_PROOF;
  _derive_rule if-chain -> exact-type dict _DERIVE (16 typed handlers _d_*).
  Behavior-identical: 125 passed, ruff clean, pyright 0. Sort walkers (sort_of/
  _sort_structure/_collect_consistent/_sorts_of_var) LEFT AS-IS - they get the
  sorts x quantifiers capability in Phase 3 (#21, red-first: sort_of handles BVar
  via a scope of bound sorts; the walkers recurse into Forall/Exists threading
  binder sort). TODO: update ARCHITECTURE.md (derive is dict dispatch, not methods
  on Pf - trust boundary), then COMMIT checker phase.
- PHASE 2 COMPLETE (commits 49b0439 syntax, 4108fe9 checker, e46a52e notation;
  proof/theories/proofs/verify already clean). All core ops methods or exact-type
  tables; no sprawling type-switch left.
- PHASE 3 DONE: sorts x quantifiers (df5f132), stack-safety (f4d80a9). 131 passed.
- PHASE 4 (#23) Robinson experiment: cold_start/robinson.py = bridge(a,b,c) [Eq:
  S(ac)S(bc)=S(c²S(ab))] + (1,S,·) Peano axioms A1,A2,A4'(=bridge(a,1,Sa)),
  A5'(=bridge(a,b,c)->bridge(a,Sb,Sc)), A6, A7'(=bridge(ab,a,a·Sb)) + ROBINSON_PEANO
  Theory. tests/test_robinson.py: bridge IS the graph of addition in N (parametrized,
  2+3=5 true / 2+3=4 false); (1,S,·) axioms true in N over positives; checker
  re-derives Inst(Axiom(ADD_ONE),"a",2) = bridge(2,1,3). 310 passed, ruff+pyright
  clean. TODO: write papers/Robinson_1949_.../notes.md (findings), COMMIT, then
  FINAL green gate (#20: full suite+ruff+pyright, confirm verify CLI).
- PHASE 3 sorts x quantifiers DONE+COMMITTED df5f132 (130 passed). NEXT in #21:
  stack-safety (deep proof -> only Type/ValueError, never RecursionError). Plan:
  red test in test_properties (Refl(numeral(5000)) currently RecursionErrors via
  validate); guard = catch RecursionError in check() -> ValueError (makes check
  TOTAL; full iterative rewrite is the gold standard but huge/risky - guard
  satisfies the totality property, documented honestly). Then Phase 4 Robinson (#23).
- PHASE 3 IN PROGRESS (#21), red-first. sorts x quantifiers coexistence: 5 RED
  tests in test_sorts.py (TypeError "not a formula" - sort-checker rejects
  quantified formulas). IMPLEMENTING: thread a SORT SCOPE through binders:
  sort_of(t, sig, scope) handles BVar(i)->scope[i] (scope=tuple of bound sorts;
  add scope param, update callers, keep lru_cache - test_sort_of_is_memoized still
  passes since closed terms use scope=()); _sort_structure(f, sig, scope) recurse
  Forall/Exists body with (f.sort,*scope); _collect_consistent + _sorts_of_var
  recurse Forall/Exists body (free-var by name, no scope). Then GREEN + remaining
  Phase 3 (stack-safety) + Phase 4 Robinson.
- SYNTAX PHASE PROGRESS: checker.py + notation.py call sites migrated to methods;
  Term/Formula got covariant subst narrowing; tests sed-migrated to method form
  (incl nested f.subst(x,t).free_vars()); test_quantifiers import cleaned. TODO:
  drop subst from test_model import + free_vars/subst from test_properties import;
  then pytest+ruff+pyright, fix, COMMIT syntax phase. (validators have benign
  unused-arg hints from the uniform (node,depth) signature.)

## HOUSEKEEPING DONE (repo restructure)
- All 9 test files moved root -> tests/ (git mv). tests/conftest.py registers
  Hypothesis profiles default/fast (HYPOTHESIS_PROFILE env). pyproject:
  testpaths=["tests"], pythonpath=["."]. Removed mutmut dep (Windows=WSL-only;
  use tools/mutate.py). test_checker uses REPO_ROOT for the verify subprocess
  cwd. tools/mutate.py TEST_CMD points at tests/. .gitignore += .coverage.
  Full suite green from new layout; ruff + pyright clean.
- notes-cold-start.md moved into the repo. (NOTES.md also exists; older/stale ->
  consider consolidating.)
- NEXT: safe worktree mutation run; then resume walker consolidation (validate
  fold, eval fold, stack-safe iterative traversal -> also fixes RecursionError).

## WALKER CONSOLIDATION STATUS (commits)
- cf31c9c: children/map_children/is_a + free_vars fold.
- 2f6d080: subst fold (overloaded Formula->Formula/Term->Term).
- 3ef28e0: DELETED term/formula_free_vars + term/formula_subst.
- 2513257: validate consolidation -> ONE validate(node, depth). Trust gate, so
  EXACT-type (NOT reflection) -- merges validate_term+validate_formula. All
  callers migrated; property test_validate_accepts_canonical_nodes.
- a24613a: EVAL fold DONE. tests/semantics.py = ONE evaluate(node, model, env,
  denv) + Model dataclass + ModelLike Protocol(interp:dict) + _carrier (getattr
  carriers[sort] else .carrier, raises if neither -- no silent vacuous-∀). All 5
  evaluator files migrated, NO SHIM: deleted eval_/interp_/ev_ + Uninterpretable;
  test_model has N=Model("N",interp{0/S/+}) and ALL 22 call sites ->evaluate(.,N,.);
  test_logic uses `from test_model import N` + `from semantics import evaluate`.
  Multi-line/string call sites rewritten with a paren+string-aware Python pass
  (throwaway tools/_migrate_eval.py, deleted after). 108 passed, ruff+pyright clean.
- Walker count: 20 -> 8 deleted (free_vars x2, subst x2, validate 2->1,
  evaluators 10->1). Remaining: checker SORT walkers (sort_of, _sort_structure,
  _collect_consistent, _sorts_of_var ~4, TRUSTED core) + test helper walkers
  (_vars_with_sorts in test_sorts, encode/decode in syntax are reflection already).
- HARD RULE (Q, emphatic, session-ending): NEVER write a shim/wrapper/facade.
  Update EVERY call site. Use Rope/ast/LibCST or exhaustive edits. See memory
  no-shims-rule.md.
- IN PROGRESS NOW: PRESBURGER/PEANO split (red-first). DONE so far:
  * tests/test_presburger.py written, confirmed RED (ImportError MUL_SUCC_F).
    Tests: peano=presburger+mul axioms; presburger proves 0+n=n; 2*0=0 under
    PEANO; same rejected under PRESBURGER; mul_proof(a,b) computes a*b in PEANO.
  * cold_start/presburger.py CREATED: ZERO,S,add,numeral, ADD_ZERO_F,ADD_SUCC_F,
    SUCC_NEQ_ZERO,SUCC_INJ, induction, PRESBURGER theory.
  * cold_start/peano.py REWRITTEN: imports PRESBURGER,ZERO,S,add from presburger;
    defines mul, MUL_ZERO_F (x*0=0), MUL_SUCC_F (x*Sy=x*y+x);
    PEANO=replace(PRESBURGER, axioms=...|{MUL_ZERO_F,MUL_SUCC_F}). NO re-export
    facade (removed an initial noqa re-export -- shim violation).
  * cold_start/proofs.py: imports split (ADD_*/ZERO/add/induction/numeral from
    presburger; MUL_*/mul from peano; +Refl); added mul_proof(a,b) recursing via
    mul axioms + reusing add_proof; __main__ now checks vs PRESBURGER.
  IMPORTERS ALL UPDATED (no shim): __init__.py (PEANO,mul from peano;
  PRESBURGER,ZERO,S,add,induction,numeral from presburger; __all__ has both
  theories+mul); test_checker/test_properties/test_quantifiers/test_logic/
  test_model each split `from cold_start.peano import ...` -> PEANO from peano,
  base pieces from cold_start.presburger. verify.py keeps `from .peano import
  PEANO` (unchanged, valid).
  GATE: ruff --fix clean (pruned unused `mul` from proofs.py), pyright 0/0,
  test_presburger.py 9/9 GREEN. REMAINING: run FULL pytest (verify import split
  broke nothing); then commit the PRESBURGER/PEANO split. Update DESIGN docs/
  layout line in this notes file (checker layout mentions peano only).
  NOTE: theory EXTENSION via dataclasses.replace (Theory is frozen data), NOT
  subclassing -- checker never dispatches on Python type.
- DETAILS (agreed order) for reference: split PRESBURGER out of "PEANO". Current
  cold_start/peano.py is the ADDITION-ONLY fragment = Presburger (complete+
  decidable). True Peano = + multiplication (`*` with x*0=0, x*S(y)=x*y+x) -> then
  incomplete. Encode as theory EXTENSION (data), NOT class inheritance (Theory is
  a frozen dataclass; checker never dispatches on Python type). Plan: rename ->
  cold_start/presburger.py PRESBURGER; peano.py builds PEANO = PRESBURGER + mul
  axioms. Red tests: Presburger proves 0+n=n; Peano proves a `*` fact.
- THEN: stack-safe iterative traversal (kills RecursionError; red test = very
  deep proof checks cleanly / raises only TypeError|ValueError).
- Trust audit done: pytest-cov (checker 91%), gaps closed (5971e06). Mutation
  harness tools/mutate.py exists; run it in a git WORKTREE (never live file).

## State: DONE & GREEN
- pytest: **108 passed**  ·  ruff: clean  ·  pyright (repo-rooted CLI): 0/0
- Editor's inline Pyright is rooted at parent `code\` and ignores our
  `cold-start/pyrightconfig.json` → shows bogus import errors. CLI is authoritative.

## What this is
Number theory from scratch in dependency-free Python via the **De Bruijn
criterion**: untrusted prover emits a serializable proof term; one small trusted
`check(proof, theory)` re-derives the sequent from inert data. Trust = the
verifier, not the object.

## Layout (cold-start/)
syntax.py (language, not trusted) · proof.py (proof terms + JSON, not trusted) ·
checker.py (TRUSTED ~190 lines: validate_proof + check + pure _derive) ·
peano.py (theory: 0/S/+, add axioms, induction recognizer) · proofs.py
(0+n=n by induction) · verify.py (cross-process CLI) · test_checker.py (21).

## Soundness journey — Q found 3 attacks, all now closed at ONE gate
1. object.__new__(Theorem) forges a theorem → abandoned opaque-Theorem LCF
   design for De Bruijn (nothing to forge but a recipe that checks).
2. Lying Term/str subclass __eq__ derives 1=0 from reflexivity (== trusts
   __eq__). Closed by exact-type validate_term/validate_formula.
3. Lying Formula subclass __hash__/__eq__ strips a real hypothesis via
   implies_intro's frozenset subtraction → discharge unproved assumption.
   Already closed: all set-op formulas come via validated Assume / ImpIntro.hyp.
4. Aliasing: Fun("f", mutable_list) lets you rewrite a proved term by mutating
   the list later. Fixed: Fun.__post_init__ snapshots args to tuple (immutable
   by construction) + validate_term exact-tuple backstop.
Key property: one up-front `validate_proof` pass canonicalizes everything, so
every "lying subclass"/aliasing attack dies at the same chokepoint. All 4 are
regression sentinels in test_checker.py.

## What worked / what didn't
- WORKED: De Bruijn redesign collapsed the trust boundary to one function.
- WORKED: exact-type checks (`type(x) is Var`, NOT isinstance — subclasses ARE
  the attack) + single validation pass (cleaner than per-body or a decorator).
- DIDN'T: opaque guarded Theorem (unenforceable in Python). Deleted kernel.py.

## DONE: classical NOT (committed fa1c031). 86 passed, ruff+pyright clean.
Bottom + Not sugar + ExFalso + RAA. Peano now PROVES 1!=0, 2!=1 (SUCC_NEQ_ZERO,
SUCC_INJ). Model net extended to emit Bottom/ExFalso/RAA -> negation is in the
honesty net now.

PROCESS NOTE (Q called it out, correctly): I built Not impl-FIRST then tested
(test-after, not TDD). The tests never went red. Partial repair: wired
Bottom/ExFalso/RAA into the model-soundness generator (could have gone red;
stayed green = corroborated). COMMITMENT: quantifiers (∀/∃) MUST be red-first,
rule by rule -- write the failing test, watch it fail, then implement. This
matters most for capture-avoiding substitution (where bugs hide).

## IN PROGRESS: quantifiers ∀/∃ — RED-FIRST (Q watching the discipline)
Doing this properly: each behavior = failing test, confirmed red, then implement.
Cycles so far:
1. DONE capture-avoiding subst: red (formula_subst TypeError on Forall) -> impl
   (Forall case + _fresh) -> green. test_subst_into_forall_avoids_capture.
2. DONE ForallElim: red (P.ForallElim missing) -> impl (proof node,
   validate_formula(Forall), validate_proof case, _derive rule w/ sorted-elim
   sort guard) -> green. test_forall_elim_instantiates.
3. IN PROGRESS ForallIntro + eigenvariable condition: red CONFIRMED (node
   missing). Just added proof.ForallIntro(var,sort,sub). STILL TODO:
   - checker validate_proof: ForallIntro case (var/sort str, validate sub).
   - checker _derive: ForallIntro rule = require var NOT free in s.hyps
     (eigenvariable), return Sequent(s.hyps, Forall(var,sort,s.concl)).
   Tests: test_forall_intro_generalizes (|- ∀x.x=x from refl),
   test_forall_intro_rejects_free_eigenvariable ({x=0} can't generalize x).

Syntax done: Forall(var,sort,body) node; free_vars (body - var); capture-avoiding
formula_subst; validate_formula(Forall). Forall NOT yet in: _sort_structure /
_collect_consistent (checker sort wrapper) [needed only for SORTED quantifier
theories -- defer red-first], serialization (proof.to_dict/from_dict for
Forall/ForallElim/ForallIntro and formula ser for Forall) [defer until a
round-trip test], model eval of Forall (finite carriers) [defer].

## DONE: quantifier honesty net (committed 187b1ca). 97 passed, clean.
test_quant_soundness.py: Z/3 commutative-ring finite model; ev_formula decides
∀/∃ by enumerating the carrier (red-first: ev raised on Forall, then added).
Honesty net = generator of COMM_RING proofs emitting ForallIntro/ForallElim/
ExistsIntro + Assume; conditional validity property (hyps-true => concl-true)
over sampled Z/3 envs -> catches eigenvariable escapes on open sequents.
Non-vacuity meta-test proves the net fires on a false ∀.

KNOWN GAP (flagged to Q, not hidden): ExistsElim is NOT in the generator
(valid ∃-elim proofs are hard to generate) -- only hand-picked tests cover it.

## IN PROGRESS: generic reflection-based ser/des (Q: hand-coded ser is a smell)
Replaced hand-coded to_dict/from_dict in syntax.py AND proof.py with generic
reflection over frozen-dataclass fields:
- syntax.encode_node(node)->dict + _encode_value(field)->object; decode_node(raw,
  registry)->object (validates exact field set; rejects unknown kinds).
  SYNTAX_REGISTRY = {Var,Fun,Eq,Implies,Bottom,Forall,Exists}.
  term_to_dict/formula_to_dict = encode_node; *_from_dict narrow to Term/Formula.
- proof._PROOF_REGISTRY = SYNTAX_REGISTRY + all Pf nodes; to_dict=encode_node,
  from_dict narrows to Pf. Adding a node now needs NO ser code.
- Q's completeness tests (test_json_examples_cover_every_concrete_node_class +
  per-kind round-trips, using *.JSON_EXAMPLES + __subclasses__) are the safety
  net; they stay green. Tests pass (~101). 
- REMAINING NITS: pyright wants fields(node) arg typed (node:object). Fix:
  cast/ignore or type node as DataclassInstance. ruff long lines fixed.
- TODO: rerun ruff+pyright clean, commit.

## IN PROGRESS: LOCALLY-NAMELESS (C), red-first. Signature.rank dict DONE(13dbc93).
Headline red test PASSING-TARGET: forall("x",P)==forall("y",P) (alpha-eq == ==).
RED confirmed (forall import missing).

Migration state (BIG, trusted-core):
- DONE syntax: BVar(index:int) node (Term); term_free_vars/term_subst handle BVar.
  Forall/Exists now (sort, body) [no name]. Added _abstract/_instantiate (term+
  formula, depth-tracked), public forall/exists/instantiate smart ctors.
  formula_free_vars(Forall)=free_vars(body) [no var-subtract]; formula_subst
  recurses body (NO capture, _fresh DELETED).
- TODO NOW syntax: validate_term needs BVar case + validate must be DEPTH-AWARE
  (local closure: BVar(i) valid iff 0<=i<depth). validate_formula(Forall) ->
  depth+1. Add validate_term(t, depth=0)/validate_formula(f, depth=0).
  Then: ser must handle int field (BVar.index) -> _encode_value/decode_node add
  int passthrough; register BVar in SYNTAX_REGISTRY.
- TODO checker.py: ForallElim -> instantiate(s.concl.body? use syntax.instantiate
  on the Forall) ; ForallIntro -> Forall(sort, _abstract(var, concl,0)) i.e. use
  forall(var,sort,concl) closing; ExistsIntro: claim is Exists(sort,body),
  witness check = instantiate(claim, witness)==sub.concl; ExistsElim: instance =
  instantiate(ex, FRESH FREE VAR Var(eigenvar)) ... eigenvar condition same.
  Sort walkers (_sort_structure/_collect_consistent/_sorts_of_var) need Forall/
  Exists/BVar cases (recurse body; BVar no-op) -- but sorted-quant still deferred.
- TODO tests: test_quantifiers (Forall(3)->forall()), test_quant_soundness,
  test_properties generators+JSON_EXAMPLES (Forall example), and the 5 MODEL
  EVALUATORS need de Bruijn env (denv stack): eval(Forall)=enumerate carrier,
  eval(BVar i)=denv[i]. This is the big test-side change.
- Pyright errors are all .var-on-Forall leftovers in checker/syntax -> migrate.
- Strategy: get alpha-eq + capture-free props green first (syntax-only), then
  cascade-fix checker, then tests. Run frequently. Commit when full suite green.

### PROGRESS (locally-nameless migration)
- DONE syntax core: BVar, Forall/Exists(sort,body), abstract/instantiate/forall/
  exists/instantiate, free_vars/subst(no capture), validate depth-aware(local
  closure), ser int-passthrough + BVar registered. alpha-eq test GREEN.
- DONE checker: ForallElim uses instantiate(s.concl,term); ForallIntro uses
  forall(var,sort,concl); ExistsIntro expected=instantiate(claim,witness);
  ExistsElim instance=instantiate(ex, Var(eigenvar,sort)). Imports forall,
  instantiate.
- DONE test_properties: import BVar/forall/exists; formulas() uses forall/exists;
  TERM_JSON_EXAMPLES += BVar(0); FORMULA_JSON_EXAMPLES uses forall/exists.
- TODO test_quantifiers: migrate Forall("x","",..) -> forall(); the ForallElim/
  Intro/ExistsIntro/Elim tests build/assert Forall/Exists(3-arg). assertions like
  seq.concl == Forall(...) must become forall(...). The capture test
  (test_subst_into_forall_avoids_capture) -- reconsider: with locally-nameless
  subst NEVER captures; keep a test but adapt (e.g. subst into forall body).
- TODO test_quant_soundness: ev_formula needs de Bruijn env (denv stack):
  ev_formula(Forall,...)=all(ev(body, denv=[e]+denv)); ev_term(BVar i)=denv[i].
  And the meta-test builds Forall("x","",..) -> forall(). generator builds
  Exists("q","",concl) -> exists("q","",concl).
- TODO others: test_model/algebra/rings/sorts evaluators only need BVar/Forall
  handling IF their generators produce quantifiers (they don't currently) -- but
  CHECK. test_model.nat_formulas: does it make Forall? (Believe not.)
- Then full suite green -> commit locally-nameless.
- BLOCKER: none; just cascade work.

### MIGRATION PROGRESS (cont.)
- DONE test_quantifiers (9 green): sed Forall("->forall(", Exists("->exists(";
  imports forall/exists; capture comment updated (now capture-free by construction).
- DONE test_quant_soundness (3 green): ev_term/ev_formula take denv=() de Bruijn
  stack; BVar->denv[index]; Forall/Exists enumerate carrier pushing (e,*denv);
  constructors -> forall/exists.
- NEXT: run FULL suite. test_model/algebra/rings/sorts evaluators likely DON'T
  see quantifiers (their generators don't make them) but CHECK. test_properties
  round-trips/check_is_total now include Forall/Exists/BVar (check handles them).
  Also: capture test in test_quantifiers still named *_avoids_capture (fine).
- After green: ruff+pyright, commit locally-nameless. Then consider adding a
  red test for stack-safety LATER (roadmap), and the generic-traversal fold.

## WALKER COUNT (done): 20 hand-rolled recursive walkers over term/formula tree
TRUSTED (10): syntax.{term_free_vars,term_subst,formula_free_vars,formula_subst,
validate_term,validate_formula}; checker.{sort_of,_sort_structure,
_collect_consistent,_sorts_of_var}.
TESTS (10): eval_term/eval_formula (test_model), interp_term/interp_formula x3
(test_algebra/rings/sorts), ev_term/ev_formula (test_quant_soundness).
(ser/des was 4 more -> now generic.) Each new node = touch all of these; binders
(Forall/Exists) make free_vars/subst especially bug-prone.

## BIG: Q wants a HIGHER-LEVEL Formula concept + "count the walkers" (~24->)
Proposal to present (get steer): spectrum A/B/C.
A lightweight generic map_children/fold by reflection (keeps named binders;
  consolidates non-binding walkers; binder free_vars/subst still special).
B ABT-style binding declaration: declare each op's binding arity; derive
  free_vars + capture-avoiding subst + alpha-eq GENERICALLY (kills _fresh/rename
  hand-roll). Moderate redesign. RECOMMENDED.
C locally-nameless / de Bruijn indices: capture impossible by construction;
  biggest representation change (touches every Var/axiom/test).
Semantic ops (eval/sort-check) stay per-node but as folds over shared traversal.
This is a TRUSTED-CORE redesign -> design + Q steer before rewriting.
After ser/des: enumerate ALL hand-rolled recursive walkers (term/formula_free_vars,
term/formula_subst, validate_term/formula, _sort_structure, _collect_consistent,
_sorts_of_var, the 4+ model eval_formula/ev_formula in test files, ser/des[now
generic]). Propose a higher-level binding-aware AST: declare structure +
BINDING once; derive free_vars / capture-avoiding subst / traversal generically
(map_children / fold). This is a TRUSTED-CORE redesign -> design + get Q's steer,
don't unilaterally rewrite. Discuss after ser/des commit.

## ROADMAP / OWED (each red-first when done):
### STACK-SAFETY (Q flagged; agreed sequencing)
EVERYTHING is recursive (walkers, _derive, _abstract/_instantiate, validate,
evaluators) -> deep term/formula/proof hits Python ~1000-frame limit ->
RecursionError. This even VIOLATES "check is total" (RecursionError is neither
TypeError nor ValueError). Latent only because test inputs are shallow.
PLAN: do NOT hand-trampoline 20 walkers. Fold stack-safety into the generic-
traversal consolidation: one explicit-work-stack fold/map_children, every
walker derived from it -> all stack-safe at once. Refuse sys.setrecursionlimit
band-aid (segfaults past real C-stack depth). Add a red test: a very deep proof
must `check` cleanly or raise TypeError/ValueError (never RecursionError).
Sequencing: finish locally-nameless recursively FIRST, then this.

### TRUST AUDIT: coverage + mutation (Q: do this before more deletion)
- DONE coverage (pytest-cov added). 88% overall; checker 89%, syntax 92%.
  Real gaps found: checker:507 ExistsElim eigenvariable-in-REMAINING-hypothesis
  (untested soundness branch!); syntax:178/180 instantiate into Implies/Bottom
  body (untested binder-open); checker:451-453/480-482 sorted-quantifier guards
  (deferred, no sorted-quant theory); verify.py 0% = SUBPROCESS ARTIFACT (it IS
  tested cross-process). Rest are defensive raise-fallthroughs.
- MUTATION: mutmut is Windows=WSL-only. Built tools/mutate.py (AST mutation
  harness, Windows-native). BUT I recklessly ran it IN-PLACE on live checker.py
  + backgrounded -> Q halted. Restored checker.py from git, suite green, no harm.
  SAFE REDO LATER: run mutation in a git WORKTREE (live file never touched).
  tools/mutate.py exists; just needs to run against a worktree copy.
- IN PROGRESS: closing the coverage gaps with tests (Q said "fix those").
  Added 6 tests to test_quantifiers.py (each fails if its checker line deleted):
  exists_elim hyp-eigenvariable (507), forall_elim through Implies+Bottom
  (syntax 178/180), exists_intro non-Exists claim (476), exists_elim
  non-existential (492), exists_elim missing-instance (496).
  NEXT: run pytest -k these; full suite; re-run coverage to confirm lines hit;
  ruff+pyright; commit. THEN: safe worktree mutation run. THEN resume walker
  consolidation (validate fold, eval fold, stack-safe).

### DELETION IN PROGRESS (brick3) — migrate callers, delete 4 walkers
- DONE syntax: subst now has @overload (Formula->Formula, Term->Term), impl
  `-> object`. DELETED term_free_vars, formula_free_vars, term_subst,
  formula_subst. Generic free_vars + subst remain.
- DONE checker: sed formula_free_vars->free_vars, formula_subst->subst (import +
  all calls). Import order may need ruff isort fix.
- DONE test_properties: removed the 2 agreement tests. STILL TODO: sed
  term_free_vars/formula_free_vars->free_vars, term_subst/formula_subst->subst
  in remaining property bodies (test_subst_of_nonfree_var_is_identity,
  test_free_vars_after_subst, test_subst_idempotent, alpha-eq); DEDUP the import
  block (will have duplicate free_vars/subst); drop unused Term import if now
  unused.
- TODO test_model: sed formula_subst->subst; fix import.
- TODO test_quantifiers: sed formula_free_vars->free_vars, formula_subst->subst;
  fix import.
- THEN: uv run pytest + ruff --fix + pyright; commit deletion.
- BLOCKER: none. Just finish the sed+import-dedup across test files.

### WALKER CONSOLIDATION — IN PROGRESS (red-first)
- DONE brick1 (commit cf31c9c): syntax children/map_children/_is_node/is_a +
  fold-derived free_vars; agreement property green. is_a defined (def, tuple-ok)
  but not yet used (free_vars uses `type() is` for pyright narrowing); will use
  is_a in checker shape-checks migration.
- IN PROGRESS brick2: generic subst. RED test added
  (test_generic_subst_agrees_with_hand_rolled). NEXT: implement
  `def subst(node,var,repl)`: if type(node) is Var -> repl/node else
  map_children(node, lambda c: subst(c,var,repl)). (BVar/Bottom leaves handled
  by map_children.) Then GREEN.
- THEN: migrate callers free_vars/subst (checker: formula_free_vars in Inst/
  ForallIntro/ExistsElim guards; formula_subst in Inst). Delete term/formula_
  free_vars + term/formula_subst. Remove the two agreement tests (served).
  Update test_properties property bodies using term_free_vars/term_subst/
  formula_subst -> free_vars/subst. Run green; commit.
- THEN bricks: generic validate (depth-aware, per-node scalar checks), model
  eval fold, then stack-safe iterative fold (kills RecursionError roadmap item).

### WALKER CONSOLIDATION PLAN (NOW, red-first)
Principle (Q-agreed): EXACT-type for concrete nodes (trust-correct + canonical
data); isinstance ONLY for abstract bases (Term/Formula/Pf membership). Helper
`def is_a(node, kind)` (def not lambda; supports a tuple) for residual concrete
checks. Locally-nameless made free_vars/subst UNIFORM (binders not special), so
a generic fold is now clean.

Primitives (syntax.py, generic over any dataclass node incl. Pf):
- children(node): field values that are dataclass instances (+ tuple elements).
- map_children(node, fn): rebuild node applying fn to child fields.
Then DERIVE as folds, each with a red "agrees with hand-rolled" test, THEN delete
the hand-rolled:
1. free_vars (Var->{name}, BVar->{}, else union children) replaces term/formula_free_vars.
2. subst (map_children recursively; Var->repl) replaces term/formula_subst.
3. validate (per-node scalar checks + recurse children; binder depth+1) replaces
   validate_term/formula. [keep depth for local closure]
4. model eval: fold with a per-theory algebra (the 5 evaluators collapse).
5. checker sort walkers similarly if cleanly foldable.
Make the ONE traversal stack-safe (explicit work stack) -> kills RecursionError
roadmap item at the same time. Add red test: very deep proof checks cleanly /
raises only TypeError|ValueError.
CALLERS to migrate after each: checker uses formula_free_vars (Inst/ForallIntro/
ExistsElim guards), formula_subst (Inst). 

### GENERIC TRAVERSAL / higher-level Formula (the "count the walkers" cure)
map_children/fold by reflection; derive validate/free_vars/eval/sort-check as
folds over ONE scope-correct traversal. Locally-nameless already removes the
binder-specific capture machinery, making a generic fold viable. Make the fold
iterative (see stack-safety above).

## STILL OWED (each red-first when done):
- ExistsElim in the honesty-net generator (or argue it's adequately covered).
- Serialization round-trip for quantifier nodes (Forall/Exists/ForallIntro/
  ForallElim/ExistsIntro/ExistsElim) in proof.to_dict/from_dict + formula
  ser/deser for Forall/Exists. (proof.py serialization NOT yet updated for any
  quantifier node -> from_json/to_json would fail on them.)
- Sorted-quantifier sort-checking: _sort_structure/_collect_consistent/
  _sorts_of_var don't handle Forall/Exists -> under a SIGNATURE a quantified
  formula currently FAILS SAFE (rejected). Needed for ∀x:V in modules.
- Model eval of ∀/∃ in the OTHER test evaluators (test_algebra/rings/sorts) if
  those theories ever get quantifier axioms.

## NEXT BIG DIRECTION: modules / vector spaces (needs sorts[done] + ring[done];
   sorted quantifiers will be wanted for ∀-vector statements).
## Commit chain: ... fa1c031(Not) dd1befc(Forall) 267aced(Exists) 187b1ca(qnet)

## (history) EXISTS — done, committed 267aced
Forall committed dd1befc (90 passed). Now Exists, red-first. 4 tests RED
CONFIRMED (subst capture + ExistsIntro/Elim missing):
test_subst_into_exists_avoids_capture, test_exists_intro_from_witness,
test_exists_elim_proves_no_successor_is_zero (real theorem: ¬∃x. Sx=0),
test_exists_elim_rejects_eigenvariable_escape.

Implementing:
- DONE syntax: Exists node + free_vars; formula_subst handles (Forall,Exists)
  via type(f) (shared capture-avoiding); validate_formula(Forall|Exists).
- DONE proof.py: ExistsIntro(claim, witness, sub), ExistsElim(eigenvar, sub_ex,
  sub_use) nodes.
- DONE checker import Exists. STILL TODO:
  * validate_proof: ExistsIntro (validate claim/witness/sub), ExistsElim
    (eigenvar str, validate both subs).
  * _derive ExistsIntro: claim must be Exists; sub.concl == body[var:=witness];
    sorted witness sort guard; return Sequent(sub.hyps, claim).
  * _derive ExistsElim: s_ex.concl Exists; instance = body[x:=Var(eigenvar,sort)];
    instance in s_use.hyps; phi=s_use.concl; result_hyps = s_ex.hyps |
    (s_use.hyps - {instance}); EIGENVAR not free in phi and not free in any
    result hyp (else reject). return Sequent(result_hyps, phi).
- Then full suite + ruff + pyright; commit.

## REMAINING quantifier cycles (each red-first)
- Exists (dual): ExistsIntro (body[x:=t] => ∃x.body), ExistsElim (eigenvar).
- Serialization round-trip for quantifier nodes.
- Sorted quantifier sort-checking (_sort_structure/_collect_consistent Forall).
- Model eval of ∀/∃ over finite-carrier models -> honesty net covers quantifiers.
- Last commit: fa1c031 (Not). Quantifiers uncommitted.

## (history) NEXT: explicit quantifiers
- Keep free-vars schematic (implicit-∀ top level); add Forall(var,sort,body),
  Exists(var,sort,body) as BINDING connectives.
- Real cost: capture-avoiding substitution (alpha-rename) + eigenvariable
  conditions on ForallIntro/ExistsElim. Sorted quantifiers. Finite-model eval
  (enumerate carrier) for the honesty net.
- DO IT RED-FIRST. Each rule: failing test -> implement -> green.

## (history) IN PROGRESS classical NOT
Q confirmed: classical negation now; explicit ∀/∃ come soon (their real cost =
binders + CAPTURE-AVOIDING substitution; keep free-vars schematic + add Forall/
Exists on top). NOT is small/self-contained; quantifiers get their own pass.

Design for NOT (classical, minimal):
- Bottom (⊥) formula constant; Not(A) = sugar Implies(A, Bottom()). No new
  connective. ¬-intro = ImpIntro, ¬-elim = MP (already have both).
- New proof rules: ExFalso(sub, concl): sub|-⊥ => |- concl (any formula).
  RAA(goal, sub): sub: G,¬goal |- ⊥  =>  G |- goal  (classical reductio).
- Model eval: eval(Bottom)=False; eval(Not A)=not eval A falls out of Implies.

Progress:
- DONE syntax.py: Bottom + Not(); free_vars/subst/validate/ser-deser.
- DONE proof.py: ExFalso(sub, concl), RAA(goal, sub) + ser/deser.
- DONE checker.py: import Bottom/Not; validate_proof ExFalso/RAA; _derive_rule
  ExFalso (sub|-Bottom => concl) and RAA (sub|-Bottom => goal, discharging
  Not(goal)); _sort_structure handles Bottom (pass); _collect_consistent no-op
  on Bottom (no else clause).
- DONE __init__: importing Bottom/Not/ExFalso/RAA. STILL TODO: add them to
  __all__ list (currently pyright "not accessed").
- TODO test_model.py eval_formula: Bottom->False.
- TODO peano.py: add SUCC_NEQ_ZERO (0 != S x) axiom + maybe SUCC_INJ; worked
  theorem S(0) != 0.
- TODO test_logic.py (new): TDD ex falso, RAA/double-negation, disequality,
  negation model soundness, can't-prove-a-false-negation.
- NOT YET RUN since edits. Run full suite next (single-sorted theories must be
  unchanged -- no Bottom used there yet).
- Run full suite; single-sorted/equational theories unchanged (no ⊥ used there).
- Last good state: 79 passed (commit 7be5470). Don't break it.

## SORT SOUNDNESS FIXES — DONE & GREEN (committed 7be5470)
79 passed, ruff clean, pyright 0/0. Both High bugs fixed at the root via a
rule-invariant wrapper.
- `_derive` is now a WRAPPER: calls `_derive_rule` then `_sort_check_sequent`
  on the result when signature present. `_sort_check_sequent` = _sort_structure
  (Eq same-sort) + _collect_consistent (one sort per var NAME across hyps+concl).
- Removed redundant inline sort checks (Axiom/Assume/Refl/Cong); KEPT Inst
  cross-sort guard (degenerate x:K:=v:V case).
- Both red tests now green (ImpIntro ill-sorted hyp rejected; var-name-at-two-
  sorts rejected). Added impintro to the action_proofs generator.
- Docs fixed: README test list (removed stale "induction recognizer"),
  algebra.py header (sorts now exist via MONOID_ACTION/ACTION_SIG).
- Issue 3 (sorted induction): left as-is; the wrapper makes it FAIL-SAFE
  (rejected) under a signature since Induct builds Var(var, "") -> sort "" not
  in sig.sorts. No sorted-induction theory exists. TODO if/when needed.
- FOUND a stray `temp/cold_start/` copy in the repo dir (grep hit
  temp\cold_start\algebra.py). NOT mine. Need to flag to Q + likely gitignore;
  do NOT commit it. Check git status before committing.
- NEXT: git status (exclude temp/), commit the fix.

## (history) FIXING reviewer-found SORT SOUNDNESS BUGS
External reviewer found real holes in the sort layer (trusted core):
1. HIGH: ImpIntro never sort-checks pf.hyp -> accepts ill-sorted antecedent
   like (m:M = x:X) -> (e=e). CONFIRMED red test.
2. HIGH: vars are bare names; a formula can use `x` at sorts M AND X; Inst
   substitutes by name across all sorts + no result sort-check -> can put an
   M-term into an X-position. CONFIRMED red test.
3. MED: sorted induction not signature-compatible (Var(pf.var) sort ""); fine
   now (no sorted induction theory); wrapper will reject it safely.
4. LOW: stale docs (README "induction recognizer"; algebra.py "sorts later").

FIX (reviewer's "rule invariant" direction): sort-check EVERY derived sequent.
- DONE: split sort_check_formula -> _sort_structure (structural) + public
  sort_check_formula (= structure + _collect_consistent). Added
  _collect_consistent (one sort per var NAME) and _sort_check_sequent
  (structure + consistency across hyps+concl with shared acc).
- TODO: refactor _derive into wrapper that calls _sort_check_sequent(seq, sig)
  on every result (gated on signature); rename body -> _derive_rule; recursion
  calls go through wrapper. Remove now-redundant inline sort checks; KEEP Inst
  var-sort guard (catches degenerate x:K := v:V where result is well-sorted).
  (pyright errors at 182-184 are just the object-typed seq; clear when wired.)
- TODO: red tests (test_impintro_rejects_ill_sorted_hypothesis,
  test_variable_name_at_two_sorts_rejected) must go green; full suite stays
  green (single-sorted unchanged: sig None => no checks).
- TODO: fix stale docs. Commit.
- Single-sorted suite MUST stay byte-for-byte (no signature => wrapper no-op).

## (done earlier this step) SORTS base implementation
Goal: add optional sorts so scalars != vectors. Q wants this for "rich
properties to test." Touches TRUSTED core; single-sorted path must stay
byte-for-byte unchanged (signature=None => no sort checks).

Design (committed-to):
- Var gains `sort: str = ""` default. Existing Var("x") unchanged (sort="").
- Theory gains optional `signature: Signature | None`. Signature declares sort
  names + each function symbol's rank (arg sorts -> result sort).
- Sort-checking in the TRUSTED checker, gated on signature: reject ill-sorted
  Assume/Refl, Cong results must respect ranks, and INST cannot cross sorts.

Progress:
- DONE syntax.py: Var.sort field + repr; validate_term checks sort; ser/deser
  round-trips sort. Confirmed 61 tests still green (backward compat).
- DONE checker.py: Signature dataclass (sorts + ranks + rank()); Theory.signature;
  sort_of / sort_check_formula / _sorts_of_var; wired into _derive GATED on
  signature: Axiom/Assume/Refl sort-checked, Cong result sort-checked, Inst
  cross-sort guard. zip strict=True. 61 still green + pyright/ruff clean.
- DONE algebra.py: MONOID_ACTION theory (sorts M,X; e/* /act ranks via
  ACTION_SIG; axioms M_ASSOC/M_LEFT_ID/M_RIGHT_ID/ACT_ID/ACT_COMP).
- DONE test_sorts.py written: SortedModel (T_2 acting on {0,1}, per-sort
  carriers), worked sorted proof, rejection tests (cross-sort inst, ill-sorted
  term, eq-across-sorts, unknown symbol, wrong arity), forward proofs
  well-sorted + sound in model. NOT YET RUN.
- NEXT: run test_sorts.py + full suite + ruff + pyright; fix; commit.
- NOTE: Induct + signature not yet sort-checked (no sorted+induction theory
  exists; gated by zero/succ). Future work if needed.

## READY FOR Q'S REVIEW (previous step, committed c295cd4)
- 56 passed, ruff clean, pyright 0/0 (uv run). Commits: 552a0d3 (rule-preservation
  model probes), ac57b9d (checker exact-type type() dispatch, was isinstance).
- Rule-preservation: per-rule local soundness (sym/trans/cong/mp/impintro/inst
  preserve model validity) + substitution lemma (under Inst) + bounded induction
  principle in N (under Induct).
- Checker now uses `type(x) is C` everywhere (dispatch + shape checks), matching
  validate_*; model probes confirm soundness preserved.
- NEXT after review: maybe start USING it -> commutativity of + (nested induction).

## MODEL-SOUNDNESS PROBE SUITE (Q: ~90% Hypothesis) — IN PROGRESS
Added test_model.py: an N-evaluator (eval_term/eval_formula over {0,S,+,=,->})
plus the invariant "every closed theorem the checker accepts is true in N".
Probes: arbitrary nat proofs sound; forward-constructed proofs sound; declared
axioms true; no-accepted-formula-is-false (schema-shaped danger zone);
addition proofs true; schema-false-in-N; probe-not-vacuous; end-to-end net
catches a bad-theory exploit (just added).
Refactor: prove_add -> cold_start.proofs.add_proof (package), both test files
import it (killed a nested-@given health check from importing test_properties
inside a running test).
STATUS at last run BEFORE the end-to-end test: 47 passed, ruff clean,
pyright 0/0. Need to re-run after adding test_model_net_catches_end_to_end.
NEXT: run uv pytest/ruff/pyright; commit. Then commutativity.

## CRITICAL SOUNDNESS BUG (external reviewer found it) — FIXED & GREEN (committed bcb1fcb)
RESOLVED. 39 passed, ruff clean, pyright 0/0. Exploit test flipped red->green.
Induction is now first-class `Induct(var,pred,base,step)`; schema-as-axiom path
(is_induction_instance + Theory.schemas) deleted; Theory gained zero/succ.
README + roadmap updated. NEXT: commit, then commutativity.
Details below (kept for the record):

## (resolved) CRITICAL SOUNDNESS BUG — was IN PROGRESS
Induction was encoded as a recognized AXIOM formula `P[0] -> ((P -> P[Sx]) -> P)`
with free x. Under implicit-forall, that means forall x.[...] which is FALSE
(the forall must wrap only the STEP). EXPLOIT CONFIRMED (red test):
P(n):=n=0, instantiate x:=1, prove the closed step (1=0)->(2=0), extract
`|- S(0) = 0` i.e. 1=0. test_induction_schema_not_exploitable_to_derive_falsehood
FAILS against pre-fix code. This is real unsoundness, not style.

FIX (reviewer's design): first-class `Induct(var, pred, base, step)` proof term.
Checked atomically:
  base: G |- pred[var:=0]; step: D |- pred -> pred[var:=S var];
  var NOT free in G u D  ==>  G u D |- pred.
Delete the schema-as-axiom path entirely (is_induction_instance + Theory.schemas)
so the false formula can never be cited as an axiom.

### Progress on the fix
- checker.Theory: dropped `schemas`; added `zero`/`succ` (induction structure);
  accepts() = f in axioms only. DONE.
- checker: added Var import; validate_proof handles Induct; _derive implements
  the Induct rule with the var-not-free-in-hyps side condition. DONE (pyright
  noise until proof.Induct lands + Term annotations).
- proof.Induct node added. DONE. STILL TODO: serialization (to_dict/from_dict).
- peano: remove is_induction_instance; PEANO=Theory(axioms,zero=ZERO,succ="S");
  induction() returns Induct node. TODO.
- Theory.zero/succ annotate as Term|None / str|None (+ Term import) to clear
  pyright arg-type. TODO.
- Tests: IN PROGRESS.
  * proof.Induct + serialization DONE. checker Induct rule DONE. peano DONE
    (PEANO zero=ZERO succ="S", induction()->Induct, recognizer removed).
    __init__ exports Induct DONE.
  * test_checker: removed is_induction_instance import. STILL must replace
    test_induction_recognizer_accepts_genuine_instance and _rejects_bogus
    (lines ~272-283) with Induct rule tests (wrong-base, wrong-step,
    var-free-in-hyp reject). Keep test_induction_builder_roundtrips (uses
    induction()->Induct now).
  * test_properties: remove is_induction_instance import + the two recognizer
    property tests (is_complete, rejects_wrong_shape). Maybe add a property:
    prove_add-style is fine; could add induction-based property later.
- Run uv pytest/ruff/pyright; commit. TODO.
- The 3 `"other" not accessed` pyright stars in test_checker are the Evil
  __eq__ params — harmless, pre-existing style infos.

## DONE earlier: uv env + property tests + package move
- Package move COMPLETE. cold_start/ holds the 6 modules + __init__.py (public
  API). All intra-package imports relative; tests import `cold_start.x`;
  verify subprocess uses `python -m cold_start.verify`; proofs/verify run via
  `-m`. check() params now `object` (honest + kills pyright unreachable).
  README module paths + run cmds updated to package/uv. Roadmap ticked.
- VERIFIED: uv run pytest = **37 passed** (23 example + 14 property);
  uv run ruff = clean; uv run pyright = 0/0; `-m cold_start.proofs` prints
  `|- +(0, n) = n`.
- NEXT ACTION: commit the package move + property tests + README. (uncommitted)

## (historical) IN PROGRESS notes below
- DONE: converted to uv project (.venv + uv.lock, dev deps pinned; commit d360532).
  Run everything via `uv run pytest|ruff|pyright`. NO MORE system python / npx.
- DONE: test_properties.py — 14 Hypothesis property tests, all green. Covers
  JSON round-trips, checker totality, validate accepts canonical, subst algebra
  (nonfree identity / free-vars law / idempotence), a SOUND prove_add generator
  the checker must agree with, serialization-preserves-sequent, determinism,
  induction recognizer completeness + wrong-shape rejection.
- IN PROGRESS: moving 6 modules into `cold_start/` package (flat, no src). Done:
  git mv all 6; added __init__.py (public API); fixed relative imports in
  proof.py, checker.py, peano.py; changed check() params to `object` (kills a
  pyright unreachable warning, more honest). STILL TODO:
    - proofs.py imports -> relative (peano/proof/syntax + __main__ block).
    - verify.py imports -> relative; run as `python -m cold_start.verify`.
    - test_checker.py + test_properties.py imports -> `from cold_start.x import`.
    - test_checker subprocess call -> `[sys.executable, "-m", "cold_start.verify"]`.
    - README module paths -> cold_start/.
    - Re-run uv run pytest/ruff/pyright; commit the package move.

## Next step (after move)
- `n + 0 = 0 + n` → commutativity of `+`, then associativity (first nested
  induction). Alt: add `Not` for `0 != S(x)` + successor injectivity.

## Blockers
None.

## 2026-08-03: verify theory registry + derived Robinson addition (in progress)
Task: (1) register presburger + robinson in verify.THEORIES; (2) proofs.robinson_add_proof(a,b)
deriving bridge(a,b,a+b) from ADD_ONE/ADD_SUCC by MP recursion; (3) ARCHITECTURE.md honesty
paragraph. Read: verify.py (_load_theories only has peano), robinson.py (ADD_ONE=bridge(a,1,Sa),
ADD_SUCC=Implies(bridge(a,b,c),bridge(a,Sb,Sc)), free vars "a","b","c"), proof.Inst(sub,var,term),
proof.MP(imp,ant), proofs.add_proof pattern. No blocker yet.
- TASK 1 DONE = 62e1d72: verify.THEORIES now has peano/presburger/robinson; 3 new
  cross-process tests in test_checker.py (_run_verify takes *args now).
- TASK 2 DONE = 52eeaf8: proofs.robinson_add_proof(a,b) = Inst(Axiom(ADD_ONE),"a",N a)
  at b==1, else MP(Inst^3(Axiom(ADD_SUCC), a/b/c := N a, N(b-1), N(a+b-1)),
  robinson_add_proof(a,b-1)). ValueError for a<1 or b<1 (positive-integer domain).
  30 new tests in test_robinson.py. 352 passed, ruff clean (on cold_start+tests),
  pyright 0. NOTE: `uv run ruff check .` also descends into .claude/worktrees/
  agent-*/ (another agent's tactics work) and reports 3 F401 there -- not ours.
- TASK 3 IN PROGRESS: ARCHITECTURE.md last paragraph rewrote "make her bridge a
  checked theorem" -> concrete instances are DERIVED (cites robinson_add_proof +
  tests), with an explicit note that the general definability theorem is NOT derived.
  No blocker.
- TASK 3 DONE = cddd630 (ARCHITECTURE.md + these notes). ALL THREE TASKS COMMITTED:
  62e1d72, 52eeaf8, cddd630. Final gate after the last commit: 352 passed, ruff clean
  on cold_start+tests, pyright 0 errors, git status clean (only untracked .claude/ and
  papers/Wehrung_2024_*, neither mine). Stale editor diagnostic about test_checker.py
  ~line 368 (undefined robinson_add_proof/ADD_ONE/numeral) is RESOLVED: line 23 imports
  robinson_add_proof from cold_start.proofs, and ADD_ONE/numeral are no longer
  referenced there (ruff --fix pruned the now-unused numeral import when the
  cross-process robinson test was upgraded from the bare axiom instance to the derived
  proof). No blocker; work complete.

LEAN 4 RESOLVED: 4.32.2 extracted to ~\.lean4, linked as elan toolchain
`lean4-manual`, set default. Shim: %LOCALAPPDATA%\Microsoft\WinGet\Links\
lean.exe -> 4.32.2, sanity-compiled a Nat theorem OK. Told lean-coder to
prefer the shim (bare `lean` is still choco 3.4.2) and make the compile
test actually run against ColdStart.lean.

ANALYST VERDICT (tactics layer, merged main): NO soundness defect, no
BLOCKER. All four tactic theorems exact (empty hyps, literal conclusions).
Findings -> dispatched to fixes-coder as fix list:
1 MAJOR: rules-as-generator silently yields non-normal form (rules iterated
  inside walk loop; fix = materialize tuple at public entry points).
2 MINOR: normalize budget off-by-one (N-step chain needs N+1; budget=0
  rejects even a normal form).
3 MINOR: Rule garbage escapes as TypeError/AttributeError deep inside.
4 MINOR: lemma_rule "hypothesis-free" contract unenforced (violation is
  sound — hyps surface in sequent — but API overpromises; docs+tests).
5 NOTEs: bare assert in _under_context spine walk; free_var_sorts dict
  collapse on dual-sorted var. Plus missing tests: lemma_rule at all,
  budget step counts, `!`-named-var adversarial, sorted-theory tactics.
7: add_proof/mul_proof/robinson_add_proof recurse per unit of b
  (RecursionError ~950-1000) -> convert to loops; checker itself fine at
  depth (iterative claim HOLDS, round-trip clean at 500).
Also: ruff format --check would reformat 18 files repo-wide (pre-existing;
project gates on ruff check only — leave alone).

## 2026-08-03 pt2: analyst findings in the tactics layer (7 items)
Baseline on merged main (7148bbc): 389 passed. Items, priority order:
1 MAJOR one-shot iterable of rules exhausted in _find_redex -> DONE = 5bad4ea
  (tuple(rules) at normalize/prove_eq/by_induction/rewrite_step; 4 red tests first).
2 budget off-by-one (range(budget) spends one iteration detecting the fixpoint;
  budget=0 on a normal form raises) -> IN PROGRESS, 2 red tests written.
3 Rule input garbage -> TypeError/AttributeError from deep inside; add cheap
  __post_init__ + sigma validation raising TacticError.
4 lemma_rule precondition unenforced -> sharpen docstring + pin both behaviours.
  DECISION: NOT adding the bare-Assume structural guard -- it catches exactly one
  spelling (Trans(Assume(lie),Refl(..)) walks straight past), so it would make the
  "unenforced" docstring self-contradictory and read as enforcement it isn't.
  Report this to the lead.
5 _under_context bare assert -> explicit raise; Rule.instance dict(free_var_sorts())
  silently collapses a var used at two sorts -> raise TacticError naming it.
6 tests only: `!`-suffixed var name in a rule equation (plan: lemma_rule over
  Inst(Axiom(ADD_SUCC_F),"y",Var("x!")) -- a real hypothesis-free lemma with free
  vars {x, x!}); many-sorted run over algebra.MONOID_ACTION (ACT_ID/ACT_COMP).
7 separate commit: add_proof/mul_proof/robinson_add_proof recurse per unit of b
  -> convert to loops building from the base upward, identical proof terms.
Do NOT touch: cold_start/lean.py, tests/test_lean.py, lean_export/.

LEAN-CODER DONE (worktree branch worktree-agent-ad5a787c7340c95ed, 6 commits):
cold_start/lean.py + tests/test_lean.py (43 tests) + lean_export/ColdStart.lean.
THE RESULT: corpus COMPILED under Lean 4.32.2, exit 0, zero emitter fixes
needed; negative control (corrupt an induction base) fails compile -> the
check has teeth. 395 passed in its tree, zero skips, ruff+pyright clean.
Design: Inst emits nothing (substitution env threaded through rendering, so
instantiation is independent of Inst nesting); conditional theorems (axioms
as hypotheses, never `axiom`); Robinson stays conditional deliberately
(succ a ≠ 1 false at 0, ℕ not a model); Presburger/Peano get ℕ epilogue.
Version-gated probe: elan shim first, choco lean 3.4.2 skipped on version.
MERGE ON HOLD until fixes-coder (analyst findings, working in main checkout)
reports — avoid git-index contention. Then: merge lean branch, full gates,
one-line lean.py mentions in README/ARCHITECTURE (lean-coder left docs to
us), final wrap. This notes edit deliberately uncommitted until main is free.
- Items 2,3 DONE = c2ac121 (budget counts applied steps; while-loop charges only on
  apply), 030b705 (Rule.__post_init__ + sigma check at top of instance, before the
  ground-rule early exit; fire computes instance FIRST so _subst_all never sees junk).
- Item 4 DONE (docstring + 3 characterization tests; NO behaviour change -- they pass
  on write, which is the point of pinning). Found a third failure mode worth pinning:
  a lemma_rule lie WITH free variables cannot even be instantiated, because Inst
  refuses to substitute a variable free in a hypothesis -> check rejects outright.
  Still declining the bare-Assume guard for the reason logged above.
- Item 5 DONE = 19e57ed (_under_context assert -> TacticError raise; instance builds
  the sorts dict with setdefault and raises on a var used at two sorts).
- Item 6 DONE (tests only): bang-name rule via lemma_rule over
  Inst(Axiom(ADD_SUCC_F),"y",Var("x!")) -- free vars exactly {x, x!}; many-sorted run
  over algebra MONOID_ACTION (ACT_ID/ACT_COMP) plus a wrong-sort instance that check
  rejects. NON-VACUITY PROBED: neutering _fresh's avoid loop makes the bang test fail
  (x and x! collapse, proof proves a different equation). Restored via git checkout.
- NEXT: item 7, iterative add_proof/mul_proof/robinson_add_proof (separate commit).
- Item 7 IN PROGRESS: all three builders converted to loops (build base, fold upward).
  Proof terms verified IDENTICAL to the recursive spelling over a 7x7 grid of (a,b)
  against a scratch reference implementation -- 0 mismatches. Red confirmed first:
  add_proof/robinson_add_proof(1,2000) both RecursionError; threshold was b~990.
  NOW SIZING the test: timing run at 2000 exceeded a 120s foreground timeout, so
  check() at that depth is the expensive part (quadratic-ish: each of b steps embeds
  numerals of size up to b). Waiting on the background timing to pick sizes.
- Item 7 DONE. Sizing measured: add_proof(1,2000) build 2.4s/check 4.3s;
  robinson_add_proof(1,2000) build 9.2s/CHECK 82s (bridge repeats each argument ->
  quadratic term growth); mul_proof(2,1200) build 1.7s/check 44s. So the test builds
  at DEEP=1200 (recursion limit is exactly 1000; the recursive spelling was confirmed
  RecursionError at 1000/1100/1200) and checks end-to-end at 300/250. ~12s added,
  suite now 75s. check()'s own iterativeness is pinned separately at 6000 deep.

WRAP-UP: fixes-coder landed all 7 analyst findings (5bad4ea..b049eed; its
judgment calls accepted: no fake bare-Assume guard, deep-check at 1200
build / 300 check for runtime sanity). My notes append rode along in
b049eed, which made my later notes-commit a no-op and short-circuited the
first lean merge attempt (&&-chain) — reran merge, clean, no conflicts.
MERGED MAIN GATES: 453 passed in 73s, ruff clean, pyright 0/0/0 — includes
the real Lean 4.32.2 kernel-compile tests (no skips). Docs one-liners
added: README (lean.py entry), NOTES.md layout + count 317->453,
ARCHITECTURE.md new "The independent kernel (lean.py)" section (NB file had
drifted on disk — reports/lean-export-notes.md also arrived in merge).
REMAINING: commit docs, verify worktree cleanup, final report to Q.
Blockers: none.

## Session 2026-08-03: improving cold_start.robinson (theory brainstorm)
- Q asked: how to improve robinson.py; modern extensions; "something actually cool".
- STATE SURVEYED: robinson.py = 6 axioms over (1,S,·), bridge() = Robinson Thm 1.1
  identity; robinson_add_proof climbs A4'/A5' for closed numerals. Notes list two
  open follow-ups: mechanise Thm 1.2 (S,|) and a genuine induction proof in
  ROBINSON_PEANO. proofs.py has add laws (comm/assoc) via tactics; NO mul laws yet
  (README roadmap: `*` laws unchecked). Tactics = directed rewriting + by_induction.
- FOUND: papers/Wehrung_2024 (arXiv 2405.08364, untracked) IS the modern extension:
  brachymorphisms f(1+x)=1+f(x), f(xy)=f(x)f(y) between rings — is every one
  additive? Open in general; positive for Artinian, 2x2 matrices, pi-regular, etc.
- PDF was owner-password protected (like Robinson's); qpdf --decrypt to scratchpad
  succeeded, qpdf reports "not encrypted", but the Read tool STILL refuses it
  (current blocker; Robinson notes say the workaround was qpdf + magick -> PNGs).
- CANDIDATE PROPOSALS (to pitch): (1) prove PEANO |- bridge(a,b,a+b) as a ring
  identity — both sides ab(a+b)^2+(a+b)^2+1 — needs mul laws first, closes roadmap
  item; then A4'/A5'/A7' as Peano theorems = interpretation soundness / relative
  consistency. (2) Padoa's method as a test: prime-swap automorphism of (N,·)
  preserves · but not + (2+2=4 vs 3+3=6≠9) — cheap, exactly Robinson's p.100 cite.
  (3) Brachymorphism rigidity: axioms f(1)=1, f(Sx)=S(fx) |- ∀x f(x)=x by induction
  — Wehrung tie-in. (4) big digs: full interpretation functor, Thm 1.2 (S,|).
- DISPATCHED (Opus, worktree-isolated, background): (1) bridge-prover — mul laws
  ladder, PEANO |- bridge(a,b,a+b), A4'/A7' (+A5' stretch); (2) padoa-tester —
  prime-swap automorphism tests, tests/test_padoa.py; (3) wehrung-tester —
  ROBINSON_PEANO induction rigidity f=id (+ multiplicativity bonus), Komatsu
  brachynomial search tests, Wehrung notes.md. Each gates on pytest/ruff/pyright
  and commits in its worktree; I merge + final-gate on completion.
- MERGED: padoa-tester (8f32e58, 0bd8119 -> merge) and wehrung-tester (13d5fef..
  d144570 -> merge). Gate on merged main: 1055 passed in 107s, ruff clean
  (--exclude .claude, since the live bridge worktree leaks into root ruff runs),
  pyright 0/0/0. Wehrung metadata.json + notes committed (c218537 + follow-up).
  Merged worktrees/branches removed. REMAINING: bridge-prover still running
  (diagnostics show ordered-rewriting work in tactics.py + robinson_proofs.py —
  the mul-laws ladder and bridge theorem in progress).
- bridge-prover DONE, all 4 levels: mul ladder (0n, Sxy, comm, distrib LR, assoc),
  PEANO |- bridge(a,b,a+b) via new ORDERED (permutative) rewriting in tactics.py +
  poly_kit canonical-polynomial normalization; A4'/A7' derived on the nose; A5'
  REFUTED — false in N at c=0 (vacuous hypothesis, conclusion forces a+b=0), the
  precise job of Robinson's positive-integer domain, pinned by a test. Its gates:
  552 passed, ruff/pyright clean. Commits 25e7948..8a0d69d.
- MERGING now: conflicts in README.md (module list, resolved: both-additive — mul
  ladder + robinson_proofs.py + rigidity.py entries) and Robinson notes.md
  (resolved: keep Padoa section + bridge-theorem section). One stray >>>>>>> marker
  left in notes.md to remove; then verify Open follow-ups list, commit merge, run
  full gate (pytest tests, ruff --exclude .claude — bridge worktree still present
  until cleanup — pyright), then remove last worktree/branch.
- No blockers.
- bridge-prover MERGED (c3732bd): README/notes.md conflicts resolved both-additive;
  ticked the ROBINSON_PEANO-induction follow-up (rigidity.py) in Robinson notes.
  FINAL GATE on merged main: 1154 passed in 101s, ruff clean, pyright 0/0/0.
  All three worktrees/branches removed. Campaign complete: bridge theorem + mul
  ladder + ordered rewriting; A5' refutation; Padoa tests; rigidity + Komatsu;
  Wehrung paper notes. Suite 453 -> 1154.
