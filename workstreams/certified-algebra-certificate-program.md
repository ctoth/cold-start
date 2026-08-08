# Certified Algebra and Portable Proof Certificates

Date: 2026-08-08

Status: accepted for full execution on 2026-08-08; implementation in progress.

## Decision summary

The next program should build one connected capability in three layers:

1. Harden the existing checker for shared, possibly hostile in-memory proof
   graphs. It must reject cycles and derive each exact proof object once without
   changing any logical rule.
2. Replace raw tree-shaped proof bytes with a versioned, theory-bound,
   claim-bound, resource-bounded certificate whose wire representation preserves
   proof and syntax sharing.
3. Consolidate polynomial reasoning behind one untrusted sparse normalizer, then
   use it to replay characteristic-2 Groebner ideal-membership witnesses produced
   by an untrusted Buchberger search.

No CAS operation becomes a trusted proof rule. The final authority remains the
ordinary checker re-deriving an ordinary proof graph against an explicitly
registered theory.

The recommended execution order is:

```text
checker graph hardening
        |
        v
F2 sparse ring normalization ---> measured certificate sizes
        |                                  |
        v                                  v
certified F2 ideal membership       certificate wire + budgets
        |                                  |
        +----------------+-----------------+
                         v
                  certifying Cooper
```

This inserts a bounded certified-algebra campaign before the already-authorized
Cooper milestone. It does not silently reorder the decidability program; that
ordering requires explicit approval before implementation begins.

## Evidence for the change

The present design is logically well factored but its artifact representation is
not scaling with its mathematics.

- The current Jacobian determinant proof has 47,147 proof-node occurrences but
  only 13,682 distinct in-memory proof objects. Its Hamblin tree encoding is
  2,094,481 bytes.
- The complete ring-of-integers interpretation has a 51-node bridge and an
  876,035-node proof toll.
- `checker.py` stores derived sequents by object identity, but its validation and
  postorder traversals still expand every incoming edge. In-memory sharing
  therefore does not currently reduce traversal work.
- `codec.py` serializes proof trees. Shared subproof identity is lost on the wire.
- `verify.py` receives the theory choice outside the proof bytes, and a raw proof
  carries neither an asserted sequent nor a stable theory fingerprint.
- Rewriting has a tactic budget, but decoding and trusted checking have no
  deterministic byte, graph, syntax-construction, or sequent-work budget.
- `peano_proofs.ring_kit`, `jacobian2_proofs.normal_form_rules`, and
  `combination.by_combination` expose the same missing abstraction at different
  levels: compute a polynomial identity, then replay it through ordinary
  equality rules.
- The proposed cofactor replay is not a new proof shape: it is exactly
  `by_combination`'s current checked shuffle
  `goal.lhs + H_R = goal.rhs + H_L`, with its manually supplied coefficients
  replaced by Buchberger-synthesized cofactors.

## Governing constraints

The implementation must preserve all of these boundaries.

- `checker.py`, the intrinsic syntax/proof/sequent validation it drives, and the
  chosen theory's axioms remain the trusted proof authority.
- Proof and syntax values remain inert. Constructing a `Certificate`, `Pf`,
  polynomial, Groebner basis, or cofactor witness proves nothing.
- `codec.py` remains the singular byte owner. No proof or certificate byte methods
  move onto syntax, proof, certificate, CAS, or theory classes.
- Lean syntax/proof export remains an untrusted external adapter. Its exhaustive
  cases continue to read the canonical owner sets; its coverage and inspection
  traversals receive an explicit disposition when proof sharing lands rather than
  becoming an accidental second certificate verifier.
- The portable certificate is bound to a caller-authorized registered theory. An
  embedded arbitrary theory must never authorize its own axioms.
- The checker must independently validate a decoded proof graph. It must not rely
  on the untrusted decoder's topological or exact-type claims.
- The CAS layers emit only the existing sixteen proof constructors. There will be
  no trusted `RingNormalize`, `Groebner`, `Oracle`, or certificate-by-assertion
  proof rule.
- Characteristic 2 means coefficient parity, not Boolean-ring semantics.
  `x*x = x` is unavailable unless a separate theory explicitly assumes it.
- Old and new production wire formats, polynomial normalizers, and helper APIs do
  not remain in parallel at the fixed point. Migration is deletion-first by
  bounded slice.
- Existing untracked notes and unrelated worktree material remain untouched.

## Target ownership

| Concept | Owner | Responsibility | Forbidden responsibility |
|---|---|---|---|
| Canonical proof nodes | `proof.py` | The existing inert rule dataclasses and canonical type inventory | Wire references, DAG tables, CAS certificates |
| Proof-graph validation and derivation | `checker.py` | Exact types, acyclicity, unique postorder, deterministic work accounting, rule semantics | Hamblin parsing, theory routing, polynomial reasoning |
| Portable artifact value | `certificate.py` | Inert `Certificate` value: version, theory binding, claimed sequent, proof root | Encoding, checking, theory authorization |
| External bytes | `codec.py` | Canonical certificate table encoding/decoding, size/count limits at the IO boundary | Logical derivation or trusting the artifact's claim |
| Registered verification workflow | `verify.py` | Read-limited input, registered theory routing, fingerprint comparison, checker invocation, claim comparison, stable diagnostics | Accepting embedded axioms or CAS-specific validation |
| Generic polynomial normalization | `ring_nf.py` | Sparse polynomial IR, algebra contexts, reification, quotation, proof-producing normalization | Theory-specific axioms, Buchberger search, trusted shortcuts |
| Characteristic-2 proof kit | `diffring2_proofs.py` | Derived zero/identity/AC/cancellation lemmas and the `DIFF_RING_2` normalization context | Jacobian definitions or generic polynomial algorithms |
| Ideal-membership search | `groebner2.py` | F2 monomial arithmetic, Buchberger, cofactor tracking, bounded deterministic search | General rings, field semantics, proof authority |
| Jacobian certificate | `jacobian2_proofs.py` | Map, derivative statements, determinant, collisions, and use of generic certified algebra | Owning a second ring normalizer |

The decoded `Certificate` contains the shared canonical `Pf` graph, not the wire
table DTOs. Wire-only records stay private to `codec.py` and are reconstructed
from the canonical syntax/proof owner metadata rather than maintained as a second
handwritten rule inventory.

### Reconciliation with the earlier cleanup workstream

The opening target diagram in `repository-architecture-cleanup.md` assigned
trusted rule semantics to proof classes. The completed current implementation
instead has inert proof dataclasses and exact exhaustive rule semantics in
`checker.py`; the later fixed-point record in that workstream and current source
are the authority for this program.

This design does not reopen proof-method ownership or move rule semantics back to
`proof.py`. Such a methodization would overlap the trusted Phase 1 traversal and
requires a separate explicit architectural decision. Phase 0 records the early
workstream wording as superseded by current production so the two plans cannot be
executed concurrently as if they agreed.

## 1. Checker graph hardening

### Target invariant

For the current proof language, a proof node's derived sequent is a pure function
of:

- the exact node and its immutable fields;
- the already-derived sequents of its child proof nodes; and
- the selected validated theory.

No rule receives an ancestor-supplied local context. Hypotheses accumulate upward
in returned sequents. This context-independence is the reason one shared proof
object may be derived once and reused by several parents.

That invariant becomes a documented admission condition for every future proof
rule. A rule whose meaning depends on its parent occurrence may not enter this
proof language without redesigning the memoization key and the soundness argument.

### Required traversal

`checker.py` will own one iterative tri-color graph traversal:

- unseen: the object has not been entered;
- active: its exact type and immediate fields passed local validation and its
  children are being explored;
- complete: every child is complete and the node is in unique postorder.

An edge to an active node is a cycle and is rejected. An edge to a complete node
is sharing and is not expanded again. The resulting postorder contains each
reachable proof object identity exactly once.

The traversal must work for hostile exact dataclass instances mutated through
Python escape hatches. Backward-only wire references are insufficient because
library callers may pass in-memory graphs directly to `check()`.

`validate_proof` and `_derive` consume the same validated unique postorder so they
cannot disagree about graph shape. `id()` is safe as a per-call key because the
root strongly retains every reachable node for the traversal's lifetime; no
identity cache survives the call.

### Deterministic work accounting

Resource limits are caller policy, not attacker-supplied certificate fields. A
`CheckLimits`/work-meter contract must eventually account for at least:

- unique proof nodes and child edges;
- unique input syntax nodes and syntax edges;
- hypothesis-set elements processed;
- nodes visited or rebuilt by substitution, binder instantiation, sort checking,
  and derived formula construction;
- maximum single term/formula size and maximum derived sequent size.

Wall-clock time is not an acceptable semantic budget. The initial graph-hardening
slice may land before full syntax-operation metering, but the certificate cannot
be called resource-bounded until both decode limits and deterministic trusted-work
limits are enforced.

## 2. Portable certificate design

### Runtime value

The inert runtime artifact has these semantic fields:

```text
Certificate
  version: exact positive integer
  theory_key: stable registered slug
  theory_fingerprint: 32 bytes
  claim: Sequent
  proof: Pf
```

Constructing this object proves nothing. Verification succeeds only when all of
the following hold:

1. the version is supported;
2. `theory_key` resolves through the verifier's closed registry;
3. the registered theory's canonical fingerprint equals the embedded fingerprint;
4. the checker accepts the proof under that registered theory within local limits;
5. the checker-derived sequent equals `claim` exactly.

The theory key routes to an externally authorized trust base. The fingerprint
detects registry drift and misrouting; it does not let the certificate authorize
axioms. Unknown theory keys are rejected.

### Theory fingerprint

Version 1 fixes SHA-256 and a domain-separated, length-prefixed canonical
preimage. The semantic preimage includes:

- a format tag such as `cold-start-theory-v1`;
- sorted signature sorts;
- function ranks sorted by symbol name, with argument and result sorts;
- relation ranks sorted by symbol name, with argument sorts;
- axioms sorted lexicographically by their canonical formula bytes;
- explicit absent/present markers plus the canonical zero term and successor
  symbol for induction.

Tuple or frozenset iteration order never affects the digest. The theory slug is
not part of the semantic digest; two registry names may intentionally identify
the same exact theory, while routing remains explicit.

### Wire graph

The version-1 byte payload contains:

```text
header
  magic
  version
  theory key
  theory fingerprint
syntax table
  exact canonical node tag + primitive fields + lower syntax references
proof table
  exact canonical proof tag + primitive fields + syntax references
  + lower proof references
claim
  sorted hypothesis syntax references + conclusion syntax reference
root
  proof-table index
```

All references are unsigned bounded indices. A table entry may reference only a
lower index in the same table; the proof table may reference any completed syntax
entry. This makes wire cycles and forward references structurally invalid.

Encoding uses structural hash-consing in the following fixed order:

1. Compute an exact structural key for each reachable syntax value iteratively
   from its exact canonical tag, primitive fields, ordered tuple fields, and
   child structural keys. Sets use their members' sorted structural keys. A hash
   may accelerate lookup but equality and ordering never rely on a digest alone.
2. The syntax roots are the claim conclusion; claim hypotheses sorted by exact
   structural key; then every syntax-valued field encountered in the proof
   root's dataclass-field/tuple-index depth-first traversal. Claim-only and
   proof-reachable syntax share this one key space and one table.
3. Visit each syntax root depth first, fields in dataclass declaration order and
   tuple elements in increasing index order, append children before parents, and
   reuse the existing index for an equal structural key. This is the syntax
   table's canonical postorder.
4. Compute exact structural keys for proof values from the exact proof tag,
   primitive fields, syntax-table references, ordered tuple fields, and child
   proof structural keys. Traverse the proof root depth first in dataclass-field
   and tuple-index order, append children before parents, and reuse the existing
   index for an equal structural key. This is the proof table's canonical
   postorder.

Consequently every table reference is backward, structurally equal subgraphs are
shared regardless of producer allocation identity, and two independent encoders
following the field-order algorithm produce the same tables and bytes. Decoding
materializes each entry once and reuses that exact object for all references.
Equality, not object identity, remains the logical notion; sharing is an artifact
compression and evaluation property.

Wire tags and fields are derived from `CANONICAL_NODE_TYPES`,
`CANONICAL_PROOF_TYPES`, and dataclass metadata. The codec must still fail closed
if its supported field-kind logic is not exhaustive. It must not hand-maintain a
second list of rule schemas that can drift from the owners.

### Canonicality

- Unknown magic, version, type tag, field kind, or trailing bytes are rejected.
- Strings are genuine strings with length limits and one fixed UTF-8 encoding.
- Integers use one fixed minimal unsigned encoding where applicable.
- Sets are represented by lexicographically sorted canonical entry bytes or
  sorted table references.
- Duplicate structurally equal syntax or proof entries are rejected on decode.
  The deduplication key is the exact tag-and-field structural key defined by the
  canonical postorder algorithm, not object identity or a hash alone.
- Re-encoding a decoded accepted certificate must produce identical bytes.

Structural hash-consing gives content-canonical bytes. In-memory identity sharing
alone is insufficient because two producers may allocate the same proof
differently.

### Decode and verification limits

`verify.py` reads at most the configured maximum bytes plus one sentinel byte; it
does not call an unbounded `read()` first. `codec.py` rejects before allocation
when declared counts or string lengths exceed local policy.

At minimum, local `CertificateLimits` cover:

- input bytes;
- syntax entries and syntax edges;
- proof entries and proof edges;
- tuple/set arity;
- string bytes;
- claim hypothesis count.

These are combined with the trusted checker work meter described above. Limits
have safe repository defaults and may be lowered by a caller. Raising beyond a
repository hard ceiling requires a deliberate code/configuration change, not a
field in an untrusted artifact.

### Migration boundary

The final public proof-wire API is `encode_certificate` and
`decode_certificate`. `encode_term`/`decode_term` and
`encode_formula`/`decode_formula` remain legitimate standalone fragment APIs.

The old public `encode_proof`/`decode_proof` API and the raw-proof verifier input
are deleted after all repository callers migrate. There is no dual decoder,
version sniffing fallback, compatibility alias, or raw-proof wrapper. This is a
v0 repository with no named external compatibility constraint.

`verify.py` routes from the embedded theory key and rejects an unknown or
fingerprint-mismatched theory. The current default-to-Peano behavior and the
external `--theory` selector are removed; the artifact states its trust base and
the verifier reports it.

## 3. Sparse proof-producing polynomial normalization

### Scope

`ring_nf.py` is an untrusted prover component. It reifies a supported term into a
sparse polynomial, computes a canonical form, and emits an ordinary proof of the
input term's equality to the quoted canonical term.

It does not ask the checker to evaluate a polynomial object. The polynomial is a
search/planning representation and never crosses the certificate boundary.

### Polynomial representation

```text
AtomKey     = canonical supported atomic Term
Monomial    = sorted tuple of (AtomKey, positive exponent)
Coefficient = natural | integer | bit, selected by the algebra context
Polynomial  = sorted finite map Monomial -> nonzero Coefficient
```

The monomial order is explicit, total, deterministic, and versioned within the
untrusted CAS layer. It is not the proof rule's termination order and must not
reuse a private tactic ordering accidentally. Quoted terms use a single exact
right-associated representation.

Atoms initially include variables and declared nullary generators. Unsupported
functions, relations, binders, or derivative applications are rejected at the
reification boundary. Derivative rules must eliminate `DX`/`DY`/`DZ` before ring
normalization begins.

### Algebra context

An immutable untrusted `AlgebraContext` supplies:

- exact symbol names for zero, one, addition, multiplication, and optional
  negation;
- coefficient domain: natural, integer, or mod 2;
- proved equality formulas and proof builders for additive/multiplicative
  associativity and commutativity, identities, zero multiplication,
  distributivity, and coefficient-specific cancellation/sign laws;
- quotation rules and deterministic proof budgets.

The context carries proof recipes, not semantic authority. Every emitted proof is
checked against the caller's theory. Supplying an F2 context to PEANO therefore
fails when it cites `CHAR2`; it cannot smuggle coefficient reduction into the
theory.

Three contexts are the target fixed point:

- commutative semiring: natural coefficients, used by PEANO polynomial
  identities and the integer-ring bridge's PEANO-side payments;
- commutative ring: integer coefficients and explicit negation laws;
- commutative characteristic-2 ring: bit coefficients, with duplicate monomials
  cancelled only through a checked `x+x=0` theorem.

Characteristic 2 does not reduce exponents. `x^2` remains distinct from `x`.
Grothendieck pairs are terms in a PEANO-side semiring proof, not a special
coefficient domain for the generic normalizer.

### Proof production

Reification returns both the polynomial and a proof from the original term to its
quoted form. Addition and multiplication recursively combine child proofs with
`Cong`, then use context-owned proved lemmas to merge sorted monomial lists,
distribute products, normalize coefficients, and right-associate the result.

This avoids making correctness depend on a second unchecked equality comparison
between a Python polynomial result and a term. `ring_eq(lhs, rhs, context)` proves
both sides equal to the same quoted form and joins the proofs with `Trans` and
`Sym`. If the canonical polynomials differ, it reports tactic failure and emits no
candidate proof.

The first implementation may reuse the existing `Rule` machinery for local
lemma instantiation, but the target owner is the sparse proof-producing fold, not
a new global rewrite schedule under another name.

### Deletion target

At fixed point:

- `jacobian2_proofs.normal_form_rules`, its AC rotation/cancellation schedule,
  and its generic zero/identity ring lemmas are absent;
- DIFF_RING_2 derived algebra facts and its context live in
  `diffring2_proofs.py`;
- `peano_proofs.ring_kit` is replaced by the semiring context and is absent;
- `combination.by_combination` is consolidated into the polynomial-combination
  elaborator or reduced to a private operation owned there; no forwarding facade
  remains;
- `ring_z.py` and existing proof libraries consume the one normalizer directly.

## 4. Certified Groebner ideal membership over F2

### Exact logical problem

Given checked or assumed equations

```text
hyp_i: L_i = R_i
goal:  L = R
```

reification over characteristic 2 produces

```text
h_i = poly(L_i) + poly(R_i)
g   = poly(L)   + poly(R)
```

because subtraction equals addition. Membership succeeds only with explicit
cofactors `q_i` satisfying the polynomial identity

```text
g = sum(q_i * h_i).
```

Buchberger must track each derived basis element as a vector of cofactors over the
original generators. A zero target remainder without that representation is not
an acceptable certificate.

### Search contract

`groebner2.py` owns:

- sparse F2 polynomial arithmetic;
- a fixed documented monomial order;
- S-polynomial construction and deterministic critical-pair ordering;
- reduction while carrying original-generator cofactor vectors;
- explicit step, degree, monomial, basis-size, and cofactor-size budgets;
- `NotMember`/`SearchExhausted` outcomes that prove nothing.

The algorithm is deliberately F2-only. Leading coefficients are either zero or
one, so reduction needs no coefficient division. Generalization to natural
semirings or integer/PID Groebner bases is a different project and cannot enter
through a generic flag.

The result `remainder != 0` means only that this complete bounded computation did
not establish membership under the implemented contract. A budget exhaustion is
never reported as non-membership. Neither outcome becomes a negative theorem.

### Witness elaboration

The cofactor identity is translated back to the existing equality proof language
without a CAS proof rule.

For each source equation and cofactor, the elaborator scales the equation using
`Cong("*", ...)`, combines scaled equations using `Cong("+", ...)`, and asks
`ring_nf` to prove the cross-sum identity

```text
L + sum(q_i * R_i) = R + sum(q_i * L_i).
```

The existing additive cancellation theorem then yields `L = R`. This is the
general form of the current `by_combination` recipe, with coefficients synthesized
rather than hand-authored.

The characteristic-2 rearrangement is explicit: in an exponent-2 abelian group,
`a+b=c+d` is equivalent to `a+c=b+d`. That theorem, replayed from AC and
`x+x=0`, justifies the cross-pairing above; it is not delegated to Python
polynomial equality.

Every source proof's hypotheses ride into the result through ordinary sequent
derivation. If callers use `Assume`, the result is conditional; if callers provide
closed theorem proofs, the result is closed. The CAS layer never discards or
asserts hypotheses.

Wrong cofactors cause `ring_nf` to find unequal canonical forms or produce a proof
the checker rejects. A deliberately corrupted witness is a required negative
control.

### Semantic boundary

This proves ideal consequences valid in commutative characteristic-2 rings. It
does not imply:

- variables range over the two-element field;
- every nonzero element is invertible;
- `x*x=x`;
- a common zero exists or does not exist;
- Hilbert Nullstellensatz conclusions;
- finite-field point enumeration.

Field equations or semantic-model claims require separate explicit theories and
proofs.

## Implementation plan

Each phase is one bounded branch/commit and records red evidence before its green
implementation. No phase is merged merely because later work depends on it.

### Phase 0 - Freeze contracts and baselines

Deliverables:

- accept this design and the proposed insertion before Cooper;
- record current determinant tree/unique/wire measurements and full gate timing;
- specify canonical certificate bytes and deterministic work units precisely
  enough for a future independent checker;
- identify every current raw proof-wire and polynomial-kit caller;
- inventory every non-checker consumer of `CANONICAL_PROOF_TYPES`,
  `CANONICAL_NODE_TYPES`, or generic proof traversal, including
  `lean/proof.py`, `lean/syntax.py`, `lean/models.py`, and `lean/coverage.py`;
- record that Lean proof emission remains tree-shaped presentation output, while
  coverage/model inspection is updated to identity-deduplicated traversal where
  duplicate visits add no semantics;
- reconcile the completed cleanup workstream's early ownership prose with the
  current inert-proof/central-checker implementation;
- correct the stale method-dispatch description in `cold_start/CLAUDE.md` before
  Phase 1 so repository working rules describe the current inert proof classes
  and central checker rather than the superseded `pf.derive(theory)` design;
- measure current Lean output bytes and proof-occurrence expansion for a valid
  deliberately shared proof graph, establishing the external-emission baseline
  before DAG-aware checking lands.

Reproduction commands for the current baselines are:

```powershell
uv run python -m cold_start.jacobian2_proofs
uv run python -m cold_start.ledger
```

The determinant tree/identity/wire measurement was obtained with
`det_proof()`, a dataclass-field traversal counting every `Pf` occurrence and
distinct `id(Pf)`, and `len(encode_proof(pf))`; Phase 0 preserves that exact
measurement procedure in its evidence record before the raw proof API is
deleted. Current results are 47,147 occurrences, 13,682 distinct proof objects,
and 2,094,481 bytes.

The exact command used for those three figures is:

```powershell
@'
from dataclasses import fields, is_dataclass
from cold_start.codec import encode_proof
from cold_start.jacobian2_proofs import det_proof
from cold_start.proof import Pf

proof = det_proof()
stack = [proof]
occurrences = 0
identities = set()
while stack:
    node = stack.pop()
    if isinstance(node, Pf) and is_dataclass(node):
        occurrences += 1
        identities.add(id(node))
        for field in fields(node):
            value = getattr(node, field.name)
            stack.extend(value if type(value) is tuple else (value,))
print(f"tree_nodes={occurrences}")
print(f"unique_objects={len(identities)}")
print(f"hamblin_bytes={len(encode_proof(proof))}")
'@ | uv run python -
```

Exit gates:

- design has no unresolved owner, trust, coefficient, or compatibility decision;
- current worktree dirt is inventoried and preserved;
- no implementation file has changed.

### Phase 1 - Unique acyclic proof graph

Red contracts:

- an exact canonical `Pf` object graph containing a cycle is rejected without a
  hang or recursion failure;
- one subproof shared through several parents is locally validated and derived
  once;
- sharing changes neither the derived sequent nor rejection behavior;
- every canonical proof type remains independently handled by the checker;
- Lean coverage/model inspection terminates without duplicate semantic counting,
  and a deliberately low external emission budget rejects tree expansion cleanly
  rather than exhausting memory or producing partial output.

Implementation:

- create the single tri-color unique-postorder owner in `checker.py`;
- make validation and derivation consume it;
- document context-independent child derivation as a proof-rule admission
  invariant;
- add focused trusted-base mutations for missing cycle/sharing guards.

The same shared/cyclic synthetic proofs are passed through current Lean entry
points after `check()`. Lean coverage/model inspection must terminate and avoid
duplicate semantic counting. Lean text emission may initially expand a valid DAG
as a tree because it is external presentation, but it receives its own explicit
output-byte and expansion-work limits; DAG-aware `have` emission is a later
optional optimization. Input DAG limits alone do not bound unfolded Lean text.

Exit gates:

- focused checker, kernel-boundary, quantifier, sort, property, and hostile-input
  tests pass;
- full repository gate and forced trusted-base mutation campaign pass;
- no logical rule, proof dataclass, or accepted sequent changed.

### Phase 2 - F2 sparse normalizer vertical slice

Red contracts:

- `ring_nf` does not exist for basic F2 identities, duplicate cancellation,
  genuine powers, and unequal-polynomial rejection;
- unsupported derivative/binder/relation terms fail explicitly;
- supplying the F2 context under a theory without `CHAR2` cannot yield an
  accepted proof.

Implementation:

- add `ring_nf.py` with only the coefficient/context surface needed by F2;
- add `diffring2_proofs.py` and move the generic derived DIFF_RING_2 algebra
  lemmas there;
- migrate Jacobian derivative post-processing and determinant normalization;
- delete the old Jacobian polynomial normal-form schedule in the same slice.

Exit gates:

- every current Jacobian statement and fresh-process check is unchanged;
- determinant proof toll and construction time are measured against baseline and
  may not regress without an accepted explanation;
- old F2 normalizer/helper search gates have zero production hits;
- full gate, Lean freshness, and Lean compilation pass.

### Phase 3 - F2 ideal-membership hello world

Red contracts:

- a small two-generator membership requiring a nontrivial S-polynomial has no
  prover;
- corrupted cofactor vectors fail;
- a true non-member returns `NotMember` without a proof;
- a deliberately tiny budget returns `SearchExhausted`, not `NotMember`;
- no Boolean-ring identity is accepted from characteristic 2 alone.

Implementation:

- add deterministic `groebner2.py` with original-generator cofactor tracking;
- add the polynomial-combination elaborator through `ring_nf` and existing proof
  constructors;
- prove one small closed/conditional example before applying it to a
  Jacobian-derived consequence.

Exit gates:

- ordinary `check()` accepts the generated proof under DIFF_RING_2;
- the checker and proof inventories have no CAS-specific addition;
- toll, search steps, maximum degree, basis size, and proof construction time are
  reported;
- full repository gates pass.

### Phase 4 - Portable DAG certificate wire

Red contracts:

- certificate import fails before the new owner exists;
- unknown version/tag, malformed field, trailing bytes, forward/cyclic/out-of-
  range references, duplicate noncanonical entries, theory mismatch, claim
  mismatch, and each resource limit are rejected;
- repeated subproofs and syntax decode to shared exact objects;
- encode/decode/re-encode bytes are identical;
- a deep valid graph remains recursion-free.

Implementation:

- add inert `certificate.py`;
- add canonical theory fingerprinting and private table records in `codec.py`;
- add read-limited, embedded-theory certificate verification in `verify.py`;
- migrate every repository proof-wire caller;
- delete public raw proof encode/decode and the external theory selector.

This phase also extends assurance tooling without relabeling the codec or CLI as
logical proof trust. `tools/mutate.py` and `gate.ps1` gain two explicit campaigns:

- the existing logical-kernel campaign for checker/proof/syntax/sequent/theory;
- a portable-verifier boundary campaign for `codec.py`, `verify.py`, certificate
  fingerprint/claim routing, and their adversarial tests.

Changes to either source/test slice trigger its own campaign. The portable
campaign proves fail-closed routing, canonical decoding, claim comparison, and
resource rejection; it does not make decoded values authoritative without the
ordinary checker.

Exit gates:

- no raw proof-wire production API or fallback decoder remains;
- independent fresh-process acceptance/rejection tests cover every registered
  theory, including DIFF_RING_2;
- current determinant certificate shows material byte and repeated-work
  reduction;
- full gate plus both forced logical-kernel and portable-verifier mutation
  campaigns pass.

### Phase 5 - Deterministic checker work limits

Red contracts:

- small graph/large-substitution amplification, excessive hypotheses, huge
  strings, and large derived formulas exceed named deterministic limits;
- lowering limits rejects predictably while defaults accept all official
  certificates;
- an artifact cannot raise its verifier limits.

Implementation:

- thread a trusted work meter through intrinsic syntax reconstruction,
  substitution, binder instantiation, sort checking, sequent combination, and
  proof derivation;
- size repository defaults from Phases 2-4 with explicit headroom;
- expose only lowering overrides at the verifier boundary.

Exit gates:

- the certificate path is truthfully resource-bounded end to end;
- official artifact measurements and limits are reported by tooling;
- forced full mutation, test, type, generated corpus, and Lean gates pass.

### Phase 6 - General polynomial consolidation

Red contracts:

- semiring and signed-ring identities are specified independently of F2;
- an F2 coefficient hook cannot be used in PEANO or a general ring;
- current `by_combination` and ring-of-integers payments have behavioral parity
  under the new elaborator.

Implementation:

- generalize `AlgebraContext` to natural and integer coefficients;
- migrate `peano_proofs.ring_kit`, `combination.by_combination`, and `ring_z.py`;
- delete the old kits and combination surface after the last caller moves.

Exit gates:

- one polynomial owner remains;
- all interpretation tolls reverify and any toll change is explained;
- old helper/import/search gates are zero-hit;
- full repository gates pass.

### Phase 7 - Resume the decidability program

Use the certificate/DAG/resource pattern for certifying Cooper, but do not reuse
the polynomial IR: Presburger quantifier elimination has different objects,
side conditions, and proof reconstruction.

Groebner membership does not pay Robinson Theorem 1.2's `totality:*` or
`uniqueness:*` debts. Those still require quantified Euclid/Bezout, coprime-lcm,
CRT extraction, and prime/witness existence. Concrete extended-Euclid search may
produce useful witnesses later, but it is not a substitute for the arbitrary
quantified theorem.

## Security and soundness review gates

The following are merge blockers, not advisory concerns.

1. **Ambient-context dependency:** DAG memoization is invalid if any rule derives
   differently by parent occurrence. Every current and future rule must satisfy
   the context-independence invariant.
2. **Cycle handling:** exact canonical Python objects can still be maliciously
   cycled. The checker, not only the decoder, rejects cycles.
3. **Self-authorizing theory:** the embedded theory key/fingerprint routes only to
   a closed external registry. The artifact never supplies accepted axioms.
4. **Claim substitution:** verification compares the exact checker result with
   the claimed sequent; it never prints an unchecked embedded claim as verified.
5. **Hash confusion:** fingerprints use canonical semantic theory bytes and a
   fixed domain-separated algorithm. Hash equality never replaces axiom checking.
6. **Decode amplification:** byte and table bounds are enforced before unbounded
   allocation. Checker-generated syntax is separately metered.
7. **Characteristic confusion:** coefficient parity does not reduce monomial
   exponents and does not import field or Boolean laws.
8. **Missing cofactors:** a zero Groebner remainder without a representation in
   the original generators is discarded.
9. **Budget semantics:** exhaustion is an unknown/search-failed result, never a
   mathematical non-membership theorem.
10. **Compatibility retention:** raw proof bytes, old normalizers, and old
    combination helpers do not survive through aliases, wrappers, or fallback
    branches.

## Measurements and success criteria

Correctness comes first, but this program exists partly to remove an observed
scaling wall. Every phase records:

- unique proof nodes and edges;
- unique syntax nodes and edges;
- prior tree occurrence count for comparison;
- encoded bytes;
- proof construction, decode, and check time;
- maximum derived formula and hypothesis counts;
- CAS search steps, maximum degree, basis size, and cofactor size where relevant;
- checker work units consumed versus configured limits.

The program reaches fixed point only when:

- the checker rejects cycles and derives shared proofs once;
- certificate bytes bind version, theory, and exact claimed sequent;
- official certificate verification is deterministically resource-bounded;
- one sparse polynomial owner serves semiring, ring, and F2 proof production;
- F2 ideal membership produces independently checked ordinary proofs;
- the old raw proof wire, duplicate normalizers, and superseded combination
  surfaces are absent;
- all required local, mutation, generated-corpus, and Lean gates pass.

## Collaboration record

The design was produced through a Codex/Claude review loop over the current
repository.

Claude's independent proposal contributed these decisive points:

- memoization is sound only because current rule derivation has no downward
  ambient context;
- a characteristic-2 normalizer must preserve exponents and must not infer
  Boolean-ring laws;
- Buchberger must carry cofactors in the original generators, not merely report a
  zero remainder;
- F2 is the correct first Groebner coefficient domain because every nonzero
  leading coefficient is one; natural-semiring and integer/PID variants are
  materially different algorithms;
- the small F2 normalizer should provide real measurements before final wire
  limit defaults are selected.

The synthesis strengthens that proposal in four places:

- tri-color cycle rejection is required in the trusted checker for hostile
  in-memory graphs, not only backward wire references;
- the portable artifact binds and verifies an exact claimed `Sequent`;
- the theory digest is defined over semantic canonical ordering rather than
  incidental tuple/set iteration;
- end-to-end resource bounding includes checker-created syntax and sequent work,
  not just wire table counts.

The main ordering compromise is intentional: trusted checker graph hardening
lands first; the F2 normalizer and ideal-membership slice then produce empirical
sizes; the full wire format and deterministic limits are sized from those results
before Cooper begins.

## Minimal vertical slice

If only one implementation slice is authorized initially, do Phase 1: reject a
cyclic exact proof graph and derive a deliberately shared proof graph once, with
no logical-rule or result change and the full trusted-base mutation gate green.

If one mathematical slice is authorized, do Phase 2 immediately afterward:
create the F2 sparse normalizer, migrate the current Jacobian determinant, and
delete its bespoke normal-form schedule. That provides the smallest honest base
for a subsequent Groebner certificate without adding CAS assumptions to the
kernel.
