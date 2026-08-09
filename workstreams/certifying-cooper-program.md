# Certifying Cooper Program

Date: 2026-08-08

Status: authorized and resumed after certified-algebra fixed point; implementation
has not begun.

## Objective

Decide closed formulas of `cold_start.presburger.PRESBURGER` by quantifier
elimination while emitting ordinary cold-start proof terms. Search, affine
normalization, least-common-multiple calculations, residue enumeration, and
certificate compression are untrusted. `checker.check` under the existing
`PRESBURGER` theory remains the only authority.

The implementation follows the proof-synthesis shape of Chaieb and Nipkow's
[Generic Proof Synthesis for Presburger Arithmetic](https://www21.in.tum.de/~nipkow/pubs/presburger.html)
and the executable/formalized Cooper decomposition in Isabelle's
[Linear Quantifier Elimination AFP entry](https://isa-afp.org/entries/LinearQuantifierElim.html).
Those sources work over integer linear arithmetic. This repository's registered
`PRESBURGER` theory is natural-number arithmetic, so their integer semantics may
guide search but cannot authorize a cold-start proof.

## Domain fidelity

C1 will not silently reinterpret `PRESBURGER` over the integers. Signed affine
coefficients are an untrusted calculation representation only. Every affine
expression is quoted back as two natural sums, with negative coefficients moved
to the opposite side of an equation.

Order and divisibility are derived formulas, not new trusted predicates:

- `a <= b` is represented by `exists k. a + k = b`;
- `a < b` is represented by `exists k. a + S(k) = b`;
- divisibility of a signed difference uses a pair of natural witnesses for an
  integer multiple and is replayed as an equality of natural sums.

Any use of an integer-domain Cooper lemma therefore owes an explicit
natural-domain transport proof. Until that theorem is paid, the implementation
must use a nat-native elimination lemma. Model agreement on bounded inputs is a
negative control and oracle, never a proof.

## Separate certificate IR

The polynomial IR is forbidden here. Cooper owns different immutable values:

```text
Affine       = sorted variable -> integer coefficient, plus integer constant
Atom         = equality | strict order | non-strict order | constant divisibility
NNF          = atom | negated atom | conjunction | disjunction
Elimination  = normalized head coefficients, positive LCM, lower bounds,
               divisors, minus-infinity form, finite residue candidates
```

Every collection is canonical, deterministic, and tuple-backed. DAG sharing is
by exact immutable identity. The certificate records the input formula, exact
output formula, each normalization/elimination step, side-condition witnesses,
and the final truth value. It contains no axiom, theorem key, callback, or proof
rule. It is not the portable proof certificate format and cannot be decoded as
one.

## Proof reconstruction

The elaborator produces ordinary equality, propositional, quantifier, and
induction proof terms in five explicit stages:

1. translate the object formula to NNF and affine atoms while proving
   equivalence;
2. normalize the eliminated variable's coefficients to one via a positive LCM,
   proving every divisibility side condition;
3. prove the nat-native boundary/minus-infinity and periodicity lemmas;
4. replace one existential with the finite disjunction of residue and bound
   candidates, proving both directions;
5. repeat from innermost quantifier outward, evaluate the closed quantifier-free
   result, and compose the equivalences into a proof of the input or its
   negation.

A failed side condition, malformed certificate, false finite evaluation, or
budget exhaustion emits no candidate proof.

## Deterministic limits

`CooperLimits` will bound input formula nodes, affine terms, coefficient bit
length, NNF nodes, quantifiers, elimination steps, LCM bit length, divisors,
lower bounds, residues, candidate substitutions, output nodes, proof nodes, and
elapsed checker work under the existing `WorkLimits`. Limits are local policy,
not certificate fields. Exhaustion is `SearchExhausted`, never falsehood.

## Milestones and red gates

### C1.0 - IR and domain lemmas

- Red: canonical signed-affine normalization; rejected polynomial values;
  rejected zero/negative divisors; natural/integer counterexamples that expose a
  missing nonnegativity guard.
- Green: immutable Cooper IR and checked definitions/proofs for order,
  constant multiplication, signed-difference equality, and divisibility.

### C1.1 - Quantifier-free proof synthesis

- Red: true and false affine equalities/inequalities/divisibility formulas,
  Boolean nesting, malformed atoms, coefficient and DAG limits.
- Green: a proof of the closed formula or its negation, rechecked under
  `PRESBURGER`, with no quantifier elimination yet.

### C1.2 - One existential

- Red: coefficient normalization, lower-bound and periodic arms, no-bound arm,
  divisibility residues, corrupt LCM/residue/bound witnesses, and exhaustion.
- Green: one complete nat-native Cooper elimination with an independently
  checked equivalence proof.

### C1.3 - Full closed sentences

- Red: nested existential/universal alternation, negation conversion, shared
  subformulas, hostile cycles, and formulas whose finite candidate set reaches
  each configured ceiling.
- Green: eliminate innermost quantifiers to a closed Boolean result and emit the
  corresponding proof or refutation.

### C1.4 - Portable integration and measurement

- Encode only the final ordinary proof through the existing portable certificate
  path; keep the Cooper search certificate internal unless a separate frozen wire
  format is later justified.
- Record Cooper search work, proof DAG/tree sizes, bytes, decode/check time, and
  checker headroom on an official corpus.
- Run the mutation-free repository gate and an explicit Cooper assurance
  campaign in CI. Routine `tools/gate.ps1` remains mutation-free.

## Non-goals

- no polynomial or Groebner reuse;
- no new trusted Cooper proof rule;
- no assumption that Lean `omega`, an SMT solver, or bounded evaluation is an
  oracle of truth;
- no claim that this pays the separate Robinson `totality:*` or `uniqueness:*`
  debts;
- no compatibility facade for a partial or uncertified decision procedure.
