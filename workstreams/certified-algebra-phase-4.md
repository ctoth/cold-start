# Certified Algebra Phase 4 Evidence

Date: 2026-08-08

Status: implemented; both mutation campaigns and the full repository gate are green.

## Red contracts

`uv run pytest -q tests/test_certificate.py` initially failed during collection
because `cold_start.certificate` did not exist. The frozen contracts cover
unknown versions and classes; unknown or wrong field tags; invalid UTF-8;
nonminimal varints; truncation and trailing bytes; cyclic, forward, and
out-of-range syntax/proof references; duplicate/noncanonical table entries;
unsorted or duplicate claim hypotheses; wrong root kinds; theory, fingerprint,
and claim mismatch; every certificate I/O limit; exact-object sharing;
byte-identical re-encoding; and deep recursion-free graphs.

## Portable certificate boundary

`certificate.py` contains only the inert `Certificate` dataclass. Possessing one
proves nothing. `codec.py` derives its closed syntax and proof schemas from the
canonical owner sets and encodes version-1 `CSPC` bytes as canonical structural
postorder tables. Structurally duplicate syntax and proof nodes receive one
table entry, and decoded references reuse that exact object.

Every field count, field marker, class, reference direction/range, tuple arity,
table count, claim reference, string, fingerprint length, and trailing byte is
checked fail-closed. Accepted input must encode back to byte-identical output.
`CertificateLimits` bounds input bytes, syntax entries, proof entries, edges,
tuple arity, string bytes, and claim hypotheses before the corresponding
allocation. Artifact bytes contain no limits.

Theory fingerprints implement the frozen SHA-256 preimage: canonical sorted
sorts, function/relation ranks, standalone canonical axiom bytes, and the
induction zero/successor declarations. The slug is absent from the digest.

`verify.py` has no external theory selector. It resolves only the artifact's
embedded key against the closed five-theory registry, checks the semantic
fingerprint, invokes ordinary `check()`, and compares the exact derived sequent
to the embedded claim. The raw proof encode/decode API and fallback decoder are
deleted. Standalone term/formula Hamblin adapters remain because they are syntax
serialization, not a proof boundary.

All repository callers now construct and consume complete certificates.
Fresh-process acceptance covers Peano, Presburger, Robinson, DIFF_RING_2, and
GROUP_RING_P2. Wrong embedded keys, fingerprints, claims, forged axioms, and the
removed `--theory` selector are rejected.

## Scaling repair and measurements

The property suite exposed an initial quadratic decoder implementation that
rebuilt the identity-index map for every table entry. Incremental syntax/proof
maps removed that defect. A direct 50,000-node nested-syntax measurement now
encodes in 0.299 seconds and decodes in 0.702 seconds.

The current determinant artifact reports:

```text
portable certificate bytes: 39,605
decoded proof tree occurrences: 12,019
decoded unique proof objects: 2,633
proof construction: 0.271895s
claim derivation: 1.000971s
encoding: 0.079380s
decoding: 0.054959s
fresh verification: 0.730906s
```

Against the frozen Phase 0 raw-tree artifact of 2,094,481 bytes, the portable
artifact is 98.1% smaller. Within the current proof, canonical DAG sharing
reduces 12,019 proof occurrences to 2,633 unique decoded proof objects (78.1%).

## Assurance split

Routine `tools/gate.ps1` now runs tests, Ruff, strict Pyright, corpus
generation/freshness, and Lean compilation only. Mutation is deliberately an
explicit assurance and CI responsibility, as requested by the user.

`tools/mutate.py` requires one of two named campaigns:

- `logical`: checker, proof, sequent, syntax, and theory with kernel tests;
- `portable`: certificate, codec, and verifier with adversarial wire tests.

CI runs both in a matrix, while the ordinary local full suite never implicitly
starts either long campaign. CI test slices also include the certificate,
Gröbner, group-ring, Jacobian, and ring-normalizer suites.

## Verification

The 18 adversarial certificate tests, migrated checker/codec/relation/Jacobian
suites, 24 property tests, and tool-contract tests pass. Ruff is clean and
repository strict Pyright reports 0 errors, 0 warnings, and 0 informations.

The Phase 4 implementation was committed before mutation so the disposable
worktrees tested the actual portable boundary. Both forced campaigns passed:

```text
portable: certificate 0, codec 111, verifier 8; 119/119 killed
portable elapsed: 197.2350209 seconds
logical: checker 77, proof 0, sequent 3, syntax 56, theory 44; 180/180 killed
logical elapsed: 600.0500413 seconds
```

The mutation-free routine repository gate then passed:

```text
1449 tests collected; pytest passed
Ruff: all checks passed
Pyright strict: 0 errors, 0 warnings, 0 informations
Lean corpus generation: passed
Lean corpus freshness: clean
Lean 4 compilation: passed
GATE GREEN
elapsed: 377.0788304 seconds
```

The unrelated package-smoke directory and all untracked notes remain excluded.
