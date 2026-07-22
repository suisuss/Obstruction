# Obstruction

Machine-checked theorems (Lean 4, sorry-free, no axioms beyond Lean's kernel) about encodings: a code for the terms of a formal language cannot be simultaneously faithful (injective) and structure-preserving (homomorphic) once the language's semantics identifies any two distinct terms.

In one sentence: **semantics is a lossy compressor whose loss is forced by the Leibniz rule; simulating semantics requires compressing at least that much; a faithful (injective) code compresses nothing; therefore no faithful code simulates semantics.**

## The encoding trilemma

Any formal system that talks about itself needs an encoding — a map from its own terms to the objects it reasons about. Three properties are each individually desirable:

1. **Injectivity** — distinct terms get distinct codes (needed to tell sentences apart)
2. **Homomorphism** — the encoding respects operations (`ε(a + b) = ε(a) + ε(b)`, needed to track computations faithfully)
3. **Non-trivial semantics** — the system has distinct terms that mean the same thing (`S(S(0))` and `S(0)+S(0)` both mean 2)

All three together are impossible.

| Pick two | What you get | What breaks |
|---|---|---|
| Injective + Homomorphic | Perfect self-simulation | Forces trivial semantics; in the Leibniz setting, possible only for the empty term algebra (see below) |
| Injective + Non-trivial | Gödel-style coding | The code cannot be homomorphic |
| Homomorphic + Non-trivial | Semantic evaluation | The code cannot be injective |

This repo proves the two non-degenerate corners concretely — for Peano arithmetic and for ZF set theory — as the Lean theorems tabulated below.

## The trilemma, resolved

The general form — the trilemma as a single theorem, the exact status of the first cell, and witnesses for every cell — is proved in [`Trilemma.lean`](https://github.com/suisuss/SpectralArithmeticTheory/blob/main/SpectralArithmetic/Obstruction/Trilemma.lean) in the parent project, over every constant signature and every Leibniz algebra. Three facts sharpen the picture:

- **Non-triviality is a theorem, not an assumption** (`nontrivialSemantics_of_term`). In any term algebra whose composition, addition, and observation are related by the Leibniz rule, a term and its Leibniz rewrite are syntactically distinct but semantically equal in every model. The third property cannot be traded away.
- **The trilemma therefore collapses to a dilemma** (`no_injective_homomorphism`): once a single term exists, no encoding is both injective and homomorphic. The injective + homomorphic cell is inhabited exactly by term algebras with no terms at all (`exists_injective_homomorphism_iff`).
- **The whole configuration is a corollary of the bisimulation boundary** (`supportsBisimF_iff_extensionalF` in [`UniversalBisimulation.lean`](https://github.com/suisuss/SpectralArithmeticTheory/blob/main/SpectralArithmetic/Obstruction/UniversalBisimulation.lean)): an observable of syntax supports a bisimulation with the semantics iff it is extensional. Homomorphic encodings sit on the extensional side; injective encodings are maximally intensional; the boundary keeps the sides apart.

The compression reading makes the one-sentence summary above a theorem rather than a slogan (`supportsBisimF_iff_ker_le`): an observable supports a bisimulation with the semantics iff its kernel contains eval's kernel — iff it discards at least the distinctions the semantics discards. A homomorphic encoding is the exact semantic compression; an injective encoding is lossless; and lossless compression to a non-trivial semantic quotient is impossible (`no_lossless_semantic_compression`).

## Scope: what these theorems do and do not show

These are structural results about term algebras and codings, machine-checked end to end. They exhibit the structural pattern behind classical self-reference limitations — an injective code must separate what evaluation identifies — but they do not derive Gödel's incompleteness theorems, and nothing here should be read as an explanation of why incompleteness holds. Machine-checked incompleteness for actual PA (via the Foundation library, on standard Lean axioms) lives in the parent project, where these results form the intensional side of the bisimulation-boundary program.

One scope note on generality: `universal_encoding_obstruction` in this repo quantifies over arbitrary atom types of a fixed signature (composition, sum, observation). The fully signature-generic form — arbitrary constant signatures, arbitrary Leibniz algebras — is the parent project's `UniversalBisimulation.lean`.

## Origin

This repo extracts the encoding obstruction results from [SpectralArithmeticTheory](https://github.com/suisuss/SpectralArithmeticTheory), which builds an algebraic framework where numbers emerge as eigenvalues of an observation operator and derives both PA and ZF from unified axioms. The [original obstruction proofs](https://github.com/suisuss/SpectralArithmeticTheory/tree/main/SpectralArithmetic/Obstruction) live within that framework, where the encoding-observation square makes the morphism failure concrete: the system can observe its eigenstates but cannot faithfully encode the act of observation.

## Formalized results

All proofs compile against Mathlib v4.28.0 with zero `sorry` statements.

### `Obstruction/General.lean` — Framework

| Definition | Statement |
|---|---|
| `Obstruction α β P` | No morphism `f : α → β` satisfies property `P` |
| `ConditionalObstruction α β Q P` | No morphism satisfying `Q` also satisfies `P` |
| `InjectiveObstruction α β P` | No *injective* morphism satisfies `P` |

### `Obstruction/Encoding.lean` — Structural Obstruction

For any term algebra with composition, sum, and observation connected by the Leibniz rule, the rewrite changes the top-level constructor. Any injective encoding must map the rewritten and original terms to different codes.

| Theorem | Statement |
|---|---|
| `encoding_obstruction` | No injective encoding commutes with observation on compound terms |
| `morphism_square_obstruction` | If syntactic and semantic paths disagree, no injective encoding makes them agree |
| `universal_encoding_obstruction` | The above for any atom type (fixed signature; see scope note) |

### `Obstruction/Peano.lean` — PA Encoding Trilemma

Both non-degenerate corners of the trilemma for Peano arithmetic:

**Corner 1: Homomorphic + Non-trivial → Not Injective**

| Theorem | Statement |
|---|---|
| `eval_homomorphism` | `eval` respects all PA operations (it is a homomorphism) |
| `eval_not_injective` | `eval` is not injective: `S(S(0))` and `S(0)+S(0)` both map to 2 |

**Corner 2: Injective + Non-trivial → Not Homomorphic**

| Theorem | Witness terms | Semantic collision |
|---|---|---|
| `succ_add_obstruction` | `S(S(0))` vs `S(0)+S(0)` | Both map to 2 under ε(0)=0, ε(S(t))=ε(t)+1, ε(a+b)=ε(a)+ε(b) |
| `mul_zero_obstruction` | `0×S(0)` vs `0` | Both map to 0 under ε(0)=0, ε(a×b)=ε(a)×ε(b) |
| `succ_mul_obstruction` | `S(0)×S(0)` vs `S(0)` | Both map to 1 under ε(0)=0, ε(S(t))=ε(t)+1, ε(a×b)=ε(a)×ε(b) |

### `Obstruction/ZF.lean` — ZF Encoding Trilemma

Both non-degenerate corners of the trilemma for ZF set theory:

**Corner 1: Homomorphic + Non-trivial → Not Injective**

| Theorem | Identity | Conclusion |
|---|---|---|
| `not_injective_of_union_empty` | ⋃∅ = ∅ | Any function respecting this is not injective |
| `not_injective_of_pair_single` | {a,a} = {a} | Any function respecting this is not injective |
| `not_injective_of_union_single` | ⋃{a} = a | Any function respecting this is not injective |
| `not_injective_of_power_empty` | 𝒫(∅) = {∅} | Any function respecting this is not injective |

**Corner 2: Injective + Non-trivial → Not Homomorphic**

| Theorem | Set-theoretic identity | Witness |
|---|---|---|
| `union_empty_obstruction` | ⋃∅ = ∅ | `union(empty) ≠ empty` as terms |
| `pair_single_obstruction` | {a,a} = {a} | `pair(empty,empty) ≠ single(empty)` |
| `union_single_obstruction` | ⋃{a} = a | `union(single(empty)) ≠ empty` |
| `power_empty_obstruction` | 𝒫(∅) = {∅} | `power(empty) ≠ single(empty)` |

### `Obstruction/Arithmetic.lean` — Representation-Level Results

Results closing off representation-level workarounds:

| Theorem | Statement |
|---|---|
| `bool_char_two` | Any commutative, cancellative operation with identity on Bool has characteristic 2 |
| `oplus_bitwise_impossible` | Any commutative, cancellative Bool operation with identity has characteristic 2 (cannot have characteristic 0) |
| `add_not_injective_on_pairs` | Addition is not injective on pairs: `3 + 5 = 4 + 4` |
| `injective_pairing_unbounded` | Any injective pairing is unbounded on the diagonal (pigeonhole) |
| `carry_propagation` | Base-2 addition of `(2^k - 1) + 1` witnesses carry from bit 0 to bit k |
| `pairing_bounded_obstruction` | Formal `ConditionalObstruction`: no injective pairing is bounded on the diagonal |

## The argument

```
        O (operation)
  A ──────────────────► A
  │                     │
  │ ε (encode)          │ ε (encode)
  │                     │
  ▼                     ▼
  ℕ ──────────────────► ℕ
        O* (encoded op)
```

For the two paths through this square to agree — encode-then-operate versus operate-then-encode — the encoding must be a homomorphism. For the system to distinguish all of its own terms, the encoding must be injective. The theorems above show these requirements collide whenever two distinct terms share a meaning, and the resolved form shows the Leibniz rule manufactures such a pair from any single term: the collision is not an artifact of a badly chosen semantics, it is forced by evaluation itself. The gap is also quantitative — the parent project's [`QuotationCost.lean`](https://github.com/suisuss/SpectralArithmeticTheory/blob/main/SpectralArithmetic/Obstruction/QuotationCost.lean) proves compositional codings pay super-polynomial quotation overhead along observation trajectories, while an exact counterexample shows injectivity alone forces no such growth. Compositionality, not injectivity, is that boundary.

## Building

Requires Lean 4 (v4.28.0) and Mathlib.

```bash
lake build
```

## Further reading

- [docs/encoding-obstruction.md](docs/encoding-obstruction.md) — extended discussion (predates the resolution above; interpretive claims there should be read against the Scope section)
- [SpectralArithmeticTheory](https://github.com/suisuss/SpectralArithmeticTheory) — the parent project: eigenvalue arithmetic, the bisimulation boundary program, and machine-checked incompleteness for real PA via the Foundation library
- [`Trilemma.lean`](https://github.com/suisuss/SpectralArithmeticTheory/blob/main/SpectralArithmetic/Obstruction/Trilemma.lean) — the trilemma resolved: single-theorem form, cell characterization, boundary corollary, compression reading
- [`UniversalBisimulation.lean`](https://github.com/suisuss/SpectralArithmeticTheory/blob/main/SpectralArithmetic/Obstruction/UniversalBisimulation.lean) — the boundary theorem over every signature and Leibniz algebra
