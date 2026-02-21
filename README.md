# Obstruction

Machine-checked proofs (Lean 4, sorry-free) that no formal system can perfectly reason about itself.

## The encoding trilemma

Any formal system that talks about itself needs an encoding — a map from its own sentences to the objects it reasons about. That encoding has three desirable properties:

1. **Injectivity** — distinct terms get distinct codes (needed to tell sentences apart)
2. **Homomorphism** — the encoding respects operations (`ε(a + b) = ε(a) + ε(b)`, needed to track computations faithfully)
3. **Non-trivial semantics** — the system has distinct terms that mean the same thing (`S(S(0))` and `S(0)+S(0)` both mean 2)

**Any two are compatible. All three together are impossible.**

| Pick two | What you get | What breaks |
|---|---|---|
| Injective + Homomorphic | Perfect self-simulation | Only works for trivial systems with no interesting equalities |
| Injective + Non-trivial | Gödel encoding — self-reference works | Can't track computations faithfully; incompleteness follows |
| Homomorphic + Non-trivial | Semantic evaluation — meaning is preserved | Can't distinguish sentences; self-reference breaks |

This is why incompleteness is unavoidable. To escape it while retaining self-reference, you would need an encoding that is both injective and homomorphic. This repo proves that's impossible — for Peano arithmetic, for ZF set theory, and for any term algebra with composition and observation.

## Origin

This repo extracts and generalizes the encoding obstruction results from [SpectralArithmeticTheory](https://github.com/suisuss/SpectralArithmeticTheory), which builds an algebraic framework where numbers emerge as eigenvalues of an observation operator and derives both PA and ZF from unified axioms. In that framework, the encoding-observation square (`encoding_obstruction_term`) makes the morphism failure concrete: the system can observe its eigenstates but cannot faithfully encode the act of observation.

The present repo proves the obstruction in full generality, independent of the spectral framework — for any term algebra, any encoding, any sufficiently expressive formal system.

## Formalized results

All proofs compile against Mathlib v4.28.0 with zero `sorry` statements.

### `Obstruction/General.lean` — Framework

| Definition | Statement |
|---|---|
| `Obstruction α β P` | No morphism `f : α → β` satisfies property `P` |
| `ConditionalObstruction α β Q P` | No morphism satisfying `Q` also satisfies `P` |
| `InjectiveObstruction α β P` | No *injective* morphism satisfies `P` |

### `Obstruction/Encoding.lean` — Structural Obstruction

The most general result. For any term algebra with composition, sum, and observation connected by the Leibniz rule, the rewrite changes the top-level constructor. Any injective encoding must map the rewritten and original terms to different codes.

| Theorem | Statement |
|---|---|
| `encoding_obstruction` | No injective encoding commutes with observation on compound terms |
| `morphism_square_obstruction` | If syntactic and semantic paths disagree, no injective encoding makes them agree |
| `universal_encoding_obstruction` | The above holds for **any** atom type |

### `Obstruction/Peano.lean` — PA Encoding Trilemma

Both corners of the trilemma for Peano arithmetic:

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

Both corners of the trilemma for ZF set theory:

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

### `Obstruction/Arithmetic.lean` — No Workaround Exists

These results close off representation-level escape routes:

| Theorem | Statement |
|---|---|
| `bool_char_two` | Any commutative, cancellative operation with identity on Bool has characteristic 2 |
| `oplus_bitwise_impossible` | No bit-level operation satisfies commutativity + cancellation + identity + characteristic 0 |
| `add_not_injective_on_pairs` | Addition is not injective on pairs: `3 + 5 = 4 + 4` |
| `injective_pairing_unbounded` | Any injective pairing is unbounded on the diagonal (pigeonhole) |
| `carry_propagation` | Base-2 addition of `(2^k - 1) + 1` witnesses carry from bit 0 to bit k |

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

For a system to be complete and self-referential, the two paths through this diagram must agree: `ε(O(a, b)) = O*(ε(a), ε(b))`. The left-then-bottom path (encode inputs, operate on codes) must match the top-then-right path (operate on terms, encode the result).

The encoding trilemma proves this diagram cannot commute for any non-trivial system. Distinct terms with equal semantics exist in any interesting formal system. Injectivity forces them apart. Homomorphism forces them together. The gap between the two paths is where true-but-unprovable sentences live.

This is not a retrospective explanation of Gödel's theorem. It is a characterization of the barrier: to escape incompleteness while retaining self-reference, you would need to close this gap. These proofs show it cannot be closed.

## Building

Requires Lean 4 (v4.28.0) and Mathlib.

```bash
lake build
```

## Further reading

- [docs/encoding-obstruction.md](docs/encoding-obstruction.md) — extended discussion of the trilemma, its connections to Gödel/Turing/Rice, and accessible explanations
- [SpectralArithmeticTheory](https://github.com/suisuss/SpectralArithmeticTheory) — the algebraic framework where numbers emerge as eigenvalues, PA and ZF are derived from unified axioms, and the encoding obstruction is proved at the spectral level
