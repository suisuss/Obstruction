# Obstruction

Lean 4 formalization of arithmetic obstructions: the structural reasons why encoding cannot commute with execution.

## Thesis

Gödel encoding is not a technique that happened to reveal incompleteness. It is the *best case* — the maximum you can achieve before the obstruction kicks in. You get injectivity. You get representability. You never get commutativity with arithmetic operations. That's where it stops, and that's where it must stop.

The standard narrative presents it backwards: "Gödel was clever enough to encode syntax into arithmetic, and then diagonalization produced undecidable sentences." As if incompleteness were a consequence of the encoding being too good.

The opposite is true. Incompleteness is a consequence of the encoding being *necessarily broken*. The encoding exists (injectivity works fine), but it doesn't commute with execution. The gap between "the encoding of the result" and "the result of operating on the encoding" — that gap IS incompleteness. The unprovable-but-true sentences live exactly in that gap.

The reason the gap exists is not logical but arithmetic: **carry propagation**. Addition is non-local in any positional encoding. When a system tries to reason about its own encoded computations, every step involving addition introduces distortion between what the computation actually does and what the encoding says it does.

## The hierarchy

1. **Gödel encoding works** — you can map terms to numbers injectively
2. **Gödel encoding doesn't commute** — the morphism fails at addition
3. **Incompleteness follows** — the system can name but not faithfully track its own execution
4. **This is unavoidable** — because addition is a primitive of arithmetic, not an accident of the encoding scheme

Every formal system with arithmetic hits the same wall. Not because self-reference is paradoxical, but because addition has carry propagation, and carry propagation breaks the morphism.

## Formalized results

All proofs are sorry-free.

### `Obstruction/General.lean` — Framework

| Definition | Statement |
|---|---|
| `Obstruction α β P` | No morphism `f : α → β` satisfies property `P` |
| `ConditionalObstruction α β Q P` | No morphism satisfying `Q` also satisfies `P` |
| `InjectiveObstruction α β P` | No *injective* morphism satisfies `P` |

### `Obstruction/Arithmetic.lean` — Proofs

| Theorem | Statement |
|---|---|
| `bool_char_two` | Any commutative, cancellative operation with identity on Bool has characteristic 2 |
| `oplus_bitwise_impossible` | No bit-level operation satisfies commutativity + cancellation + identity + characteristic 0 |
| `add_not_injective_on_pairs` | Addition is not injective on pairs: `3 + 5 = 4 + 4` |
| `injective_pairing_unbounded` | Any injective pairing is unbounded on the diagonal (pigeonhole) |
| `carry_propagation` | Base-2 addition of `(2^k - 1) + 1` witnesses carry from bit 0 to bit k |
| `pairing_bounded_obstruction` | Formal `ConditionalObstruction` instance packaging the above |

## Building

Requires Lean 4 (v4.28.0) and Mathlib.

```bash
lake build
```

## Related

- [SpectralArithmeticTheory](https://github.com/suisuss/SpectralArithmeticTheory) — the eigenvalue framework where the encoding obstruction makes the morphism failure visible as two different numbers where there should be one
