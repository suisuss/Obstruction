# The Encoding Obstruction

## Why no formal system can perfectly reason about itself

### The one-sentence version

Any system powerful enough to describe its own operations cannot faithfully simulate them — because the encoding required to name things distinctly is incompatible with the encoding required to track what they mean.

---

## The Trilemma: Pick Two

Three properties. Any two are compatible. All three together are impossible.

1. **Injectivity** — distinct terms get distinct codes (you can tell sentences apart)
2. **Homomorphism** — the encoding preserves what operations mean (`ε(a + b) = ε(a) + ε(b)`)
3. **Non-trivial semantics** — the system has distinct terms that mean the same thing (`S(S(0))` and `S(0)+S(0)` both mean 2)

Pick any two:

**Injective + Homomorphic:** Only possible if no two distinct terms are semantically equal. This means your system is trivial — every term is the unique name for its value. No redundancy, no alternative expressions, no algebra. You can't even write `1 + 1` as a separate thing from `2`. This isn't mathematics; it's a lookup table.

**Injective + Non-trivial:** This is what we actually have. Gödel encoding. You can name every sentence distinctly, your system has real expressive power, but the encoding doesn't track operations faithfully. You get self-reference (enough to construct G) but not self-simulation (not enough to verify G). This is the world we live in. Incompleteness follows.

**Homomorphic + Non-trivial:** You can track what operations mean, and your system has real content, but you lose injectivity. Different sentences that mean the same thing get the same code. You can no longer distinguish `S(S(0))` from `S(0)+S(0)` at the code level. Self-reference breaks — you can't point to a specific sentence, because you can't tell sentences apart. No Gödel sentence, but also no ability to reason about your own syntax.

This has the same shape as the CAP theorem in distributed systems (consistency, availability, partition tolerance — pick two). Not the same content, but the same structure: three desirable properties that are pairwise compatible but jointly impossible.

The proofs in the repo make this a theorem rather than a slogan. `Peano.lean` proves that injectivity + homomorphism fails whenever you have non-trivial semantics (the concrete witnesses are the term pairs that collide). `ZF.lean` proves the same for set theory. `Encoding.lean` proves the structural version: the Leibniz rule itself generates the semantic equality that breaks the combination.

---

## Part I: The Map and the Territory

Every formal system — every system of rules for reasoning — eventually needs to talk about itself. Mathematics needs to prove things about mathematics. Programs need to analyze programs. Any sufficiently powerful language turns inward.

To do this, it needs a **map of itself**. It takes its own symbols, sentences, and rules, and encodes them as numbers so it can reason about them. This is what Gödel did in 1931 — he showed you can turn any mathematical statement into a number, and then mathematics can talk about those numbers.

The map works. You can assign a unique number to every statement. No two different statements get the same number. That part is fine.

The problem is: **the map can't perfectly simulate the territory.**

When you do an operation on the *actual* mathematical objects — say, add two numbers — you get a result. When you do the *encoded version* of that operation on the *codes* of those numbers, you get a different code than the code of the actual result.

Here's the simple version. The number 2 can be written two ways:

- "1 + 1"
- "the successor of the successor of 0"

These are different sentences. Different strings of symbols. So they get different codes in the encoding. But they mean the same thing. They're both just 2.

Any map that gives different sentences different codes (which it must, to be useful) will be forced to give the *same meaning* two *different* codes. And any map that gives the same meaning the same code can't distinguish different sentences anymore.

**You can't have both.** You can keep things distinct, or you can keep meaning intact. Not both.

This means the system's self-model is always slightly wrong. It can *name* all its own statements, but it can't perfectly *track* what they do. It's like having a map of a city where every building is labeled, but the roads don't quite connect the way the real ones do. You can find any address, but you can't trust the map to get you there.

Because the map is distorted, the system can construct statements it can see are true (by looking at the territory) but can't verify through the map. Those are the true-but-unprovable sentences. They live in the gap between the map and the territory.

And the gap can't be closed. Not by drawing a better map. Not by using a different encoding. Not by being cleverer. The gap is a consequence of the fact that *different descriptions of the same thing exist*, and any labeling system must either collapse them (losing the ability to distinguish sentences) or separate them (losing the ability to track meaning). That's it. That's the whole thing.

---

## Part II: Compilation vs Execution

There is an everyday version of this that every programmer encounters.

**Source code is not the same as what the program does.** Two completely different programs can produce the same output. The same program, compiled differently, produces different binaries. There is no compiler that preserves a one-to-one correspondence between "what the source says" and "what the machine does" while also preserving the meaning of every operation.

This is the same obstruction:

- **Compilation** is like encoding — it maps source terms to machine representations
- **Execution** is like semantic evaluation — it produces actual results
- The compiler can be *faithful* (same source always gives same binary) or *meaning-preserving* (the binary always does what the source says), but making it perfectly both while keeping every intermediate step in correspondence is impossible

When a compiler optimizes `x = 1 + 1` into `x = 2`, it has collapsed two syntactically different expressions into one. It lost the distinction. When it preserves both as separate computations, it wastes work — but more fundamentally, when a system tries to reason about what its own compiled code will do, it hits the same wall: the compiled representation and the execution semantics don't perfectly correspond at every step.

This is why **no program can perfectly predict its own behavior**. Not because self-reference is paradoxical in some mystical sense, but because the encoding it must use to represent itself to itself is structurally incapable of faithfully tracking all its operations.

---

## Part III: Why Models Can't Be Complete

In science, a model is a simplified representation of reality. Everyone accepts that models are incomplete — "all models are wrong, some are useful." But there is a tendency to think this is a practical limitation: if we just had enough data, enough compute, enough detail, we could make a perfect model.

The encoding obstruction says: **no, you can't.** And the reason is mathematical, not practical.

Any model of a system that is rich enough to include a model of itself faces the encoding obstruction. The model must represent its own components (injectivity — each component gets a distinct label), and it must track what those components do (homomorphism — operations on labels correspond to operations on components). These two requirements are mutually exclusive for any system with non-trivial operations.

This applies to:

- **Mathematical foundations.** PA can't have a complete self-theory. ZF can't have a complete self-theory. No foundational system can.
- **AI systems.** Any AI system modeling its own reasoning process faces the same gap. It can represent its internal states, or it can faithfully track their dynamics, but not both perfectly.
- **Physical theories.** Any physical theory that includes the observer as part of the system being described hits a version of this. The measurement problem in quantum mechanics — where the act of observation changes what is observed — has structural similarities, though the connection is analogical rather than formal.
- **Economic models.** Models that include agents who use the model to make decisions (rational expectations, reflexivity) face the same loop: the model's predictions change the behavior it's predicting.

The common thread: **any system modeling itself must encode itself, and the encoding is necessarily unfaithful.**

---

## Part IV: The Formal Results

All results are machine-checked in Lean 4, with no unproved assumptions (`sorry`-free). The proofs compile against Mathlib (v4.28.0).

### The structural obstruction

**File:** `Obstruction/Encoding.lean`

Take any term algebra with binary composition, binary sum, and unary observation, connected by the Leibniz rule:

```
obs(compose(a, b)) = sum(compose(obs(a), b), compose(a, obs(b)))
```

The Leibniz rule changes the top-level constructor: it takes an `obs` node and produces a `sum` node. These are syntactically different terms. Any injective encoding must map them to different codes. Therefore:

> **No injective encoding commutes with observation on compound terms.**

This holds for *any* atom type. It doesn't matter whether the system is about numbers, sets, categories, or anything else. The obstruction lives in the algebra of composition and observation, not in the atoms.

### Peano arithmetic obstructions

**File:** `Obstruction/Peano.lean`

Suppose an injective encoding `ε : PATerm → ℕ` respects the semantics:

- `ε(0) = 0`
- `ε(S(t)) = ε(t) + 1`
- `ε(a + b) = ε(a) + ε(b)`

Then `ε(S(S(0))) = 2` and `ε(S(0) + S(0)) = 2`. Same code, different terms. Injectivity violated.

| Theorem | Witness terms | Collision |
|---|---|---|
| `succ_add_obstruction` | `S(S(0))` vs `S(0)+S(0)` | Both map to 2 |
| `mul_zero_obstruction` | `0×S(0)` vs `0` | Both map to 0 |
| `succ_mul_obstruction` | `S(0)×S(0)` vs `S(0)` | Both map to 1 |

Each theorem is packaged as a formal `InjectiveObstruction PATerm ℕ`.

### ZF set theory obstructions

**File:** `Obstruction/ZF.lean`

The PA obstruction comes from arithmetic: different expressions for the same number. ZF hits the same wall through a completely different mechanism — **set-theoretic identities**.

Sets have axioms that force equalities between structurally different constructions. These aren't computational coincidences like `1+1 = 2`. They are *definitional* properties of what it means to be a set:

- **⋃∅ = ∅** — the union of nothing is nothing. But `union(empty)` is a compound term (apply union to the empty set), while `empty` is atomic. Two different terms, one set.
- **{a, a} = {a}** — a pair where both elements are the same is just a singleton. But `pair(∅, ∅)` and `single(∅)` are built from different constructors. Two different terms, one set.
- **⋃{a} = a** — the union of a singleton is its element. But `union(single(∅))` is a three-layer compound term, while `∅` is atomic. Two different terms, one set.
- **𝒫(∅) = {∅}** — the power set of the empty set is the set containing just the empty set. But `power(empty)` and `single(empty)` use different constructors. Two different terms, one set.

Each identity produces the same trilemma:

**Corner 1 — Homomorphic + Non-trivial → Not Injective:** Any function that respects the identity (maps both sides to the same value) collapses distinct terms. It cannot be injective.

| Theorem | Identity | Conclusion |
|---|---|---|
| `not_injective_of_union_empty` | ⋃∅ = ∅ | Any function respecting this is not injective |
| `not_injective_of_pair_single` | {a,a} = {a} | Any function respecting this is not injective |
| `not_injective_of_union_single` | ⋃{a} = a | Any function respecting this is not injective |
| `not_injective_of_power_empty` | 𝒫(∅) = {∅} | Any function respecting this is not injective |

**Corner 2 — Injective + Non-trivial → Not Homomorphic:** Any injective encoding must assign different codes to the two sides. It cannot respect the identity.

| Theorem | Identity | Witness |
|---|---|---|
| `union_empty_obstruction` | ⋃∅ = ∅ | `union(empty) ≠ empty` as terms |
| `pair_single_obstruction` | {a,a} = {a} | `pair(empty,empty) ≠ single(empty)` |
| `union_single_obstruction` | ⋃{a} = a | `union(single(empty)) ≠ empty` |
| `power_empty_obstruction` | 𝒫(∅) = {∅} | `power(empty) ≠ single(empty)` |

Each packaged as `InjectiveObstruction ZFTerm ℕ`.

The significance: **the obstruction is not about numbers.** PA hits the wall because different arithmetic expressions evaluate to the same number. ZF hits the wall because different set constructions denote the same set. The common pattern is that any system with non-trivial semantic equalities — any system where you can say the same thing two different ways — produces the trilemma. Arithmetic is one instance. Set theory is another. Any foundation for mathematics will be a third.

### The arithmetic infrastructure

**File:** `Obstruction/Arithmetic.lean`

These results prove there is no workaround at the representation level:

**Characteristic obstruction.** Any commutative, cancellative operation with identity on `Bool` has characteristic 2. The only candidate is XOR, which satisfies `x ⊕ x = 0`. You cannot build a characteristic-zero operation from bit-independent components.

**Pairing unboundedness.** Any injective pairing `π : ℕ × ℕ → ℕ` is unbounded on the diagonal (by pigeonhole). You cannot pack two pieces of information into one number with bounded overhead.

**Carry propagation.** `(2^k - 1) + 1 = 2^k`: neither input has a nonzero bit at position `k`, but the output does. Addition moves information non-locally across the entire representation. This is why no bounded, local encoding can track addition faithfully.

---

## Part V: The Core Argument

### What completeness would require

For a formal system to be complete *and* self-referential, two paths through a diagram would need to agree:

```
        O (operation)
  A ──────────────────► A
  │                     │
  │ ε (encode)          │ ε (encode)
  │                     │
  ▼                     ▼
  ℕ ──────────────────► ℕ
        O* (encoded operation)
```

- **Top-then-right (semantic path):** perform the operation, then encode the result: `ε(O(a, b))`
- **Left-then-bottom (syntactic path):** encode the inputs, then perform the encoded operation: `O*(ε(a), ε(b))`

If `ε(O(a, b)) = O*(ε(a), ε(b))` for all inputs, the system can perfectly simulate its own computations by working entirely with codes. Every true statement could be verified by chasing it through the encoding. The system would be complete.

### Why it can't

The encoding obstruction proves this diagram cannot commute:

1. **Injectivity** (needed for self-reference): different terms must get different codes, so `ε` is injective
2. **Semantic preservation** (needed for faithful simulation): `ε` must respect what operations mean, so `ε(O(a,b)) = O*(ε(a), ε(b))`
3. **But** any system with non-trivial operations has semantically equal, syntactically distinct terms — and injectivity forces them apart while semantic preservation forces them together

The three levels of proof:
- **Level 1 (Encoding.lean):** The Leibniz rule structurally changes the term, so the syntactic and semantic paths produce different constructors
- **Level 2 (Peano.lean, ZF.lean):** The specific semantics of PA and ZF generate concrete witness pairs that collide
- **Level 3 (Arithmetic.lean):** At the bit level, carry propagation makes addition non-local, so no bounded encoding absorbs the distortion

### The connection to classical results

**Gödel's incompleteness (1931)** proved that the diagram doesn't commute, by constructing a specific sentence that exploits the gap. The encoding obstruction characterizes *why* the gap exists and proves it cannot be closed — not by any encoding, not for any sufficiently expressive system.

**Turing's halting problem (1936)** is the computational face of the same obstruction. A halting decider would need the diagram to commute for program execution. It can't, because the encoding of a computation diverges from the computation itself. The diagonalization argument is the logical proof; the encoding obstruction is the structural reason it works.

**Rice's theorem (1953)** extends this: deciding *any* non-trivial semantic property of programs requires faithful tracking of what programs compute. The encoding can't provide this, for the same reason.

### What it means for "going beyond Gödel"

The encoding obstruction is not a retrospective explanation of incompleteness. It is a characterization of the barrier.

To build a formal system that escapes incompleteness while retaining self-reference, you would need an encoding that is simultaneously injective (to name things) and homomorphic (to track operations). The obstruction proves this is impossible for any system with:

- Successor and addition (PA)
- Union and power set (ZF)
- Composition and observation connected by any product rule (any system)

There is no workaround:

- **Better encoding?** The obstruction holds for *all* injective encodings, not a specific one.
- **Different primitives?** The structural obstruction (Level 1) holds for *any* atom type.
- **Weaker semantics?** Any system with at least two syntactically distinct terms that are semantically equal hits the wall — and any system interesting enough to do mathematics has this property.
- **Stronger axioms?** Adding axioms (like `Con(PA)`) creates a stronger system that still has its own encoding obstruction, its own Gödel sentence, its own incompleteness.

The gap between the map and the territory is not a defect. It is a theorem.

---

## Part VI: The Spectral Perspective

The [SpectralArithmeticTheory](https://github.com/suisuss/SpectralArithmeticTheory) framework provides a complementary view. Instead of starting with numbers and asking about encodings, it starts with *states* and *observation*:

- **States** are the primitive objects (like eigenstates in physics)
- **Observation** (`obs`) extracts structure from states
- **Numbers emerge as eigenvalues**: `obs(f_n) = n · f_n`

In this framing, the eigenvalue *is* the number. The framework derives Peano arithmetic and ZF set theory from algebraic axioms about composition and observation, and proves the encoding-observation square doesn't commute (`encoding_obstruction_term`).

The spectral view makes the obstruction concrete: the system can *observe* its eigenstates (read off eigenvalues) but cannot faithfully *encode* the act of observation. The observation path and the encoding path produce different answers — not because of any particular encoding choice, but because of the algebraic structure of observation itself.

---

## Building

Requires Lean 4 (v4.28.0) and Mathlib.

```bash
lake build
```

All proofs compile with zero `sorry` statements.

## Summary

| Layer | Proves | Significance |
|---|---|---|
| `Encoding.lean` | Leibniz rule changes constructors; no injective encoding commutes with `obs` | The obstruction is algebraic, not system-specific |
| `Peano.lean` | Semantic equalities (`S(S(0)) = S(0)+S(0)`) kill injectivity | PA's own operations generate the collisions |
| `ZF.lean` | Set-theoretic identities (`⋃∅ = ∅`) kill injectivity | Same obstruction in set theory — universal |
| `Arithmetic.lean` | Char 2 on bits, pairing unbounded, carry propagation | No representation-level workaround exists |
| SpectralArithmetic | Numbers as eigenvalues; eval-quote diagram doesn't commute | The morphism failure as concrete, computable divergence |

The argument chain: carry propagation makes addition non-local, so no bounded encoding absorbs the distortion, so the encoding-operation square doesn't commute, so no system can faithfully simulate its own computations, so true statements exist that the system can name but cannot verify. This is incompleteness — not as a consequence of a clever trick, but as a structural impossibility at the interface between syntax and semantics.
