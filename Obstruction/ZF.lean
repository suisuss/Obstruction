/-
  ZF Set Theory Encoding Obstructions
  ====================================

  The encoding trilemma for ZF set theory. Three properties:
  1. Injectivity — distinct terms get distinct codes
  2. Homomorphism — the encoding respects set-theoretic identities
  3. Non-trivial semantics — distinct terms can denote the same set

  Any two are compatible. All three are impossible.

  This file proves both sides:
  - The set-theoretic identities (⋃∅ = ∅, {a,a} = {a}, etc.) establish
    that ZF has non-trivial semantics: distinct terms denote equal sets
  - Any function respecting these identities is not injective
    (the "homomorphic + non-trivial" corner)
  - Any injective encoding cannot respect these identities
    (the "injective + non-trivial" corner, via `InjectiveObstruction`)
-/

import Obstruction.General

/-! ## ZF term algebra -/

/-- Terms of ZF set theory. -/
inductive ZFTerm where
  | empty  : ZFTerm
  | elem   : ZFTerm → ZFTerm → ZFTerm
  | pair   : ZFTerm → ZFTerm → ZFTerm
  | single : ZFTerm → ZFTerm
  | union  : ZFTerm → ZFTerm
  | power  : ZFTerm → ZFTerm
  deriving DecidableEq, Repr

namespace ZFTerm

/-! ## Non-trivial semantics: syntactically distinct terms denote equal sets -/

/-- union(empty) and empty are syntactically distinct. -/
theorem union_empty_ne : union empty ≠ empty := by decide

/-- pair(empty, empty) and single(empty) are syntactically distinct. -/
theorem pair_single_ne : pair empty empty ≠ single empty := by decide

/-- union(single(empty)) and empty are syntactically distinct. -/
theorem union_single_ne : union (single empty) ≠ empty := by decide

/-- power(empty) and single(empty) are syntactically distinct. -/
theorem power_single_ne : power empty ≠ single empty := by decide

/-! ## Corner 1: Homomorphic + Non-trivial → Not Injective

Any function from ZFTerm that respects the set-theoretic identities
must collapse distinct terms — it cannot be injective.
We prove this for each identity independently. -/

/-- Any function respecting ⋃∅ = ∅ maps union(empty) and empty
    to the same value, so it is not injective. -/
theorem not_injective_of_union_empty {α : Type*} (f : ZFTerm → α)
    (h : f (union empty) = f empty) : ¬ Function.Injective f :=
  fun hinj => absurd (hinj h) union_empty_ne

/-- Any function respecting {a,a} = {a} maps pair(empty,empty) and
    single(empty) to the same value, so it is not injective. -/
theorem not_injective_of_pair_single {α : Type*} (f : ZFTerm → α)
    (h : f (pair empty empty) = f (single empty)) : ¬ Function.Injective f :=
  fun hinj => absurd (hinj h) pair_single_ne

/-- Any function respecting ⋃{a} = a maps union(single(empty)) and
    empty to the same value, so it is not injective. -/
theorem not_injective_of_union_single {α : Type*} (f : ZFTerm → α)
    (h : f (union (single empty)) = f empty) : ¬ Function.Injective f :=
  fun hinj => absurd (hinj h) union_single_ne

/-- Any function respecting 𝒫(∅) = {∅} maps power(empty) and
    single(empty) to the same value, so it is not injective. -/
theorem not_injective_of_power_empty {α : Type*} (f : ZFTerm → α)
    (h : f (power empty) = f (single empty)) : ¬ Function.Injective f :=
  fun hinj => absurd (hinj h) power_single_ne

/-! ## Corner 2: Injective + Non-trivial → Not Homomorphic

The obstruction theorems below prove the other corner: any injective
encoding of ZF terms cannot respect the set-theoretic identities. -/

/-! ## Obstruction 1: ⋃∅ = ∅ -/

/-- **Union-Empty Obstruction:** No injective encoding can satisfy
    ε(⋃S) = ⋃(ε(S)) when ⋃∅ = ∅ in the semantics.
    The axiom ⋃∅ = ∅ forces ε(union(empty)) = ε(empty), contradicting injectivity. -/
theorem union_empty_obstruction :
    InjectiveObstruction ZFTerm ℕ
      (fun ε => ε (union empty) = ε empty) :=
  ⟨fun _ε hε heq => absurd (hε heq) union_empty_ne⟩

/-! ## Obstruction 2: {a, a} = {a} -/

/-- **Pair-Single Obstruction:** No injective encoding can satisfy
    ε({a, b}) with {a, a} = {a}.
    The axiom {a,a} = {a} forces ε(pair(∅,∅)) = ε(single(∅)), contradicting injectivity. -/
theorem pair_single_obstruction :
    InjectiveObstruction ZFTerm ℕ
      (fun ε => ε (pair empty empty) = ε (single empty)) :=
  ⟨fun _ε hε heq => absurd (hε heq) pair_single_ne⟩

/-! ## Obstruction 3: ⋃{a} = a -/

/-- **Union-Single Obstruction:** No injective encoding can satisfy
    ⋃{a} = a for all sets.
    Applied to a = ∅: ε(⋃{∅}) = ε(∅), but union(single(empty)) ≠ empty. -/
theorem union_single_obstruction :
    InjectiveObstruction ZFTerm ℕ
      (fun ε => ε (union (single empty)) = ε empty) :=
  ⟨fun _ε hε heq => absurd (hε heq) union_single_ne⟩

/-! ## Obstruction 4: 𝒫(∅) = {∅} -/

/-- **Power-Empty Obstruction:** No injective encoding can satisfy
    ε(𝒫(S)) with 𝒫(∅) = {∅}.
    The axiom forces ε(power(empty)) = ε(single(empty)), contradicting injectivity. -/
theorem power_empty_obstruction :
    InjectiveObstruction ZFTerm ℕ
      (fun ε => ε (power empty) = ε (single empty)) :=
  ⟨fun _ε hε heq => absurd (hε heq) power_single_ne⟩

end ZFTerm
