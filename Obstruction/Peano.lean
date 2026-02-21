/-
  Peano Arithmetic Encoding Obstructions
  =======================================

  The encoding trilemma for Peano arithmetic. Three properties:
  1. Injectivity — distinct terms get distinct codes
  2. Homomorphism — the encoding respects PA operations
  3. Non-trivial semantics — distinct terms can denote the same number

  Any two are compatible. All three are impossible.

  This file proves both sides:
  - `eval` is a homomorphism on a non-trivial system, therefore NOT injective
    (the "homomorphic + non-trivial" corner)
  - Any injective encoding on this non-trivial system is NOT a homomorphism
    (the "injective + non-trivial" corner, via `InjectiveObstruction`)
-/

import Obstruction.General

/-! ## PA term algebra -/

/-- Terms of first-order Peano arithmetic. -/
inductive PATerm where
  | zero : PATerm
  | succ : PATerm → PATerm
  | add  : PATerm → PATerm → PATerm
  | mul  : PATerm → PATerm → PATerm
  deriving DecidableEq, Repr

namespace PATerm

/-! ## Semantic evaluation -/

/-- Standard interpretation of PA terms in ℕ. -/
def eval : PATerm → ℕ
  | .zero => 0
  | .succ t => eval t + 1
  | .add a b => eval a + eval b
  | .mul a b => eval a * eval b

/-! ## Corner 1: Homomorphic + Non-trivial → Not Injective

`eval` is a homomorphism by construction: it maps zero to 0, succ to +1,
add to +, mul to ×. PA has non-trivial semantics (distinct terms denote
the same number). Therefore `eval` cannot be injective. -/

/-- `eval` is a homomorphism: it respects all PA operations. -/
theorem eval_homomorphism :
    eval zero = 0 ∧
    (∀ t, eval (succ t) = eval t + 1) ∧
    (∀ a b, eval (add a b) = eval a + eval b) ∧
    (∀ a b, eval (mul a b) = eval a * eval b) :=
  ⟨rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **eval is not injective.** Two syntactically distinct terms evaluate
    to the same number: S(S(0)) and S(0)+S(0) both evaluate to 2.
    This is the "homomorphic + non-trivial → not injective" corner
    of the encoding trilemma. -/
theorem eval_not_injective : ¬ Function.Injective eval := by
  intro h
  have : succ (succ zero) = add (succ zero) (succ zero) := h (by simp [eval])
  exact absurd this (by decide)

/-! ## Corner 2: Injective + Non-trivial → Not Homomorphic

The obstruction theorems below prove the other corner: any injective
encoding of PA terms cannot respect the semantics. -/

/-! ## Obstruction 1: S(S(0)) vs S(0) + S(0) -/

/-- S(S(0)) and S(0) + S(0) are syntactically distinct. -/
theorem succ_ne_add : succ (succ zero) ≠ add (succ zero) (succ zero) := by decide

/-- S(S(0)) and S(0) + S(0) both evaluate to 2. -/
theorem succ_add_eval : eval (succ (succ zero)) = eval (add (succ zero) (succ zero)) := by
  simp [eval]

/-- **Succ-Add Obstruction:** No injective encoding ε : PATerm → ℕ can satisfy
    ε(S(t)) = ε(t) + 1 and ε(a + b) = ε(a) + ε(b) simultaneously.
    Witness: S(S(0)) and S(0) + S(0) both map to ε(0) + 2, but are distinct terms. -/
theorem succ_add_obstruction :
    InjectiveObstruction PATerm ℕ
      (fun ε => ε zero = 0 ∧
                (∀ t, ε (succ t) = ε t + 1) ∧
                (∀ a b, ε (add a b) = ε a + ε b)) :=
  ⟨fun ε hε ⟨hz, hs, ha⟩ => by
    have h1 : ε (succ (succ zero)) = 2 := by rw [hs, hs, hz]
    have h2 : ε (add (succ zero) (succ zero)) = 2 := by rw [ha, hs, hz]
    have := hε (h1.trans h2.symm)
    exact absurd this succ_ne_add⟩

/-! ## Obstruction 2: 0 × S(0) vs 0 -/

/-- 0 × S(0) and 0 are syntactically distinct. -/
theorem mul_zero_ne : mul zero (succ zero) ≠ zero := by decide

/-- 0 × S(0) and 0 both evaluate to 0. -/
theorem mul_zero_eval : eval (mul zero (succ zero)) = eval zero := by
  simp [eval]

/-- **Mul-Zero Obstruction:** No injective encoding can satisfy
    ε(0) = 0 and ε(a × b) = ε(a) × ε(b).
    Witness: 0 × S(0) maps to 0 × ε(S(0)) = 0 = ε(0), but they are distinct. -/
theorem mul_zero_obstruction :
    InjectiveObstruction PATerm ℕ
      (fun ε => ε zero = 0 ∧
                (∀ a b, ε (mul a b) = ε a * ε b)) :=
  ⟨fun ε hε ⟨hz, hm⟩ => by
    have h1 : ε (mul zero (succ zero)) = 0 := by rw [hm, hz, Nat.zero_mul]
    have h2 : ε zero = 0 := hz
    have := hε (h1.trans h2.symm)
    exact absurd this mul_zero_ne⟩

/-! ## Obstruction 3: S(0) × S(0) vs S(0) -/

/-- S(0) × S(0) and S(0) are syntactically distinct. -/
theorem succ_mul_ne : mul (succ zero) (succ zero) ≠ succ zero := by decide

/-- S(0) × S(0) and S(0) both evaluate to 1. -/
theorem succ_mul_eval : eval (mul (succ zero) (succ zero)) = eval (succ zero) := by
  simp [eval]

/-- **Succ-Mul Obstruction:** No injective encoding can satisfy
    ε(0) = 0, ε(S(t)) = ε(t) + 1, and ε(a × b) = ε(a) × ε(b).
    Witness: S(0) × S(0) maps to 1 × 1 = 1 = ε(S(0)), but they are distinct. -/
theorem succ_mul_obstruction :
    InjectiveObstruction PATerm ℕ
      (fun ε => ε zero = 0 ∧
                (∀ t, ε (succ t) = ε t + 1) ∧
                (∀ a b, ε (mul a b) = ε a * ε b)) :=
  ⟨fun ε hε ⟨hz, hs, hm⟩ => by
    have h1 : ε (mul (succ zero) (succ zero)) = 1 := by
      rw [hm, hs, hz, Nat.one_mul]
    have h2 : ε (succ zero) = 1 := by rw [hs, hz]
    have := hε (h1.trans h2.symm)
    exact absurd this succ_mul_ne⟩

end PATerm
