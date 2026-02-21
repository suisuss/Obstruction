/-
  Arithmetic Obstructions
  =======================

  Obstructions intrinsic to arithmetic: results showing that certain
  algebraic properties are incompatible with finiteness, boundedness,
  or bit-level representation.

  These are not specific to any particular framework — they are
  consequences of arithmetic itself.
-/

import Obstruction.General
import Mathlib.Data.Fintype.Card

/-! ## Finite characteristic obstruction

Any commutative, cancellative operation with identity on a finite type
has finite characteristic. In particular, on Bool the characteristic is 2.
This obstructs any attempt to realize characteristic-zero addition on bits. -/

/-- On Bool, any commutative cancellative operation with identity
    satisfies x ⊕ x = e for all x (characteristic 2). -/
theorem bool_char_two
    (f : Bool → Bool → Bool)
    (e : Bool)
    (hcomm : ∀ a b, f a b = f b a)
    (hid : ∀ x, f e x = x)
    (hcancel : ∀ a b c, f a b = f a c → b = c) :
    ∀ x, f x x = e := by
  intro x
  cases e with
  | false =>
    cases x with
    | false => exact hid false
    | true =>
      have hf_tf : f true false = true := by rw [hcomm]; exact hid true
      by_contra h
      push_neg at h
      have : f true true ≠ false := h
      have : f true true = true := by cases f true true <;> simp_all
      have : false = true := hcancel true false true (by rw [hf_tf, this])
      exact absurd this Bool.false_ne_true
  | true =>
    cases x with
    | true => exact hid true
    | false =>
      have hf_ft : f false true = false := by rw [hcomm]; exact hid false
      by_contra h
      push_neg at h
      have : f false false ≠ true := h
      have : f false false = false := by cases f false false <;> simp_all
      have : true = false := hcancel false true false (by rw [hf_ft, this])
      exact absurd this (Ne.symm Bool.false_ne_true)

/-- **Bitwise ⊕ impossibility:** no Bool operation is simultaneously
    commutative, cancellative, has an identity, and avoids characteristic 2. -/
theorem oplus_bitwise_impossible :
    ∀ (f : Bool → Bool → Bool) (e : Bool),
      (∀ a b, f a b = f b a) →
      (∀ x, f e x = x) →
      (∀ a b c, f a b = f a c → b = c) →
      (∀ x, f x x = e) :=
  bool_char_two

/-! ## Pairing obstructions

Fundamental limitations on pairing functions ℕ × ℕ → ℕ. -/

/-- Addition is not an injective pairing: 3 + 5 = 4 + 4 but (3,5) ≠ (4,4). -/
theorem add_not_injective_on_pairs :
    ¬ (∀ a b c d : ℕ, a + b = c + d → a = c ∧ b = d) := by
  intro h
  have := h 3 5 4 4 (by omega)
  omega

/-- The diagonal map n ↦ (n, n) is injective. -/
theorem diag_injective : Function.Injective (fun n : ℕ => (n, n)) :=
  fun _ _ h => (Prod.mk.inj h).1

/-- **Injective pairings are unbounded on the diagonal.**
    For any bound B, there exists n with π(n, n) > B.
    Proof: pigeonhole on B+2 distinct images in {0,...,B}. -/
theorem injective_pairing_unbounded (π : ℕ × ℕ → ℕ) (hπ : Function.Injective π)
    (B : ℕ) : ∃ n : ℕ, π (n, n) > B := by
  by_contra h
  push_neg at h
  have hg : ∀ k : Fin (B + 2), π (↑k, ↑k) < B + 1 := fun k => by
    have := h k.val; omega
  let g : Fin (B + 2) → Fin (B + 1) := fun k => ⟨π (↑k, ↑k), hg k⟩
  have hg_inj : Function.Injective g := by
    intro a b hab
    simp only [g, Fin.mk.injEq] at hab
    have hab' : (a.val, a.val) = (b.val, b.val) := hπ hab
    exact Fin.ext (Prod.mk.inj hab').1
  exact absurd (Fintype.card_le_of_injective g hg_inj) (by simp)

/-- **Carry propagation witness:** base-2 addition of (2^k - 1) + 1 = 2^k
    demonstrates carry propagation from bit 0 to bit k. -/
theorem carry_propagation (k : ℕ) (hk : k ≥ 1) :
    2 ^ k - 1 + 1 = 2 ^ k
    ∧ (2 ^ k - 1) / 2 ^ k = 0
    ∧ 1 / 2 ^ k = 0
    ∧ 2 ^ k / 2 ^ k = 1 := by
  have hpow : 2 ^ k ≥ 1 := Nat.one_le_two_pow
  refine ⟨by omega, ?_, ?_, ?_⟩
  · exact Nat.div_eq_of_lt (by omega)
  · have : 1 < 2 ^ k := Nat.one_lt_two_pow_iff.mpr (by omega)
    exact Nat.div_eq_of_lt (by omega)
  · exact Nat.div_self (by omega)

/-! ## Packaging as Obstruction instances -/

/-- The pairing boundedness obstruction as a formal `Obstruction`. -/
def pairing_bounded_obstruction (B : ℕ) :
    ConditionalObstruction (ℕ × ℕ) ℕ
      Function.Injective
      (fun π => ∀ n, π (n, n) ≤ B) :=
  ⟨fun π hπ hbound => by
    obtain ⟨n, hn⟩ := injective_pairing_unbounded π hπ B
    exact absurd (hbound n) (by omega)⟩
