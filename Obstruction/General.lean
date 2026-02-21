/-
  General Obstruction Framework
  =============================

  An obstruction is a proof that no morphism between two structures
  can satisfy a given property. This file defines the vocabulary.

  Pattern: given structures A and B and a desired property P on
  morphisms f : A → B, an obstruction witnesses ∀ f, ¬ P(f).

  Instances:
  - Encoding obstruction: A = Term, B = ℕ, P = "commutes with obs"
  - ⊕ impossibility: A = Bool op, P = "comm ∧ cancel ∧ identity ∧ char 0"
  - Pairing bounds: A = ℕ × ℕ → ℕ, P = "injective ∧ bounded on diagonal"
-/

import Mathlib.Tactic

/-! ## Obstruction witnesses -/

/-- An `Obstruction` witnesses that no morphism f : α → β can satisfy
    property P. -/
structure Obstruction (α β : Type*) (P : (α → β) → Prop) where
  /-- No morphism satisfies P -/
  impossible : ∀ f, ¬ P f

/-- A `ConditionalObstruction` witnesses that no morphism satisfying
    precondition Q can also satisfy postcondition P. -/
structure ConditionalObstruction (α β : Type*) (Q P : (α → β) → Prop) where
  /-- Any morphism satisfying Q fails P -/
  obstructs : ∀ f, Q f → ¬ P f

/-! ## Constructors -/

/-- Build an obstruction from a universal negation. -/
def Obstruction.mk' {α β : Type*} {P : (α → β) → Prop}
    (h : ∀ f, ¬ P f) : Obstruction α β P :=
  ⟨h⟩

/-- A conditional obstruction where the precondition is injectivity. -/
abbrev InjectiveObstruction (α β : Type*) (P : (α → β) → Prop) :=
  ConditionalObstruction α β Function.Injective P

/-! ## Composition -/

/-- If Q implies R and R is obstructed, then Q is obstructed. -/
def ConditionalObstruction.weaken {α β : Type*}
    {Q R P : (α → β) → Prop}
    (obs : ConditionalObstruction α β R P)
    (hQR : ∀ f, Q f → R f) :
    ConditionalObstruction α β Q P :=
  ⟨fun f hq => obs.obstructs f (hQR f hq)⟩

/-- An unconditional obstruction is a conditional one with trivial precondition. -/
def Obstruction.toConditional {α β : Type*} {P : (α → β) → Prop}
    (obs : Obstruction α β P) (Q : (α → β) → Prop) :
    ConditionalObstruction α β Q P :=
  ⟨fun f _ => obs.impossible f⟩
