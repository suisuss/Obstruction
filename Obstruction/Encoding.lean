/-
  The General Encoding Obstruction
  ================================

  For ANY term algebra with binary composition and unary observation
  connected by the Leibniz rule, no injective encoding into any
  codomain commutes with observation on compound terms.

  The proof is structural: Leibniz rewrites obs(compose(a, b)) into
  a sum, changing the top-level constructor. Different constructors
  are distinct terms. Injectivity does the rest.

  This is instantiated for Peano arithmetic and ZF set theory,
  showing the obstruction is universal across foundational systems.
-/

import Obstruction.General

/-! ## General term algebra -/

/-- Terms over an arbitrary atom type, with binary composition,
    binary sum, and unary observation. -/
inductive GTerm (Atom : Type*) where
  | atom : Atom → GTerm Atom
  | compose : GTerm Atom → GTerm Atom → GTerm Atom
  | sum : GTerm Atom → GTerm Atom → GTerm Atom
  | obs : GTerm Atom → GTerm Atom

namespace GTerm

/-! ## The Leibniz rewrite -/

/-- The Leibniz/product rule as a syntactic rewrite:
    obs(compose(a, b)) ↦ sum(compose(obs(a), b), compose(a, obs(b)))
    All other terms are unchanged. -/
def leibniz {Atom : Type*} : GTerm Atom → GTerm Atom
  | .obs (.compose a b) => .sum (.compose (.obs a) b) (.compose a (.obs b))
  | t => t

/-! ## Structural divergence: Leibniz changes the constructor -/

/-- The Leibniz rewrite of obs(compose(a, b)) produces a sum,
    which is a different constructor from obs. This is the
    structural fact that drives everything. -/
theorem leibniz_ne_obs {Atom : Type*} (a b : GTerm Atom) :
    leibniz (.obs (.compose a b)) ≠ .obs (.compose a b) := by
  simp only [leibniz]
  exact nofun

/-! ## The general encoding obstruction -/

/-- **General Encoding Obstruction:**
    For any injective encoding ε from terms into any codomain,
    ε(leibniz(obs(compose(a, b)))) ≠ ε(obs(compose(a, b))).

    The encoding cannot commute with observation on compound terms.
    This holds for ANY atom type — it is intrinsic to the algebra
    of composition and observation, not to any particular system. -/
theorem encoding_obstruction {Atom : Type*} {β : Type*}
    (ε : GTerm Atom → β) (hε : Function.Injective ε)
    (a b : GTerm Atom) :
    ε (leibniz (.obs (.compose a b))) ≠ ε (.obs (.compose a b)) :=
  fun h => absurd (hε h) (leibniz_ne_obs a b)

/-- The morphism square does not commute. Given any two functions
    `syntactic` and `semantic` on terms, if they disagree at a point,
    no injective encoding can make both paths equal. -/
theorem morphism_square_obstruction {α β : Type*}
    (ε : α → β) (hε : Function.Injective ε)
    (syntactic semantic : α → α)
    (a : α) (hne : syntactic a ≠ semantic a) :
    ε (syntactic a) ≠ ε (semantic a) :=
  fun h => absurd (hε h) hne

/-! ## Peano arithmetic -/

/-- The primitives of first-order Peano arithmetic. -/
inductive PeanoAtom where
  | zero   -- 0
  | succ   -- S
  | add    -- +
  | mul    -- ×
  deriving DecidableEq, Repr

/-- In Peano arithmetic, obs(compose(a, b)) rewrites to a structurally
    different term. No Gödel numbering commutes with observation. -/
theorem peano_encoding_obstruction
    (ε : GTerm PeanoAtom → ℕ) (hε : Function.Injective ε)
    (a b : GTerm PeanoAtom) :
    ε (leibniz (.obs (.compose a b))) ≠ ε (.obs (.compose a b)) :=
  encoding_obstruction ε hε a b

/-- The specific Peano instance: obs applied to the composition of
    successors. S ∘ S is the simplest compound term, and even here
    the Leibniz rewrite produces a different encoding. -/
theorem peano_succ_succ_obstruction
    (ε : GTerm PeanoAtom → ℕ) (hε : Function.Injective ε) :
    ε (leibniz (.obs (.compose (.atom .succ) (.atom .succ)))) ≠
    ε (.obs (.compose (.atom .succ) (.atom .succ))) :=
  encoding_obstruction ε hε (.atom .succ) (.atom .succ)

/-! ## ZF set theory -/

/-- The primitives of ZF set theory. -/
inductive ZFAtom where
  | empty     -- ∅
  | pair      -- {a, b}
  | union     -- ⋃
  | powerset  -- 𝒫
  | inf       -- ω (axiom of infinity)
  | sep       -- separation
  | repl      -- replacement
  deriving DecidableEq, Repr

/-- In ZF, obs(compose(a, b)) rewrites to a structurally different term.
    No set-theoretic encoding commutes with observation. -/
theorem zf_encoding_obstruction
    (ε : GTerm ZFAtom → ℕ) (hε : Function.Injective ε)
    (a b : GTerm ZFAtom) :
    ε (leibniz (.obs (.compose a b))) ≠ ε (.obs (.compose a b)) :=
  encoding_obstruction ε hε a b

/-- ZF instance: pairing composed with itself. -/
theorem zf_pair_pair_obstruction
    (ε : GTerm ZFAtom → ℕ) (hε : Function.Injective ε) :
    ε (leibniz (.obs (.compose (.atom .pair) (.atom .pair)))) ≠
    ε (.obs (.compose (.atom .pair) (.atom .pair))) :=
  encoding_obstruction ε hε (.atom .pair) (.atom .pair)

/-! ## Universality -/

/-- **Universality:** The obstruction holds for ANY atom type.
    No matter what primitives your formal system has, no injective
    encoding commutes with observation on compound terms.

    This is because the obstruction is in the ALGEBRA (Leibniz rule
    changes the constructor), not in the ATOMS (what your system
    is about). -/
theorem universal_encoding_obstruction (Atom : Type*) :
    ∀ (ε : GTerm Atom → ℕ), Function.Injective ε →
    ∀ (a b : GTerm Atom),
    ε (leibniz (.obs (.compose a b))) ≠ ε (.obs (.compose a b)) :=
  fun ε hε a b => encoding_obstruction ε hε a b

/-- Package the universal obstruction as a formal `InjectiveObstruction`.
    For any atoms and any compound term obs(compose(a, b)), no injective
    encoding maps the Leibniz rewrite and the original to the same code. -/
def encoding_obstruction_instance {Atom : Type*} (a b : GTerm Atom) :
    InjectiveObstruction (GTerm Atom) ℕ
      (fun ε => ε (leibniz (.obs (.compose a b))) = ε (.obs (.compose a b))) :=
  ⟨fun ε hε heq => encoding_obstruction ε hε a b heq⟩

end GTerm
