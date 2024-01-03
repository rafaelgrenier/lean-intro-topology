import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Ring.Basic

/-
# Order Relation

Formally, a relation on a type α is implemented in Lean as a function with type
α → α → Prop, and this is equivalent to the set theoretic construction of some
subset of α × α. (α → α → Prop is equiv to α × α → Prop)
-/
namespace Order
-- A strict order relation just needs to be transitive and irreflexive, defined here
def trans_rel {X : Type} (r : X → X → Prop) := ∀ x y z : X, r x y → r y z → r x z
def irrefl_rel {X : Type} (r : X → X → Prop) := ∀ x : X, r x x → False

structure StrictOrder (α : Type) where
  lt : α → α → Prop
  lt_trans : trans_rel lt
  lt_irrefl : irrefl_rel lt

-- Let's consider some relations on ℕ
def rel₁ (a b : Nat) : Prop := 2*a < b
def rel₂ (a b : Nat) : Prop := a < 2*b
-- Are both of them order relations?
-- The first line of each proof should be `apply Or.inl` or `apply Or.inr`
example : trans_rel rel₁ ∨ ¬(trans_rel rel₁) := by
  sorry

example : irrefl_rel rel₁ ∨ ¬(irrefl_rel rel₁) := by
  sorry

example : trans_rel rel₂ ∨ ¬(trans_rel rel₂) := by
  sorry

example : irrefl_rel rel₂ ∨ ¬(irrefl_rel rel₂) := by
  sorry


end Order
