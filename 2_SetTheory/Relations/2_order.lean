import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Prod.Lex

/-
# Order Relation

There are many types of order relations: preorders, partial orders, strict orders,
total orders, linear orders, etc.
-/
#print IsStrictOrder
#print Preorder
#print PartialOrder
#print LinearOrder
#check Prod.Lex

section Order
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

def wellOrdered (X : Type) [Preorder X] : Prop :=
  ∀ S : Set X, S ≠ ∅ → ∃ x, IsLeast S x

example {X : Type} [LinearOrder X] (m : X) (mLeast : ∀ x : X, m ≤ x) :
  (∀ P : X → Prop, P m → (∀ x, (∀ y, y < x → P y) → P x) → ∀ x, P x) ↔ wellOrdered X := by
  constructor
  · intro h₁
    by_contra h
    dsimp [wellOrdered, IsLeast] at h
    push_neg at h
    rcases h with ⟨S, Snonempty, hS⟩
    apply Snonempty
    rw [Set.eq_empty_iff_forall_not_mem]
    have base : m ∉ S := by
      sorry
    have ih : ∀ (x : X), (∀ (y : X), y < x → y ∉ S) → x ∉ S := by
      clear h₁ Snonempty
      sorry
    exact (h₁ (λ x ↦ x ∉ S) base ih)
  · intro wO P Pm h x
    let S := {x | ¬P x}
    suffices S = ∅ by {simp [Set.eq_empty_iff_forall_not_mem] at this; apply this}
    apply not_not.mp
    intro Snonempty
    let ⟨n, nS, hn⟩ := wO S Snonempty
    apply nS
    dsimp [lowerBounds] at hn
    apply h
    intro y
    contrapose
    simp only [not_lt] --This is the only part of the proof where Linear Order is necessary
    apply hn



def openInterval {X : Type} [Preorder X] (a b : X) : Set X := {x | a < x ∧ x < b}
-- Mathlib.Data.Set.Intervals.Basic covers all the common intervals

/-
  Bounds
  Supremum
  Successor
  Well-Ordered
  Lexicographic Order
  Intervals
  Rays
Needed for Order Topology:
  Intervals, rays, and lexicographic
-/


end Order
