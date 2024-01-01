/-
# Cartesian Products

Cartesian Products allow for a new way to create new sets. For sets (S : set α) and (T : set β),
the new set S ⨯ˢ T is of type set (α × β) such that for each p ∈ S and q ∈ T,
the pair (p, q) is in S ×ˢ T.
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Prod
variable (α β : Type)
variable (S T : Set α) (U V : Set β)
open Set

-- here are a few examples of proofs involving Cartesian Products
example {p : α} {q : β} (hp : p ∈ S) (hq : q ∈ U) : (p, q) ∈ S ×ˢ U := by
  rw [mem_prod_eq]
  dsimp
  constructor
  · exact hp
  · exact hq

example (hST : S ⊆ T) (hUV : U ⊆ V) : S ×ˢ U ⊆ T ×ˢ V := by
  intro p hp
  rw [mem_prod_eq] at *
  constructor
  · apply hST
    exact And.left hp
  · apply hUV
    exact And.right hp

-- You try!
example {p : α} {q : β} : (p, q) ∈ S ×ˢ U ↔ (q, p) ∈ U ×ˢ S := by
  sorry

-- Cartesian Products get more interesting when we consider the product of not just two set,
-- but a whole family of sets!
-- "I" is an index set, so A and B are functions which map elements in I to sets of α
--variable (I : Type) (A B : I → Set α)

/-
# TODO: sUnion, Quotient, Structures, Typeclasses
-/
