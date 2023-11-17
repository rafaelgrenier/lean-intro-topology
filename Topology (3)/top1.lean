/-
# Topology in LEAN
For some space X, a topology T is a collection of sets of elements from X satisfying the following:
· univ ∈ T,
· ∅ ∈ T,
· The union of arbitrarily many sets in T is also in T, and
· The intersection of any two sets in T is also in T.
The sets included in the topology are called "open" sets, and their complements are "closed."

Specifying a particular topology is cumbersome to do directly from the above definition, so instead
there are a handful of other means to describe a topology on a space. In this section, we will
discuss two: Bases and Filters.

-/
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic
open TopologicalSpace
#check TopologicalSpace
#check IsOpen
#check isOpen_univ
#check IsOpen.inter
#check isOpen_sUnion

/-
A basis B for a topology is a collection of sets such that
· B covers the entire space, i.e. ⋃₀ B = univ , and
· ∀ S₁ ∈ B, ∀ S₂ ∈ B, ∀ x ∈ S₁ ∩ S₂, ∃ S₃ ∈ B, x ∈ S₃ ∧ S₃ ∈ S₁ ∩ S₂.
  (for any pair of sets in B, there are sets in B which lie within the intersection and cover it)
This notion of a basis yields a topology T whose open sets are all possible unions of basis sets.
You may check for yourself that the properties of a basis guarantee that T will be a topology.
-/
namespace BasisYieldsTopology
variable {X : Type} (B : Set (Set X)) (Bcover : ⋃₀ B = Set.univ)
variable (Bcover_inter: ∀ S₁ ∈ B, ∀ S₂ ∈ B, ∀ x ∈ S₁ ∩ S₂, ∃ S₃ ∈ B, x ∈ S₃ ∧ S₃ ⊆ S₁ ∩ S₂)
variable (T : Set (Set X)) (hT : ∀ S : Set X, S ∈ T ↔ ∃ C : Set (Set X), C ⊆ B ∧ S = ⋃₀ C)

example : Set.univ ∈ T := by sorry

example : ∀ S₁ S₂ : Set X, S₁ ∈ T → S₂ ∈ T → S₁ ∩ S₂ ∈ T := by sorry

example : ∀ C : Set (Set X), C ⊆ T → (⋃₀ C) ∈ T := by sorry
end BasisYieldsTopology
