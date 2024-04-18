import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic
open TopologicalSpace
open Set
namespace BasisYieldsTopology
/-
# Topology in LEAN
For some space X, a topology T is a collection of sets of elements from X satisfying the following:
· univ ∈ T,
· ∅ ∈ T,
· The union of arbitrarily many sets in T is also in T, and
· The intersection of any two sets in T is also in T.
The sets included in the topology are called "open" sets, and their complements are "closed."
-/
class TopologicalSpace (α : Type u) where
  IsOpen : Set α → Prop
  IsOpenUniv : IsOpen Set.univ
  IsOpenInter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  IsOpenSetUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s) -- ∅ ∈ T follows from s = ∅

def IsOpen [TopologicalSpace α] : Set α → Prop := TopologicalSpace.IsOpen


/-
Specifying a particular topology is cumbersome to do directly from the above definition, so instead
there are a handful of other means to describe a topology on a space. In this section, we will
discuss two: Bases and Filters.

A basis B for a topology is a collection of sets such that
B covers the entire space and covers the intersection of any two sets in B.
(for any pair of sets in B, there are sets in B which lie within the intersection and cover it)
This notion of a basis yields a topology T whose open sets are all possible unions of basis sets.
You may check for yourself that the properties of a basis guarantee that T will be a topology.
-/
structure Basis (α : Type u) where
  Carrier : Set (Set α) --The sets which comprise the basis
  Basis_Cover : ⋃₀ Carrier = Set.univ --The basis covers the entire space
  Basis_Cover_Inter {B₁ B₂ : Set α}: --The basis covers intersections of basis sets
    B₁ ∈ Carrier → B₂ ∈ Carrier → ∀ x ∈ B₁ ∩ B₂, ∃ B₃ ∈ Carrier, x ∈ B₃ ∧ B₃ ⊆ B₁ ∩ B₂
-- Here's a little bit of code for convenience: now we can write B₁ ∈ B rather than B₁ ∈ B.Carrier
instance {α : Type*} : Membership (Set α) (Basis α) := ⟨fun U B => U ∈ B.Carrier⟩
variable {X : Type} [TopologicalSpace X]

-- Now to prove that a basis specifies a topology!
instance (B : Basis X) : TopologicalSpace X := {
  IsOpen := λ S ↦ ∃ C : Set (Set X), C ⊆ B.Carrier ∧ S = ⋃₀ C,
  IsOpenUniv := by
    sorry

  IsOpenInter := by
    intro U V UT VT
    rcases UT with ⟨C₁, hC₁, UC₁⟩
    rcases VT with ⟨C₂, hC₂, VC₂⟩
    have h : ∀ x ∈ U ∩ V, ∃ B₃ ∈ B, B₃ ⊆ U ∩ V ∧ x ∈ B₃ := by
      rintro x ⟨xU, xV⟩
      rw [UC₁] at xU
      rw [VC₂] at xV
      let ⟨B₁, B₁C₁, xB₁⟩ := xU
      let ⟨B₂, B₂C₂, xB₂⟩ := xV
      clear xU xV
      let ⟨B₃, B₃B, xB₃, B₃inter⟩ := B.Basis_Cover_Inter (hC₁ B₁C₁) (hC₂ B₂C₂) x ⟨xB₁, xB₂⟩
      exists B₃
      sorry
    choose! f hf₁ hf₂ hf₃ using h
    exists {S | ∃ x ∈ U ∩ V, S = f x}
    constructor
    · sorry
    · sorry

  IsOpenSetUnion := by
    intro C hC
    choose! f hf₁ hf₂ using hC
    exists (⋃₀ {C' | ∃ S ∈ C, C' = f S})
    simp
    constructor
    · intro C' S SC C'fS
      rw [C'fS]
      exact hf₁ S SC
    · ext x
      constructor
      · rintro ⟨S, hS, xS⟩
        simp
        rw [hf₂ S hS] at xS
        let ⟨U, UfS, xU⟩ := xS
        exists U
        refine ⟨?_, xU⟩
        exists f S
        refine ⟨(by exists S), UfS⟩
      · sorry
}

end BasisYieldsTopology
