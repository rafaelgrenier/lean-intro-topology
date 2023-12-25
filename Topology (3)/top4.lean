import Mathlib.Data.Set.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Bases
open TopologicalSpace
/-
# Product Topology
Given a pair of spaces X and Y with topologies T_X and T_Y, the product topology
on the space X×Y is given by the basis consisting of all possible products of
open sets
-/

namespace ProductTop
variable {X Y : Type} [T_X : TopologicalSpace X] [T_Y : TopologicalSpace Y]

def ProdBasis : Set (Set (X×Y)) :=
  {B | ∃ U : Set X, ∃ V : Set Y, T_X.IsOpen U ∧ T_Y.IsOpen V ∧ B = (U ×ˢ V)}
  -- Conventionally written {U × V | U is open in X and V is open in Y}

instance T_XY : TopologicalSpace (X × Y) := generateFrom (ProdBasis)

theorem ProdBasis_Cover_Inter :
    ∀ (t₁ : Set (X × Y)), t₁ ∈ ProdBasis →
    ∀ (t₂ : Set (X × Y)), t₂ ∈ ProdBasis →
    ∀ x ∈ t₁ ∩ t₂,
    ∃ t₃, t₃ ∈ ProdBasis ∧ x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂ := by
  rintro B₁ ⟨U₁, V₁, _, _, B₁def⟩ B₂ ⟨U₂, V₂, _, _, B₂def⟩ p hp
  simp [B₁def, B₂def] at *
  clear B₁def B₂def
  exists ((U₁∩U₂) ×ˢ (V₁∩V₂))
  constructor
  · simp [ProdBasis]
    refine ⟨U₁∩U₂, ?_, V₁∩V₂, ?_, ?_⟩
    use (by apply T_X.isOpen_inter <;> assumption)
    use (by apply T_Y.isOpen_inter <;> assumption)
    rfl
  have aux : (U₁ ∩ U₂) ×ˢ (V₁ ∩ V₂) = (U₁ ×ˢ V₁) ∩ (U₂ ×ˢ V₂) := by
    ext; constructor <;>
      rintro ⟨⟨⟩,⟨⟩⟩ <;>
        constructor <;>
          constructor <;>
            assumption
  rw [aux];
  use hp
  constructor <;> simp

theorem ProdBasis_Cover : ⋃₀ (ProdBasis) = (Set.univ : Set (X × Y)) := by
  ext p
  simp [ProdBasis]
  exists Set.univ
  refine ⟨?_, (by trivial)⟩
  exists Set.univ
  use isOpen_univ
  exists Set.univ
  use isOpen_univ
  simp

example : IsTopologicalBasis (@ProdBasis X Y T_X T_Y) where
  exists_subset_inter := ProdBasis_Cover_Inter
  sUnion_eq := ProdBasis_Cover
  eq_generateFrom := rfl
end ProductTop
