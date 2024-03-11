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
  {B | ∃ U : Set X, ∃ V : Set Y, IsOpen U ∧ IsOpen V ∧ B = (U ×ˢ V)}
  -- Conventionally written {U × V | U is open in X and V is open in Y}

-- `generateFrom` is a function which creates the smallest topology on a space α
-- which contains some given collection of sets on α
instance T_XY : TopologicalSpace (X × Y) := generateFrom (ProdBasis)
-- Now that we have a topology on X × Y, let's affirm that ProdBasis is a basis

theorem ProdBasis_Cover_Inter :
    ∀ (t₁ : Set (X × Y)), t₁ ∈ ProdBasis →
    ∀ (t₂ : Set (X × Y)), t₂ ∈ ProdBasis →
    ∀ x ∈ t₁ ∩ t₂,
    ∃ t₃ ∈ ProdBasis, x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂ := by
  rintro B₁ ⟨U₁, V₁, _, _, B₁def⟩ B₂ ⟨U₂, V₂, _, _, B₂def⟩ p hp
  simp [B₁def, B₂def] at *
  clear B₁def B₂def
  exists ((U₁∩U₂) ×ˢ (V₁∩V₂))
  constructor
  · exists (U₁ ∩ U₂), (V₁ ∩ V₂)
    refine ⟨?_, ?_, rfl⟩ <;> (apply IsOpen.inter <;> assumption)
  rw [←Set.prod_inter_prod];
  refine ⟨hp, ?_, ?_⟩
  · exact Set.inter_subset_left (U₁ ×ˢ V₁) (U₂ ×ˢ V₂)
  · exact Set.inter_subset_right (U₁ ×ˢ V₁) (U₂ ×ˢ V₂)

theorem ProdBasis_Cover : ⋃₀ (ProdBasis) = (Set.univ : Set (X × Y)) := by
  ext p
  simp [ProdBasis]
  refine ⟨Set.univ, ?_, trivial⟩
  exact ⟨Set.univ, isOpen_univ, Set.univ, isOpen_univ, Eq.symm Set.univ_prod_univ⟩

instance ProdBasisIsBasis : IsTopologicalBasis (@ProdBasis X Y T_X T_Y) where
  exists_subset_inter := ProdBasis_Cover_Inter
  sUnion_eq := ProdBasis_Cover
  eq_generateFrom := rfl

#check ProdBasisIsBasis.isOpen_iff

lemma open_prod_iff_covered_prod_nhds : ∀ U : Set (X×X), IsOpen U ↔ ∀ p ∈ U,
  ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ p.1 ∈ A ∧ p.2 ∈ B ∧ A ×ˢ B ⊆ U := by
  intro U
  rw [ProdBasisIsBasis.isOpen_iff]
  dsimp [ProdBasis]
  constructor
  · rintro openU ⟨x, y⟩ xyU
    let ⟨V, ⟨A, B, openA, openB, V_def⟩, xyV, VsubU⟩ := openU ⟨x, y⟩ xyU
    use A, B, openA, openB
    rw [V_def] at xyV VsubU
    use xyV.1, xyV.2
  · rintro h ⟨x, y⟩ xyU
    let ⟨A, B, openA, openB, xA, yB, AxBsubU⟩ := h ⟨x, y⟩ xyU
    exists (A ×ˢ B)
    refine ⟨?_, ?_, AxBsubU⟩
    use A, B, openA, openB
    use xA

end ProductTop
