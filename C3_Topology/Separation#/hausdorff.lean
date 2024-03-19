import Mathlib.Data.Set.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Bases
open TopologicalSpace
/-

# Hausdorff

-/
namespace Separation
variable {X : Type} [T_X : TopologicalSpace X]

def Hausdorff := ∀ x y, x ≠ y → ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v
def diagonal : Set (X × X) := {p | p.1 = p.2}
def ProdBasis : Set (Set (X×X)) :=
  {B | ∃ U V : Set X, T_X.IsOpen U ∧ T_X.IsOpen V ∧ B = (U ×ˢ V)}

instance T_XX : TopologicalSpace (X × X) := generateFrom (ProdBasis)
lemma name (U : Set (X×X)) (openU : IsOpen U) (x y : X) (hU : ⟨x, y⟩ ∈ U) :
  ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ A ×ˢ B ⊆ U := sorry

theorem diag_closed_iff_Haus : @Hausdorff X T_X ↔ IsClosed (@diagonal X) := by
  constructor
  · intro haus
    rw [←isOpen_compl_iff, ←interior_eq_iff_isOpen]
    ext ⟨x, y⟩
    rw [mem_interior]
    constructor
    · intro ⟨U, h, _, xyU⟩
      apply h xyU
    · intro h
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at h
      let ⟨U, V, openU, openV, xU, yV, djUV⟩ := haus x y h
      exists (U ×ˢ V)
      constructor
      · intro q ⟨q1U, q2V⟩
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
        intro h'
        have aux : {q.1} ⊆ U := by
          intro x xq1
          rw [(Set.mem_singleton_iff).mp xq1]
          exact q1U
        have : {q.fst} ⊆ V := by
          sorry
        apply (djUV aux this ((Set.mem_singleton_iff).mpr (refl q.1)))
      constructor
      · constructor
        dsimp [ProdBasis]
        exists U, V
      simp
      exact ⟨xU, yV⟩
  · rintro ⟨h⟩ x y xney
    rcases name (diagonalᶜ) h x y xney with ⟨U, V, openU, openV, xU, yV, hUV⟩
    use U, V, openU, openV, xU, yV
    intro S SU SV z zS
    simp only [Set.bot_eq_empty, Set.mem_empty_iff_false]
    simp only [compl, diagonal, Set.mem_setOf_eq] at hUV
    have aux : ⟨z, z⟩ ∈ U ×ˢ V := by
      exact ⟨SU zS, SV zS⟩
    apply hUV aux
    rfl





end Separation
