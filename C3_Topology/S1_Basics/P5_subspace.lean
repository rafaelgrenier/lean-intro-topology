import Mathlib.Data.Set.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Topology.Order
import Mathlib.Topology.Bases
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
open TopologicalSpace

/-
# Subspace Topology

Given a space X with a defined topology, any subset S of X (or as we
will implement, a subtype) inherits a topology.
The open sets on the subspace are just the open sets of the superspace,
only intersected with the subspace so that the sets are actually contained
within the subspace.

-/

#check instTopologicalSpaceSubtype

example {X : Type} [TopologicalSpace X] {p : X → Prop} (S : Set X) (Sopen : IsOpen S) :
  IsOpen ({x : Subtype p | x.val ∈ S}) := by
  rw [isOpen_induced_eq]
  exists S

-- If a subspace is open, then any open set in the subspace topology is
-- also open in the ambient topology

example {X : Type} [TopologicalSpace X] (p : X → Prop) (hopen : IsOpen {x | p x}) :
  ∀ U : Set X, U ⊆ {x | p x} → (IsOpen {x : Subtype p | x.val ∈ U}) → IsOpen U := by
  intro U hU Uopen_p
  simp [isOpen_induced_eq] at Uopen_p
  rcases Uopen_p with ⟨V, openV, hV⟩
  simp [Set.preimage, Set.ext_iff] at hV
  have : U = V ∩ {x | p x} := by
    ext x
    constructor
    · intro xU
      constructor
      · rw [hV x (hU xU)]
        exact xU
      exact hU xU
    · rintro ⟨xV, hpx⟩
      rw [←hV x hpx]
      exact xV
  rw [this]
  exact IsOpen.inter openV hopen

-- It's not necessarily true that for ANY subspace, its open sets are open in the superspace

-- This topology is called the "trivial topology" and is the smallest
-- collection of open sets which constitutes a topology.
instance : TopologicalSpace ℕ where
  IsOpen := λ S ↦ S = Set.univ ∨ S = ∅
  isOpen_univ := Or.inl rfl
  isOpen_inter := by
    intro S T
    dsimp only
    rintro (Suniv | Sempty)
    · rintro (Tuniv | Tempty)
      · apply Or.inl
        rw [Suniv, Tuniv]
        exact Set.univ_inter Set.univ
      · apply Or.inr
        rw [Tempty]
        exact Set.inter_empty S
    · intro
      apply Or.inr
      rw [Sempty]
      exact Set.empty_inter T
  isOpen_sUnion := by
    intro C hC
    rw [Set.sUnion_eq_univ_iff, Set.sUnion_eq_empty]
    rcases (em (Set.univ ∈ C)) with (h | h)
    · apply Or.inl
      intro
      exists Set.univ
    apply Or.inr
    intro S SC
    let claim := hC S SC
    rcases claim with (Suniv | Sempty)
    · apply False.elim (h _)
      rw [← Suniv]
      exact SC
    exact Sempty

def ex1 := Subtype (λ n ↦ n = 0)

instance t_ex1 : TopologicalSpace ex1 := instTopologicalSpaceSubtype

example : ∃ S : Set ℕ, t_ex1.IsOpen {x : ex1 | x.val ∈ S} ∧ ¬(IsOpen S) := by
  exists {0}
  constructor
  · have : {x : ex1 | (x.val : ℕ) ∈ ({0} : Set ℕ)} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro ⟨n, neq0⟩
      simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
      exact neq0
    rw [this]
    apply isOpen_univ
  dsimp [IsOpen, TopologicalSpace.IsOpen]
  simp only [Set.singleton_ne_empty, or_false]
  show {0} ≠ Set.univ
  rw [Set.ne_univ_iff_exists_not_mem {0}]
  exists 1
