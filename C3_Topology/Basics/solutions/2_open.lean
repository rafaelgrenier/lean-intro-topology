import Mathlib.Data.Set.Basic
import Mathlib.Topology.Instances.Int
open TopologicalSpace
open Set
namespace OpenClosed
/-
# Open and Closed
Recall that sets included in the topology are called "open" sets, and their complements are "closed."
Since open-ness is preserved under finite intersections and arbitrary unions,
which set operations preserved closedness?
-/
variable {X : Type} [T_X : TopologicalSpace X]
def IsClosed (S : Set X) := T_X.IsOpen (Sᶜ)

-- finite union
theorem isClosed_union {S T : Set X} : IsClosed S → IsClosed T → IsClosed (S ∪ T) := by
  intro _ _
  simp only [IsClosed] at *
  rw [compl_union]
  apply T_X.isOpen_inter <;> assumption

-- arbitrary intersection
theorem isClosed_sInter {C : Set (Set X)} (hC : ∀ S ∈ C, IsClosed S) : IsClosed (⋂₀ C) := by
  simp only [IsClosed] at *
  have aux : (⋂₀ C)ᶜ = ⋃₀ {T : Set X | ∃ S ∈ C, Sᶜ = T} := by
    ext x
    simp
  rw [aux]
  apply T_X.isOpen_sUnion
  intro T ⟨S, SinC, ScompT⟩
  rw [←ScompT]
  apply hC S SinC

-- let's mix open and closed sets
lemma set_diff_inter_comp (A B : Set X) : A \ B = A ∩ Bᶜ := rfl

example {U A : Set X} : IsOpen U → IsClosed A → IsOpen (U \ A) := by
  intro openU cloA
  rw [set_diff_inter_comp]
  apply IsOpen.inter openU
  exact cloA

-- note that a set might be both open and closed, or neither
example (S T : Set X) (hST : Disjoint S T) (openS : IsOpen S) (openT : IsOpen T) :
  IsOpen (Set.univ : Set X) ∧ IsClosed (Set.univ : Set X) := by
  use isOpen_univ
  have : ∅ = S ∩ T := Eq.symm (Disjoint.inter_eq hST)
  simp [IsClosed, compl_univ]
  rw [this]
  exact TopologicalSpace.isOpen_inter S T openS openT

/-!
### Interior of a set

One of the most frequent ways to prove a set S is open is to show that all
points in that set are 'interior points,' meaning there is an open set Uₓ contained
in S and containing x for each point x in S.

Here we put in a little bit of work to prove that a set is open iff it equals
its interior. (The following theorems are slightly modified from Mathlib)
-/
-- The interior of a set `S` is the the union of all open subsets of `S`.
def interior (S : Set X) : Set X :=
  ⋃₀ { U | IsOpen U ∧ U ⊆ S }
-- The following theorems from Mathlib may come in handy
#check TopologicalSpace.isOpen_sUnion
#check sUnion_subset
#check subset_sUnion_of_mem

-- The interior of any set is open
theorem isOpen_interior {S : Set X} : IsOpen (interior S) := by
  apply isOpen_sUnion
  simp only [mem_setOf_eq, and_imp]
  intro T openT _
  exact openT

lemma interiorSubset {S : Set X} : interior S ⊆ S := λ _ ⟨_, ⟨_, hUS⟩, xU⟩ ↦ hUS xU

-- Any open set in S is also in the interior of S
theorem interior_maximal {S U : Set X} (h₁ : U ⊆ S) (h₂ : IsOpen U) : U ⊆ interior S := by
  intro x xU
  dsimp only [interior]
  rw [mem_sUnion]
  exists U

-- If S is open, S is its own interior, and vice versa
theorem interior_eq_iff_isOpen {S : Set X} : interior S = S ↔ IsOpen S := by
  constructor
  · intro h
    rw [←h]
    exact isOpen_interior
  · intro openS
    apply Subset.antisymm interiorSubset (interior_maximal (Subset.rfl) openS)

/-
### Closure and Boundary of a Set

The closure of a set is somewhat the opposite of the interior; the interior is the
union of all open sets contained within and the closure is the intersection of all
closed sets containing the original set.
As the name implies, the closure of a set is closed.

The boundary of a set is the difference between the closure and interior. In Mathlib,
the boundary of a set is referred to as the frontier.
From here we'll prove some theorems about the closure and boundary of a set.
-/
#check IsOpen.union --useful for binary union of open sets
def closure (S : Set X) : Set X :=
  ⋂₀ {T | IsClosed T ∧ S ⊆ T }

def boundary (S : Set X) : Set X :=
  closure S \ interior S

theorem isClosed_closure {S : Set X} : IsClosed (closure S) := by
  apply isClosed_sInter
  rintro A ⟨cloA, _⟩
  exact cloA

lemma subsetClosure {S : Set X} : S ⊆ closure S := λ _ xS _ ⟨_, hSA⟩ ↦ hSA xS

theorem closure_eq_iff_isClosed {S : Set X} : closure S = S ↔ IsClosed S := by
  constructor
  · intro h
    rw [←h]
    exact isClosed_closure
  · intro cloS
    ext x
    simp only [closure, mem_sInter, mem_setOf_eq, and_imp]
    exact ⟨λ h ↦ h S cloS (Eq.subset rfl), λ xS _ _ hSA ↦ hSA xS⟩

lemma isClosed_setDiff {S T : Set X} (openS : IsOpen S) (cloT : IsClosed T) :
  IsClosed (T \ S) := by
  have : ⋂₀ {T, Sᶜ} = T ∩ Sᶜ := by
    simp only [mem_singleton_iff, sInter_insert, sInter_singleton]
  rw [set_diff_inter_comp, ←this]
  apply isClosed_sInter
  simp only [mem_singleton_iff, mem_insert_iff, forall_eq_or_imp, forall_eq]
  use cloT
  dsimp [IsClosed]
  rw [compl_compl]
  exact openS

theorem isClosed_boundary {S : Set X} : IsClosed (boundary S) := by
  apply isClosed_setDiff
  · exact isOpen_interior
  · exact isClosed_closure

theorem empty_boundary_iff_open_and_closed {S : Set X} :
    boundary S = ∅ ↔ (IsOpen S ∧ IsClosed S) := by
  simp [boundary]
  have aux (U V : Set X) : U \ V = ∅ ↔ U ⊆ V := by
    simp [ext_iff]
    rfl
  rw [aux, ←closure_eq_iff_isClosed, ←interior_eq_iff_isOpen]
  constructor
  · intro h
    constructor
    · exact Subset.antisymm interiorSubset (Subset.trans subsetClosure h)
    · exact Subset.antisymm (Subset.trans h interiorSubset) subsetClosure
  · rintro ⟨openS, cloS⟩
    rw [openS, cloS]

/-
Later, we will investigate the topological property of connectedness. A connected space
has some set not equal to univ or ∅ which is both open and closed, i.e. a set with no boundary.
-/
end OpenClosed
