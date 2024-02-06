/-
# Sets and Functions in LEAN (Pt. 2: Practice)

The following sample problems are pulled from Math in Lean chapter 4, plus a few
of my own making.

-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Image
section SetPractice --This keyword just marks a local scope, so the following variables
                      --are only defined for the following problems
variable {α I : Type*}
variable (s t u : Set α)
variable (A B : I → Set α)
open Set

#check mem_empty_iff_false
#check mem_univ

--MIL 4.1 Problem #1
example : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u := by
  sorry

--MIL 4.1 Problem #2
example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  sorry

--MIL 4.1 Problem #7
example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  sorry

--MIL 4.1 Problem #11
example : (s ∪ (⋂ i, A i)) = ⋂ i, A i ∪ s := by
  sorry

example: (s ∩ ∅ = ∅) ∧ (s ∪ ∅ = s) := by
  sorry

example : ∀ Q : Set α, (Q = ∅ ↔ ¬ ∃ a : α, a ∈ Q) := by
  sorry

example : sᶜ ∩ tᶜ = (s ∪ t)ᶜ := by
  sorry

end SetPractice

section FuncPractice
variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)
open Set
open Function

--MIL 4.2 Problem #1
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  sorry

example : s ⊆ f ⁻¹' (f '' s) := by
  sorry
end FuncPractice
open Function
--MIL 4.2 Problem #22
theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
/-
This is a proof that no function mapping a set to its power set can be surjective.
The idea behind this proof is to construct a subset of the domain (here denoted S) such that
no element from the domain can be mapped to that subset. Try proving the last two blocks!
-/
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h1 : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  clear surjf
  have h2 : j ∈ S := by {sorry}
  have h3 : j ∉ S := by {sorry}
  contradiction
