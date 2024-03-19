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
  ext x
  apply Iff.intro
  · rintro ⟨xs, xt | xu⟩
    · apply Or.inl
      exact ⟨xs, xt⟩
    · apply Or.inr
      exact ⟨xs, xu⟩
  · rintro (⟨xs, xt⟩ | ⟨xs, xu⟩)
    · exact ⟨xs, Or.inl xt⟩
    · exact ⟨xs, Or.inr xu⟩

lemma convenience : ∀ x : α, (x ∉ t ∪ u) → x ∉ t ∧ x ∉ u := by
  intro a h
  apply And.intro
  · intro hat
    apply h
    apply Or.inl hat
  · intro hau
    apply h
    apply Or.inr hau

--MIL 4.1 Problem #2
example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, h⟩
  rcases convenience t u x h with ⟨xnt, xnu⟩
  exact ⟨⟨xs, xnt⟩, xnu⟩

--MIL 4.1 Problem #7
example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  apply Iff.intro
  · rintro (⟨xs, xnt⟩|⟨xt, xns⟩)
    · refine ⟨Or.inl xs, ?_⟩
      rintro ⟨_, xt⟩
      exact xnt xt
    · refine ⟨Or.inr xt, ?_⟩
      rintro ⟨xs, _⟩
      exact xns xs
  · rintro ⟨(xs | xt), h⟩
    · apply Or.inl
      use xs
      intro xt
      apply h
      exact ⟨xs, xt⟩
    · apply Or.inr
      use xt
      intro xs
      apply h
      exact ⟨xs, xt⟩

--MIL 4.1 Problem #11
example : (s ∪ (⋂ i, A i)) = ⋂ i, A i ∪ s := by
  ext x
  apply Iff.intro
  · rintro (xs | h)
    · rw [Set.mem_iInter]
      intro i
      exact Or.inr xs
    · rw [Set.mem_iInter] at *
      intro i
      apply Or.inl
      exact h i
  · intro h
    simp at *
    rcases (em (x ∈ s)) with (xs | xns)
    · exact Or.inl xs
    · apply Or.inr
      intro i
      rcases h i with (xAi | xs)
      · exact xAi
      · apply False.elim (xns xs)

example: (s ∩ ∅ = ∅) ∧ (s ∪ ∅ = s) := by
  apply And.intro
  · ext x
    apply Iff.intro
    · rintro ⟨_, xe⟩
      exact xe
    · exact False.elim
  · ext x
    apply Iff.intro
    · rintro (xs | h)
      · exact xs
      · exact False.elim h
    · intro xs
      apply Or.inl
      exact xs

example : ∀ Q : Set α, (Q = ∅ ↔ ¬ ∃ a : α, a ∈ Q) := by
  intro S
  apply Iff.intro
  · intro Sempt ⟨a, as⟩
    rw [Sempt] at as
    exact as
  · intro h
    ext x
    refine ⟨?_, False.elim⟩
    intro xS
    apply h
    exists x

example : sᶜ ∩ tᶜ = (s ∪ t)ᶜ := by
  ext x
  apply Iff.intro
  · rintro ⟨xns, xnt⟩ (xs | xt)
    · exact xns xs
    · exact xnt xt
  · apply convenience

end SetPractice

section FuncPractice
variable {α β γ : Type*}
variable (f : α → β) (g : β → γ)
variable (s t : Set α)
variable (u v : Set β)
open Set
open Function

--MIL 4.2 Problem #1
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  apply Iff.intro
  · intro h x xs
    apply h
    exists x
  · intro h b ⟨a, as, fab⟩
    rw [←fab]
    exact h as

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  change f x ∈ f '' s
  exists x

example (injf : Injective f) (injg : Injective g) : Injective (g ∘ f) := by
  intro x y h
  apply injf
  apply injg
  exact h

example (surjf : Surjective f) (surjg : Surjective g) : Surjective (g ∘ f) := by
  intro z
  rcases surjg z with ⟨y, hy⟩
  rcases surjf y with ⟨x, hx⟩
  exists x
  rw [←hy, ←hx]
  rfl

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
  have h2 : j ∈ S := h1
  have h3 : j ∉ S := by {
    rw [←h]
    exact h1
  }
  contradiction
