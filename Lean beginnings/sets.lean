/-
# Sets in Lean

For any type α, Set α is the type which contains all sets of elements which are 
of type α. This is actually part of how type theory was developed, as this
construction of sets prevents Russell's paradox, since the set of all sets
is not well-defined in the type-theoretic construction.


-/
import Mathlib.Init.Set
open Set
variable (α β : Type) (S T U : Set α) (V W : Set β)

example : S ∩ (T ∪ U) = (S ∩ T) ∪ (S ∩ U) := by
  apply ext
  intro x
  apply Iff.intro
  · intro ⟨xS, xTU⟩
    apply Or.elim xTU
    · intro xT
      apply Or.inl
      exact ⟨xS, xT⟩
    · intro xU
      apply Or.inr
      exact ⟨xS, xU⟩
  · intro hx
    apply Or.elim hx
    · intro ⟨xS, xT⟩
      apply And.intro
      exact xS
      apply Or.inl
      exact xT
    · intro ⟨xS, xU⟩
      apply And.intro xS
      apply Or.inr xU




