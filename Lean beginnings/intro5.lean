/-
# Sets in Lean

For any type α, Set α is the type which contains all sets of elements which are
of type α. This is actually part of how type theory was developed, as this
construction of sets prevents Russell's paradox, since the set of all sets
is not well-defined in the type-theoretic construction.

There are two sets that always exist for any type: univ and ∅.
univ : Set α has the property that ∀ x : α, x ∈ univ.
∅ : Set α has the property that ∀ x : α, ¬x ∈ ∅.
The symbol ∈ denotes inclusion in a set, and for any S : Set α and
any x : α, either x ∈ S or x ∉ S.

Let X be a type, P : X → Prop.
Then a new set on X can be created by S := {a : X | p a} : Set X.
S is then the set which only included a : X which make p a True.

For two sets S and T, we say S ⊆ T if ∀ x : α, x ∈ S → x ∈ T.
In fact, these are definitionally equal statements.
-/
import Mathlib.Init.Set
open Set
variable (α β : Type) (S T U : Set α) (V W : Set β)

example : ∅ ⊆ (univ : Set α) := by
  intro x
  intro _
  trivial

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
