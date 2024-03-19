import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card

/-

# Finite Types

Before we can discuss finiteness, we need to delve a little further
into the Type theory which underpins Lean. If `α : Type` and
`P : α → Prop` is a predicate on α, then we can create a subtype
which consists of only those terms of α which satisfy the predicate,
denoted `{a : α // P a} : Type`. One such subtype is `Fin : ℕ → Type`, where
for any `n : ℕ`, `Fin n` is defined `{k : ℕ // k < n}`. If there exists a
bijective function `f : α → β`, then we can map back and forth between
the two types, so we call those type equivalent, denoted `α ≃ β`.

Now we have enough tools to define what it means for a type to be finite.
A Type α is Finite if there exists some n : ℕ for which α ≃ Fin n. We will
be using Subtypes in particular more as time goes on.
-/

#print Subtype
#check Subtype.mk
#print Equiv
#check Equiv.mk
#print Finite

#check Finite.of_injective
#check Finite.of_surjective

example {α : Type} [Finite α] (P : α → Prop) : Finite {a : α // P a} := by
  let f : {a : α // P a} → α := λ ⟨a, _⟩ ↦ a
  apply Finite.of_injective f
  intro ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩
  simp only [Subtype.mk.injEq, imp_self]
