import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Prod.Lex

/-
# Order Relation

There are many types of order relations: preorders, partial orders, strict orders,
total orders, linear orders, etc. The basic requirement for a strict order
is that the relation be transitive and irreflexive, but we will investigate a
variety of order relations in this section.
-/
#print IsStrictOrder
#print Preorder
#print PartialOrder
#print LinearOrder
#check Prod.Lex

section Order
-- A strict order relation just needs to be transitive and irreflexive, defined here
def trans_rel {X : Type} (r : X → X → Prop) := ∀ x y z : X, r x y → r y z → r x z
def irrefl_rel {X : Type} (r : X → X → Prop) := ∀ x : X, r x x → False

structure StrictOrder (α : Type) where
  lt : α → α → Prop
  lt_trans : trans_rel lt
  lt_irrefl : irrefl_rel lt

-- Let's consider some relations on ℕ
def rel₁ (a b : Nat) : Prop := 2*a < b
def rel₂ (a b : Nat) : Prop := a < 2*b

-- Are both of them order relations?
-- The first line of each proof should be `apply Or.inl` or `apply Or.inr`
example : trans_rel rel₁ ∨ ¬(trans_rel rel₁) := by
  sorry

example : irrefl_rel rel₁ ∨ ¬(irrefl_rel rel₁) := by
  sorry

example : trans_rel rel₂ ∨ ¬(trans_rel rel₂) := by
  sorry

example : irrefl_rel rel₂ ∨ ¬(irrefl_rel rel₂) := by
  sorry

namespace Bounds
/-
Order relations also give us an opportunity to think about boundedness.
A set `S : Set X` is "bounded above" if there is some term `x : X` which is
greater than all elements of the set. In that case, `x` is called an "upper bound"
of `S`. Similarly, a set can be "bounded below" by some "lower bound." Let's
formalize these notions, but we'll use the same approach as Mathlib: first we
consider the set of ALL upper bounds.
-/
variable {X : Type} [PartialOrder X] --Note that only a Preorder is necessary, Partial Order will be useful later
def upperBounds (S : Set X) : Set X := {x | ∀ a ∈ S, a ≤ x}
def lowerBounds (S : Set X) : Set X := {x | ∀ a ∈ S, x ≤ a}
-- Note that the set of upper or lower bounds could be empty
def BddAbove (S : Set X) : Prop := (upperBounds S).Nonempty
def BddBelow (S : Set X) : Prop := (lowerBounds S).Nonempty
-- Let's briefly examine some examples
example : ∀ S : Set ℕ, BddBelow S := by
  intro S
  dsimp [BddBelow, Set.Nonempty, lowerBounds]
  exists 0
  intro n _
  exact Nat.zero_le n

example : ¬ BddAbove (Set.univ : Set ℕ) := by
  dsimp [BddAbove, Set.Nonempty, upperBounds]
  push_neg
  intro n
  exists n + 1
  apply And.intro
  · trivial
  simp only [lt_add_iff_pos_right]

example (S : Set X) : S ⊆ upperBounds (lowerBounds S) := by
  sorry
/-
We can also think of the least and greatest elements of a set using this
framework: the least element of a set is just an element in the set which is also
a lower bound (a similar definition for greatest element). Then, as the previous
exercise may have made you consider, the sets of lower and upper bounds are themselves
sets which might have lower or upper bounds. We define the "least upper bound," or LUB,
or "supremum" of a set as the least element of the set of upper bounds. Similarly,
we define the "greatest lower bound," or GLB, or "infimum" of a set as the greatest
element of the set of lower bounds. Note that this explanation has been casually
using the word "the", but we haven't actually proven that least and greatest
elements of a set are unique. Thankfully, they are unique so long as we upgrade
our Preorder to a PartialOrder.
-/
def IsGreatest (S : Set X) (a : X) : Prop :=
  a ∈ S ∧ a ∈ upperBounds S
def IsLeast (S : Set X) (a : X) : Prop :=
  a ∈ S ∧ a ∈ lowerBounds S
example (S : Set X) (a b : X) (aLeastS : IsLeast S a) (bLeastS : IsLeast S b) : a = b := by
  dsimp [IsLeast, lowerBounds] at aLeastS bLeastS
  rcases aLeastS with ⟨aS, abelowS⟩
  rcases bLeastS with ⟨bS, bbelowS⟩
  have aleb : a ≤ b := abelowS b bS
  have blea : b ≤ a := bbelowS a aS
  -- This is the part where the partial order is necessary
  apply le_antisymm
  · exact aleb
  · exact blea

def IsLUB (S : Set X) (a : X) : Prop := IsLeast (upperBounds S) a
def IsGLB (S : Set X) (a : X) : Prop := IsGreatest (lowerBounds S) a
example (S : Set X) (a b : X) : IsGLB S a → IsGLB S b → a = b := by
  sorry
end Bounds

section Dict
/- # Lexicographic Order!
The Lexicographic order combines order relations with the cartesian product.
Given two types `X Y : Type` and two relations `rx : X → X → Prop` and
`ry : Y → Y → Prop`, the lexicographic relation on `(x₁, y₁)` and `(x₂, y₂)`
holds if either
· `rx x₁ x₂`, or
· `x₁ = x₁ ∧ ry y₁ y₂`.
By that construction, we now have a relation `Prod.Lex rx ry : X×Y → X×Y → Prop`.
-/
#check Prod.Lex
#check Prod.lex_def
-- Let's look at an example: pairs of natural numbers, each with <
def rel : ℕ × ℕ → ℕ × ℕ → Prop := λ p₁ p₂ ↦ Prod.Lex Nat.lt Nat.lt p₁ p₂

example : rel (0, 1) (3, 4) := by
  dsimp [rel]
  rw [Prod.lex_def]
  dsimp
  apply Or.inl
  norm_num

example : rel (2, 5) (2, 300) := by
  rw [rel, Prod.lex_def]
  dsimp
  apply Or.inr
  use rfl
  norm_num

-- Now let's prove that the lexicographic "order" is actually an order when
-- it's built from two orders. For convenience, we will use the same type and
-- relation in each half of the pair.
variable {X : Type} [preoX : Preorder X]
def r : X × X → X × X → Prop := Prod.Lex preoX.lt preoX.lt

lemma irrefl_lex : ∀ p : X × X, ¬ r p p := by
  rintro ⟨x, y⟩
  rw [r, Prod.lex_def]
  simp [lt_iff_le_not_le]

lemma trans_lex : ∀ p q s : X × X, r p q → r q s → r p s := by
  rintro ⟨a, x⟩ ⟨b, y⟩ ⟨c, z⟩
  simp [r, Prod.lex_def]
  rintro (altb | ⟨aeqb, xlty⟩) (bltc | ⟨beqc, yltz⟩)
  · apply Or.inl
    apply lt_trans altb bltc

  · apply Or.inl
    rwa [←beqc]

  · apply Or.inl
    rwa [aeqb]

  · apply Or.inr
    rw [aeqb, beqc]
    use rfl
    exact lt_trans xlty yltz

-- We have our tools ready, now let's demonstrate that a preorder on X
-- induces a natural partial order on X×X, using the lexicographic order.
instance : PartialOrder (X × X) where
  le := λ p q ↦ r p q ∨ p = q
  lt := r
  le_refl := by
    intro a
    apply Or.inr
    rfl
  le_trans := by
    intro a b c
    rintro (rab | aeqb) (rbc | beqc)
    · apply Or.inl
      apply trans_lex _ _ _ rab rbc
    · rw [←beqc]
      apply Or.inl
      exact rab
    · rw [aeqb]
      apply Or.inl
      exact rbc
    · rw [aeqb, beqc]
      apply Or.inr
      rfl
  lt_iff_le_not_le := by
    intro a b
    dsimp [LE.le]
    constructor
    · intro rab
      use (Or.inl rab)
      rintro (rba | beqa)
      · apply irrefl_lex a
        exact trans_lex _ _ _ rab rba
      · apply irrefl_lex b
        nth_rw 1 [beqa]
        exact rab

    · rintro ⟨(rab | aeqb), h⟩
      · exact rab
      apply False.elim
      apply h
      apply Or.inr
      rw [aeqb]
  le_antisymm := by
    sorry

end Dict


end Order
