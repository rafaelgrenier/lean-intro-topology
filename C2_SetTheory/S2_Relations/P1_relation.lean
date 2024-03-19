import Mathlib.Data.Set.Basic
import Mathlib.Tactic.NormNum
/-

# Relations and Typeclasses

In Type theory, a relation on a type α is a function r : α → α → Prop.
From this bare definition, there are lots of properties in a relation
one might investigate: transitivity, symmetry, reflexivity, totality, etc.

This multiplicity of properties and the interesting math that follows from their
interactions actually poses a problem to formalization. If some theorem follows from
a relation having 10 such properties, should each property be individually passed as
a hypothesis? If so, ring theory and field theory will be nightmares to formalize.
So what if instead these combinations of properties are packaged together into a
single hypothesis?

Lean has "structures" and "typeclasses" to solve this problem. A structure is
just a bundle of types, and a typeclass is a bundle of types which can be passed
implicitly as a parameter.
-/

section relation_struct
variable {α : Type}

def reflexive (r : α → α → Prop) := ∀ x, r x x

def symmetric (r : α → α → Prop) := ∀ x y, r x y → r y x

def transitive (r : α → α → Prop) := ∀ x y z, r x y → r y z → r x z

/- Here's the typical syntax:
structure name_of_structure (term : type) : type where
  term1 : type
  term2 : type
  .
  .
  .
-/
structure refl_and_trans (r : α → α → Prop) : Prop where
  refl : reflexive r
  trans : transitive r

-- Let's consider an example
def sseq : Set α → Set α → Prop := λ S T ↦ S ⊆ T

lemma refl_sseq : reflexive (@sseq α) := by
  intro S x xS
  exact xS

/- And here's the typical way to construct a term with the of the structure type
example : name_of_structure (arg_term1) (arg_term2) where
  term1 := sorry
  term2 := sorry
  .
  .
  .
-/
example : refl_and_trans (@sseq α) := sorry--placing the cursor after `sorry`
-- should prompt VSCode to show a blue lightbulb icon at the beginning of the
-- line. Selecting that icon and choosing "Generate a skeleton ..." will
-- automatically build all the fields of the structure.

example : refl_and_trans (@sseq α) where
  refl := refl_sseq
  trans := by
    intro S T U hST hTU x xS
    apply hTU
    apply hST
    exact xS

def total (r : α → α → Prop) := ∀ x y, r x y ∨ r y x

def irreflexive (r : α → α → Prop) := ∀ x, ¬ r x x

def antisymmetric (r : α → α → Prop) := ∀ x y, r x y → ¬(r y x)

-- Another example
def divides : ℕ → ℕ → Prop := λ a b ↦ ∃ k, b = a*k

example : reflexive divides := by
  intro x
  exists 1
  simp only [Nat.mul_one]

example : ¬ antisymmetric divides := by
  dsimp [antisymmetric, divides]
  push_neg
  exists 12, 12
  constructor
  exists 1
  exists 1

example : transitive divides ∨ ¬ transitive divides := by
  sorry --prove this without using the excluded middle.

-- Try to come up with a relation which is reflexive and symmetric,
-- but not transitive
def your_relation : ℤ → ℤ → Prop := λ a b ↦ sorry
structure rsnt (r : α → α → Prop) : Prop where
  refl : reflexive r
  symm : symmetric r
  intrans : ¬ transitive r
example : rsnt your_relation := sorry

end relation_struct

namespace typeclass
/-
## Section on Typeclasses
Typeclasses are very similar to structures, but are typically used to make
assertions about qualities a Type might have. To create a new typeclass, the
exact same syntax is used as for creating a structure, except the
`structure` keyword is replaced with `class`. When actually constructing
an instance of the typeclass, you use the keyword `instance`, which can
either be followed by name for the instance or can be left blank. Lean can
allow for these unnamed instances because of Typeclass Inference, where Lean
keeps a record of the most recently defined instance of each typeclass and uses
that instance. This is best seen through an example:
-/
class Relation (X : Type) : Type where
  r : X → X → Prop

instance : Relation ℕ where
  r := λ a b ↦ a < b

#check Relation.r -- Without supplying any arguments, Lean doesn't assume the particular instance
#check Relation.r 3 -- Now Lean knows to use the recent instance
#check Relation.r 3 4

example : Relation.r 3 4 := by
  dsimp [Relation.r]
  norm_num

-- Typeclasses can also be used as hypotheses, and pre-existing typeclasses like
-- `Mul` and `LE` let the common notation `*` and `≤` be used in place of
-- the longer expressions `Mul.mul` and `LE.le`.
def square {X : Type} [Mul X] (x : X) : X := x * x --bracket [] notation is used for implicit instances

#eval square 5 = Mul.mul 5 5

-- Somewhere within Lean, there is an instance of Mul Nat, so `square 5` can automatically be evaluated
#eval square 5
-- Of course, we can overwrite that instance
instance : Mul Nat where
  mul := λ a b ↦ a -- Now multiplication on the type Nat just returns the first argument

#eval Mul.mul 4 7
#eval 3 * 2
#eval square 120

end typeclass
