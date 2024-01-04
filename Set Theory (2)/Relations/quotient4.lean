import Mathlib.Data.Set.Basic
import Mathlib.Tactic
/-

# Quotients

Mathlib has two types of Quotients: `Quot` and `Quotient`. For any Type α, and
any relation `r : α → α → Prop`, `Quot r` is a new type. `Quotient` is built on top
of Quot and requires that the relation is an equivalence relation. Quotients that
use the equivalence relation demonstrate nicer properties and are better studied, so
we will focus our attention on `Quotient` rather than `Quot`.

Since Quotients require equivalence relations, the typeclass Setoid exists to bundle
together the relation and the proof that it's an equivalence relation.
-/
example (X : Type) : Setoid X where
  r := λ x y ↦ x = y -- this is a very simple relation
  iseqv := eq_equivalence -- which is already proven in Mathlib to be an equivalence

--Quotient then takes the Setoid instance as an argument to define a new type
def QType (X : Type) (inst : Setoid X) := Quotient inst

-- Now that you have the basics, let's look a worked example: ℤ₅
namespace QuotientExample

def eqv (a b : ℤ) : Prop := ∃ k, a-b = 5*k --defining a relation
theorem iseqv : Equivalence eqv where --proving it's an equivalence
  refl := by
    intro x
    exists 0
    simp only [sub_self, mul_zero]
  symm := by
    dsimp [eqv]
    sorry --left as an exercise to the reader
  trans := by
    rintro x y z ⟨k, hk⟩ ⟨l, hl⟩
    exists (k+l)
    rw [mul_add, ←hl, ←hk, sub_add_sub_cancel]

-- It's possible to pack the above definition and theorem into the Setoid instance
-- instead of declaring them first (as is done in the first example), but this method
-- is arguably more readable.
instance ZSetoid : Setoid ℤ where
  r := eqv
  iseqv := iseqv
-- A Setoid instance gives meaning to `≈` as the provided equivlance relation.

-- eqv_def is a QoL theorem, allowing the tactic `rw` to break down `≈` quickly.
theorem eqv_def {a b : ℤ} : a ≈ b ↔ ∃ k, a-b = 5*k := by rfl

def Zmod5 := Quotient ZSetoid -- Zmod5 will be the name of our Quotient type.

-- To actually create specific elements with type `Quotient ZSetoid`, Mathlib
-- has `Quotient.mk` (and `Quotient.mk'` if you don't want to specify the Setoid).
def mod5ify : ℤ → Zmod5 := Quotient.mk ZSetoid -- just abbreviation

-- Here are a few example elements of the type ZSetoid
def zero := mod5ify 0
def one := mod5ify 1
def two := mod5ify 2
def three := mod5ify 3
def four := mod5ify 4
def Zmod5univ : Set Zmod5 := {zero, one, two, three, four}

/-
Once elements of the Quotient type exist, how can they be related to each other?
Quotient.eq is a theorem stating that for some {X : Type}, [s : Setoid X], and {a b : X},
then `(Quotient.mk s a = Quotient.mk s b ↔ a ≈ b)`. Both directions of the Iff are also
named theorems, where `exact` is implication to the left and `sound` to the right.

The following two examples demonstrate each direction.
-/
example : zero = mod5ify 100 := by
  apply Quotient.sound
  rw [eqv_def]
  exists -20

example (n : ℤ) (h : mod5ify n = three) : ∃ k, 5*k + 3 = n := by
  let claim := Quotient.exact h
  rw [eqv_def] at claim
  rcases claim with ⟨k, hk⟩
  exists k
  rw [←hk, sub_add_cancel]

-- Now we consider how functions on ℤ can be transferred over to functions on Zmod5
def square (n : ℤ) : ℤ := n * n -- `square : ℤ → ℤ`

-- This lemma assures that `square` makes sense on Zmod5; for any two representatives
-- of the same equivalence class, their squares need to be equivalent.
lemma square_respects_eqv : ∀ ⦃a b : ℤ⦄, a ≈ b → square a ≈ square b := by
  intro a b aeqvb
  rw [eqv_def] at *
  rcases aeqvb with ⟨k, hk⟩
  dsimp [square]
  exists k*(a+b)
  rw [←mul_assoc, ←hk]
  ring

-- Now we can create a function with type `Zmod5 → Zmod5`
def squareMod5 := Quotient.map square square_respects_eqv

example : squareMod5 (three) = four := by
  dsimp [squareMod5]
  rw [three, four, mod5ify]
  simp only [Quotient.map_mk] -- `Quotient.map_mk` decomposes `Quotient.map`
  apply Quotient.sound
  rw [eqv_def]
  exists 1

/-
There are a slew of theorems which adapt functions involving the base type X to
functions involving the quotient type. Each one is suited to a slightly different
situation. For the following explanations, assume X : Type, s : Setoid X, and Q : Quotient s.
· `Quotient.lift`
  For a function (f : X → α) and a hypothesis (h : ∀ x y, x ≈ y → f x = f y),
  `Quotient.lift f h` has type Q → α.
  Then `Quotient.lift_mk` asserts `Quotient.lift f h (Quotient.mk s x) = f x`.
· `Quotient.map`
  For a function (f : X → X) and a hypothesis (h : ∀ x y, x ≈ y → f x ≈ f y),
  `Quotient.map f h` has type Q → Q.
  Then `Quotient.map_mk` asserts `Quotient.lift f h (Quotient.mk s x) = Quotient.mk s (f x)`.
· `Quotient.lift₂` is analogous to .lift, but instead takes functions with two arguments.
· `Quotient.map₂` is analogous to .map, but instead takes functions with two arguments.

The last part of this section involves `Quotient.exists_rep`, a powerful theorem stating
that all elements of the quotient type are made from some element in the base type.
-/
#check Quotient.exists_rep

def hasSqrtMod5 (z : Zmod5) := ∃ s : Zmod5, squareMod5 s = z

example : hasSqrtMod5 (four) := by
  exists two

example : ¬hasSqrtMod5 (two) := by
  rintro ⟨s, hs⟩
  dsimp [squareMod5, two, mod5ify] at hs
  -- Without Quotient.exists_rep, this proof cannot continue.
  -- To decompose Quotient.map, `s` must be expressed
  -- as the equivalence class of some n : ℤ
  let ⟨n, hn⟩ := Quotient.exists_rep s
  rw [←hn, Quotient.map_mk, Quotient.eq, eqv_def] at hs
  dsimp only [square] at hs
  clear hn s
  sorry -- at this point the proof is entirely free of quotients and amounts to
        -- showing that `n*n - 2 = 5*k` has no solutions over the integers.

end QuotientExample
