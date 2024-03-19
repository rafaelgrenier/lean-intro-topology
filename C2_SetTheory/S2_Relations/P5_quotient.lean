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

-- Now that you have the basics, let's look a worked example: the integers modulo 3.
namespace QuotientExample

def eqv (a b : ℤ) : Prop := ∃ k, a-b = 3*k --defining a relation
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
theorem eqv_def {a b : ℤ} : a ≈ b ↔ ∃ k, a-b = 3*k := by rfl

def Zmod3 := Quotient ZSetoid -- Zmod3 will be the name of our Quotient type.

-- To actually create specific elements with type `Quotient ZSetoid`, Mathlib
-- has `Quotient.mk` (and `Quotient.mk'` if you don't want to specify the Setoid).
def mod3ify : ℤ → Zmod3 := Quotient.mk ZSetoid -- just abbreviation

-- Here are a few example elements of the type Quotient ZSetoid
def zero := mod3ify 0
def one := mod3ify 1
def two := mod3ify 2

def Zmod3univ : Set Zmod3 := {zero, one, two}

/-
Once elements of the Quotient type exist , how can they be related to each other?
`Quotient.eq` is a theorem stating that
for some {X : Type}, [s : Setoid X], and {a b : X},
then `(Quotient.mk s a = Quotient.mk s b ↔ a ≈ b)`.
Both directions of the Iff are also named theorems,
where `exact` is implication to the left and `sound` to the right.

The following two examples demonstrate each direction.
-/
example : one = mod3ify 100 := by
  apply Quotient.sound
  rw [eqv_def]
  exists -33

example (n : ℤ) (h : mod3ify n = two) : ∃ k, 3*k + 2 = n := by
  let claim := Quotient.exact h
  rw [eqv_def] at claim
  rcases claim with ⟨k, hk⟩
  exists k
  rw [←hk, sub_add_cancel]

-- Now we consider how functions on ℤ can be transferred over to functions on Zmod3
def square (n : ℤ) : ℤ := n * n -- `square : ℤ → ℤ`

-- This lemma assures that `square` makes sense on Zmod3; for any two representatives
-- of the same equivalence class, their squares need to be equivalent.
lemma square_respects_eqv : ∀ ⦃a b : ℤ⦄, a ≈ b → square a ≈ square b := by
  intro a b aeqvb
  rw [eqv_def] at *
  rcases aeqvb with ⟨k, hk⟩
  dsimp [square]
  exists k*(a+b)
  rw [←mul_assoc, ←hk]
  ring

-- Next we can create a function with type `Zmod3 → Zmod3`
def squareMod3 := Quotient.map square square_respects_eqv

example : squareMod3 (two) = one := by
  dsimp [squareMod3]
  rw [two, one, mod3ify]
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

def hasSqrtMod3 (z : Zmod3) := ∃ s : Zmod3, squareMod3 s = z

example : hasSqrtMod3 (one) := by
  exists one

example : two ≠ one := by
  dsimp [two, one, mod3ify]
  rw [Quotient.eq, eqv_def]
  change ¬ 3 ∣ (2 - 1 : ℤ)
  exact of_decide_eq_false rfl

example : ¬hasSqrtMod3 (two) := by
  rintro ⟨s, hs⟩
  dsimp [squareMod3, two, mod3ify] at hs
  -- Without Quotient.exists_rep, this proof cannot continue.
  -- To decompose Quotient.map, `s` must be expressed
  -- as the equivalence class of some n : ℤ
  let ⟨n, hn⟩ := Quotient.exists_rep s
  rw [←hn, Quotient.map_mk, Quotient.eq, eqv_def] at hs
  dsimp only [square] at hs
  clear hn s
  sorry -- at this point the proof is entirely free of quotients and amounts to
        -- showing that `n*n - 2 = 3*k` has no solutions over the integers.
        -- Let's try going about this another way.

-- First we show that Zmod3univ actually encompasses all of Zmod3
-- In other words, every term of type Zmod3 is either `zero`, `one`, or `two`.
lemma Zmod3univ_legit : ∀ p : Zmod3, p ∈ Zmod3univ := by
  intro p
  simp only [Zmod3univ, zero, mod3ify, one, two, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases (Quotient.exists_rep p) with ⟨n, hn⟩
  rw [←hn, Quotient.eq, Quotient.eq, Quotient.eq]
  clear p hn
  simp [eqv_def]
  sorry /- This sorry can be resolved with induction. We will prove that
  `∀ n : ℤ, (∃ k, n = 3 * k) ∨ (∃ k, n - 1 = 3 * k) ∨ ∃ k, n - 2 = 3 * k`
  in the section on induction. -/

def square_range : Set Zmod3 := squareMod3 '' Zmod3univ

lemma sq_aux₀ : squareMod3 (zero) = zero := by
  dsimp [squareMod3, zero, mod3ify, square]
  simp only [mul_zero]

lemma sq_aux₁ : squareMod3 (one) = one := by
  sorry --exercise for the reader

lemma sq_aux₂ : squareMod3 (two) = one := by
  sorry --exercise for the reader

-- Now we show that `squareMod3` maps `Zmod3univ` to `Zmod3univ` excluding `two`:
lemma square_range_def : square_range = {zero, one} := by
  ext p
  constructor
  · intro ⟨q, qZmod3, hq⟩
    simp [Zmod3univ] at qZmod3
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff]
    rcases qZmod3 with (q0 | q1 | q2)
    · rw [q0, sq_aux₀] at hq
      exact Or.inl (Eq.symm hq)
    · rw [q1, sq_aux₁] at hq
      exact Or.inr (Eq.symm hq)
    · rw [q2, sq_aux₂] at hq
      exact Or.inr (Eq.symm hq)
  · simp only [square_range, Set.image, Zmod3univ, Set.mem_singleton_iff, Set.mem_insert_iff]
    rintro (p0 | p1)
    · exists zero
      simp only [true_or, true_and]
      rw [p0]
      rfl
    · exists one
      simp only [true_or, or_true, true_and]
      rw [p1]
      rfl

-- Now we can revisit the theorem that stalled out earlier
theorem two_not_square : ¬hasSqrtMod3 (two) := by
  dsimp [hasSqrtMod3, two, mod3ify]
  push_neg
  intro p
  let q := squareMod3 p
  have hq : q = squareMod3 p := rfl
  rw [←hq]
  have : q ∈ square_range := by
    exists p
    constructor
    apply Zmod3univ_legit
    rw [hq]
  intro h
  rw [h] at this
  have : two ∈ square_range := by
    exact this
  contrapose this
  rw [square_range_def]
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff]
  push_neg
  dsimp [zero, one, two, mod3ify]
  rw [Quotient.eq, Quotient.eq, eqv_def, eqv_def]
  change (¬ 3 ∣ (2 - 0 : ℤ)) ∧ (¬ 3 ∣ (2 - 1 : ℤ))
  constructor
  · exact of_decide_eq_false rfl
  · exact of_decide_eq_false rfl

-- And we can prove the stumbling block!
example : ∀ n k : ℤ, n * n - 2 ≠ 3 * k := by
  let claim := two_not_square
  dsimp [hasSqrtMod3, two, mod3ify] at claim
  push_neg at claim
  dsimp [squareMod3] at claim
  intro n
  let aux := claim (mod3ify n)
  simp [mod3ify, square, eqv_def] at aux
  exact aux

end QuotientExample
