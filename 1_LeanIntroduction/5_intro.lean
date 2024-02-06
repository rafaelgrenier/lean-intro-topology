import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Basic
/-
# Logical Quantifiers, ∃ and ∀
-- MIL has an excellent introduction to these quantifier in its 3rd chapter.

To introduce these quantifiers, first we need to briefly discuss types.

In Lean, every expression has some type. In the previous examples, P, Q, R,
True, and False had the type Prop. Lean has some built-in types like Nat for the
Natural numbers and Real (ℝ) for the Real numbers.

The quantifier ∃ means 'there exists,' so an expression like
∃ x : ℝ, x = 0 means that 'there exists an x with type ℝ such that x = 0.'
The quantifier ∀ means 'for all' or 'for every,' so an expression like
∀ n : Nat, n ≥ 0 means 'for all n with type Nat, n is at least 0.'

The Universal Quantifier ∀ functions like an implication, so the statement
'∀ n : Nat, n ≥ 0' can be thought of 'n being of type Nat' → n ≥ 0. Thus the
intro tactic can be used as the introduction rule for a ∀ statement, and the
elimination rule is the same as for →, which is treating the ∀ statement as
a function. This is best illustrated as an example: -/

example : ∀ n : Nat, n ≥ 0 := by
  intro v
  -- now I have 'v' as an arbitrary Nat object in my proof and my goal is '⊢ v ≥ 0'
  apply Nat.zero_le -- this is a theorem stating all Nat's are at least 0

-- another example

example : ∀ P : Prop, ¬(P ∧ ¬P) := by
  intro P
  intro hP
  apply hP.right
  exact hP.left

example (h : ∀ n : Nat, n ≤ n + 1) : 0 ≤ 1 := by -- here we will use a ∀ statement
  let aux := h 0 -- the 'let' tactic introduces new hypotheses with explicit names
  -- now 'aux' is the hypothesis that 0 ≤ 0 + 1
  -- Lean is smart enough to figure out that 0 + 1 is equivalent to 1, so we have
  -- our conclusion already!
  exact aux

example: ∀ P Q : Prop, ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  sorry

example (Q R : Prop) (h : ∀ P : Prop, P → Q) (hR : R) : Q := by
  sorry

/-
The Existential Quantifier ∃ can be thought of as a pair, both the object
which is claimed to exists and the property hypothesized to that object.
So '∃ x : ℝ, x = 0' is the claim that there is some x with type ℝ, and that
x has the property that x = 0. Thus the introduction rule for Exists is
Exists.intro {α : Type} {p : α → Prop} (w : α) (h : p w) : (∃ x : α, p x).
  - Here {p : α → Prop} means that p is something called a "predicate," which
    is a function which takes some object of a given type to a Proposition. One
    example of a predicate might be "is_positive" on the type ℝ, since expressions
    of type ℝ are either positive or not, so we would expect
    is_positive 5 to evaluate as True and is_positive -12 to evaluate as False.
Now that we know how to prove an existential claim, let's discuss what to do with
such a claim as a hypothesis. The elimination rule for Exists is
Exists.elim {α : Type} {p : α → Prop} (h₁ : ∃ x : α, p x) (h₂ : ∀ (a : α), p a → b) : b.
In other words, if you have a proof that some x : α satisfies p x and a proof that
any x satisfying p x implies b, then b is implied.
-/
#check Exists.intro
#check Exists.elim

example : ∃ n : Nat, n = (0 : Nat) := by
  apply Exists.intro 0
  rfl

#check Nat.lt_irrefl
example : ¬ ∃ a : Nat, ∀ b : Nat, b < a := by
  intro h'
  apply Exists.elim h'
  intro a ha
  apply Nat.lt_irrefl a
  apply ha

example : ∀ a : Nat, ∃ b : Nat, a < b := by
  sorry

example (α : Type) (p : α → Prop) : (¬ ∃ a : α, p a) ↔ ∀ a : α, ¬ p a := by
  apply Iff.intro
  · sorry
  · sorry

-- Let's do a proof from Real Analysis!

def continuous (f : ℝ → ℝ) : Prop :=
  ∀ x₀ : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, abs (x - x₀) < δ → abs (f x - f x₀) < ε

theorem cont_const (c : ℝ) : continuous (λ x ↦ c) := by
  intro x₀ ε εpos
  apply Exists.intro ε
  apply And.intro εpos
  intro x _
  rw [sub_self, abs_zero]
  exact εpos

-- This lemma will be useful for `cont_double`
lemma double_thru_abs (a b c : ℝ) (h : |a - b| < c / 2) : |2*a - 2*b| < c := by
  rw [←mul_sub, abs_mul, abs_two]
  rw [lt_div_iff'] at h
  · exact h
  · exact two_pos

theorem cont_double {f : ℝ → ℝ} (fcont : continuous f) : continuous (λ x ↦ 2 * f x) := by
  intro x₀ ε εpos
  dsimp
  have half_ε_pos : ε / 2 > 0 := half_pos εpos
  let hf := fcont x₀ (ε/2) half_ε_pos
  -- you will need to break down the `∃` in `hf`
  sorry

theorem cont_add {f g : ℝ → ℝ} (fcont : continuous f) (gcont : continuous g) :
  continuous (λ x ↦ f x + g x) := by
  intro x₀ ε epos
  dsimp
  have half_ε_pos : ε / 2 > 0 := half_pos epos
  let hf := fcont x₀ (ε/2) half_ε_pos
  apply Exists.elim hf
  intro δ₁ ⟨δ₁pos, h₁⟩
  let hg := gcont x₀ (ε/2) half_ε_pos
  apply Exists.elim hg
  intro δ₂ ⟨δ₂pos, h₂⟩
  apply Exists.intro (min δ₁ δ₂)
  apply And.intro
  · apply lt_min δ₁pos δ₂pos
  · intro x xltmin
    calc
      |f x + g x - (f x₀ + g x₀)| ≤ |(f x - f x₀) + (g x - g x₀)| := by ring_nf; apply le_refl
      _                           ≤ |f x - f x₀| + |g x - g x₀|   := abs_add (f x - f x₀) (g x - g x₀)
      _                           < ε / 2 + |g x - g x₀|          := add_lt_add_right (h₁ x (lt_of_lt_of_le xltmin (min_le_left δ₁ δ₂))) _
      _                           < ε / 2 + ε / 2                 := add_lt_add_left (h₂ x (lt_of_lt_of_le xltmin (min_le_right δ₁ δ₂))) _
      _                           ≤ ε                             := by rw [add_halves]
