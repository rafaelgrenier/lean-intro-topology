/-

# Inductive Types and Recursion

Please read Chapter 5 section 2 from Mathematics in Lean! This chapter
introduces induction and inductive types.

-/
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Interval


open BigOperators
open Finset

-- You now have the tools to prove the theorem from the section on quotients!
-- Try proving the following theorem, which is a slightly simplified version.
theorem nats_div_3_classes : ∀ n : ℕ,
(∃ k, n = 3 * k) ∨ (∃ k, n = 1 + 3 * k) ∨ ∃ k, n = 2 + 3 * k := by
  sorry

/-
This next theorem is the exact theorem from the quotient section. To solve this,
we do need to make note of one more detail:
the integers are not the natural numbers!
So how can we use induction? The integers are defined as an Inductive Type in
Lean, with two constructors: ofNat : (Nat → Int) which is the straightforward
inclusion map and negSucc : (Nat → Int) which maps an natural number `n` to
the integer `-(n+1)`. Since Integers are an inductive type in Lean, we can
use the `induction` tactic to break any claim about integers into cases:
one for each constructor.

When using `induction` (not `induction'`), the syntax goes like follows:
-/

inductive myType
| cons₁ : myType
| cons₂ (t : myType) : myType
| cons₃ (n : Nat) : myType

def somePredicate : myType → Prop := by
  intro t
  induction t with
  | cons₁ => sorry
  | cons₂ t ih => sorry
  | cons₃ n => sorry
-- These `sorry`s are not meant to be filled in as an exercise, just to draw
-- attention to the rest of the syntax.

theorem integers_div_3_classes :
∀ n : ℤ, (∃ k, n = 3 * k) ∨ (∃ k, n - 1 = 3 * k) ∨ ∃ k, n - 2 = 3 * k := by
  intro n
  induction n with --Now let's use that ℤ is an inductive type
  | ofNat n =>
    -- first constructor
    rcases nats_div_3_classes n with (⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩)
    · apply Or.inl
      exists Int.ofNat k
      rw [hk]
      simp
    · apply Or.inr; apply Or.inl
      exists Int.ofNat k
      rw [hk]
      simp
    · apply Or.inr; apply Or.inr
      exists Int.ofNat k
      rw [hk]
      simp
  | negSucc n =>
    -- second constructor
    simp [Int.negSucc_coe']
    induction' n with n ih -- Now we're doing typical induction on ℕ
    · apply Or.inr; apply Or.inr;
      exists -1
    rcases ih with (⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩)
    · apply Or.inr; apply Or.inr
      exists (k-1)
      rw [mul_sub, ←hk, Nat.succ_eq_add_one]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    · apply Or.inl
      exists k
      rw [←add_neg_eq_zero] at hk
      ring_nf at hk
      rw [←zero_add 1, ←hk]
      simp
      ring
    · apply Or.inr; apply Or.inl
      exists k
      simp
      rw [←hk]
      ring

def sum_nats_le : ℕ → ℕ := λ n ↦ ∑ k in range (n + 1), k
def sum_cubes_le : ℕ → ℕ := λ n ↦ ∑ k in range (n + 1), k^3
#eval sum_nats_le 5
#eval sum_cubes_le 5
-- note that (sum_nats_le 5) ^ 2 = sum_cubes_le 5
#eval (sum_nats_le 13) ^ 2
#eval sum_cubes_le 13
-- let's prove this pattern to hold for all n
example (n : ℕ) : (sum_nats_le n)^2 = sum_cubes_le n := by
  sorry
