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
  intro n
  induction' n with n ih
  · apply Or.inl
    exists 0
  rcases ih with (⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩)
  · apply Or.inr (Or.inl _)
    exists k
    rw [hk, Nat.succ_eq_add_one, add_comm]
  · apply Or.inr (Or.inr _)
    exists k
    rw [hk, Nat.succ_eq_add_one]
    ring
  · apply Or.inl
    exists k + 1
    rw [hk, Nat.succ_eq_add_one]
    ring

def sum_nats_le : ℕ → ℕ := λ n ↦ ∑ k in range (n + 1), k
def sum_cubes_le : ℕ → ℕ := λ n ↦ ∑ k in range (n + 1), k^3

-- let's prove this pattern to hold for all n
example (n : ℕ) : (sum_nats_le n)^2 = sum_cubes_le n := by
  induction' n with n ih
  · simp only
  dsimp [sum_nats_le, sum_cubes_le] at *
  rw [sum_range_succ]
  rw [sum_range_succ _ (Nat.succ n), Nat.succ_eq_add_one]
  rw [←ih]
  clear ih
  rw [add_pow_two, add_assoc, Nat.add_left_cancel_iff, pow_two, ←add_mul]
  rw [pow_three, mul_comm]
  congr 1
  induction' n with n ih
  · simp only
  simp [Nat.succ_eq_add_one]
  rw [sum_range_succ, mul_add, two_mul (n + 1), ←add_assoc _ (n+1) (n+1), ih]
  ring

example : ∀ n : ℕ, 6 ∣ (2 * n ^ 3 + 3 * n ^ 2 + n) := by
  intro n
  induction' n with n ih
  · simp only
  simp [Nat.succ_eq_add_one]
  ring_nf at *
  rcases ih with ⟨k, hk⟩
  exists (1 + 2*n + n^2 + k)
  rw [mul_add, ←hk]
  ring
