import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Interval

def seq : ℕ → ℕ
| 0 => 1
| n + 1 => 2 * seq n + 1

#eval seq 3

example (n : ℕ) : 1 + seq n = 2 ^ (n+1) := by
  induction' n with n ih
  · rfl
  dsimp [seq, Nat.succ_eq_add_one]
  ring
  have : 2 + seq n * 2 = 2 * (1 + seq n) := by
    ring
  rw [this, ih]
  ring

def fibb : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fibb n + fibb (n + 1)

#eval fibb 10

open BigOperators
open Finset

example : ∀ n : ℕ, 1 + ∑ k in range (n), (fibb k) = fibb (n + 1) := by
  intro n
  induction' n with n ih
  · rfl
  rw [sum_range_succ, ←add_assoc, ih, Nat.succ_eq_add_one, add_comm]
  simp only [fibb, Nat.add_eq, add_zero]

example : ∀ n : ℕ, 12 ≤ n → ∃ k l : ℕ, n = 4 * k + 5 * l := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro nge12
  let m := n - 12
  have hm : n-12 = m := rfl
  have : n = m + 12 := by
    rw [←hm, Nat.sub_add_cancel nge12]
  rw [this]
  match m with
  | 0 => exists 3, 0
  | 1 => exists 2, 1
  | 2 => exists 1, 2
  | 3 => exists 0, 3
  | m + 4 =>
    have h₁ : m + 12 < n := by
      rw [this]
      apply Nat.add_lt_add_right
      apply Nat.lt_add_of_pos_right
      simp only
    have h₂ : 12 ≤ m + 12 := Nat.le_add_left 12 m
    rcases ih (m+12) h₁ h₂ with ⟨k, l, hkl⟩
    exists k+1, l
    rw [Nat.add_right_comm, hkl]
    ring

example : ∀ n : ℕ, ∃ j k : ℕ, n + 24 = 5 * j + 7 * k := by
  intro n
  induction' n using Nat.strong_induction_on with n ihn
  match n with
  | 0 => exists 2, 2
  | 1 => exists 5, 0
  | 2 => exists 1, 3
  | 3 => exists 4, 1
  | 4 => exists 0, 4
  | n + 5 =>
    have h₁ : n < n + 5 := sorry
    rcases ihn n h₁ with ⟨j, k, hjk⟩
    exists j + 1, k
    rw [add_right_comm, hjk]
    ring
