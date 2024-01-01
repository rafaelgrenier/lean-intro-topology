/-

# Induction

-/
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Interval

open BigOperators
open Finset

theorem named : ∀ n : Nat, n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
  intro n
  induction n with
  | zero => apply Or.inl; simp
  | succ n ih =>
    rcases ih with (h | h | h | h | h)
    · apply Or.inr; apply Or.inl
      show (n + 1) % 5 = 1
      rw [←Nat.mod_add_mod, h]
      simp
    · apply Or.inr; apply Or.inr; apply Or.inl
      show (n + 1) % 5 = 2
      rw [←Nat.mod_add_mod, h]
      simp
    · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
      show (n + 1) % 5 = 3
      rw [←Nat.mod_add_mod, h]
      simp
    · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      show (n + 1) % 5 = 4
      rw [←Nat.mod_add_mod, h]
      simp
    · apply Or.inl
      show (n + 1) % 5 = 0
      rw [←Nat.mod_add_mod, h]
      simp


lemma helper : ∀ {n : Nat}, 2 ∣ n * (n+1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    let ⟨k, hk⟩ := ih
    exists (n + k + 1)
    rw [((by rfl) : Nat.succ n = n + 1)]
    ring
    rw [mul_comm k, ←hk]
    ring



example (n : ℕ) : ∑ k in range (n + 1), k = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    suffices : ∑ k in (insert (n + 1) (range (n+1))), k = (n + 1) * (n + 2) / 2
    have aux : (insert (n + 1) (range (n+1))) = range (n+2) := by
      ext x
      rw [mem_insert, mem_range, mem_range]
      constructor
      · intro h
        rw [Nat.lt_succ]
        apply le_of_eq_or_lt h
      · rw [Nat.lt_succ]
        exact eq_or_lt_of_le
    rw [aux] at this
    exact this
    rw [Finset.sum_insert, ih]
    apply Eq.symm
    rw [Nat.div_eq_iff_eq_mul_left (by norm_num : 0 < 2) (?_ : 2 ∣ (n+1) * (n+2))]
    ring
    rw [Nat.div_mul_cancel (?_ : 2 ∣ (n + n^2))]
    ring
    · rw [(by ring : n + n ^ 2 = n * (n+1))]
      apply helper
    · apply helper
    rw [mem_range]
    exact Nat.lt_irrefl (n + 1)
