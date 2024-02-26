import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-

# Finiteness

You likely have an intuitive sense of what it means to be finite;
perhaps a set is finite if you can count out elements one by one
and eventually you'll be able to stop counting. Or maybe we assume sets to
be finite unless there's some sort of condition that makes that set unlimited,
like induction for ℕ. But in mathematics, and particularly in Lean, formalizing
these notions is the name of the game.

One way that mathematicians think about finiteness has to do with sections
of the natural numbers. A section of natural numbers is the set of all
natural numbers less than "n", denoted Sₙ. We can then define a set A
to be "finite" if there exists a natural number n and a function f : Sₙ → A
such that f is bijective. For such as set A, n is "the cardinality of A".
-/
open BigOperators
open Finset

#check Multiset

def bin (S : Finset ℕ) : ℕ := ∑ k in S, 2 ^ k

def add_one_set (S : Finset ℕ) : Finset ℕ where
  val := S.1.map (λ n ↦ n + 1)
  nodup := sorry

lemma add_one_double (S : Finset ℕ) : bin (add_one_set S) = 2 * bin S := by
  dsimp [bin]
  sorry

lemma even_odd (n : ℕ) : (∃ k, n = 2 * k) ∨ ∃ k, n = 2 * k + 1 := by
  induction' n with n ih
  · apply Or.inl
    exists 0
  rcases ih with (even | ⟨k, hk⟩)
  · apply Or.inr
    simp; exact even
  · apply Or.inl
    exists k + 1
    rw [hk, Nat.succ_eq_add_one, mul_add]



example : Function.Surjective bin := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => exists ∅
  | 1 => exists {0}
  | k + 2 =>
    have : (k / 2) + 1 < k + 2 := sorry
    rcases ih (k/2 + 1) this with ⟨S, hS⟩
    rcases even_odd (k) with (⟨j, hj⟩ | ⟨j, hj⟩)
    · rw [hj] at hS ⊢
      simp at hS
      exists add_one_set S
      rw [add_one_double, hS, mul_add]
    · rw [hj] at hS ⊢
      rw [add_comm (2*j), Nat.add_mul_div_left] at hS
      exists insert 0 (add_one_set S)
      dsimp [bin]
      rw [sum_insert]
      change 2 ^ 0 + bin (add_one_set S) = 2 * j + 1 + 2
      rw [add_one_double, hS]
      ring
      · sorry
      norm_num
