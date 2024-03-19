import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Interval

/-

# Recursive Definitions

We have already witnessed inductive types, like Nat, which are
defined in terms of themselves. In general, when an object is
defined in terms of similar objects of the same category, we
call the phenomenon a "recursive definition." The Fibonacci
sequence is famously recursively defined; to get the nth term in the
sequence, one must add the previous two terms. How can we do
this in Lean?

For a function which takes an inductive type as an input, we
can break into cases: the base case and the recursive case.
Consider a sequence of natural numbers which starts with 1, and
each successive term is defined as twice the previous term plus 1.
-/

def seq : ℕ → ℕ
| 0 => 1 -- the first term is 1
| n + 1 => 2 * seq n + 1 -- any term which has a predecessor is defined in terms of that predecessor

#eval [seq 0, seq 1, seq 2, seq 3]

/-
Lean is very cautious with recursion, since it's easy to define a function
recursively in a way that causes Lean to loop forever trying to evaluate
a term.

`def bad_seq : ℕ → ℕ`
`| 0 => 0`
`| n+1 => bad_seq (n + 2)`

To calculate `bad_seq 1`, you need `bad_seq 2`, which needs `bad_seq 3`, and so on.

let's look at an example of a recursively defined object being used
in a proof.
-/

example (n : ℕ) : 1 + seq n = 2 ^ (n+1) := by
  induction' n with n ih
  · rfl
  dsimp [seq, Nat.succ_eq_add_one]
  ring
  rw [mul_comm]
  nth_rw 1 [←mul_one 2]
  rw [←mul_add, ih, pow_add, pow_one, mul_comm, mul_assoc]
  rfl

example : ∀ n, n < seq n := by sorry

-- Here's a more complicated example

def fibb : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fibb n + fibb (n + 1) -- defined using the previous TWO terms

#eval fibb 10 -- Lean has no problem with it

open BigOperators
open Finset

example : ∀ n : ℕ, 1 + ∑ k in range (n), (fibb k) = fibb (n + 1) := by
  intro n
  induction' n with n ih
  · rfl
  rw [sum_range_succ, ←add_assoc, ih, Nat.succ_eq_add_one, add_comm]
  simp only [fibb, Nat.add_eq, add_zero]

theorem fibb_nondec_succ : ∀ n : ℕ, fibb n ≤ fibb (n + 1) := by
  intro n
  induction' n using Nat.strong_induction_on with n ihn
  /-
  What follows in this proof is called pattern-matching.
  We already used pattern matching without explicitly stating it
  in the above recursively defined sequences. Since n : ℕ and Nat is
  a type with two constructors, we can identify that any term n must
  have been constructed using one of those constructors. Lean lets us
  break our proof into cases, one for each constructor. In the case of
  `fibb`, we actually use nested constructors; each n : Nat comes from
  Nat.zero or Nat.succ (m) where m is another term of type Nat. Since m
  is also type Nat, we can consider two cases: m = Nat.zero or
  m = Nat.succ (k) where k : Nat. Thus n has three options now:
  Nat.zero, Nat.succ (Nat.zero), and Nat.succ (Nat.succ k).
  Written more comfortably, n = 0, n = 1, or n = k + 2.
  -/
  match n with
  | 0 => exact Nat.zero_le _
  | 1 => dsimp [fibb]; rfl
  | k + 2 =>
    dsimp [fibb]
    rw [add_comm, Nat.add_le_add_iff_left, add_comm]
    show fibb k ≤ fibb (k + 2)
    apply le_trans
    · apply ihn
      apply Nat.lt_add_of_pos_right
      exact Nat.succ_pos 1
    apply ihn
    exact Nat.lt.base (k + 1)

-- try proving the following theorems about the fibonacci sequence

lemma fibb_pos_of_npos : ∀ n, 0 < n → 0 < fibb n := by
  sorry

lemma fibb_lt_fibb_succ_of_ngt1 : ∀ n, 1 < n  → fibb n < fibb (n + 1) := by
  sorry

lemma fibb_increasing_after_1 : ∀ n m, 1 < n → n < m → fibb n < fibb m := by
  sorry

lemma n_lt_fibb_n_of_ngt5 : ∀ n, 5 < n → n < fibb n := by
  sorry
