import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Prime
import Mathlib.Order.Bounds.Basic
/-
# Induction

Induction is the following property of the Natural numbers:
Let P : ℕ → Prop, so P is a predicate on ℕ. If P 0 is true and
for all k:ℕ, P k → P (k+1), then P is true for all of ℕ. In other words, for any
proposition that is true of the first natural number AND is true of n given that
the same proposition is true of n-1, that proposition must be true for
all natural numbers.
This ought to be somewhat intuitive; if the natural numbers
are laid out as dominoes standing upright and knocking any domino causes the next to
fall, then knocking over the first domino will cause every domino to fall.

Induction allows us to make claims about an infinite set (or type, in this case)
by proving only two finite cases: the base case that the property holds for 0,
and the "induction step" that the property for n implies the property for n+1.
-/
section ind
lemma nat_ge_zero : ∀ n : ℕ, n ≥ 0 := by
  -- We will prove this by induction
  intro n
  induction' n with n ih
  · -- Base case: `0 ≥ 0` (Note: Nat.zero is the formal way to express 0)
    apply Nat.le_refl
  -- Induction step: `n ≥ 0 → (n+1) ≥ 0` (Note: Nat.succ n = n + 1)
  apply le_trans ih
  apply Nat.le_succ

lemma one_le_two_pow_nat : ∀ n : ℕ, 1 ≤ 2 ^ n := by
  intro n
  induction' n with n ih
  · -- Base case: `1 ≤ 2 ^ 0`
    sorry
  -- Induction step : `1 ≤ 2 ^ n → 1 ≤ 2 ^ (n+1)`
  rw [Nat.pow_succ, Nat.mul_two]
  sorry

example : ∀ n : ℕ, n ≤ 2^n := by
  intro n
  induction' n with n ih
  · -- Base case: `0 ≤ 2 ^ 0`
    change 0 ≤ 1
    apply nat_ge_zero
  -- Induction step: `n ≤ 2 ^ n → n + 1 ≤ 2 ^ (n+1)`
  rw [Nat.pow_succ, Nat.succ_eq_add_one, Nat.mul_two]
  apply Nat.add_le_add
  · exact ih
  · exact one_le_two_pow_nat n

-- Try using induction to prove all Natural numbers are even or odd
def even (n : ℕ) := ∃ k, n = 2 * k
def odd (n : ℕ) := ∃ k, n = 2 * k + 1
theorem even_or_odd (n : ℕ) : (even n) ∨ (odd n) := by {
  induction' n with n ih
  · sorry
  rw [Nat.succ_eq_add_one]
  dsimp [even, odd]
  sorry
}
/- ## Strong vs. Weak Induction

The principle of induction we have introduced thus far is also known as
"weak induction," because only a proof of `P n` is supplied in the induction
step. "Strong induction" adds to the induction hypothesis that `P k` should
be true for ALL `k ≤ n + 1`.
-/
#check Nat.strong_induction_on

def well_ordered (X : Type) [Preorder X] : Prop :=
  ∀ S : Set X, S.Nonempty → ∃ m, IsLeast S m

example : well_ordered ℕ := by
  dsimp [well_ordered]
  intro S
  contrapose
  simp [Set.Nonempty]
  intro noLeastS n
  induction' n using Nat.strong_induction_on with n ih
  intro nS
  apply noLeastS n
  dsimp [IsLeast, lowerBounds]
  use nS
  intro a aS
  apply Nat.not_lt.mp
  intro altn
  apply ih a altn
  exact aS

example : ¬well_ordered ℤ := by
  dsimp [well_ordered, Set.Nonempty, IsLeast]
  push_neg
  exists Set.univ
  use ⟨0, by trivial⟩
  intro n _ nlower
  apply (by norm_num : ¬(n ≤ n-1))
  apply nlower
  trivial



end ind
