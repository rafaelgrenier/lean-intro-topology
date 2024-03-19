import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Real.Basic
/-

# Natural and Real Numbers

The natural numbers are 0, 1, 2, and so on, continuing forever. In Lean, the
natural numbers are defined as a type called `Nat` or `ℕ`, which is defined recusively

For every term of type `ℕ`, the term is either `Nat.zero` (representing 0),
or `Nat.succ n` for some other `n : ℕ` (representing n+1). Thus `3` unfolds
to be defined as `Nat.succ (Nat.succ (Nat.succ Nat.zero))`.

The natural numbers have the defined binary operations of addition and multiplication,
plus modified versions of subtraction (a - b = 0 if a < b) and division (a / b = c,
where c is the largest natural number satisfying b*c ≤ a, or b = c = 0).

Subtraction can be made a true inverse of addition by extending the natural
numbers to the integers, denoted `ℤ` or `Int` in Lean. Division can also
be made a true inverse to multiplication by extending the integers to the
rational numbers, denoted `Rat` or `ℚ` in Lean.

The real numbers, denoted `Real` or `ℝ` in Lean, complete the rationals.

All of these familiar sets of numbers are instead Types in Lean.
-/

#check 4
#check (4 : ℤ)
#eval 9 + 10
#eval 16 * 5
#eval 7 - 13 -- Subtraction is defined on ℕ so that negative numbers are avoided
#eval 22 / 7 -- The same goes for division
#eval (7 : ℤ) - 13 -- Now that Lean knows 7 is meant to be an Integer, Lean assumes integer subtraction
#eval 22 / (7 : ℚ)

#check lt_trans
#check le_trans
#check lt_of_lt_of_le
#check lt_of_le_of_lt

example {a b c d : ℝ} (aleb : a ≤ b) (bltc : b < c) (cled : c ≤ d) : a < d := by
  apply lt_of_le_of_lt aleb
  apply lt_of_lt_of_le bltc
  exact cled
