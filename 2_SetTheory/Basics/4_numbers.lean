/-

# Natural Numbers & Induction

The natural numbers are 0, 1, 2, and so on, continuing forever. In Lean, the
natural numbers are defined as a type called `Nat` or `ℕ`, which is defined recusively

For every element of type `ℕ`, the element is either `Nat.zero` (representing 0),
or `Nat.succ n` for some other `n : ℕ` (representing n+1). Thus `3` unfolds
to be defined as `Nat.succ (Nat.succ (Nat.succ Nat.zero))`.


-/
