/-
# Not, And, and Or

Now that we have some basics for propositions, let's explore other ways to create new
propositions. The connective "not" (written ¬) is encoded in lean like so:
"¬P" is definitionally equal to "P → False."
Let's look at a few examples.
-/

variable (P Q R : Prop) -- This means P, Q, and R will be propositions


example : P → ¬(¬P) := by
  intro hP
  intro notP -- ¬(¬P) is the same as (¬P) → False, so intro tactic gives us ¬P
  apply notP
  exact hP

example : ¬False := by
  intro h
  exact h

example : ¬True → P := by
  intro h
  apply False.elim
  apply h
  apply True.intro

-- try one for yourself!

example : (P → Q) → (¬Q → ¬P) := by
  sorry

/-
Next up in our introduction to first-order logic are "and" and "or."
Your intuition for these logical connectives gets you most of the way already,
but the introduction and elimination rules may run contrary to your expectations.

"And" is expressed as ∧ in Lean, and comes with the following intro and elim rules:
And.intro - P → Q → P ∧ Q
And.left - P ∧ Q → P     # And has two elimination rules, one for extracting each component proposition
And.right - P ∧ Q → Q

"Or" is expressed as ∨ in Lean, and comes with the following intro and elim rules:
Or.inl - P → P ∨ Q
Or.inr - Q → P ∨ Q
Or.elim - P ∨ Q → (P → R) → (Q → R) → R
  the Or.elim rule states that R only follows from P ∨ Q if R can be proven
  from each of P and Q individually.
-/

example : (P ∧ Q) → P := by
  intro hPQ
  exact And.left hPQ

example : (P ∧ Q) → (Q ∧ P) := by
  intro hPQ
  apply And.intro -- requires two hypothesis, so now there are 2 goals
  · exact And.right hPQ -- "·" notation indicates that only one of the goals is being worked towards in the subsequent block
  · exact And.left hPQ

-- this same example can be done faster with some syntatic sugar "⟨⟩"

example : (P ∧ Q) → (Q ∧ P) := by
  intro ⟨hP, hQ⟩ -- P ∧ Q is automatically broken into two hypotheses, hP : P and hQ : Q
  apply And.intro
  · exact hQ
  · exact hP

-- now you try!

example : (P ∧ Q) → (P ∧ (P ∧ Q)) := by
  sorry

example : R → (R ∧ R) := by
  sorry

-- Now let's look at "or"

example : (P ∨ Q) → (Q ∨ P) := by
  intro hPQ
  apply (Or.elim hPQ) --Or.elim is taking hPQ : P ∨ Q as an argument
  · intro hP
    apply Or.inr
    exact hP
  · intro hQ
    apply Or.inl
    exact hQ

example : False ∨ ¬False := by
  apply Or.inr
  intro hFalse
  exact hFalse

example : (¬P ∨ Q) → (P → Q) := by
  intro hnPorQ
  intro hP
  apply Or.elim hnPorQ
  · intro hnP
    apply False.elim
    apply hnP
    exact hP
  · intro hQ
    exact hQ

/-
The following exercises are left to you. More practice problems are available in both
Mathematics in Lean and Theorem Proving in Lean. These two textbooks are accessible
in the VSCode editor by typing ctrl-shift-p and selecting "Open Documentation View."
-/

example : ¬(P ∨ Q) → (¬P ∧ ¬Q) := by
  sorry

example : ¬(P → Q) → (¬Q) := by
  sorry

example : (P → Q) → ¬P → ((P → Q) → Q) → Q := by
  sorry
