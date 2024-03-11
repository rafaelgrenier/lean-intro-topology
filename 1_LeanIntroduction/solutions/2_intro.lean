/-
# Not, And, and Or

Now that we have some basics for propositions, let's explore other ways to create new
propositions. The connective "not" (written ¬) is encoded in lean like so:
"¬P" is definitionally equal to "P → False."
Let's look at a few examples.
-/

variable (P Q R : Prop) -- This means P, Q, and R will be propositions

-- try one for yourself!

example : (P → Q) → (¬Q → ¬P) := by
  intro hPQ hnQ hP
  apply hnQ
  apply hPQ
  exact hP

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

-- now you try!

example : (P ∧ Q) → (P ∧ (P ∧ Q)) := by
  intro hPaQ
  apply And.intro
  · exact hPaQ.1
  · apply And.intro
    · exact hPaQ.1
    · exact hPaQ.2

example : R → (R ∧ R) := by
  intro hR
  apply And.intro
  · exact hR
  · exact hR

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
  intro h
  apply And.intro
  · intro hP
    apply h
    exact Or.inl hP
  · intro hQ
    apply h
    apply Or.inr
    exact hQ

example : ¬(P → Q) → (¬Q) := by
  intro h hQ
  apply h
  intro _
  exact hQ

example : (P → Q) → ¬P → ((P → Q) → Q) → Q := by
  intro hPQ hnP hPQQ
  apply hPQQ
  exact hPQ
