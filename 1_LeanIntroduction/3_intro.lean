import Init.Classical
/-
# Classical Logic, Iff

We briefly take a foray into the differences between classical logic
and constructive logic. All of the logic we've discussed thus far has been
constructive: If you want to prove something to be true, you must
construct a proof from the axioms and other known hypotheses.
This approach to logic fails to prove some critical theorems which we
would like to know as true:
  For any P : Prop, we expect P ∨ ¬P to be true  (the law of the excluded middle)
  We would also expect ¬(¬P) → P,   (this follows from the previous axiom)
  and a variety of other propositions.

To leverage classical logic in Lean, we import the package Classical.
-/

open Classical
#check em -- short for "Excluded Middle"
section
variable (P Q R : Prop)

example : P ∨ ¬P := by
  exact em P

-- now we can prove ¬(¬P) → P

example : ¬(¬P) → P := by
  intro hnnP
  apply Or.elim (em P) -- splits proof into two cases: P true or ¬P true
  · intro hP
    exact hP
  · intro hnP
    apply False.elim
    apply hnnP
    exact hnP

-- in fact, there's a theorem from Classical for the previous example
#check byContradiction

example : ¬(¬P) → P := by
  intro hnnP
  apply byContradiction
  exact hnnP

-- since breaking a proof into two cases (P true or false) is often useful, we have
#check byCases

example : ¬(¬P) → P := by
  intro hnnP
  apply byCases
  · intro hP
    exact hP
  · intro hnP
    apply False.elim
    apply hnnP
    exact hnP



/-
Let's also take this sidebar to introduce Iff, denoted ↔ in Lean.
'P ↔ Q' means that 'P → Q' and 'Q → P'
The three elimination and introduction rules for Iff are
· Iff.intro : (P → Q) → (Q → P) → (P ↔ Q)
· Iff.mp : (P ↔ Q) → (P → Q)
· Iff.mpr : (P ↔ Q) → (Q → P)

Now that we have the excluded middle and iff, we can prove all of DeMorgan's laws
-/
example : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  apply Iff.intro
  -- proof of ¬(P ∧ Q) → (¬P ∨ ¬Q)
  · intro hnPaQ
    apply Or.elim (em P) -- using Classical logic to show P or ¬P
    · intro hP
      apply Or.inr -- choosing to prove ¬Q rather than ¬P to establish ¬P ∨ ¬Q
      intro hQ
      apply hnPaQ
      exact ⟨hP, hQ⟩
    · intro hnP
      apply Or.inl
      exact hnP
  -- proof of (¬P ∨ ¬Q) → ¬(P ∧ Q)
  · intro hnPonQ
    intro hPaQ
    apply Or.elim hnPonQ
    · intro hnP
      apply hnP
      exact hPaQ.left
    · intro hnQ
      apply hnQ
      exact hPaQ.right

example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by --classical logic isn't necessary for this one
  apply Iff.intro
  · intro h
    sorry
  · intro ⟨h₁, h₂⟩
    sorry

example : (P ↔ Q) ↔ ((P → Q) ∧ (Q → P)) := by
  sorry
end
