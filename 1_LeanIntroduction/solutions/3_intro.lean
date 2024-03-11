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

example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by --classical logic isn't necessary for this one
  apply Iff.intro
  · intro h
    apply And.intro
    · intro hP
      apply h
      exact Or.inl hP
    · intro hQ
      apply h
      exact Or.inr hQ
  · intro ⟨h₁, h₂⟩ hPoQ
    apply Or.elim hPoQ
    · exact h₁
    · exact h₂

example : (P ↔ Q) ↔ ((P → Q) ∧ (Q → P)) := by
  apply Iff.intro
  · intro hPQ
    apply And.intro
    · exact hPQ.mp
    · exact hPQ.mpr
  · intro ⟨hPQ, hQP⟩
    apply Iff.intro
    · exact hPQ
    · exact hQP
end
