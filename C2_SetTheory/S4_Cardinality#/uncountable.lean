import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

example : ¬ (Countable (Set ℕ)) := by
  intro h
  rw [countable_iff_exists_surjective] at h
  rcases h with ⟨f, hf⟩
  let S : Set ℕ := {n | n ∉ f n}
  rcases hf S with ⟨a, hfa⟩
  have : a ∉ f a := by
    intro ha
    rw [hfa] at ha
    apply ha
    rw [hfa]
    exact ha
  apply this
  rw [hfa, Set.mem_setOf_eq]
  exact this

-- We have now shown that Finset ℕ is countable, yet Set ℕ is uncountable!
