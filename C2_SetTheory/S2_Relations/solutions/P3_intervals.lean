import Mathlib.Data.Set.Basic
/-
# Intervals and Successors
-/

def openInterval {X : Type} [Preorder X] (a b : X) : Set X := {x | a < x ∧ x < b}
def closedInterval {X : Type} [Preorder X] (a b : X) : Set X := {x | a ≤ x ∧ x ≤ b}
/- Mathlib.Data.Set.Intervals.Basic covers all the common intervals
There are nine options, but one of them is trivial
The general interval is {x | L a x ∧ U x b} where L and U are relations,
either <, ≤, or the "always-true" relation. Here's a table for what
permutations of L and U are called, both in mathematics and in Mathlib:

L↓ U→ |            <            |            ≤            |      true       |
  <   |    open interval, Ioo   | half-open interval, Ioc |  open ray, Ioi  |
  ≤   | half-open interval, Ico |   closed interval, Icc  | closed ray, Ici |
 true |      open ray, Iio      |     closed ray, Iic     | --------------- |

-/

-- The 'successor' to some element in an ordered set is the next largest element
def isSuccessorTo {X : Type} [Preorder X] (a b : X) : Prop :=
  b < a ∧ openInterval b a = ∅
-- And the 'predecessor' is the next smallest
def isPredecessorTo {X : Type} [Preorder X] (a b : X) : Prop :=
  a < b ∧ openInterval a b = ∅

example : ¬isPredecessorTo 13 42 := by
  dsimp [isPredecessorTo, openInterval]
  rw [Set.eq_empty_iff_forall_not_mem]
  push_neg
  intro
  exists 27

-- Let's combine lexicographic order with our newly defined notion of
-- succession to produce a more interesting case
def rel : ℕ × ℕ → ℕ × ℕ → Prop := Prod.Lex Nat.lt Nat.lt
-- Since isPredecessorTo is defined with `Preorder X`, we need to
-- construct a `Preorder ℕ × ℕ` instance using the above relation
instance : Preorder (ℕ × ℕ) where
  le := λ p q ↦ p = q ∨ rel p q
  lt := rel
  le_refl := by
    intro
    apply Or.inl
    rfl
  le_trans := by
    rintro a b c (aeqb | rab) (beqc | rbc)
    · apply Or.inl
      rw [aeqb, beqc]
    · apply Or.inr
      rwa [aeqb]
    · apply Or.inr
      rwa [←beqc]
    · apply Or.inr
      dsimp [rel] at *
      simp [Prod.lex_def] at *
      rcases And.intro rab rbc with ⟨(a1b1 | ⟨hab, a2b2⟩), (b1c1 | ⟨hbc, b2c2⟩)⟩
      · apply Or.inl
        apply lt_trans a1b1 b1c1
      · apply Or.inl
        rwa [←hbc]
      · apply Or.inl
        rwa [hab]
      · apply Or.inr
        rw [hab, hbc]
        use rfl
        apply lt_trans a2b2 b2c2
  lt_iff_le_not_le := by
    rintro ⟨a, b⟩ ⟨c, d⟩
    dsimp [LT.lt, rel]
    simp [Prod.lex_def]
    push_neg
    apply Iff.intro
    · rintro (altc | ⟨hac, bltd⟩)
      · refine ⟨Or.inr (Or.inl altc), λ hca _ ↦ ?_, le_of_lt altc, λ hca ↦ ?_⟩
        · apply lt_irrefl c
          apply lt_of_le_of_lt _ altc
          rw [hca]
        · apply False.elim
          apply lt_irrefl c
          apply lt_of_le_of_lt _ altc
          rw [hca]
      · simp [hac]
        refine ⟨Or.inr bltd, λ hdb ↦ lt_irrefl b ?_, le_of_lt bltd⟩
        apply lt_of_lt_of_le bltd
        rw [hdb]
    · rintro ⟨(⟨hac, hbd⟩ | altc | ⟨hac, bltd⟩), hcaimp, alec, h⟩
      · apply False.elim
        apply hcaimp
        · rw [hac]
        · rw [hbd]
      · apply Or.inl altc
      · apply Or.inr
        use hac
lemma lt_def {p q : ℕ × ℕ} : p < q ↔ p.fst < q.fst ∨ p.fst = q.fst ∧ p.snd < q.snd := by
  rw [←Prod.lex_def]
  dsimp [LT.lt, rel]
  rfl

example : ¬ ∃ p : ℕ × ℕ, isPredecessorTo p (1,0) := by
  intro ⟨⟨a, b⟩, h⟩
  dsimp [isPredecessorTo, openInterval] at h
  rw [lt_def, Set.eq_empty_iff_forall_not_mem] at h
  dsimp at h
  rcases h with ⟨(alt1 | ⟨_, bneg⟩), h⟩
  · apply h (a, b+1)
    constructor
    · rw [lt_def]
      simp
    · rw [lt_def]
      dsimp
      exact Or.inl alt1
  · apply lt_irrefl 0
    apply lt_of_le_of_lt _ bneg
    exact Nat.zero_le b

-- For one final exercise, we will show that the intersection of two open intervals
-- is still an open interval, if certain conditions about the intervals are met.

example {X : Type} [Preorder X] (a b c d : X) (altc : a < c) (bltd : b < d) :
  openInterval c b = openInterval a b ∩ openInterval c d := by
  dsimp [openInterval]
  ext x
  simp [Set.mem_inter]
  constructor
  · rintro ⟨cltx, xltb⟩
    exact ⟨⟨lt_trans altc cltx, xltb⟩, ⟨cltx, lt_trans xltb bltd⟩⟩
  · rintro ⟨⟨_, xltb⟩,⟨cltx, _⟩⟩
    exact ⟨cltx, xltb⟩
