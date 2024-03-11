import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
/-

# Finiteness

You likely have an intuitive sense of what it means to be finite;
perhaps a set is finite if you can count out elements one by one
and eventually you'll be able to stop counting. Or maybe we assume sets to
be finite unless there's some sort of condition that makes that set unlimited,
like induction for ℕ. But in mathematics, and particularly in Lean, formalizing
these notions is the name of the game.

One way that mathematicians think about finiteness has to do with sections
of the natural numbers. A section of natural numbers is the set of all
natural numbers less than "n", denoted Sₙ. We can then define a set A
to be "finite" if there exists a natural number n and a function f : Sₙ → A
such that f is bijective. For such as set A, n is "the cardinality of A".

In Lean, rather than having a property that a set is finite, we have a new type
of set called `Finset`. Lean still understands Finset as a kind of Set, so the
conventional set theory notions of subsets, unions, intersections, etc. will
work for Finset. Sections in Lean are expressed Finset.range, so
Finset.range 3 = {0, 1, 2} and Finset.range 100 = {0, 1, 2, ..., 98, 99}.
Cardinality is expressed Finset.card
-/

#check Finset.range
#check Finset.range 0 -- this is the empty set!
#check Finset.card (Finset.range 12)
open Finset -- Now we don't need to write Finset.name and can instead write name
#check card (range 12)




/-
Munkres' Path

Lemma 1 : Let n : ℕ, A : Set α, and a₁ ∈ A.
  Then A ≃ range (n+1) ↔ A \ {a₁} ≃ range n
Proof:
  (=>) Let f be a bijection from A to range (n + 1). If f a₁ = n, then f restricted
    to A \ {a₁} is the desired bijection. If f a₁ = m ≠ n, then since f is surjective,
    there's some a₂ ∈ A such that f a₂ = n. We can define a function h from A to
    range (n + 1) which such that h a₁ = f a₂, h a₂ = f a₁, and otherwise the same. Then
    h restricted to A \ {a₁} is the desired bijection.
  (<=) Let g be a bijection from A \ {a₁} to range n. Just extend g so that g a₁ := n, then
    you have the desired bijection.

Lemma 2 : Let A B : Set α such that B ⊂ A, let n : ℕ, and assume A ≃ range (n + 1). Then
  there are two consequences:
  · There are no bijections from B to range (n + 1), i.e. ¬(B ≃ range (n + 1))
  · If B is nonempty, there exists a bijection from B to range {m + 1}, where
    m is some number less than n, i.e. (B.Nonempty → ∃ m < n, B ≃ range (m + 1))
Proof:
  We will do induction on n.
  · When n = 0, A ≃ {0}, so B ⊂ A implies B = ∅. Thus there's no bijection from B to {0},
    and anything that follows from B nonempty is vacuously true.
  So now we can assume that the above lemma holds for some n : ℕ, and we need to prove
  it for A ≃ range (n + 2). If B is empty, the logic from the base case still applies and
  we're done. Thus we can assume B is nonempty, and let b ∈ B. We can also let
  a₁ ∈ A \ B, since B is a PROPER subset. By Lemma 1, we know that A \ {b} ≃ range (n + 1).
  Since B \ {b} ⊂ A \ {b}, the induction hypothesis implies ¬(B \ {b} ≃ range (n + 1)) and
  (B \ {b} nonempty → ∃ m < n for which B \ {b} ≃ range (m + 1)). Now if we suppose that
  B ≃ range (n + 2), we would arrive at a contradiction after applying Lemma 1. If
  B \ {b} is empty, then B ≃ {0}. Thus we can assume B \ {b} is nonempty, and therefore
  there's some m < n such that B \ {b} ≃ range (m + 1). Again applying Lemma 1, we conclude
  that B ≃ range (m + 2), thus induction is complete.

Lemma 2 is very powerful and has the following corollaries:
· If A is finite, A has no bijection with any proper subset of itself.
· ℕ is not finite.
· Cardinality is unique; Any finite set A has only one natural number n such that A ≃ range (n)
· The subset of a finite set is also finite, and has a cardinality no greater than its superset
In fact, we can now describe other properties equivalent to finiteness.

Lemma 3 : Let B : Set α which is nonempty. Then the following three conditions are equivalent:
  (1) B is finite.
  (2) There is a surjection from range (n + 1) onto B for some n.
  (3) There is an injection from B into range (n + 1) for some n.
Proof:
  (1)→(2):
  Since B is nonempty, There's some n for which B ≃ range (n + 1).
  (2)→(3):
  Let f : ℕ → α which maps range (n + 1) onto B. Define g : α → ℕ by
  g a := minimum (f ⁻¹' {a}). f surjective implies each f ⁻¹' {a} is nonempty,
  and g is injective because a ≠ a' → f ⁻¹' {a} is disjoint from f ⁻¹' {a'},
  which in turn implies g a ≠ g a'.
  (3)→(1):
  Let f : ℕ → α be an injective map from B into range (n + 1). Then f is a
  bijection from B to f '' B and f '' B is a subset of range (n + 1), so
  B ≃ f '' B ≃ range (m + 1).

-/

open Function

def isCard {α : Type} (A : Set α) (n : ℕ) : Prop := ∃ f : A → Fin n, Bijective f

lemma aux : ∀ n : ℕ, isCard {k | k < n} n := by
  intro n
  exists λ ⟨x, xltn⟩ ↦ ⟨x, xltn⟩
  rw [bijective_iff_existsUnique]
  intro ⟨k, kltn⟩
  exists ⟨k, kltn⟩
  simp

lemma bijective_of_eq_card {α β : Type} (A : Set α) (B : Set β) (n : ℕ) :
  isCard A n → (isCard B n ↔ ∃ f : A → B, Bijective f) := by
  rintro ⟨fa, bijfa⟩
  apply Iff.intro
  · rintro ⟨fb, bijfb⟩
    rw [bijective_iff_has_inverse] at bijfb
    rcases bijfb with ⟨fb', fb'li, fb'ri⟩
    exists (fb' ∘ fa)
    refine Bijective.comp ?_ bijfa
    rw [bijective_iff_has_inverse]
    exists fb
  · rintro ⟨fAB, hfAB⟩
    rw [bijective_iff_has_inverse] at hfAB
    rcases hfAB with ⟨fBA, fBAli, fBAri⟩
    exists (fa ∘ fBA)
    apply Bijective.comp bijfa
    rw [bijective_iff_has_inverse]
    exists fAB


lemma card0empty {α : Type} (A : Set α) (card0 : isCard A 0) : A = ∅ := by
  rcases card0 with ⟨f, bijf⟩
  contrapose! bijf
  rw [←Set.nonempty_iff_ne_empty, Set.nonempty_def] at bijf
  rcases bijf with ⟨a, ha⟩
  rcases f ⟨a, ha⟩ with ⟨n, hn⟩
  apply False.elim
  apply Nat.not_lt_of_le (Nat.zero_le n) hn

lemma munk2 {α : Type} {A B : Set α} (hAB : B ⊂ A) (n : ℕ) (f : A → Fin (n + 1)) (bijf : Function.Bijective f) :
  (¬ isCard B (n+1)) ∧ (∃ m : ℕ, m ≤ n ∧ isCard B m) := sorry

def setFinite {α : Type} (A : Set α) : Prop := ∃ n : ℕ, isCard A n

lemma cor1 {α : Type} (A : Set α) (finiteA : setFinite A) :
  ∀ B : Set α, B ⊂ A → ¬ ∃ f : A → B, Bijective f := by
  rintro B hAB ⟨f, bijf⟩
  rcases finiteA with ⟨n, cardAn⟩
  match n with
  | 0 =>
    apply Set.nonempty_iff_ne_empty.mp (Set.nonempty_of_ssubset' hAB)
    exact card0empty A cardAn
  | n + 1 =>
    let ⟨g, bijg⟩ := cardAn
    rcases (Set.eq_empty_or_nonempty B) with (Bempty | Bnonempty)
    · sorry
    apply (munk2 hAB n g bijg).1
    rw [bijective_of_eq_card A B _ cardAn]
    exists f

lemma Nat_infinite : ¬setFinite (Set.univ : Set ℕ) := by
  intro sf
  let posNat : Set ℕ := {n | n > 0}
  have posNatsub : posNat ⊂ Set.univ := by
    constructor
    · intro _ _
      trivial
    simp [Set.not_subset_iff_exists_mem_not_mem]
  apply cor1 _ sf posNat posNatsub
  exists λ ⟨n, _⟩ ↦ ⟨n + 1, (by {simp only [gt_iff_lt, add_pos_iff, or_true]} : n + 1 > 0)⟩
  rw [bijective_iff_existsUnique]
  intro ⟨n, npos⟩
  exists ⟨n - 1, trivial⟩
  simp
  use Nat.sub_add_cancel npos
  intro a ha
  rw [←ha]
  exact rfl

lemma cardUnique {α : Type} (A : Set α) (m n : ℕ) (cardm : isCard A m) (cardn : isCard A n) : n = m := by
  contrapose cardm with nnem
  intro cardm
  wlog nltm : n < m
  · have mnen : m ≠ n := λ meqn ↦ nnem (Eq.symm meqn)
    apply this A n m cardm mnen cardn
    apply Nat.lt_of_le_and_ne _ mnen
    exact not_lt.mp nltm
  let Sm : Set ℕ := {k | k < m}
  let Sn : Set ℕ := {k | k < n}
  have SnsubSm : Sn ⊂ Sm := by
    constructor
    · intro k kltn
      simp only [Set.mem_setOf_eq] at *
      exact lt_trans kltn nltm
    simp only [Set.setOf_subset_setOf, not_forall, not_lt, exists_prop]
    exists n
  have finiteSm : setFinite Sm := by
    exists m
    apply aux
  apply cor1 Sm finiteSm Sn SnsubSm
  rw [←bijective_of_eq_card Sm Sn m (aux m)]
  rw [bijective_of_eq_card A Sn m cardm]
  rw [←bijective_of_eq_card A Sn n cardn]
  exact aux n


/-
To follow Munkres' path in Lean is possible, but exceptionally tedious and
involves more investigation into Type theory than was intended for the scope
of this introduction to Lean. At each stage where Munkres asserts a function
is bijective, at least 30 lines of Lean code were necessary for me to prove
it. Furthermore, this section need to use `Fin`, `Equiv`, and `Finite` to be
done properly, in addition to Subtype coercion. Since this was too demanding,
I have decided to leave this section of code absent, and instead describe the
structure of the basic proofs for understanding finiteness.
-/

/-

-- This was just lemma 1 from Munkres

lemma obvi (n : ℕ) : n < n + 1 := by
  simp

lemma munk1_1 {A : Type} [DecidableEq A] (n : ℕ) (a : A) (f : { x // x ≠ a } → (Fin n)) (bijf : Function.Bijective f):
  ∃ g : A → (Fin (n + 1)), Function.Bijective g := by
  let g : A → Fin (n+1) := λ x ↦ if h' : x = a then ⟨n, obvi n⟩ else
    ⟨(f ⟨x, h'⟩).val, lt_trans (f ⟨x, h'⟩).2 (obvi n)⟩
  have g_def : ∀ x, g x = if h' : x = a then ⟨n, obvi n⟩ else ⟨(f ⟨x, h'⟩).val, sorry⟩ := by
    intro x
    rfl
  exists g
  constructor
  · intro x y gxgy
    simp [g_def, dite_eq_iff] at gxgy
    rcases gxgy with (⟨xa, h⟩ | ⟨xna, h⟩)
    · replace h := Eq.symm h
      simp [dite_eq_iff] at h
      rcases h with (ya | ⟨yna, hh⟩)
      · rw [xa, ya]
      contrapose hh
      apply ne_of_lt
      apply Fin.prop
    replace h := Eq.symm h
    simp [dite_eq_iff] at h
    rcases h with (⟨ya, h⟩ | ⟨yna, h⟩)
    · contrapose h
      apply ne_of_gt
      apply Fin.prop
    have : (⟨x, xna⟩ : { x // x ≠ a }) = ⟨y, yna⟩ := by
      apply bijf.1
      ext
      exact Eq.symm h
    rw [Subtype.ext_iff_val] at this
    exact this
  intro ⟨k, klen⟩
  rcases (eq_or_ne k n) with (kn | knn)
  · exists a
    simp [g_def]
    rw [kn]
  have kltn : k < n := by
    apply Nat.lt_of_le_and_ne _ knn
    apply Nat.lt_succ.mp klen
  rcases bijf.2 ⟨k, kltn⟩ with ⟨⟨x, xna⟩, hx⟩
  exists x
  simp [g_def]
  have : x = a ↔ False := by
    simp only [iff_false]
    exact xna
  simp [this]
  rw [Fin.ext_iff] at hx
  simp at hx
  rw [←hx]

lemma swap_helper {A B : Type} [DecidableEq A] {f : A → B} (a₀ a₁ : A) (hf : Bijective f) :
  ∃ g : A → B, g a₀ = f a₁ ∧ g a₁ = f a₀ ∧ Bijective g := by
  exists λ x ↦ if x = a₀ then f a₁ else (if x = a₁ then f a₀ else f x)
  simp only [ite_self, ite_true, ite_eq_right_iff, true_and]
  apply And.intro
  · intro h
    congr
  constructor
  · intro x y
    simp [ite_eq_iff, eq_ite_iff]
    rintro (⟨ya0, h⟩ | ⟨nya0, (⟨ya1, (⟨xa0, fa1fa0⟩ | ⟨xna0, h⟩)⟩ | ⟨nya1, (⟨xa0, fa1fy⟩ | ⟨xna0, (⟨xa1, fa0fy⟩ | ⟨xna1, fxfy⟩)⟩)⟩)⟩)
    · contrapose! h
      refine ⟨λ xa0 ↦ h (?_), λ xa1 fa0fa1 ↦ h (?_), λ xna1 h' ↦ xna1 (hf.1 h')⟩
      · rw [xa0, ya0]
      · rw [xa1, ya0]
        exact hf.1 (Eq.symm fa0fa1)
    · rw [ya1, xa0]
      apply Eq.symm
      apply hf.1 fa1fa0
    · contrapose! h
      refine ⟨λ xa1 ↦ h ?_, λ h' ↦ xna0 $ hf.1 h'⟩
      rw [xa1, ya1]
    · exact False.elim $ nya1 $ Eq.symm $ hf.1 fa1fy
    · exact False.elim $ nya0 $ Eq.symm $ hf.1 fa0fy
    · exact hf.1 fxfy
  intro b
  rcases hf.2 b with ⟨x, hx⟩
  rcases (eq_or_ne x a₀) with (xa0 | xna0)
  · exists a₁
    rw [←hx, xa0]
    simp
    intro h
    congr
  rcases (eq_or_ne x a₁) with (xa1 | xna1)
  · exists a₀
    rw [←hx, xa1]
    simp
  have aux : x = a₀ ↔ False := by rwa [iff_false]
  have aux': x = a₁ ↔ False := by rwa [iff_false]
  exists x
  simp only [aux, aux', ite_false]
  exact hx

lemma munk1_2 {A : Type} [DecidableEq A] (n : ℕ) (a : A) (f : A → Fin (n + 1)) (bijf : Function.Bijective f) :
  ∃ g : { x // x ≠ a } → Fin n, Function.Bijective g := by
  rcases bijf.2 ⟨n, obvi n⟩ with ⟨a₁, ha1⟩
  wlog h : f a = ⟨n, obvi n⟩
  · rcases (swap_helper a a₁ bijf) with ⟨ff, h₁, _, bijff⟩
    let claim := this n a ff bijff a
    apply claim <;> rw [h₁, ha1]
  · exists λ x ↦ ⟨f x, ?_⟩
    apply Nat.lt_of_le_and_ne
    apply Nat.lt_succ.mp
    apply Fin.prop
    intro hn
    apply x.2
    apply bijf.1
    ext
    rw [hn, h]
    constructor
    · intro x y
      simp
      intro fxfy
      ext
      apply bijf.1
      ext
      exact fxfy
    intro ⟨k, kltn⟩
    simp only [ne_eq, Fin.mk.injEq, Subtype.exists, exists_prop]
    have klen : k < n + 1 := lt_trans kltn (obvi n)
    rcases bijf.2 ⟨k, klen⟩ with ⟨x, hx⟩
    exists x
    apply And.intro
    · intro xa
      apply (Nat.ne_of_lt kltn)
      rw [xa] at hx
      rw [hx, Fin.ext_iff] at h
      exact h
    · apply Fin.ext_iff.mp hx
-/
