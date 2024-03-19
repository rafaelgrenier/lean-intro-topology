import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-

# Countability

A set S is countable if there's some injective function from S into
the Natural numbers. If S is in bijection with the entirety of ℕ, then
S is called countably infinite. From our study into cardinality and
bijections between finite sets, we may have developed the intuition that
two sets can only be in bijection with each other if they are "the same size"
in some sense. However, this intuition gets undermined by sets which are
not finite, as we will show below. It turns out that ℕ × ℕ is also
countably infinite, despite appearing "larger" than ℕ.

-/

def triangular : ℕ → ℕ
| 0 => 0
| n + 1 => (triangular n) + n + 1

def f : {p : ℕ × ℕ // p.1 ≤ p.2} → ℕ := λ ⟨⟨a, b⟩, _⟩ ↦ a + triangular b

lemma f_inj : Function.Injective f := by
  rintro ⟨⟨a, b⟩, aleb⟩ ⟨⟨c, d⟩, cled⟩
  dsimp [f]
  intro h
  apply Subtype.ext
  rw [Prod.ext_iff]
  dsimp only
  rcases (eq_or_ne b d) with (beqd | bned)
  · refine ⟨?_, beqd⟩
    rw [beqd, Nat.add_right_cancel_iff] at h
    exact h
  · wlog h' : b < d
    · let claim := this c d cled a b aleb (Eq.symm h) (Ne.symm bned)
      suffices temp : c = a ∧ d = b by {rw [temp.1, temp.2]; simp only [and_self]}
      apply claim
      rw [not_lt] at h'
      apply Nat.lt_of_le_and_ne h' (Ne.symm bned)
    apply False.elim
    let k := d - b - 1
    have k_prop : d = b + k + 1 := by
      dsimp
      rw [add_assoc, Nat.sub_add_cancel, add_comm, Nat.sub_add_cancel]
      exact le_of_lt h'
      exact le_tsub_of_add_le_left h'
    rw [k_prop] at h' h cled
    have : ∃ m, triangular (b + k + 1) = m + (b + 1) + triangular b := by
      induction' k with k ih
      · exists 0
        dsimp [triangular]
        ring
      rw [triangular]
      rcases ih with ⟨n, hn⟩
      simp [Nat.succ_eq_add_one, ←add_assoc, hn]
      exists n + b + k + 2
      ring
    rcases this with ⟨m, hm⟩
    rw [hm] at h
    dsimp at aleb
    simp [←add_assoc] at h
    rw [←not_lt] at aleb
    apply aleb
    rw [h]
    ring_nf
    exact Nat.lt_add_of_pos_left (Nat.lt_add_right 0 (1 + c) m (Nat.lt_add_right 0 1 c Nat.one_pos))

def crisscross : ℕ × ℕ → ℕ := λ ⟨a, b⟩ ↦ f ⟨⟨b, a+b⟩, Nat.le_add_left b a⟩

lemma crisscross_injective : Function.Injective crisscross := by
  rintro ⟨a, b⟩ ⟨c, d⟩
  dsimp [crisscross, f]
  intro h
  have aux₁ : b ≤ a + b := Nat.le_add_left b a
  have aux₂ : d ≤ c + d := Nat.le_add_left d c
  have : (⟨⟨b, a+b⟩, aux₁⟩ : {p : ℕ × ℕ // p.1 ≤ p.2}) = ⟨⟨d, c+d⟩, aux₂⟩ := f_inj h
  simp only [Subtype.mk.injEq, Prod.mk.injEq] at *
  rcases this with ⟨beqd, aeqc⟩
  rw [beqd] at aeqc
  exact ⟨Nat.add_right_cancel aeqc, beqd⟩


#eval crisscross ⟨3, 6⟩
#eval crisscross (2, 1)
#eval crisscross (5, 0)

lemma crisscross_bijective : Function.Bijective crisscross := by
  sorry -- Try proving the surjectivity part

-- Now we can prove the product of any two countable types is still countable

theorem countable_product {X Y  : Type} [Countable X] [Countable Y] : Countable (X × Y) := by
  rcases exists_injective_nat X with ⟨f, hf⟩
  rcases exists_injective_nat Y with ⟨g, hg⟩
  constructor
  exists λ ⟨x, y⟩ ↦ crisscross ⟨f x, g y⟩
  intro ⟨w, x⟩ ⟨y, z⟩ h
  rw [Prod.mk.injEq]
  rcases Prod.ext_iff.mp (crisscross_injective h) with ⟨fwfy, gxgz⟩
  exact ⟨hf fwfy, hg gxgz⟩

theorem countable_of_embedded_in_countable {X Y : Type} [Countable Y] (f : X → Y) (finj : Function.Injective f) : Countable X := by
  rcases exists_injective_nat Y with ⟨g, ginj⟩
  exists g ∘ f
  exact Function.Injective.comp ginj finj

-- ℕ is known to be countable, for obvious reasons.
-- prove that Fin n is also countable!

example : ∀ n : ℕ, Countable (Fin n) := by
  sorry

example : Countable (ℕ × ℕ × ℕ) := by sorry

example : Countable ℚ := by
  let f : ℚ → ℤ × ℕ := λ ⟨p, q, _, _⟩ ↦ (p, q)
  have finj : Function.Injective f := by
    rintro ⟨a, b, bpos, hab⟩ ⟨c, d, dpos, hcd⟩
    simp only [Prod.mk.injEq, Rat.mk'.injEq, imp_self]
  exact countable_of_embedded_in_countable f finj

example {X : Type} [Countable X] : ∀ S : Set X, Countable S := by
  intro S
  let inc : S → X := λ ⟨x, _⟩ ↦ x
  rcases exists_injective_nat X with ⟨f, hf⟩
  exists f ∘ inc
  apply Function.Injective.comp hf
  intro ⟨x, hx⟩ ⟨y, hy⟩
  simp only [Subtype.mk.injEq, imp_self]

example {X : Type} (S T : Set X) (hS : Countable S) :
  Countable {x // x ∈ S ∩ T} := by
  rcases exists_injective_nat S with ⟨fS, fSinj⟩
  exists λ ⟨x, xS, _⟩ ↦ fS ⟨x, xS⟩
  intro ⟨x, xS, xT⟩ ⟨y, yS, yT⟩
  simp only [Subtype.mk.injEq]
  exact λ h ↦ Subtype.mk.inj (fSinj h)

-- We can use binary to show Countable (Finset ℕ)
open Finset
open BigOperators

def bin : Finset ℕ → ℕ := λ S ↦ ∑ x in S, 2 ^ x

#eval bin {0, 10}
#eval bin {1, 3, 5}
#eval bin ∅

lemma bin_pos_iff_nonempty {S : Finset ℕ} : 0 < bin S ↔ S.Nonempty := by
  apply Iff.intro
  · contrapose!
    simp only [not_nonempty_iff_eq_empty, nonpos_iff_eq_zero]
    intro h
    rw [h]
    simp only
  dsimp [bin]
  intro hS
  apply sum_induction_nonempty _ _ ?_ hS ?_
  · exact λ _ b h _ ↦ Nat.add_pos_left h b
  . exact λ x _ ↦ pow_pos (Nat.succ_pos 1) x

-- If we can show that bin is injective, then the type consisting of
-- all finsets over ℕ is a countable type!

lemma card_pos_iff_nonempty {S : Finset ℕ} : card S > 0 ↔ S.Nonempty := by
  rw [←not_iff_not]
  simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero, card_eq_zero, not_nonempty_iff_eq_empty]

theorem hasGreatest_of_nonempty : ∀ S : Finset ℕ, S.Nonempty → ∃ m : ℕ, IsGreatest S m := by
  have : ∀ n : ℕ, ∀ S : Finset ℕ, card S = n + 1 → ∃ m : ℕ, IsGreatest S m := by
    intro n
    induction' n with n ih
    · intro S Suniq
      simp [card_eq_one] at Suniq
      rcases Suniq with ⟨m, hS⟩
      exists m
      rw [hS]
      constructor
      · simp only [coe_singleton, Set.mem_singleton_iff]
      intro k keqm
      simp only [coe_singleton, Set.mem_singleton_iff] at keqm
      rw [keqm]
    intro S hS
    simp [Nat.succ_eq_add_one] at hS
    have : S.Nonempty := by
      rw [←card_pos_iff_nonempty, hS]
      simp only [gt_iff_lt, add_pos_iff, or_true, or_self]
    rw [←coe_nonempty, Set.nonempty_def] at this
    rcases this with ⟨x, xS⟩
    have : card (erase S x) = n + 1 := by
      apply Nat.add_right_cancel
      rw [card_erase_add_one]
      exact hS
      exact xS
    rcases ih (erase S x) this with ⟨m, hm⟩
    rcases Nat.lt_or_ge x m with (xltm | mlex)
    · exists m
      rcases hm with ⟨hm, upperm⟩
      simp at hm
      use hm.1
      intro k kS
      rcases (eq_or_ne k x) with (keqx | knex)
      · rw [keqx]
        exact le_of_lt xltm
      apply upperm
      simp
      exact ⟨kS, knex⟩
    · exists x
      use xS
      intro k kS
      rcases (eq_or_ne k x) with (keqx | knex)
      · rw [keqx]
      apply le_trans _ mlex
      apply hm.2
      simp only [coe_erase, mem_coe, Set.mem_diff, Set.mem_singleton_iff]
      use kS
  intro S hS
  apply this (card S - 1)
  rw [Nat.sub_add_cancel]
  contrapose! hS
  simp only [not_nonempty_iff_eq_empty]
  rw [Nat.lt_succ, Nat.le_zero, card_eq_zero] at hS
  exact hS

lemma bin_lt_of_ssubset {S T : Finset ℕ} (h : S ⊂ T) : bin S < bin T := by
  have : bin T = bin S + bin (T \ S) := by
    nth_rw 1 [Eq.symm (union_sdiff_of_subset (subset_of_ssubset h))]
    exact sum_union disjoint_sdiff
  rw [this, Nat.lt_add_right_iff_pos, bin_pos_iff_nonempty, Finset.Nonempty]
  rw [ssubset_iff_of_subset (subset_of_ssubset h)] at h
  simp [mem_sdiff]
  exact h

lemma bin_le_of_subset {S T : Finset ℕ} (h : S ⊆ T) : bin S ≤ bin T := by
  sorry

lemma bin_range_lt_n : ∀ n : ℕ, bin (range n) < bin {n} := by
  intro n
  induction' n with n ih
  · simp only
  dsimp only [bin]
  rw [sum_range_succ, sum_singleton, Nat.succ_eq_add_one, pow_add]
  simp only [pow_one, mul_two, add_lt_add_iff_right]
  exact ih

lemma bin_lt_of_greatest_lt {S T : Finset ℕ} {a b : ℕ} (ha : IsGreatest S a) (hb : IsGreatest T b) (altb : a < b) : bin S < bin T := by
  have : bin S ≤ bin (range (a + 1)) := by
    apply bin_le_of_subset
    intro k kS
    rw [mem_range, Nat.lt_succ]
    exact ha.2 kS
  apply lt_of_le_of_lt this
  have : {b} ⊆ T := by
    intro x xeqb
    rw [mem_singleton.mp xeqb]
    apply hb.1
  apply lt_of_lt_of_le _ (bin_le_of_subset this)
  apply lt_of_lt_of_le (bin_range_lt_n (a+1))
  simp [bin, sum_singleton]
  apply pow_le_pow
  exact Nat.le_succ 1
  exact altb

theorem bin_inj_precursor (n : ℕ) (S T : Finset ℕ) (hn : n = S.card) (h : bin S = bin T) : S = T := by
  induction' n with n ih generalizing S T
  · have : S = ∅ := Iff.mp card_eq_zero (id (Eq.symm hn))
    rw [this] at h ⊢
    have : ¬ T.Nonempty := by
      rw [←bin_pos_iff_nonempty]
      simp only [not_lt, nonpos_iff_eq_zero, ←h]
    simp at this
    rw [this]
  have nonempS : S.Nonempty := by
    rw [←card_pos_iff_nonempty, ←hn]
    exact Nat.succ_pos'
  have nonempT : T.Nonempty := by
    apply nonempty_of_ne_empty
    intro h'
    rw [h'] at h
    dsimp [bin] at h
    apply ne_of_lt (bin_pos_iff_nonempty.mpr nonempS)
    rw [←h]
    rfl
  rcases hasGreatest_of_nonempty S nonempS with ⟨a, haS⟩
  rcases hasGreatest_of_nonempty T nonempT with ⟨b, hbT⟩
  have blea : b ≤ a := not_lt.mp (λ altb ↦ ne_of_lt (bin_lt_of_greatest_lt haS hbT altb) h)
  have aleb : a ≤ b := not_lt.mp (λ blta ↦ ne_of_lt (bin_lt_of_greatest_lt hbT haS blta) (Eq.symm h))
  have aeqb : a = b := Nat.le_antisymm aleb blea
  have aux₁ : n = card (erase S a) := by
    rw [←card_erase_add_one haS.1] at hn
    simp at hn
    exact hn
  have aux₂ : bin (erase S a) = bin (erase T b) := by
    dsimp [bin]
    apply @Nat.add_left_cancel (2^a)
    nth_rw 3 [aeqb]
    rw [add_sum_erase _ _ haS.1, add_sum_erase _ _ hbT.1]
    exact h
  let claim := ih (erase S a) (erase T b) aux₁ aux₂
  have : S = insert a (erase S a) := by
    apply Eq.symm
    apply insert_erase haS.1
  rw [this, claim, aeqb]
  apply insert_erase hbT.1

theorem bin_inj : Function.Injective bin :=
  λ S T h ↦ bin_inj_precursor (card S) S T (rfl) h

example : Countable (Finset ℕ) := ⟨bin, bin_inj⟩

-- Although it's not necessary to prove Countability, try proving
-- that `bin` is a bijection

theorem bin_bij : Function.Bijective bin := by
  use bin_inj
  intro n
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => exists ∅
  | 1 => exists {0}
  | n + 2 =>
    /-
    let k be the largest number such that 2 ^ k ≤ n + 2
    let m := n + 2 - (2 ^ k)
    By induction, ∃ S : Finset ℕ such that bin S = m
    then define T : Finset ℕ := insert k S
    T should then satisfy that bin T = n + 2.
    -/
    sorry
