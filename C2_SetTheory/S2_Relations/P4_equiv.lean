import Mathlib.Data.Real.Basic

/-
# Equivalence Relations

An Equivalence relation is any relation which is reflexive, symmetric, and
transitive. Typically equivalence relations are denoted with the symbol `~`
or `≈`.
-/
#print Equivalence
structure Equivalence₁ {α : Type} (r : α → α → Prop) : Prop where
  /-- An equivalence relation is reflexive: `x ~ x` -/
  refl  : ∀ x, r x x
  /-- An equivalence relation is symmetric: `x ~ y` implies `y ~ x` -/
  symm  : ∀ {x y}, r x y → r y x
  /-- An equivalence relation is transitive: `x ~ y` and `y ~ z` implies `x ~ z` -/
  trans : ∀ {x y z}, r x y → r y z → r x z

def parity (x y : ℤ) : Prop := ∃ k, x - y = 2 * k

lemma parity_reflexive (x : ℤ) : parity x x := by
  use 0
  rw [sub_self, mul_zero]

lemma parity_symmetric {x y : ℤ} (h : parity x y) : parity y x := by
  rcases h with ⟨k, hk⟩
  use -k
  rw [mul_neg, ←hk, neg_sub]

lemma parity_transitive {x y z : ℤ} (hxy : parity x y) (hyz : parity y z) : parity x z := by
  rcases hxy with ⟨j, hj⟩
  rcases hyz with ⟨k, hk⟩
  use j + k
  rw [mul_add, ←hj, ←hk]
  ring_nf

lemma Eqv_parity : Equivalence₁ parity where
  refl := parity_reflexive
  symm := parity_symmetric
  trans := parity_transitive

-- To use the typical `≈` notation, we need one more type: Setoid
#print Setoid
instance Setoid₁ : Setoid ℤ where
  r := parity
  iseqv := ⟨parity_reflexive, parity_symmetric, parity_transitive⟩

example : -4 ≈ 12 := by
  use -8
  norm_num

example (a b : ℤ) : a ≈ b → (a + b) ≈ 0 := by
  rintro ⟨k, hk⟩
  use (k + b)
  rw [mul_add, ←hk]
  ring_nf

example (a b c d : ℤ) : a ≈ b → c ≈ d → (a + c) ≈ (b + d) := by
  sorry

-- Now that we have fleshed out the notion of equivalence, let's move on
-- to one of the main uses: equivalence classes! For any term `a`, the
-- equivalence class of `a` is the set of all terms which are equivalent
-- to `a`. Let's develop this theory for our parity example.
def eqv_class (a : ℤ) : Set ℤ := {x | x ≈ a}

lemma mem_self_eqv_class (a : ℤ) : a ∈ eqv_class a := parity_reflexive a

lemma mem_eqv_class_symm (a b : ℤ) :
  a ∈ eqv_class b → b ∈ eqv_class a :=
    parity_symmetric

lemma mem_eqv_class_trans (a b c : ℤ) :
  a ∈ eqv_class b → b ∈ eqv_class c → a ∈ eqv_class c :=
    parity_transitive

lemma eqv_class_eq_iff_eqv (a b : ℤ) : eqv_class a = eqv_class b ↔ a ≈ b := by
  constructor
  · intro h
    change a ∈ eqv_class b
    rw [←h]
    exact mem_self_eqv_class a
  · intro h
    ext x
    exact ⟨λ hxa ↦ parity_transitive hxa h,
           λ hxb ↦ parity_transitive hxb (parity_symmetric h)⟩


def isPartition {X : Type} (P : Set (Set X)) : Prop :=
  (∀ S ∈ P, ∀ T ∈ P, S ≠ T → Disjoint S T) ∧ (∀ x, ∃ S ∈ P, x ∈ S)

-- CLAIM: Equivalence classes form a partition
example : isPartition {S | ∃ x, S = eqv_class x} := by
  apply And.intro
  · intro S ⟨x, Seqvx⟩ T ⟨y, Teqvy⟩
    rw [Seqvx, Teqvy]
    intro hnxy
    rw [Set.disjoint_iff_forall_ne]
    intro a hax b hby hab
    rw [ne_eq, eqv_class_eq_iff_eqv] at hnxy
    rw [hab] at hax
    apply hnxy
    apply parity_transitive _ hby
    apply parity_symmetric hax
  · intro x
    exists eqv_class x
    simp
    use ⟨x, rfl⟩
    exact mem_self_eqv_class x

-- CLAIM: A partition specifies an equivalence relation
section
variable {X : Type} (P : Set (Set X))
def specify (x y : X) : Prop :=
  ∃ S ∈ P, x ∈ S ∧ y ∈ S

example : isPartition P → Equivalence (specify P) := λ ⟨Pdisj, Pcover⟩ ↦ {
  refl := by
    intro x
    rcases (Pcover x) with ⟨S, _, _⟩
    use S
  symm := by
    rintro x y ⟨S, _, _, _⟩
    use S
  trans := by
    rintro x y z ⟨S, hSP, xS, yS⟩ ⟨T, hTP, yT, zT⟩
    use S
    use hSP
    use xS
    have : S = T := by
      by_contra h
      let h2 := Pdisj S hSP T hTP h
      rw [Set.disjoint_iff_forall_ne] at h2
      apply (h2 yS yT)
      rfl
    rwa [this]
}

end
