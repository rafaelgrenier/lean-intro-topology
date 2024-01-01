/-

# Quotients

-/
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace QuotientExpo
/-Equivalence relations
  Setoid
  Quotient
    .mk
    .lift
    .sound
    .exact
    .exists_rep
  ℤ mod 5 as an example
-/
def eqv (a b : ℤ) : Prop := ∃ k, a-b = 5*k
--theorem iseqv : Equivalence eqv := sorry <- write that, then VSCode suggests a skeleton
theorem iseqv : Equivalence eqv where
  refl := by
    intro x
    exists 0
    simp
  symm := by
    rintro x y ⟨z, hz⟩
    exists (-z)
    simp
    rw [←hz]
    simp
  trans := by
    rintro x y z ⟨k, hk⟩ ⟨l, hl⟩
    exists (k+l)
    rw [mul_add, ←hl, ←hk]
    simp
instance ZSetoid : Setoid ℤ where
  r := eqv
  iseqv := iseqv
theorem eqv_def {a b : ℤ} : a ≈ b ↔ ∃ k, a-b = 5*k := by
  dsimp [HasEquiv.Equiv, Setoid.r, eqv]
  rfl
def Zmod5 := Quotient ZSetoid
def mod5ify : ℤ → Zmod5 := Quotient.mk ZSetoid
def zero := mod5ify 0
def one := mod5ify 1
def two := mod5ify 2
def three := mod5ify 3
def four := mod5ify 4
def Zmod5univ : Set Zmod5 := {zero, one, two, three, four}

example : zero = mod5ify 100 := by
  apply Quotient.sound
  rw [eqv_def]
  exists -20


theorem add_respects : ∀ a b : ℤ, a ≈ b → ∀ c d : ℤ, c ≈ d → a + c ≈ b + d := by
  rintro a b ⟨j, hj⟩ c d ⟨k, hk⟩
  exists j + k
  rw [mul_add, ←hj, ←hk]
  ring

def add : Zmod5 → Zmod5 → Zmod5 := Quotient.map₂ Int.add add_respects
instance : Add Zmod5 := ⟨add⟩
theorem add_def {a b : Zmod5} : a + b = add a b := rfl

theorem add_comm : ∀ a b : Zmod5, a + b = b + a := by
  intro a b
  let ⟨x, xdef⟩ := Quotient.exists_rep a
  let ⟨y, ydef⟩ := Quotient.exists_rep b
  rw [←xdef, ←ydef]
  dsimp [add_def, add]
  apply Quotient.sound
  rw [eqv_def]
  exists 0
  simp [←sub_sub]

example : ∀ {x y z : ℤ}, (x + y ≈ z) ↔ (mod5ify x + mod5ify y = mod5ify z) :=
  ⟨Quotient.sound, Quotient.exact⟩

theorem mul_respects : ∀ a b : ℤ, a ≈ b → ∀ c d : ℤ, c ≈ d → a * c ≈ b * d := by
  rintro a b ⟨j, hj⟩ c d ⟨k, hk⟩
  exists d*j + b*k + 5*j*k
  rw [eq_add_of_sub_eq hj, eq_add_of_sub_eq hk]
  ring

def mul : Zmod5 → Zmod5 → Zmod5 := Quotient.map₂ Int.mul mul_respects
instance : Mul Zmod5 := ⟨mul⟩
theorem mul_def {a b : Zmod5} : a * b = mul a b := rfl

def divis_by_5 (n : ℤ) : Prop := ∃ k, n = 5*k

lemma can_lift : ∀ (a b : ℤ), a ≈ b → divis_by_5 a = divis_by_5 b := by
  intro a b ⟨k, hk⟩
  dsimp [divis_by_5]
  ext
  constructor
  · intro ⟨j, hj⟩
    exists j - k
    rw [mul_sub, ←hk, hj]
    ring
  · intro ⟨j, hj⟩
    exists k + j
    rw [mul_add, ←hk, hj]
    ring

def lifted : Zmod5 → Prop := Quotient.lift divis_by_5 can_lift

end QuotientExpo
