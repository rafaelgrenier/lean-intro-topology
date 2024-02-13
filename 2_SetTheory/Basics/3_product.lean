/-
# Cartesian Products

Cartesian Products allow for a new way to create new sets. For sets (S : set α) and (T : set β),
the new set S ⨯ˢ T is of type set (α × β) such that for each p ∈ S and q ∈ T,
the pair (p, q) is in S ×ˢ T.
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Prod
variable {α β : Type}
variable {A S T : Set α} {B U V : Set β}
open Set

-- here are a few examples of proofs involving Cartesian Products
example {p : α} {q : β} (hp : p ∈ S) (hq : q ∈ U) : (p, q) ∈ S ×ˢ U := by
  rw [mem_prod_eq]
  dsimp
  constructor
  · exact hp
  · exact hq

example (hST : S ⊆ T) (hUV : U ⊆ V) : S ×ˢ U ⊆ T ×ˢ V := by
  intro p hp
  rw [mem_prod_eq] at *
  constructor
  · apply hST
    exact And.left hp
  · apply hUV
    exact And.right hp

-- You try!
example {p : α} {q : β} : (p, q) ∈ S ×ˢ U ↔ (q, p) ∈ U ×ˢ S := by
  sorry

example : (S ∩ T) ×ˢ (U ∩ V) = (S ×ˢ U) ∩ (T ×ˢ V) := by
  sorry

def swap_map (X Y : Type) (p : X×Y) : (Y × X) := ⟨p.2, p.1⟩

example : Function.Surjective (swap_map α β) := by
  rintro ⟨b, a⟩
  use ⟨a, b⟩
  rfl

example : Function.Injective (swap_map α β) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hswap
  rw [Prod.eq_iff_fst_eq_snd_eq] at hswap
  dsimp only [swap_map] at hswap
  rw [hswap.left, hswap.right]

example : (swap_map α β) '' (S ×ˢ U) = (U ×ˢ S) := by
  sorry
