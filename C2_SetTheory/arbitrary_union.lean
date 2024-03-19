/-
# Arbitrary Unions and Intersections

How does one intersect some arbitrary number of sets? Or take the union of
infinitely many sets? There are two ways: indexed sets, and sets of sets

-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Data.Nat.Interval
namespace UnionInter
open Set

def moreThanN (n : Nat) : Set Nat := {m | n ≤ m}
-- so moreThanN maps from particular numbers to sets
def unionAll : Set Nat := ⋃ n : Nat, moreThanN n
-- unionAll is the union of moreThanN n for each Natural number n

example : unionAll = univ := by
  rw [eq_univ_iff_forall]
  intro x
  dsimp [unionAll, moreThanN]
  rw [mem_iUnion]
  simp only [mem_setOf_eq]
  exists x

def interAll : Set Nat := ⋂ n : Nat, moreThanN n

example : interAll = ∅ := by
  rw [eq_empty_iff_forall_not_mem]
  dsimp [interAll, moreThanN]
  intro x hx
  rw [mem_iInter] at hx
  contrapose hx
  push_neg
  exists (x+1)
  simp



end UnionInter
