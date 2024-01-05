/-
# Filters

The other way of concocting a topology is by prescribing neighborhood filters. Firstly, let's define
what a filter is. A filter F on a space X is a collection of subsets of X such that
· univ ∈ F
· ∀ S T : Set X, S ∈ F → S ⊆ T → T ∈ F
· ∀ S T : Set X, S ∈ F → T ∈ F → S ∩ T ∈ F

There are a couple of useful filters we can consider right away:
- given any s : Set X, "𝓟 s" is the filter consisting of all supersets of s, called the 'principal filter.'
- 𝓝 x is all supersets of open neighborhoods of x : X, where X is a topological space.
- atTop is a filter on ℕ defined by {S | ∃ N, ∀ n ≥ N, n ∈ S}.

In particular, we're interested in the neihborhoods filter. Given a topology on X, 𝓝 is a map
X → Filter X defined by 𝓝 x = {s | ∃ t : Set X, isOpen t ∧ t ⊆ s ∧ x ∈ t}. The converse doesn't
come quite as easily; not every map n : X → Filter X generates a topology which in turn has n = 𝓝.

The canonical way to construct a topology from such a map n : X → Filter X is defined below
-/
import Mathlib.Topology.Filter
example (X : Type) (n : X → Filter X) : TopologicalSpace X where
  IsOpen s := ∀ a ∈ s, s ∈ n a
  /-
  Feel free to prove that this definition for a topological space actually satisfies
  the definition of a topology.
  -/
  isOpen_univ _ _ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry
/-
To guarantee that this topology has 𝓝 = n, n must satisfy two more properties:
· ∀ S ∈ n x → x ∈ S
· ∀ x : X, ∀ S ∈ n x → ∃ T ∈ n x, T ⊆ S ∧ ∀ y ∈ T, S ∈ n y

This whole sidebar into filters may not seem useful yet, but they're particularly
useful for formalizing limits and compactness.
-/
