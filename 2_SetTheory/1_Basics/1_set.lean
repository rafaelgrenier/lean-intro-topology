/-
# Sets and Functions in Lean (Pt. 1: Tactics)

What is a set? A set is a collection of objects (we will call these objects
elements). In Lean, we restrict sets by requiring that all elements in a
set have the same type, so a set can't have both the Nat `15` and
the Prop `5 > 2`. So if a set has only elements of type `α`, the set can
be designated to be of type `Set α`. For some `S : Set α` and any term `a : α`,
either a IS in S (denoted `a ∈ S`), or a ISN'T in S (denoted `a ∉ S`). And this
relation of either being an element or not being an element is all there is,
there's no sense of `a` being an element multiple times.

We can construct sets in two major ways: we can enumerate all the elements of
the set, e.g.
  `def S : Set ℕ := {1, 4, 13, 40, 121}`,
or we can only include terms of a type which fit some condition, e.g.
  `def S : Set ℕ := { n | n > 12 ∧ n < 100}`.
In fact, the first way is just a special case of the second, with the condition
`n = 1 ∨ n = 4 ∨ n = 13 ∨ n = 40 ∨ n = 121` constructing the first example. We
say two sets are equal if each contains all elements of the other. Therefore
the order in which elements in a set are presented doesn't matter, since
`{0, 1} = {1, 0}` each set only needs to contain the elements of the other.

Set theory comes with a barrage of symbols, ∈ ∪ ∩ ∅ ⊆ ⊂ \ ᶜ 𝒫 and more, and
mathematicians are in the habit of using these symbols in place of the words
or ideas which they represent (as you will see for the rest of this library).
We've already seen the first one, but let's get through the rest.

The "union" of two sets is a new set which contains everything which was in either
set, and 'the union of sets S and T' is denoted `S ∪ T`. For example,
`{1, 3, 5, 7, 9} ∪ {2, 3, 5, 7, 11} = {1, 2, 3, 5, 7, 9, 11}`. we can define
membership in the union as `x ∈ S ∪ T ↔ x ∈ S ∨ x ∈ T`.
The "intersection" of two sets is a new set which contains everything which was
in both sets, and 'the intersection of S and T' is denoted `S ∩ T`. For example,
`{1, 3, 5, 7, 9} ∪ {2, 3, 5, 7, 11} = {3, 5, 7}`. We can define
membership in the intersection as `x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T`.
What happens if you intersect two sets with nothing in common? Then you're left
with a set which contains nothing, called "the empty set", denoted `∅`.The opposite
is a set which contains everything, specifically all terms of the type which the
set is restricted to. This set is called `Set.univ` in Lean.
Thus `x ∈ ∅ ↔ False` and `x ∈ Set.univ ↔ True`.
A set S is a "subset" of another set T if everything in S is also in T, and is
denoted `S ⊆ T`. If S is a subset of T AND there's something in T which is not
in S, then S is a "proper subset" or "strict subset" of T, denoted `S ⊂ T`.
We can define subsets `S ⊆ T ↔ ∀ x, x ∈ S → x ∈ T`. We also have a nice property
which follows from how we defined equality between sets, `S = T ↔ S ⊆ T ∧ T ⊆ S`.
For example, `{1, 2} ⊆ {1, 2, 3}` but `{4} ⊈ {1, 5, 3}`.
The "difference" between a set S and a set T is a new set which contains only
elements which are in S and NOT in T, denoted `S \ T` or `S - T`. For example,
`{1, 3, 5, 7, 9} \ {2, 3, 5, 7, 11} = {1, 9}`.
The "complement" of a set S is the difference between Set.univ and S, denoted
`Sᶜ` and defined `Sᶜ = Set.univ \ S`. For example, if S is the set of all
even natural numbers, `Sᶜ` is the set of all odd natural numbers.
Finally, the "power set" of some set S is a set which contains ALL possible
subset of S, and is denoted `𝒫 S`. Note that for a set `S` with type `Set X`, the
power set `𝒫 S` has type `Set (Set X)`, since it's a set whose elements are all
sets over the type X. For example, `𝒫 {0, 1} = {∅, {0}, {1}, {0, 1}}`.


The Mathematics in Lean (MIL) textbook* chapter 4 provides an excellent introduction to sets
and functions as they are implemented in Lean 4. The MIL textbook uses a few tactics in this
chapter that have not yet been introduced in this project,so we will take a brief sidebar to
explain those tactics (rw, simp, rintro, etc.) and some syntactic sugar used in MIL. These tactics
are used extensively in MIL and save a lot of space, but you don't need to use the full suite
of tactics in the proofs you write, you just need to know them well enough to read MIL. Therefore
the forthcoming explanations will be minimal.

*If you're reading this document in VSCODE, you can type ctrl-shift-P
 and select Lean4: Docview: Open Docview to be directed towards the text.

- rw : short for rewrite, this tactic is followed by a block of theorems [thm1, thm2, ...] in
  brackets and applies them in order to the goal. Specifically those theorems contain an equality
  or a logical equivalence, so if thm1 shows that P ↔ Q, then "rw [thm1]" would transform any instance
  of 'P' in the goal into 'Q.' To use the fact that equivalences are symmetric and transform P ↔ Q into
  Q ↔ P, one writes rw [←thm1].

- simp : short for simplify, this has the same syntax as rw but is far more powerful, since it can
  apply recursively and can also make some simple inferences. Certain theorems in MIL are marked
  for being automatically accessible by simp without writing said theorem into the brackets.

- rintro : short for recursive intro, this tactic does the same thing as the intro tactic but is capable of
  recursing into the definitions of nested structures

- ⟨,⟩ : syntactic sugar for And. One can write ⟨hp, hq⟩ rather than And.intro hp hq, and
  rintro ⟨hp, hq⟩ automatically breaks some hypothesis h : P ∧ Q into hp := P and hq := Q.

- (|) : syntactic sugar for Or. rintro (hp | hq) breaks some hypothesis h : P ∨ Q into hp := P
  and hq := Q, and splits the tactic state into two cases: case Or.inl with hp and case Or.inr
  with hq.

- left : tactic for breaking Or.elim into two cases

- right : tactic for breaking Or.elim into two cases

- constructor : generic tactic for breaking some type into its first constructor. For a goal
  of the type P ∧ Q, "constructor" behaves identically to "apply And.intro." For a goal of the
  type P ∨ Q, 'constructor" behaves identically to "apply Or.inl."

- have : tactic for building a subproof within the context of a larger proof. For any proposition
  P, one can write "have hP : P := by {sorry}" and within the block enclosed by curly brackets,
  the new goal is P but all the hypotheses from the previous tactic state are still accessible.
  Then after the brackets, hp : P is added to the list of hypotheses. Functionally, this tactic
  facilitates breaking a large proof into manageable steps contained within smaller blocks.

- show : tactic for rewriting the goal as something definitionally equivalent. This is often used
  in MIL as an explicit clarification of the present goals of a proof without needing to peek at
  the Lean infoview.

- rcases : short for recursive cases, this tactic breaks some connective type like Or whose elim
  rule has multiple Prop arguments into multiple individual goals.

- use : this tactic can be used to decompose a goal of the form P ∧ Q by providing an immediate proof of P.
  The remaining goal will just be Q.

- contradiction : this tactic searches through the list of hypothesis for two which are trivially
  contradictory, then completes the main goal if it finds any.

- <;> : This symbol is a tactic combinator; any tactic block following this symbol will be executed
  on each goal and subgoal.

- fun ↦ : This is the formal proof term language Lean uses that we have thus far used "intro" and
  "apply" to abstract away from.

- contrapose! : This tactic replaces a goal of the type (P → Q) with its contrapositive (¬Q → ¬P)

- rfl : short for reflexivity, this tactic attempts resolves goals which consist of showing
  two terms are equal by unpacking the definitions of each. If the two terms are definitionally
  equal, then "rfl" will close out the goal.

Now that you have the resources to make sense of the tactics used in MIL, read chapter 4
sections 4.1 and 4.2 in Math in Lean. In the next section I will present a minimal set of
problems from MIL and elsewhere to practice Set and Function proofs, so there's no need to
complete all the exercises prescribed by MIL chapter 4.
https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf

-/
