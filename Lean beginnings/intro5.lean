/-
# Sets and Functions in Lean (Pt. 1: Tactics)

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
