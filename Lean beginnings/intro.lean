/-
# Intro To Lean

What's the difference between a proof and an argument?
Arguments offer some reason for the reader to believe the truth
of a claim, e.g.
"not all horses are red, that wouldn't make any sense." A proof,
unlike an argument, is irrefutable. Proofs are also built on concrete
foundations: the definitions and premises are all made explicit.
A proof of the claim "not all horses are red" might be an example of a green horse.
(Also a separate proof that a horse can't be red and green at the same time.)

Lean is a powerful tool for writing proofs, since Lean is a programming
language which will only be able to run if the proof is complete, with
no assumptions left unpacked. Without further ado, let's get into it!

-/

example (P : Prop) (ProofOfP : P) : P := by
  exact ProofOfP

/- 
Propositions, which Lean shortens to "Prop", are true-or-false statements.
The expression (P : Prop) means that P is a proposition, and the expression
(ProofOfP : P) means that "ProofOfP" is a proof of P being true.

In Lean, 'P → Q' means "if P is true, then Q is true." We can also think of
'P → Q' as a function which takes in a proof of P and results in a proof of Q.
This second notion is how Lean thinks of implications; if we want to construct a proof
of the proposition 'P → Q', then we need to show that any proof of P can be used to make
some proof of Q.

The proof I have written above is one of the simplest possible:
It asserts that P is a Prop, ProofOfP is some proof of it, and then says that its
possible to prove P using exactly ProofOfP. Lean's notation for examples and theorems places
all of its assumptions before the colon, then it gives the Proposition it wants to prove, and
then after that there's typically ":=" to begin the proof. The keyword "by" signifies that
a tactic proof is to follow.

What are tactics?

Tactics can be used when writing proofs to update the tactic state. The Lean Infoview that appears
on the screen when modifying a lean proof (Click right before "exact" in the proof above) 
displays all the hypotheses you have proofs of and list all the propositions
you are intending to prove. Below is a sample Lean infoview from the above proof:

1 goal
  P: Prop                   -This is the hypothesis that P is a prop
  ProofOfP: P               -This is the hypothesis that ProofOfP is a proof of P
  ⊢ P                       -This states the goal: prove P

The mix of hypotheses and goals at some point in your proof is called the tactic state,
and tactics are functions which move you from one tactic state to the next.

The three tactics we'll see first are "exact", "intro", and "apply".

If the current goal in the tactic state is in the form 'P → Q', then
"intro hP" would update the tactic state so that there's a new hypothesis
hP : P and a simplified goal ⊢ Q. "hP" is an arbitrary name here, but it follows
the convention of calling hypothesis "h" followed by something about the proposition.

If the current goal in the tactic state is Q and there is a hypothesis 'hPQ : P → Q',
then the tactic "apply hPQ" would change the goal to ⊢ Q.

If the current goal in the tactic state is P and there is a hypothesis 'hP : P',
then the tactic "exact hP" would complete the goal. When no goals are left,
the proof is complete.
-/

variable (P Q R : Prop) -- This means P, Q, and R will be propositions

example (madeUpName : P) (implication : P → Q) : Q := by
  apply implication
  exact madeUpName

example : P → P := by
  intro hP
  exact hP

example (hPQ : P → Q) (hQR : Q → R) : P → R := by
  intro hP
  apply hQR
  apply hPQ
  exact hP

-- try it out for yourself!

example : P → Q → P := by
  sorry

example : P → (P → Q) → Q := by
  sorry

-- and a tricky one

example : (P → Q) → ((P → Q) → P) → Q := by
  sorry

/- 
Before we end this file, there are two more ideas to introduce: True and False.
As a hypothesis, (h : True) is completely useless, since a proof of True always exists.
In Lean, the proof of "True" is the theorem "True.intro".
Rather than writing "exact True.intro" in your tactical proof, the tactic "trivial" exists
to do the exact same thing and save a handful of letters.
False, the opposite of True, instead has no means of being proven. However (h : False) is
the most powerful hypothesis, since anything can follow from a false premise.
(e.g. If the sky is neon green with polka dots, then I have solved all of mathematics.)
In Lean, (h : False) can be used with the theorem "False.elim," which states that
'False → P' for any proposition P.

Notice that True and False have these 'intro' and 'elim' theorems. As we introduce more
logical connectives, they will also have "intro" and "elim" theorems. An intro theorem is a 
theorem which proves the logical connective (in the case of True, there are no assumptions,
but generally there will be), and an elim theorem takes the logical connective as a hypothesis
to prove something else. 
-/

example : True := by
  apply True.intro

example : False → P := by
  intro hFalse
  apply False.elim
  exact hFalse