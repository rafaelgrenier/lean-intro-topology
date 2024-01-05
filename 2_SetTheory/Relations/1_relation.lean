/-

# Relations and Typeclasses

In Type theory, a relation on a type α is a function r : α → α → Prop.
From this bare definition, there are lots of properties in a relation
one might investigate: transitivity, symmetry, reflexivity, totality, etc.

This multiplicity of properties and the interesting math that follows from their
interactions actually poses a problem to formalization. If some theorem follows from
a relation having 10 such properties, should each property be individually passed as
a hypothesis? If so, ring theory and field theory will be nightmares to formalize.
So what if instead these combinations of properties are packaged together into a
single hypothesis?

Lean has "typeclasses" to solve this problem.
-/
