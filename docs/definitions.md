# Definitions

## What does this transformation do?

This transformation, at an atomic level, takes as an argument a Coq constant `c`. 
By delta-reduction, `c` is convertible to its definition `c_def`.
Thus, `get_def c` asserts and proves the propositional equality `H: c = c_def` in the Coq proof context.

## An example