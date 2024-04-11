# Anonymous functions

This transformation is defined in the file `theories/anonymous_functions.v`.

## What does this transformation do?

This transformation takes an anonymous function in the local context
of the form `fun (x: T) => ...`, creates a definition `f := fun (x: T) => ...`
and folds the definition of `f`.

## An example

