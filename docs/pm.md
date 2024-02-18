# Elimination of pattern matching

## What does this transformation do?

This transformation `eliminate_dependent_pattern_matching`, takes as argument a hypothesis `H` whose type
is of the form :
```Coq
forall (x1: A1) ... (xn: An), 
C[match f xi1 ... xin with 
| c1 y11 ... y1j => g1 y11 ... y1j
... 
| ck yk1 ... ykj => gk yk1 ... ykj 
...
| cm ym1 ... ymj => gm ym1 ... ymj
]
```

where `C[_]` is a context.

The term `f xi1 ... xin` should be an inductive, of constructors `c1 ... cm`.

For each branch of the `match`, a new hypothesis `Hk` is created: 

```
Hk: forall x1 ... xn yk1 ... ykj, f xi1 ... xin = ck yk1 ... ykj -> 
        C[gk yk1 ... ykj]
```

There is a version of the transformation `elim_match_with_no_forall` which works on hypotheses where the 
`match` construction is not under any universal quantification. 

## An example
