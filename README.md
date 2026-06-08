A Lean 4 proof of exact global DNA alignment correctness.

The project formalizes the edit-grid model of alignment, defines a recursive edit-distance value, constructs a traceback path, and proves that the path is globally optimal.

```lean
theorem align_optimal (S : Scoring) (x y : DNA) :
    IsOptimalAlignment S x y (align S x y)
```

## Mathematical core

DNA strings are lists over four bases:

```lean
inductive Base where
  | A | C | G | T
```

An alignment is a monotone path through the edit grid:

```text
diag : (i,j) -> (i+1,j+1)
del  : (i,j) -> (i+1,j)
ins  : (i,j) -> (i,j+1)
```

A path is valid when it consumes both strings exactly:

```lean
Path.dx p = x.length
Path.dy p = y.length
```

A scoring function assigns natural-number costs:

```lean
subst : Base -> Base -> Nat
ins   : Base -> Nat
del   : Base -> Nat
```

The recursive edit-distance value is the usual minimum over the three possible first moves:

```text
ed(a :: xs, b :: ys) =
  min(
    subst(a,b) + ed(xs, ys),
    del(a)    + ed(xs, b :: ys),
    ins(b)    + ed(a :: xs, ys)
  )
```

The algorithm `align` chooses a first move attaining this minimum and recurses.

## Proof structure

The final theorem follows from three lemmas:

```lean
align_valid :
  ValidPath x y (align S x y)

align_cost :
  Cost? S x y (align S x y) = some (ed S x y)

ed_lower_bound :
  Cost? S x y p = some c -> ed S x y ≤ c
```

Thus:

```text
constructed path has cost ed
every cost-defined path has cost at least ed
therefore the constructed path is optimal
```

## Lineage

This is the classical dynamic-programming model behind exact global sequence alignment and edit distance. This project is a machine-checked proof of the recurrence, traceback, path cost, and optimality theorem.

- Needleman–Wunsch global sequence alignment  
  <https://pubmed.ncbi.nlm.nih.gov/5420325/>

- Wagner–Fischer string edit distance  
  <https://dl.acm.org/doi/10.1145/321796.321811>

## Verification

Reported axiom dependencies for the main theorem:

```text
[propext, Classical.choice, Quot.sound]
```

The development uses no `sorry`, `admit`, `axiom`, `native_decide`, or Mathlib.
