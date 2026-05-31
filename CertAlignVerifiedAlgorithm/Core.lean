inductive Base where
  | A
  | C
  | G
  | T
  deriving DecidableEq, Repr

abbrev DNA := List Base

inductive Step where
  | diag
  | del
  | ins
  deriving DecidableEq, Repr

abbrev Path := List Step

structure Scoring where
  subst : Base -> Base -> Nat
  ins : Base -> Nat
  del : Base -> Nat

def editScoring : Scoring where
  subst a b := if a == b then 0 else 1
  ins _ := 1
  del _ := 1

def Step.dx : Step -> Nat
  | .diag => 1
  | .del => 1
  | .ins => 0

def Step.dy : Step -> Nat
  | .diag => 1
  | .del => 0
  | .ins => 1

def Path.dx : Path -> Nat
  | [] => 0
  | s :: rest => s.dx + Path.dx rest

def Path.dy : Path -> Nat
  | [] => 0
  | s :: rest => s.dy + Path.dy rest

def ValidPath (x y : DNA) (p : Path) : Prop :=
  Path.dx p = x.length ∧ Path.dy p = y.length

def Cost? (S : Scoring) : DNA -> DNA -> Path -> Option Nat
  | [], [], [] => some 0
  | a :: xs, b :: ys, .diag :: rest =>
      match Cost? S xs ys rest with
      | some c => some (S.subst a b + c)
      | none => none
  | a :: xs, y, .del :: rest =>
      match Cost? S xs y rest with
      | some c => some (S.del a + c)
      | none => none
  | x, b :: ys, .ins :: rest =>
      match Cost? S x ys rest with
      | some c => some (S.ins b + c)
      | none => none
  | _, _, _ => none

def PathCostLe (S : Scoring) (x y : DNA) (p q : Path) : Prop :=
  ∀ cp cq, Cost? S x y p = some cp -> Cost? S x y q = some cq -> cp ≤ cq

def IsOptimalAlignment (S : Scoring) (x y : DNA) (p : Path) : Prop :=
  ValidPath x y p ∧ ∀ q : Path, ValidPath x y q -> PathCostLe S x y p q
