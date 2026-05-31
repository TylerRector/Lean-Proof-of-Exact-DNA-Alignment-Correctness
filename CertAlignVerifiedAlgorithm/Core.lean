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

/-- `p` is an alignment path from the start of `x` to the end of `y`. -/
def ValidPath (x y : DNA) (p : Path) : Prop :=
  Path.dx p = x.length ∧ Path.dy p = y.length

/-- Evaluates a path cost, returning `none` when a step leaves the grid. -/
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

/-- A valid path always has a defined cost. -/
theorem validPath_cost_defined
    (S : Scoring) :
    ∀ x y p, ValidPath x y p -> ∃ c, Cost? S x y p = some c := by
  intro x y p
  induction p generalizing x y with
  | nil =>
      intro hvalid
      cases x with
      | nil =>
          cases y with
          | nil =>
              exact ⟨0, rfl⟩
          | cons b ys =>
              simp [ValidPath, Path.dx, Path.dy] at hvalid
      | cons a xs =>
          simp [ValidPath, Path.dx, Path.dy] at hvalid
  | cons step rest ih =>
      intro hvalid
      cases step with
      | diag =>
          cases x with
          | nil =>
              simp [ValidPath, Path.dx, Path.dy, Step.dx] at hvalid
          | cons a xs =>
              cases y with
              | nil =>
                  simp [ValidPath, Path.dx, Path.dy, Step.dy] at hvalid
              | cons b ys =>
                  have htail : ValidPath xs ys rest := by
                    unfold ValidPath at hvalid ⊢
                    simp [Path.dx, Path.dy, Step.dx, Step.dy] at hvalid
                    omega
                  obtain ⟨c, hc⟩ := ih xs ys htail
                  exact ⟨S.subst a b + c, by simp [Cost?, hc]⟩
      | del =>
          cases x with
          | nil =>
              simp [ValidPath, Path.dx, Step.dx] at hvalid
          | cons a xs =>
              have htail : ValidPath xs y rest := by
                unfold ValidPath at hvalid ⊢
                simp [Path.dx, Path.dy, Step.dx, Step.dy] at hvalid
                omega
              obtain ⟨c, hc⟩ := ih xs y htail
              exact ⟨S.del a + c, by simp [Cost?, hc]⟩
      | ins =>
          cases y with
          | nil =>
              simp [ValidPath, Path.dy, Step.dy] at hvalid
          | cons b ys =>
              have htail : ValidPath x ys rest := by
                unfold ValidPath at hvalid ⊢
                simp [Path.dx, Path.dy, Step.dx, Step.dy] at hvalid
                omega
              obtain ⟨c, hc⟩ := ih x ys htail
              exact ⟨S.ins b + c, by simp [Cost?, hc]⟩

/-- `p` and `q` have defined costs, and `p` costs no more than `q`. -/
def PathCostLe (S : Scoring) (x y : DNA) (p q : Path) : Prop :=
  ∃ cp cq,
    Cost? S x y p = some cp ∧
    Cost? S x y q = some cq ∧
    cp ≤ cq

/-- `p` is valid, has a defined cost, and is minimal among valid paths. -/
def IsOptimalAlignment (S : Scoring) (x y : DNA) (p : Path) : Prop :=
  ValidPath x y p ∧
    (∃ cp, Cost? S x y p = some cp) ∧
    ∀ q : Path, ValidPath x y q -> PathCostLe S x y p q

theorem invalid_diag_not_optimal (S : Scoring) :
    ¬ IsOptimalAlignment S [] [] [.diag] := by
  intro h
  have hvalid := h.1
  simp [ValidPath, Path.dx, Path.dy, Step.dx] at hvalid

theorem undefined_cost_not_le_empty (S : Scoring) :
    ¬ PathCostLe S [] [] [.diag] [] := by
  intro h
  obtain ⟨cp, cq, hp, hq, hle⟩ := h
  simp [Cost?] at hp
