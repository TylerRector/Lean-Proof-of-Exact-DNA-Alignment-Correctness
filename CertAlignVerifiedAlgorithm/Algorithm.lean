import CertAlignVerifiedAlgorithm.Core

def ed (S : Scoring) : DNA -> DNA -> Nat
  | [], [] => 0
  | [], b :: ys => S.ins b + ed S [] ys
  | a :: xs, [] => S.del a + ed S xs []
  | a :: xs, b :: ys =>
      min
        (S.subst a b + ed S xs ys)
        (min
          (S.del a + ed S xs (b :: ys))
          (S.ins b + ed S (a :: xs) ys))
termination_by x y => x.length + y.length

def align (S : Scoring) : DNA -> DNA -> Path
  | [], [] => []
  | [], _ :: ys => .ins :: align S [] ys
  | _ :: xs, [] => .del :: align S xs []
  | a :: xs, b :: ys =>
      let diagCost := S.subst a b + ed S xs ys
      let delCost := S.del a + ed S xs (b :: ys)
      let insCost := S.ins b + ed S (a :: xs) ys
      if diagCost ≤ delCost ∧ diagCost ≤ insCost then
        .diag :: align S xs ys
      else if delCost ≤ insCost then
        .del :: align S xs (b :: ys)
      else
        .ins :: align S (a :: xs) ys
termination_by x y => x.length + y.length

theorem align_valid (S : Scoring) : ∀ x y : DNA, ValidPath x y (align S x y) := by
  intro x
  induction x with
  | nil =>
      intro y
      induction y with
      | nil =>
          simp [ValidPath, align, Path.dx, Path.dy]
      | cons b ys ih =>
          obtain ⟨hx, hy⟩ := ih
          exact ⟨by simpa [align, Path.dx, Step.dx] using hx,
            by simp [align, Path.dy, Step.dy, hy]; omega⟩
  | cons a xs ihx =>
      intro y
      induction y with
      | nil =>
          obtain ⟨hx, hy⟩ := ihx []
          exact ⟨by simp [align, Path.dx, Step.dx, hx]; omega,
            by simpa [align, Path.dy, Step.dy] using hy⟩
      | cons b ys ihy =>
          by_cases hdiag :
            S.subst a b + ed S xs ys ≤ S.del a + ed S xs (b :: ys) ∧
              S.subst a b + ed S xs ys ≤ S.ins b + ed S (a :: xs) ys
          · obtain ⟨hx, hy⟩ := ihx ys
            exact ⟨by simp [align, hdiag, Path.dx, Step.dx, hx]; omega,
              by simp [align, hdiag, Path.dy, Step.dy, hy]; omega⟩
          · by_cases hdel : S.del a + ed S xs (b :: ys) ≤ S.ins b + ed S (a :: xs) ys
            · obtain ⟨hx, hy⟩ := ihx (b :: ys)
              exact ⟨by simp [align, hdiag, hdel, Path.dx, Step.dx, hx]; omega,
                by simpa [align, hdiag, hdel, Path.dy, Step.dy] using hy⟩
            · obtain ⟨hx, hy⟩ := ihy
              exact ⟨by simpa [align, hdiag, hdel, Path.dx, Step.dx] using hx,
                by simp [align, hdiag, hdel, Path.dy, Step.dy, hy]; omega⟩

theorem align_cost (S : Scoring) : ∀ x y : DNA, Cost? S x y (align S x y) = some (ed S x y) := by
  intro x
  induction x with
  | nil =>
      intro y
      induction y with
      | nil =>
          simp [align, Cost?, ed]
      | cons b ys ih =>
          simp [align, Cost?, ed, ih]
  | cons a xs ihx =>
      intro y
      induction y with
      | nil =>
          simp [align, Cost?, ed, ihx]
      | cons b ys ihy =>
          by_cases hdiag :
            S.subst a b + ed S xs ys ≤ S.del a + ed S xs (b :: ys) ∧
              S.subst a b + ed S xs ys ≤ S.ins b + ed S (a :: xs) ys
          · have ih := ihx ys
            simp [align, Cost?, ed, hdiag, ih]
            omega
          · by_cases hdel : S.del a + ed S xs (b :: ys) ≤ S.ins b + ed S (a :: xs) ys
            · have ih := ihx (b :: ys)
              simp [align, Cost?, ed, hdiag, hdel, ih]
              omega
            · have ih := ihy
              simp [align, Cost?, ed, hdiag, hdel, ih]
              omega

theorem ed_lower_bound (S : Scoring) :
    ∀ p x y c, Cost? S x y p = some c -> ed S x y ≤ c := by
  intro p
  induction p with
  | nil =>
      intro x y c hcost
      cases x with
      | nil =>
          cases y with
          | nil =>
              simp [Cost?] at hcost
              subst c
              simp [ed]
          | cons b ys =>
              simp [Cost?] at hcost
      | cons a xs =>
          simp [Cost?] at hcost
  | cons step rest ih =>
      intro x y c hcost
      cases step with
      | diag =>
          cases x with
          | nil =>
              simp [Cost?] at hcost
          | cons a xs =>
              cases y with
              | nil =>
                  simp [Cost?] at hcost
              | cons b ys =>
                  cases hrest : Cost? S xs ys rest with
                  | none =>
                      simp [Cost?, hrest] at hcost
                  | some crest =>
                  simp [Cost?, hrest] at hcost
                  subst c
                  have hle := ih xs ys crest hrest
                  simp [ed]
                  omega
      | del =>
          cases x with
          | nil =>
              simp [Cost?] at hcost
          | cons a xs =>
              cases hrest : Cost? S xs y rest with
              | none =>
                  simp [Cost?, hrest] at hcost
              | some crest =>
              simp [Cost?, hrest] at hcost
              subst c
              have hle := ih xs y crest hrest
              cases y with
              | nil =>
                  simp [ed]
                  omega
              | cons b ys =>
                  simp [ed]
                  omega
      | ins =>
          cases y with
          | nil =>
              simp [Cost?] at hcost
          | cons b ys =>
              cases hrest : Cost? S x ys rest with
              | none =>
                  simp [Cost?, hrest] at hcost
              | some crest =>
              simp [Cost?, hrest] at hcost
              subst c
              have hle := ih x ys crest hrest
              cases x with
              | nil =>
                  simp [ed]
                  omega
              | cons a xs =>
                  simp [ed]
                  omega

theorem align_optimal (S : Scoring) (x y : DNA) :
    IsOptimalAlignment S x y (align S x y) := by
  constructor
  · exact align_valid S x y
  · intro q hq cp cq hp hqcost
    have hp' := align_cost S x y
    have hcp : cp = ed S x y := Option.some.inj (hp.symm.trans hp')
    have hlb := ed_lower_bound S q x y cq hqcost
    rw [hcp]
    exact hlb
