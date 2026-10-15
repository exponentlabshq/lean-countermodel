import Checker
/-! Boundary cases from peer review: the bounded semantics alone accepts invalid models and ill-formed formulas;
`Model.valid` and `Fm.wf` must reject them, so no certificate can be built from them. Each line is kernel-checked. -/
open CM

/-- Domain {0}, but the constant 0 is interpreted as 1: outside the domain. -/
def Out : Model := { n := 1, const := fun _ => 1, fn := fun _ _ => 0, pred := fun _ _ => false }
/-- The reviewer's example, `∀ x, x ≠ c`: unsatisfiable in any structure containing `c`. -/
def allNeC : Fm := .all (.not (.eq (.var 0) (.const 0)))
-- The gap: the bounded evaluator alone accepts it ...
example : allNeC.check Out [] = true := by decide
-- ... but the formula is not well formed in `Out` (the constant is out of range), so `Good` cannot hold.
example : allNeC.wf Out [] 0 = false := by decide

/-- An empty domain: `∀ x, ⊥` is vacuously true under bounded quantifiers, but the model is not valid. -/
def EmptyDomain : Model := { n := 0, const := fun _ => 0, fn := fun _ _ => 0, pred := fun _ _ => false }
example : (Fm.all .fls).check EmptyDomain [] = true := by decide
example : EmptyDomain.valid [] = false := by decide

/-- A function that leaves the domain {0, 1}: not valid. -/
def Leaks : Model := { n := 2, const := fun _ => 0, fn := fun _ _ => 2, pred := fun _ _ => false }
example : Leaks.valid [(0, 1)] = false := by decide

/-- A variable with no binder is not well formed (it would silently read as 0). -/
example : (Fm.eq (.var 3) (.var 3)).wf Out [] 0 = false := by decide
/-- A function used at an arity that `valid` never checked is not well formed. -/
example : (Fm.all (.eq (.app 0 [.var 0, .var 0]) (.var 0))).wf Out [(0, 1)] 0 = false := by decide

/-- Documented behaviour, not general truncation detection: too little fuel decodes to ⊥, which is never `Good`.
    Truncated or miscounted token streams are not detected by the decoder in general (paper §4.3). -/
example : ((decode 131145 4 1 1).map (· matches .fls)) = [true] := by decide
example : (decode 131145 4 1 1).all (fun φ => φ.wf Out [] 0 && φ.check Out []) = false := by decide
/-- The same token stream with enough fuel decodes to `∀ x, ¬ r(x, x)`. -/
example : ((decode 131145 4 1 11).map (· matches .all (.not (.atom 0 [.var 0, .var 0])))) = [true] := by decide
