/-! A verified checker for finite first-order models.

`Fm.Sem` is ordinary Tarski semantics over the elements `0 … n-1`; `Fm.check` is a Boolean evaluator for it.
`check_iff` proves them equivalent once, so a certificate is one kernel evaluation of `check` rather than one
elaborated proposition per formula. -/
namespace CM

/-- Terms: variables (de Bruijn indices), constants and function applications, as data. -/
inductive Tm where
  | var (i : Nat)
  | const (c : Nat)
  | app (f : Nat) (args : List Tm)
  deriving Repr

/-- First-order formulas, as data. -/
inductive Fm where
  | atom (p : Nat) (args : List Tm)
  | eq (a b : Tm)
  | tru
  | fls
  | not (φ : Fm)
  | and (φ ψ : Fm)
  | or (φ ψ : Fm)
  | imp (φ ψ : Fm)
  | iff (φ ψ : Fm)
  | all (φ : Fm)
  | ex (φ : Fm)
  deriving Repr

/-- A finite structure: elements `0 … n-1`, with tables for constants, functions and predicates. -/
structure Model where
  n : Nat
  const : Nat → Nat
  fn : Nat → List Nat → Nat
  pred : Nat → List Nat → Bool

mutual
/-- The value of a term, given values for its variables. -/
def Tm.val (M : Model) (env : List Nat) : Tm → Nat
  | .var i => env.getD i 0
  | .const c => M.const c
  | .app f args => M.fn f (Tm.vals M env args)
def Tm.vals (M : Model) (env : List Nat) : List Tm → List Nat
  | [] => []
  | t :: ts => t.val M env :: Tm.vals M env ts
end

/-- What a formula means in `M`: quantifiers range over the elements `0 … n-1`. -/
def Fm.Sem (M : Model) : List Nat → Fm → Prop
  | env, .atom p args => M.pred p (Tm.vals M env args) = true
  | env, .eq a b => a.val M env = b.val M env
  | _, .tru => True
  | _, .fls => False
  | env, .not φ => ¬ φ.Sem M env
  | env, .and φ ψ => φ.Sem M env ∧ ψ.Sem M env
  | env, .or φ ψ => φ.Sem M env ∨ ψ.Sem M env
  | env, .imp φ ψ => φ.Sem M env → ψ.Sem M env
  | env, .iff φ ψ => (φ.Sem M env ↔ ψ.Sem M env)
  | env, .all φ => ∀ x, x < M.n → φ.Sem M (x :: env)
  | env, .ex φ => ∃ x, x < M.n ∧ φ.Sem M (x :: env)

/-- A Boolean evaluator for `Sem`. It is lazy: `&&`, `||` and `List.all` stop at the first decisive value. -/
def Fm.check (M : Model) : List Nat → Fm → Bool
  | env, .atom p args => M.pred p (Tm.vals M env args)
  | env, .eq a b => a.val M env == b.val M env
  | _, .tru => true
  | _, .fls => false
  | env, .not φ => !φ.check M env
  | env, .and φ ψ => φ.check M env && ψ.check M env
  | env, .or φ ψ => φ.check M env || ψ.check M env
  | env, .imp φ ψ => !φ.check M env || ψ.check M env
  | env, .iff φ ψ => φ.check M env == ψ.check M env
  | env, .all φ => (List.range M.n).all fun x => φ.check M (x :: env)
  | env, .ex φ => (List.range M.n).any fun x => φ.check M (x :: env)

/-- Soundness and completeness, proved once for every formula. -/
theorem Fm.check_iff (M : Model) (φ : Fm) : ∀ env, φ.check M env = true ↔ φ.Sem M env := by
  induction φ with
  | atom => intro env; rfl
  | eq => intro env; simp [Fm.check, Fm.Sem]
  | tru => intro env; simp [Fm.check, Fm.Sem]
  | fls => intro env; simp [Fm.check, Fm.Sem]
  | not φ ih => intro env; simp [Fm.check, Fm.Sem, ← ih]
  | and φ ψ ihφ ihψ => intro env; simp [Fm.check, Fm.Sem, ← ihφ, ← ihψ]
  | or φ ψ ihφ ihψ => intro env; simp [Fm.check, Fm.Sem, ← ihφ, ← ihψ]
  | imp φ ψ ihφ ihψ => intro env; simp [Fm.check, Fm.Sem, ← ihφ, ← ihψ]; cases φ.check M env <;> simp
  | iff φ ψ ihφ ihψ => intro env; simp [Fm.check, Fm.Sem, ← ihφ, ← ihψ]
  | all φ ih => intro env; simp [Fm.check, Fm.Sem, ← ih, List.all_eq_true, List.mem_range]
  | ex φ ih => intro env; simp [Fm.check, Fm.Sem, ← ih, List.any_eq_true, List.mem_range]

/-- Every formula of a problem holds in `M` (a conjecture appears negated). -/
def Holds (M : Model) (φs : List Fm) : Prop := ∀ φ ∈ φs, φ.Sem M []

/-- The one step every certificate uses: if the evaluator accepts every formula, they all hold. -/
theorem holds_of_check (M : Model) (φs : List Fm) (h : φs.all (·.check M []) = true) : Holds M φs := by
  intro φ hφ
  exact (Fm.check_iff M φ []).1 (List.all_eq_true.1 h φ hφ)

theorem holds_append {M : Model} {a b : List Fm} (ha : Holds M a) (hb : Holds M b) : Holds M (a ++ b) := by
  intro φ hφ
  rcases List.mem_append.1 hφ with h | h
  · exact ha φ h
  · exact hb φ h

/-- Read the `w`-bit field `i` of a packed table. -/
def get (packed i w : Nat) : Nat := (packed >>> (i * w)) % 2 ^ w

/-- The position of an argument tuple in a table over `n` elements. -/
def index (n : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => x + n * index n xs

/-! ## Compact certificates: formulas as a packed token stream

A block of formulas is one natural number: `w`-bit tokens in prefix order. Formulas:
`0 p k t₁…tₖ` atom, `1 t t` =, `2` ⊤, `3` ⊥, `4 φ` ¬, `5 φ ψ` ∧, `6` ∨, `7` →, `8` ↔, `9 φ` ∀, `10 φ` ∃.
Terms: `0 i` variable, `1 c` constant, `2 f k t₁…tₖ` application. `decode` is ordinary Lean code, so a
certificate's statement `Holds M (decode …)` can be printed and read with `#eval`. -/

mutual
/-- A term at token position `i`, with the position after it; `fuel` bounds the recursion. -/
def readTm (s w : Nat) : Nat → Nat → Option (Tm × Nat)
  | 0, _ => none
  | fuel + 1, i => match get s i w with
    | 0 => some (.var (get s (i + 1) w), i + 2)
    | 1 => some (.const (get s (i + 1) w), i + 2)
    | _ => (readTms s w fuel (get s (i + 2) w) (i + 3)).map fun (ts, j) => (.app (get s (i + 1) w) ts, j)
/-- `k` terms from position `i`. -/
def readTms (s w : Nat) : Nat → Nat → Nat → Option (List Tm × Nat)
  | 0, _, _ => none
  | _ + 1, 0, i => some ([], i)
  | fuel + 1, k + 1, i => (readTm s w fuel i).bind fun (t, j) =>
      (readTms s w fuel k j).map fun (ts, l) => (t :: ts, l)
end

/-- A formula at token position `i`, with the position after it. -/
def readFm (s w : Nat) : Nat → Nat → Option (Fm × Nat)
  | 0, _ => none
  | fuel + 1, i =>
    let two (mk : Fm → Fm → Fm) := (readFm s w fuel (i + 1)).bind fun (a, j) =>
      (readFm s w fuel j).map fun (b, l) => (mk a b, l)
    let one (mk : Fm → Fm) := (readFm s w fuel (i + 1)).map fun (a, j) => (mk a, j)
    match get s i w with
    | 0 => (readTms s w fuel (get s (i + 2) w) (i + 3)).map fun (ts, j) => (.atom (get s (i + 1) w) ts, j)
    | 1 => (readTm s w fuel (i + 1)).bind fun (a, j) => (readTm s w fuel j).map fun (b, l) => (.eq a b, l)
    | 2 => some (.tru, i + 1)
    | 3 => some (.fls, i + 1)
    | 4 => one .not
    | 5 => two .and
    | 6 => two .or
    | 7 => two .imp
    | 8 => two .iff
    | 9 => one .all
    | _ => one .ex

/-- `k` formulas from position `i`. -/
def readFms (s w fuel : Nat) : Nat → Nat → List Fm
  | 0, _ => []
  | k + 1, i => match readFm s w fuel i with
    | some (φ, j) => φ :: readFms s w fuel k j
    | none => [.fls]  -- malformed data decodes to ⊥, which can never be certified

/-- The `k` formulas packed in `s` with `w`-bit tokens, nested at most `depth` deep. The kernel's cost for these
structural recursions grows with the fuel, so the generator passes the true nesting depth, not the token count;
too little fuel decodes to `⊥`, which can never be certified. -/
def decode (s w k depth : Nat) : List Fm := readFms s w depth k 0

/-! ## Fact tables: ground literals as fixed-width records

Most of a large problem is often ground facts `p(c₁, …, cₖ)` or `¬p(c₁, …, cₖ)`. A fact table stores fact `i` as
`K + 2` fields of `w` bits: polarity (1 asserted, 0 denied), predicate, then `K` constant slots, of which the first
`ar p` are used. `fact` reads one record straight into a formula, so checking needs no general decoding. -/

/-- Fact `i` of a fact table, as a formula. -/
def fact (s w K : Nat) (ar : Nat → Nat) (i : Nat) : Fm :=
  let b := i * (K + 2)
  let p := get s (b + 1) w
  let a := (List.range (ar p)).map fun j => Tm.const (get s (b + 2 + j) w)
  if get s b w == 1 then .atom p a else .not (.atom p a)

/-- The `k` facts of a table. -/
def decodeFacts (s w K : Nat) (ar : Nat → Nat) (k : Nat) : List Fm := (List.range k).map (fact s w K ar)

theorem holds_facts (M : Model) (s w K : Nat) (ar : Nat → Nat) (k : Nat)
    (h : (List.range k).all (fun i => (fact s w K ar i).check M []) = true) : Holds M (decodeFacts s w K ar k) := by
  intro φ hφ
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hφ
  exact (Fm.check_iff M _ []).1 (List.all_eq_true.1 h i hi)

end CM
