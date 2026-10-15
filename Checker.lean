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

/-- `f x` for every `x < n`, counting down: no list is built, and the first `false` stops it. -/
def allBelow (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | k + 1 => f k && allBelow f k

/-- `f x` for some `x < n`, counting down and stopping at the first `true`. -/
def anyBelow (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | k + 1 => f k || anyBelow f k

theorem allBelow_iff (f : Nat → Bool) : ∀ n, allBelow f n = true ↔ ∀ x, x < n → f x = true
  | 0 => by simp [allBelow]
  | k + 1 => by
    simp only [allBelow, Bool.and_eq_true, allBelow_iff f k]
    exact ⟨fun ⟨h, hs⟩ x hx => (Nat.lt_succ_iff_lt_or_eq.1 hx).elim (hs x) (· ▸ h),
           fun h => ⟨h k (Nat.lt_succ_self k), fun x hx => h x (Nat.lt_succ_of_lt hx)⟩⟩

theorem anyBelow_iff (f : Nat → Bool) : ∀ n, anyBelow f n = true ↔ ∃ x, x < n ∧ f x = true
  | 0 => by simp [anyBelow]
  | k + 1 => by
    simp only [anyBelow, Bool.or_eq_true, anyBelow_iff f k]
    exact ⟨fun h => h.elim (fun h => ⟨k, Nat.lt_succ_self k, h⟩) (fun ⟨x, hx, h⟩ => ⟨x, Nat.lt_succ_of_lt hx, h⟩),
           fun ⟨x, hx, h⟩ => (Nat.lt_succ_iff_lt_or_eq.1 hx).elim (fun hx => .inr ⟨x, hx, h⟩) (fun e => .inl (e ▸ h))⟩

/-- A Boolean evaluator for `Sem`. It is lazy: `&&`, `||`, `allBelow` and `anyBelow` stop at the first decisive value. -/
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
  | env, .all φ => allBelow (fun x => φ.check M (x :: env)) M.n
  | env, .ex φ => anyBelow (fun x => φ.check M (x :: env)) M.n

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
  | all φ ih => intro env; simp [Fm.check, Fm.Sem, ← ih, allBelow_iff]
  | ex φ ih => intro env; simp [Fm.check, Fm.Sem, ← ih, anyBelow_iff]

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
structural recursions grows with the fuel, so the generator passes a small bound (each formula's own token count,
which bounds its nesting depth) rather than the whole block's token count; too little fuel decodes to `⊥`, which can
never be certified. -/
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


/-! ## Ordinary first-order semantics, and when the bounded semantics agrees with it -/

/-- An ordinary first-order structure: every symbol is interpreted inside the carrier `α`. -/
structure Structure (α : Type) where
  const : Nat → α
  fn : Nat → List α → α
  pred : Nat → List α → Prop

mutual
def Tm.interp {α : Type} (S : Structure α) (d : α) (env : List α) : Tm → α
  | .var i => env.getD i d
  | .const c => S.const c
  | .app f args => S.fn f (Tm.interps S d env args)
def Tm.interps {α : Type} (S : Structure α) (d : α) (env : List α) : List Tm → List α
  | [] => []
  | t :: ts => t.interp S d env :: Tm.interps S d env ts
end

/-- Ordinary satisfaction: quantifiers range over the whole carrier. -/
def Fm.Sat {α : Type} (S : Structure α) (d : α) : List α → Fm → Prop
  | env, .atom p args => S.pred p (Tm.interps S d env args)
  | env, .eq a b => a.interp S d env = b.interp S d env
  | _, .tru => True
  | _, .fls => False
  | env, .not φ => ¬ φ.Sat S d env
  | env, .and φ ψ => φ.Sat S d env ∧ ψ.Sat S d env
  | env, .or φ ψ => φ.Sat S d env ∨ ψ.Sat S d env
  | env, .imp φ ψ => φ.Sat S d env → ψ.Sat S d env
  | env, .iff φ ψ => (φ.Sat S d env ↔ ψ.Sat S d env)
  | env, .all φ => ∀ x : α, φ.Sat S d (x :: env)
  | env, .ex φ => ∃ x : α, φ.Sat S d (x :: env)

/-- Every argument tuple of length `k` over `0 … n-1` satisfies `f`. -/
def allTuples (n : Nat) (f : List Nat → Bool) : Nat → Bool
  | 0 => f []
  | k + 1 => allBelow (fun x => allTuples n (fun xs => f (x :: xs)) k) n

theorem allTuples_iff (n : Nat) : ∀ (k : Nat) (f : List Nat → Bool),
    allTuples n f k = true ↔ ∀ xs : List Nat, xs.length = k → (∀ x ∈ xs, x < n) → f xs = true
  | 0, f => by
    simp only [allTuples]
    exact ⟨fun h xs hl _ => by rw [List.length_eq_zero_iff.1 hl]; exact h, fun h => h [] rfl (by simp)⟩
  | k + 1, f => by
    simp only [allTuples, allBelow_iff, allTuples_iff n k]
    constructor
    · intro h xs hl hr
      match xs, hl with
      | x :: xs, hl => exact h x (hr x (by simp)) xs (by simpa using hl) (fun y hy => hr y (by simp [hy]))
    · intro h x hx xs hl hr
      exact h (x :: xs) (by simp [hl]) (fun y hy => by
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hx
        · exact hr y hy)

/-- A model is valid for the functions it is used with (`fns`: symbol and arity): its domain is non-empty and
each function maps in-range arguments to an in-range value. Constants are checked where they occur (`Fm.wf`). -/
def Model.valid (M : Model) (fns : List (Nat × Nat)) : Bool :=
  0 < M.n && fns.all fun (f, k) => allTuples M.n (fun xs => M.fn f xs < M.n) k

mutual
/-- A term is well formed at variable depth `d`: variables are bound, constants are in range, and each function
is applied at an arity listed in `fns`. -/
def Tm.wf (M : Model) (fns : List (Nat × Nat)) (d : Nat) : Tm → Bool
  | .var i => i < d
  | .const c => M.const c < M.n
  | .app f args => (fns.contains (f, args.length)) && Tm.wfs M fns d args
def Tm.wfs (M : Model) (fns : List (Nat × Nat)) (d : Nat) : List Tm → Bool
  | [] => true
  | t :: ts => t.wf M fns d && Tm.wfs M fns d ts
end

/-- A formula is well formed at depth `d`: every term in it is. `d = 0` means the formula is closed. -/
def Fm.wf (M : Model) (fns : List (Nat × Nat)) : Nat → Fm → Bool
  | d, .atom _ args => Tm.wfs M fns d args
  | d, .eq a b => a.wf M fns d && b.wf M fns d
  | _, .tru => true
  | _, .fls => true
  | d, .not φ => φ.wf M fns d
  | d, .and φ ψ => φ.wf M fns d && ψ.wf M fns d
  | d, .or φ ψ => φ.wf M fns d && ψ.wf M fns d
  | d, .imp φ ψ => φ.wf M fns d && ψ.wf M fns d
  | d, .iff φ ψ => φ.wf M fns d && ψ.wf M fns d
  | d, .all φ => φ.wf M fns (d + 1)
  | d, .ex φ => φ.wf M fns (d + 1)

theorem Model.valid_pos {M : Model} {fns : List (Nat × Nat)} (h : M.valid fns = true) : 0 < M.n := by
  simp only [Model.valid, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1

theorem Model.valid_fn {M : Model} {fns : List (Nat × Nat)} (h : M.valid fns = true) {f k : Nat}
    (hf : fns.contains (f, k) = true) (xs : List Nat) (hl : xs.length = k) (hr : ∀ x ∈ xs, x < M.n) :
    M.fn f xs < M.n := by
  simp only [Model.valid, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 (f, k) (by simpa using hf)
  exact of_decide_eq_true ((allTuples_iff M.n k _).1 this xs hl hr)

/-- The ordinary structure a model with a non-empty domain describes, on the carrier `Fin M.n`. Values are clipped
into the domain; for a valid model and well-formed formulas, clipping never changes a value (`val_interp`). -/
def Model.toStructure (M : Model) (h : 0 < M.n) : Structure (Fin M.n) where
  const c := ⟨min (M.const c) (M.n - 1), Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt h Nat.one_pos)⟩
  fn f xs := ⟨min (M.fn f (xs.map Fin.val)) (M.n - 1), Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt h Nat.one_pos)⟩
  pred p xs := M.pred p (xs.map Fin.val) = true

theorem min_pred_self {a n : Nat} (h : a < n) : min a (n - 1) = a := Nat.min_eq_left (by omega)

theorem getD_map_val {n : Nat} (d : Fin n) : ∀ (env : List (Fin n)) (i : Nat), i < env.length →
    (env.map Fin.val).getD i 0 = (env.getD i d).val
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: env, i + 1, h => getD_map_val d env i (Nat.lt_of_succ_lt_succ h)

theorem interps_length {α : Type} (S : Structure α) (d : α) (env : List α) :
    ∀ ts : List Tm, (Tm.interps S d env ts).length = ts.length
  | [] => rfl
  | _ :: ts => by simp [Tm.interps, interps_length S d env ts]

mutual
/-- For a valid model and a well-formed term, the bounded value is the ordinary value. -/
theorem val_interp (M : Model) (fns : List (Nat × Nat)) (hv : M.valid fns = true) (env : List (Fin M.n))
    (d : Fin M.n) : ∀ t : Tm, t.wf M fns env.length = true →
    t.val M (env.map Fin.val) = (t.interp (M.toStructure (Model.valid_pos hv)) d env).val
  | .var i, h => by
    simp only [Tm.wf, decide_eq_true_eq] at h
    simp only [Tm.val, Tm.interp]; exact getD_map_val d env i h
  | .const c, h => by
    simp only [Tm.wf, decide_eq_true_eq] at h
    simp only [Tm.val, Tm.interp, Model.toStructure]; exact (min_pred_self h).symm
  | .app f args, h => by
    simp only [Tm.wf, Bool.and_eq_true] at h
    have ih := vals_interps M fns hv env d args h.2
    simp only [Tm.val, Tm.interp, Model.toStructure, ih]
    refine (min_pred_self (Model.valid_fn hv h.1 _ ?_ ?_)).symm
    · simp [interps_length]
    · intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; exact y.isLt
theorem vals_interps (M : Model) (fns : List (Nat × Nat)) (hv : M.valid fns = true) (env : List (Fin M.n))
    (d : Fin M.n) : ∀ ts : List Tm, Tm.wfs M fns env.length ts = true →
    Tm.vals M (env.map Fin.val) ts = (Tm.interps (M.toStructure (Model.valid_pos hv)) d env ts).map Fin.val
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Tm.wfs, Bool.and_eq_true] at h
    simp only [Tm.vals, Tm.interps, List.map_cons, val_interp M fns hv env d t h.1, vals_interps M fns hv env d ts h.2]
end

/-- **The bounded semantics is ordinary first-order semantics** for a valid model and a well-formed formula:
`Sem` with quantifiers over `x < n` holds exactly when ordinary satisfaction holds in the structure on `Fin n`. -/
theorem sem_iff_sat (M : Model) (fns : List (Nat × Nat)) (hv : M.valid fns = true) (d : Fin M.n) (φ : Fm) :
    ∀ env : List (Fin M.n), φ.wf M fns env.length = true →
    (φ.Sem M (env.map Fin.val) ↔ φ.Sat (M.toStructure (Model.valid_pos hv)) d env) := by
  induction φ with
  | atom p args =>
    intro env h; simp only [Fm.wf] at h
    simp only [Fm.Sem, Fm.Sat, Model.toStructure, vals_interps M fns hv env d args h]
  | eq a b =>
    intro env h; simp only [Fm.wf, Bool.and_eq_true] at h
    simp only [Fm.Sem, Fm.Sat, val_interp M fns hv env d a h.1, val_interp M fns hv env d b h.2, Fin.val_inj]
  | tru => intro env _; exact Iff.rfl
  | fls => intro env _; exact Iff.rfl
  | not φ ih => intro env h; simp only [Fm.wf] at h; simp only [Fm.Sem, Fm.Sat, ih env h]
  | and φ ψ ihφ ihψ => intro env h; simp only [Fm.wf, Bool.and_eq_true] at h; simp only [Fm.Sem, Fm.Sat, ihφ env h.1, ihψ env h.2]
  | or φ ψ ihφ ihψ => intro env h; simp only [Fm.wf, Bool.and_eq_true] at h; simp only [Fm.Sem, Fm.Sat, ihφ env h.1, ihψ env h.2]
  | imp φ ψ ihφ ihψ => intro env h; simp only [Fm.wf, Bool.and_eq_true] at h; simp only [Fm.Sem, Fm.Sat, ihφ env h.1, ihψ env h.2]
  | iff φ ψ ihφ ihψ => intro env h; simp only [Fm.wf, Bool.and_eq_true] at h; simp only [Fm.Sem, Fm.Sat, ihφ env h.1, ihψ env h.2]
  | all φ ih =>
    intro env h; simp only [Fm.wf] at h
    simp only [Fm.Sem, Fm.Sat]
    constructor
    · intro hs x; exact (ih (x :: env) (by simpa using h)).1 (by simpa using hs x.val x.isLt)
    · intro hs x hx; exact by simpa using (ih (⟨x, hx⟩ :: env) (by simpa using h)).2 (hs ⟨x, hx⟩)
  | ex φ ih =>
    intro env h; simp only [Fm.wf] at h
    simp only [Fm.Sem, Fm.Sat]
    constructor
    · rintro ⟨x, hx, hs⟩; exact ⟨⟨x, hx⟩, (ih (⟨x, hx⟩ :: env) (by simpa using h)).1 (by simpa using hs)⟩
    · rintro ⟨x, hs⟩; exact ⟨x.val, x.isLt, by simpa using (ih (x :: env) (by simpa using h)).2 hs⟩

/-- **What a certificate establishes.** If the model is valid, every formula is closed and well formed, and the
evaluator accepts them all, then the ordinary structure on `Fin M.n` satisfies every formula of the problem. -/
theorem certified (M : Model) (fns : List (Nat × Nat)) (φs : List Fm) (hv : M.valid fns = true)
    (hw : φs.all (·.wf M fns 0) = true) (hh : Holds M φs) (d : Fin M.n) :
    ∀ φ ∈ φs, φ.Sat (M.toStructure (Model.valid_pos hv)) d [] := by
  intro φ hφ
  exact (sem_iff_sat M fns hv d φ [] (List.all_eq_true.1 hw φ hφ)).1 (hh φ hφ)


/-! ## What a certificate proves

A block is checked in one pass for well-formedness and truth. `Good` collects both; `countermodel_of_good` turns a
valid model and a `Good` problem into ordinary first-order satisfaction (`certified`). -/

/-- Every formula is closed and well formed, and holds in `M`. -/
def Good (M : Model) (fns : List (Nat × Nat)) (φs : List Fm) : Prop := φs.all (·.wf M fns 0) = true ∧ Holds M φs

theorem good_of_check (M : Model) (fns : List (Nat × Nat)) (φs : List Fm)
    (h : φs.all (fun φ => φ.wf M fns 0 && φ.check M []) = true) : Good M fns φs := by
  refine ⟨List.all_eq_true.2 fun φ hφ => ?_, fun φ hφ => ?_⟩
  · have := List.all_eq_true.1 h φ hφ; simp only [Bool.and_eq_true] at this; exact this.1
  · have := List.all_eq_true.1 h φ hφ; simp only [Bool.and_eq_true] at this
    exact (Fm.check_iff M φ []).1 this.2

theorem good_facts (M : Model) (fns : List (Nat × Nat)) (s w K : Nat) (ar : Nat → Nat) (k : Nat)
    (h : (List.range k).all (fun i => (fact s w K ar i).wf M fns 0 && (fact s w K ar i).check M []) = true) :
    Good M fns (decodeFacts s w K ar k) := by
  apply good_of_check
  simp only [decodeFacts, List.all_map]
  exact h

theorem good_append {M : Model} {fns : List (Nat × Nat)} {a b : List Fm} (ha : Good M fns a) (hb : Good M fns b) :
    Good M fns (a ++ b) :=
  ⟨by simp only [List.all_append, Bool.and_eq_true]; exact ⟨ha.1, hb.1⟩, holds_append ha.2 hb.2⟩

/-- **The certificate's conclusion**: the ordinary structure on `Fin M.n` satisfies every formula. -/
theorem countermodel_of_good (M : Model) (fns : List (Nat × Nat)) (φs : List Fm) (hv : M.valid fns = true)
    (hg : Good M fns φs) : ∀ φ ∈ φs, φ.Sat (M.toStructure (Model.valid_pos hv)) ⟨0, Model.valid_pos hv⟩ [] :=
  fun φ hφ => certified M fns φs hv hg.1 hg.2 _ φ hφ

end CM
