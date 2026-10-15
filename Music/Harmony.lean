/-! Tonal harmony from a generative core, checked by `decide` in core Lean (no Mathlib).
Pitch classes are `Fin 12`; the major scale is an interval pattern; triads stack alternate degrees.
The triad qualities below are derived from those definitions, never stated as facts. -/
namespace Music

abbrev PC := Fin 12
def semis (n : Nat) (x : PC) : PC := x + Fin.ofNat n   -- n semitones up (mod 12)
def fifth := semis 7
def fourth := semis 5
def fifths (n : Nat) (x : PC) : PC := semis (7 * n) x

/-- The circle of fifths: from any note, twelve fifths visit all twelve pitch classes, then return. -/
theorem circle (x : PC) : ((List.range 12).map (fifths · x)).Nodup ∧ fifths 12 x = x := by
  revert x; decide

/-- A fourth undoes a fifth, yet they are different operations. -/
theorem fourth_inverts_fifth : (∀ x, fourth (fifth x) = x) ∧ fifth ≠ fourth := by
  refine ⟨by decide, fun h => absurd (congrFun h 0) (by decide)⟩

/-- n fifth-steps as a semitone offset: 3 → 9 (major sixth), 4 → 4 (major third), 6 → 6 (tritone), 9 → 3 (minor third). -/
theorem fifth_steps : [3, 4, 6, 9].map (fun n => fifths n 0) = [9, 4, 6, 3] := by decide

def major : List Nat := [0, 2, 4, 5, 7, 9, 11]
/-- Degree i (0-based, wrapping) of the major scale on tonic k. -/
def degree (k : PC) (i : Nat) : PC := semis (major.getD (i % 7) 0) k
/-- The triad on degree i: degrees i, i+2, i+4. -/
def triad (k : PC) (i : Nat) : List PC := [degree k i, degree k (i + 2), degree k (i + 4)]

inductive Quality | maj | min | dim | aug | other
  deriving DecidableEq, Repr
open Quality

/-- Quality from the two intervals above the root, in semitones. -/
def quality : List PC → Quality
  | [r, t, f] => match (t - r).val, (f - r).val with
    | 4, 7 => maj | 3, 7 => min | 3, 6 => dim | 4, 8 => aug | _, _ => other
  | _ => other

/-- I ii iii IV V vi vii°, derived, in every one of the twelve major keys. -/
theorem roman_numerals (k : PC) : (List.range 7).map (quality ∘ triad k) = [maj, min, min, maj, maj, min, dim] := by
  revert k; decide

/-- Pitch classes alone don't fix the tonic: C major and A natural minor (the major pattern from degree 6) share
their notes, so the same collection supports two tonal readings. -/
theorem relative_minor : ∀ x : PC, x ∈ (List.range 7).map (degree 0) ↔ x ∈ (List.range 7).map (degree 0 ∘ (· + 5)) := by
  decide

end Music
