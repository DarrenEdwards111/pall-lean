import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATPlusTwo

/-!
# Three disjoint gadgets in the codec: the `+3` substrate

Brick 1 of the multi-wire (`k = 2`) campaign.  The three-gadget formula — unit
clauses on `x₀`, `x₁`, `x₂` — embeds THREE disjoint `AllEqual₃` gadgets in one
73-bit codec word (signs at `15,21,27`, `34,41,48`, `56,64,72`):

* **`encodeVar'_two` (proved)** — `x₂`'s coordinate encoding;
* **`se3_concrete` (proved)** — the exact 73-bit word;
* **`SATLang_se3_append` (proved)** — padding-transparent satisfiability
  `AllEq₃ && AllEq₃ && AllEq₃` (the codec realizes `AEm 3`; 512-case dispatch,
  conflicts first);
* **`sBase3` / `zBase3`** — the all-true base word and padded completion.

The nine-sign slot machinery, the two-wire cut lemma, and the spare-split
structure theorem at budget `≤ 2·deps + 1` follow in later bricks.  Nothing here
is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor

/-- The three-gadget formula: three signed unit clauses on each of `x₀`, `x₁`, `x₂`. -/
def se3 (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ : Bool) : Formula :=
  [[((0 : ℕ), s₁)], [((0 : ℕ), s₂)], [((0 : ℕ), s₃)],
   [((1 : ℕ), s₄)], [((1 : ℕ), s₅)], [((1 : ℕ), s₆)],
   [((2 : ℕ), s₇)], [((2 : ℕ), s₈)], [((2 : ℕ), s₉)]]

theorem encodeVar'_two : encodeVar' 2 = [false, false, true, true, false] := by
  have h := encodeVar'_coords 0 0 2 (by omega)
  rw [show 3 * Nat.pair 0 0 + 2 = 2 from rfl] at h
  rw [h]
  rfl

theorem se3_concrete (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ : Bool) :
    encodeFormula' (se3 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉)
    = [true, true, true, true, true, true, true, true, true, false,
       true, false, false, false, false, s₁,
       true, false, false, false, false, s₂,
       true, false, false, false, false, s₃,
       true, false, false, false, true, false, s₄,
       true, false, false, false, true, false, s₅,
       true, false, false, false, true, false, s₆,
       true, false, false, false, true, true, false, s₇,
       true, false, false, false, true, true, false, s₈,
       true, false, false, false, true, true, false, s₉] := by
  show encodeNat 9 ++ (List.map encodeClause' (se3 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉)).flatten = _
  simp only [se3, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    encodeClause', encodeLit', List.append_nil, encodeVar'_zero, encodeVar'_one,
    encodeVar'_two]
  rfl

/-- **Padding-transparent three-gadget satisfiability (proved)**: the codec realizes
`AEm 3` — agreement per gadget, independently. -/
theorem SATLang_se3_append (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ : Bool) (rest : List Bool) :
    SATLang (encodeFormula' (se3 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) ++ rest)
      = (allEq3 s₁ s₂ s₃ && allEq3 s₄ s₅ s₆ && allEq3 s₇ s₈ s₉) := by
  cases s₁ <;> cases s₂ <;> cases s₃ <;> cases s₄ <;> cases s₅ <;> cases s₆ <;>
    cases s₇ <;> cases s₈ <;> cases s₉ <;>
    first
      | (rw [SATLang_append_unsat _ _
          (unsat_of_conflict_at 0 _ (by decide) (by decide))]; rfl)
      | (rw [SATLang_append_unsat _ _
          (unsat_of_conflict_at 1 _ (by decide) (by decide))]; rfl)
      | (rw [SATLang_append_unsat _ _
          (unsat_of_conflict_at 2 _ (by decide) (by decide))]; rfl)
      | (rw [SATLang_append_sat _ _
          ⟨fun n => if n = 0 then false else if n = 1 then false else false,
            by decide⟩]; rfl)
      | (rw [SATLang_append_sat _ _
          ⟨fun n => if n = 0 then false else if n = 1 then false else true,
            by decide⟩]; rfl)
      | (rw [SATLang_append_sat _ _
          ⟨fun n => if n = 0 then false else if n = 1 then true else false,
            by decide⟩]; rfl)
      | (rw [SATLang_append_sat _ _
          ⟨fun n => if n = 0 then false else if n = 1 then true else true,
            by decide⟩]; rfl)
      | (rw [SATLang_append_sat _ _
          ⟨fun n => if n = 0 then true else if n = 1 then false else false,
            by decide⟩]; rfl)
      | (rw [SATLang_append_sat _ _
          ⟨fun n => if n = 0 then true else if n = 1 then false else true,
            by decide⟩]; rfl)
      | (rw [SATLang_append_sat _ _
          ⟨fun n => if n = 0 then true else if n = 1 then true else false,
            by decide⟩]; rfl)
      | (rw [SATLang_append_sat _ _
          ⟨fun n => if n = 0 then true else if n = 1 then true else true,
            by decide⟩]; rfl)

/-- The all-true-signs three-gadget word (73 bits). -/
def sBase3 : List Bool :=
  [true, true, true, true, true, true, true, true, true, false,
   true, false, false, false, false, true,
   true, false, false, false, false, true,
   true, false, false, false, false, true,
   true, false, false, false, true, false, true,
   true, false, false, false, true, false, true,
   true, false, false, false, true, false, true,
   true, false, false, false, true, true, false, true,
   true, false, false, false, true, true, false, true,
   true, false, false, false, true, true, false, true]

/-- The padded three-gadget base completion. -/
def zBase3 (N : ℕ) : Fin N → Bool := fun k => sBase3.getD k.val false

theorem sBase3_length : sBase3.length = 73 := by
  simp only [sBase3, List.length_cons, List.length_nil]

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.se3_concrete
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.SATLang_se3_append
