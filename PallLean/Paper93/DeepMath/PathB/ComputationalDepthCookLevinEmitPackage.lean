import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitGlue2

/-!
# Cook–Levin M2 emitter — E6 step 10: THE FINAL PACKAGING

The tableau converse is PROVEN in the repo (`fullTableau_correct`: satisfiable ⟺ the run
halts-and-accepts, given the head bound) — so the emission's correctness closes end-to-end:

* `emittedTotal M x P B` — the init-cell unit clauses (brick 27's stream, as `fixBits`) plus
  `emittedFormula` — is the TOTAL emitted formula;
* `totalStream_encode` — the total emitted bit stream (the init-cell stream ++ `masterOut2`)
  IS `encodeClause'` of `emittedTotal`, clause-for-clause;
* `emittedTotal_correct` — **`Satisfiable (emittedTotal) ⟺ the run halts-and-accepts`**:
  forward by the real-run assignment (`emittedFormula_sound` + the cell fixes), backward
  through `emittedFormula_tableau` into `fullTableau_converse`;
* `emittedTotal_iff_fullTableau` — the emission and the tableau are equisatisfiable.

What remains for `EmitsTableau'` is machine choreography only: the majorant, the arming/morph
phase joining brick 27's init-cell layout to the six-region chain, and the `Transduces`/
`PolyBounded` wrapper.  The mathematics of the reduction — the stream, the formula, and the
satisfiability — is closed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinAssembly
open PallLean.Paper93.DeepMath.PathB.CookLevinConverse
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMaster2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitGlue
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitGlue2

/-! ## The total emitted formula -/

/-- The input-dependent init-cell fixes (brick 27's stream, at the clause level). -/
noncomputable def cellFixes (x : List Bool) (P : ℕ) : Formula :=
  fixBits ((List.range (P + 1)).map (fun p => (cellVar 0 p, x.getD p false)))

/-- The TOTAL emitted formula: the init-cell fixes plus the master chain's emission. -/
noncomputable def emittedTotal (M : Machine) (x : List Bool) (P B : ℕ) : Formula :=
  cellFixes x P ++ emittedFormula M P B

/-- **The total emitted stream is `encodeClause'` of `emittedTotal`** — the init-cell stream
(brick 27's `initCellP_family_run` output) followed by `masterOut2`. -/
theorem totalStream_encode (M : Machine) (x : List Bool) (P B : ℕ) :
    ((List.range (P + 1)).map (fun p =>
        encodeClause' [(cellVar 0 p, x.getD p false)])).flatten
      ++ masterOut2 M P B
    = ((emittedTotal M x P B).map encodeClause').flatten := by
  rw [emittedTotal, List.map_append, List.flatten_append, masterOut2_encode]
  congr 1
  rw [cellFixes, fixBits, List.map_map, List.map_map]
  rfl

/-! ## THE EMISSION IS CORRECT -/

/-- **The emitted formula is the reduction**: with the head bounded by `P` over `[0, B]`, the
total emission is satisfiable *iff* the real run halts-and-accepts by step `B`. -/
theorem emittedTotal_correct (M : Machine) (x : List Bool) (P B : ℕ)
    (hb : ∀ t, t ≤ B → (run M t (init M x)).hd ≤ P) :
    Satisfiable (emittedTotal M x P B)
      ↔ (M.halt (run M B (init M x)).st = true
          ∧ M.accept (run M B (init M x)).st = true) := by
  constructor
  · rintro ⟨a, ha⟩
    rw [emittedTotal, evalFormula_append, Bool.and_eq_true] at ha
    obtain ⟨hCells, hEmit⟩ := ha
    rw [cellFixes, fixBits_iff] at hCells
    obtain ⟨hAsm, hAcc, hWrite, hU1, hU2⟩ := emittedFormula_tableau M P B a hEmit
    apply fullTableau_converse M x P B a hb
    rw [fullTableau, fullFormula, evalFormula_append, evalFormula_append,
      evalFormula_append, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨⟨?_, hAsm⟩, hAcc⟩, hWrite⟩
    rw [initFormula, fixBits_iff]
    intro pr hpr
    simp only [List.mem_cons] at hpr
    rcases hpr with rfl | rfl | hmem
    · exact hU1
    · exact hU2
    · exact hCells pr hmem
  · rintro ⟨hh, hacc⟩
    refine ⟨fullAssign M x, ?_⟩
    rw [emittedTotal, evalFormula_append, Bool.and_eq_true]
    refine ⟨?_, emittedFormula_sound M x P B hb hh hacc⟩
    rw [cellFixes, fixBits_iff]
    intro pr hpr
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hpr
    exact init_cell_sat M x p

/-- **Equisatisfiability with the tableau**: the emission and `fullTableau` decide the same
question. -/
theorem emittedTotal_iff_fullTableau (M : Machine) (x : List Bool) (P B : ℕ)
    (hb : ∀ t, t ≤ B → (run M t (init M x)).hd ≤ P) :
    Satisfiable (emittedTotal M x P B) ↔ Satisfiable (fullTableau M x P B) := by
  rw [emittedTotal_correct M x P B hb, fullTableau_correct M x P B hb]

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage
