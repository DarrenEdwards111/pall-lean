import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitPackage
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinReduce

/-!
# Cook–Levin M2 emitter — E6 step 11: THE REDUCTION-LEVEL TARGET

`tableauReduction M x clock = fullTableau M x (|x| + clock) clock`, its head bound discharged
unconditionally by `run_bounds`.  This brick instantiates the emission at exactly those
parameters and packages the target:

* `emittedReduction M x clock` — the emission at `P := |x| + clock`, `B := clock`;
* `emittedReduction_correct` — **unconditional**: satisfiable iff `M` halts-and-accepts within
  `clock` steps (the same statement shape as `tableauReduction_correct`);
* `emittedReduction_equisat` — the emission and `tableauReduction` decide the same question;
* `satisfiable_decode_encode_emitted` — the codec round-trip preserves it;
* `emittedReductionStream_encode` — the machines' physical stream at the reduction parameters
  IS the `encodeClause'` payload of `emittedReduction`;
* `EmitsEmitted'` — the target restated for the emitted formula: a poly transducer for
  `encodeFormula' (emittedReduction M x (clock |x|))`.

`EmitsEmitted'` has the same satisfiability semantics as `EmitsTableau'` (this file proves
it); closing the LITERAL `EmitsTableau'` additionally needs the target restated to the emitted
formula — the emission is a satisfaction-blind reordering of the tableau plus sound extras,
not the identical clause list — which is a (free) design decision on the fence statement, not
mathematics.  The remaining machine work for `EmitsEmitted'` is the majorant, the layout
arming/morph, and the count-header phase.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage2

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinAssembly
open PallLean.Paper93.DeepMath.PathB.CookLevinConverse
open PallLean.Paper93.DeepMath.PathB.CookLevinReduce
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMaster2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitGlue
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitGlue2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage

/-! ## The emission at the reduction parameters -/

/-- The emitted reduction of `(M, x, clock)`: the total emission over `[0, clock]` with cell
width `|x| + clock` — the same parameters as `tableauReduction`. -/
noncomputable def emittedReduction (M : Machine) (x : List Bool) (clock : ℕ) : Formula :=
  emittedTotal M x (x.length + clock) clock

/-- **Unconditional emission correctness** — the exact statement shape of
`tableauReduction_correct`, for the formula the machines actually write. -/
theorem emittedReduction_correct (M : Machine) (x : List Bool) (clock : ℕ) :
    Satisfiable (emittedReduction M x clock)
      ↔ (HaltsBy M x clock ∧ decideOut M x clock = true) := by
  unfold emittedReduction HaltsBy decideOut
  exact emittedTotal_correct M x (x.length + clock) clock (head_bound M x clock)

/-- **The emission and the tableau reduction decide the same question.** -/
theorem emittedReduction_equisat (M : Machine) (x : List Bool) (clock : ℕ) :
    Satisfiable (emittedReduction M x clock) ↔ Satisfiable (tableauReduction M x clock) := by
  rw [emittedReduction_correct, tableauReduction_correct]

/-- **The codec round-trip preserves the emission's correctness** — the analog of
`satisfiable_decodeFormula'_encodeFormula'` for the emitted formula. -/
theorem satisfiable_decode_encode_emitted (M : Machine) (x : List Bool) (clock : ℕ) :
    Satisfiable (decodeFormula' (encodeFormula' (emittedReduction M x clock)))
      ↔ (HaltsBy M x clock ∧ decideOut M x clock = true) := by
  rw [decodeFormula'_encodeFormula']
  exact emittedReduction_correct M x clock

/-- **The machines' stream at the reduction parameters is the target's payload**: the
init-cell stream followed by `masterOut2`, instantiated at `P := |x| + clock`, `B := clock`,
is exactly the `encodeClause'` payload of `emittedReduction`. -/
theorem emittedReductionStream_encode (M : Machine) (x : List Bool) (clock : ℕ) :
    ((List.range (x.length + clock + 1)).map (fun p =>
        encodeClause' [(cellVar 0 p, x.getD p false)])).flatten
      ++ masterOut2 M (x.length + clock) clock
    = ((emittedReduction M x clock).map encodeClause').flatten :=
  totalStream_encode M x (x.length + clock) clock

/-! ## The restated target -/

/-- **The emitter target, for the formula the machines write**: a poly-time transducer
computing the coordinate encoding of `emittedReduction`.  Same satisfiability semantics as
`EmitsTableau'` (`emittedReduction_equisat`, `satisfiable_decode_encode_emitted`); the literal
`EmitsTableau'` differs only by the (satisfaction-blind) clause order and the sound extras. -/
def EmitsEmitted' (M : Machine) (clock : ℕ → ℕ) : Prop :=
  PolyComputable (fun x => encodeFormula' (emittedReduction M x (clock x.length)))

/-- Whatever transducer realises `EmitsEmitted'` computes a formula deciding exactly the
clocked acceptance question — the property every downstream use of the fence consumes. -/
theorem EmitsEmitted'_semantics (M : Machine) (clock : ℕ → ℕ) (x : List Bool) :
    Satisfiable (decodeFormula' (encodeFormula' (emittedReduction M x (clock x.length))))
      ↔ (HaltsBy M x (clock x.length) ∧ decideOut M x (clock x.length) = true) :=
  satisfiable_decode_encode_emitted M x (clock x.length)

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage2
