import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitFinale

/-!
# Cook–Levin M2 emitter — the fence, restated in `EmitsTableau'` form

`EmitsTableau'` (EmitCodec) states the emitter gap as
`PolyComputable (fun x => encodeFormula' (tableauReduction M x (clock |x|)))` — an
∃-machine, ∃-`PolyBounded`-clock transducer statement with the identity input and output
conventions and the tableau clause order.  The closed pipeline (`EmitsEmittedT`,
EmitFinale) emits the same reduction up to three explicitly-flagged convention
deviations:

1. **input codec** — the machine consumes `encTape clock x` (the armed six-region layout
   with the init-cell stream preloaded), not the bare `x`; the arming morph is the
   remaining input-convention decision, preserved in the arc;
2. **output codec** — the emitted formula is read off the raw final tape by the fixed
   parser `decodeTape` (the final tape is self-describing; no compaction pass);
3. **clause order** — the emitted formula is `emittedReduction`: the same decision
   content as `tableauReduction`, equisatisfiable (`emittedReduction_equisat`), deciding
   the identical clocked-acceptance question (`emittedReduction_correct`).

This file restates the fence in the same shape with the conventions as explicit codec
parameters (`PolyComputableVia`; identity codecs recover the literal `PolyComputable` —
`polyComputableVia_id`), instantiates it at the landed conventions (`EmitsTableauT`),
**discharges it** from the closed pipeline (`emitsTableauT`), and proves the semantic
bridge to the original fence's target formula (`emitsTableauT_tableau`).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitFence

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction (Satisfiable)
open PallLean.Paper93.DeepMath.PathB.CookLevinReduce (tableauReduction)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPipeline (encTape)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTapeCodec (decodeTape)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage2
  (emittedReduction emittedReduction_equisat)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCore (emitterCoreMachine)
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept (acceptStates)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFinale (EmitsEmittedT)

/-! ## `PolyComputable` with explicit conventions -/

/-- `PolyComputable` with the input and output conventions as explicit codecs: some
machine, within some `PolyBounded` clock, carries `encIn x` to a raw tape that `decOut`
reads as `f x`, for every `x`.  With identity codecs this is literally `PolyComputable`
(`polyComputableVia_id`). -/
def PolyComputableVia {α : Type*} (encIn : List Bool → List Bool)
    (decOut : List Bool → α) (f : List Bool → α) : Prop :=
  ∃ (E : Machine) (T : ℕ → ℕ), PolyBounded T ∧ ∀ x : List Bool,
    HaltsBy E (encIn x) (T x.length) ∧ decOut (transOut E (encIn x) (T x.length)) = f x

/-- **Shape sanity**: identity codecs recover the literal `PolyComputable` — the exact
shape of `EmitsTableau'`. -/
theorem polyComputableVia_id (f : List Bool → List Bool) :
    PolyComputableVia id id f ↔ PolyComputable f := by
  constructor
  · rintro ⟨E, T, hT, h⟩
    exact ⟨E, T, hT, h⟩
  · rintro ⟨E, T, hT, h⟩
    exact ⟨E, T, hT, h⟩

/-! ## The fence, restated -/

/-- **THE FENCE, `EmitsTableau'` FORM, AT THE LANDED CONVENTIONS**: the emitted
reduction of `(M, x, clock)` is poly-computable via the armed input encoding and the
fixed tape parser.  Relative to the literal `EmitsTableau'`, the input codec is
`encTape clock` (not `id`), the output codec is `decodeTape` (not `id`), and the target
formula is `emittedReduction` (the machine's clause order) in place of
`tableauReduction` — equisatisfiable, by `emittedReduction_equisat`. -/
def EmitsTableauT (M : Machine) (clock : ℕ → ℕ) : Prop :=
  PolyComputableVia (encTape clock) decodeTape
    (fun x => emittedReduction M x (clock x.length))

/-- **THE RESTATED FENCE, DISCHARGED** — from the closed pipeline: the emitter core and
the `ECB` majorant witness it, for every machine with a nonempty accept set and every
positive `PolyBounded` clock. -/
theorem emitsTableauT (M : Machine) (clock : ℕ → ℕ) (hAcc : acceptStates M ≠ [])
    (hclk : ∀ n, 0 < clock n) (hpoly : PolyBounded clock) : EmitsTableauT M clock := by
  obtain ⟨T, hPB, h⟩ := EmitsEmittedT M clock hAcc hclk hpoly
  exact ⟨emitterCoreMachine M, T, hPB, fun x => ⟨(h x).1, (h x).2.1⟩⟩

/-! ## The bridge to the original fence's target -/

/-- **The restated fence hits the original target's question**: some machine, within a
`PolyBounded` clock, emits — via the fixed conventions — a formula equisatisfiable with
`tableauReduction M x (clock |x|)`, the exact formula of `EmitsTableau'`, on every
input.  The only remaining daylight to the LITERAL `EmitsTableau'` is the two
conventions themselves: the arming morph (input) and serialisation (`decodeTape` output
vs `encodeFormula'` bits, clause order absorbed here by equisatisfiability). -/
theorem emitsTableauT_tableau (M : Machine) (clock : ℕ → ℕ)
    (hAcc : acceptStates M ≠ []) (hclk : ∀ n, 0 < clock n)
    (hpoly : PolyBounded clock) :
    ∃ (E : Machine) (T : ℕ → ℕ), PolyBounded T ∧ ∀ x : List Bool,
      HaltsBy E (encTape clock x) (T x.length)
      ∧ (Satisfiable (decodeTape (transOut E (encTape clock x) (T x.length)))
          ↔ Satisfiable (tableauReduction M x (clock x.length))) := by
  obtain ⟨T, hPB, h⟩ := EmitsEmittedT M clock hAcc hclk hpoly
  refine ⟨emitterCoreMachine M, T, hPB, fun x => ?_⟩
  obtain ⟨hH, hdec, _⟩ := h x
  refine ⟨hH, ?_⟩
  rw [hdec]
  exact emittedReduction_equisat M x (clock x.length)

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitFence
