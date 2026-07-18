import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceSchemaCeiling

/-!
# The non-size-dominated side: generic soundness still caps single configurations

The ceiling theorem (`TraceSchemaCeiling`) showed that any content beyond time-hardness must
come from a measure that is **not** size-dominated — one that can exceed `traceSize` on SAT
traces while staying polynomial on all poly-time-machine traces via an *earned* transfer
theorem.  This file asks what generic soundness *still* forces once size-domination is
dropped, and answers: even a non-size-dominated generically-sound measure is polynomially
bounded on **single-configuration** traces.

The witness is `haltMachine`, the machine that halts at step `0`: its trace on input `x` is
the singleton `[x]`, and it is polynomial-time (clock `0`).  So generic soundness of
`traceInv μ` applied to `haltMachine` forces the single-row profile
`n ↦ sup_{|x|=n} μ [x]` to be polynomially bounded (`genSound_singleRow_poly`) — with no
size-domination hypothesis at all.

**Consequence for the frontier.**  A size-dominated `μ` gets `μ [x] ≤ traceSize [x] = |x|+1`
for free; this theorem shows the *same* single-configuration cap is forced on **every**
generically-sound `μ`, size-dominated or not.  So dropping size-domination buys no extra power
on individual configurations — a non-size-dominated measure's hoped-for content on SAT traces
must come entirely from **multi-row / whole-trace structure** that generic soundness permits
(polynomial on realizable traces) yet that is superpolynomial on SAT-decider traces.  The
"earned transfer theorem" the ceiling demanded is therefore a bound on `μ` over *multi-row*
realizable traces, never a per-configuration largeness.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NonSizeDominated

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.SeparationNoGo
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-- The machine that halts at step `0`: its trace on any input is the singleton input tape. -/
def haltMachine : Machine where
  State := Unit
  fin := inferInstance
  dec := inferInstance
  start := ()
  halt := fun _ => true
  δ := fun _ _ => ((), none, 0)
  accept := fun _ => false

theorem haltMachine_haltsBy (x : List Bool) (t : ℕ) : HaltsBy haltMachine x t := by
  have hh : haltMachine.halt (init haltMachine x).st = true := rfl
  show haltMachine.halt (run haltMachine t (init haltMachine x)).st = true
  rw [run_of_halted haltMachine hh t]
  exact hh

theorem haltMachine_polyTime : PolyTime haltMachine :=
  ⟨fun _ => 0, ⟨0, 0, fun _ => Nat.zero_le _⟩, fun x => haltMachine_haltsBy x 0⟩

theorem minHalt_haltMachine (n : ℕ) : minHalt haltMachine n = 0 := by
  have hex : ∃ t, HaltsAllAt haltMachine n t :=
    ⟨0, fun x _ => haltMachine_haltsBy x 0⟩
  show (if h : ∃ t, HaltsAllAt haltMachine n t then Nat.find h else 0) = 0
  rw [dif_pos hex, Nat.find_eq_zero]
  exact fun x _ => haltMachine_haltsBy x 0

theorem traceObj_haltMachine (x : List Bool) : traceObj haltMachine 0 x = [x] := by
  simp [traceObj, run_zero, init]

/-- The single-row profile: the per-length worst case of `μ` on singleton-trace `[x]`. -/
noncomputable def singleRowProfile (μ : List (List Bool) → ℕ) (n : ℕ) : ℕ :=
  Finset.univ.sup fun v : Fin n → Bool => μ [List.ofFn v]

theorem traceInv_haltMachine (μ : List (List Bool) → ℕ) (n : ℕ) :
    traceInv μ haltMachine n = singleRowProfile μ n := by
  unfold traceInv singleRowProfile
  rw [minHalt_haltMachine]
  apply Finset.sup_congr rfl
  intro v _
  rw [traceObj_haltMachine]

/-- **The single-configuration cap.**  Generic soundness of `traceInv μ` — with *no*
size-domination hypothesis — forces `μ` to be polynomially bounded on single-configuration
traces: the immediately-halting machine is polynomial-time and produces exactly those traces. -/
theorem genSound_singleRow_poly (μ : List (List Bool) → ℕ)
    (hG : InvGenSound (traceInv μ)) : PolyBounded (singleRowProfile μ) := by
  have h := hG haltMachine haltMachine_polyTime
  have hcongr : traceInv μ haltMachine = singleRowProfile μ :=
    funext (traceInv_haltMachine μ)
  rwa [hcongr] at h

/-- **The cap is universal.**  For size-dominated `μ` the single-row bound is free
(`μ [x] ≤ |x|+1`); this shows generic soundness forces the *same* cap without size-domination
— so dropping size-domination gives no per-configuration freedom, only whole-trace freedom. -/
theorem sizeDominated_singleRow_le (μ : List (List Bool) → ℕ) (hμ : SizeDominated μ)
    (x : List Bool) : μ [x] ≤ x.length + 1 := by
  have h := hμ [x]
  unfold traceSize at h
  simpa using h

end PallLean.Paper93.DeepMath.PathB.NonSizeDominated
