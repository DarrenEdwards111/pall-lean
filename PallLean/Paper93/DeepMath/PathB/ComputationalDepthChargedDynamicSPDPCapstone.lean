import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedCanonicalQueryAudit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedDynamicQueryCollapse

/-!
# Capstone: the charged dynamic-SPDP arc as a reduction, and its two-horn boundary

This closes the charged holographic dynamic-SPDP investigation.  Starting from the collapsed `ClockedMachine`
(whose uncharged `init` made `InP` all languages — `HolographicDynamicSPDPInitNoGo`), the arc built a genuinely
charged single-tape machine (`ChargedHolographicMachine`), length-indexed finite observers
(`ChargedLengthObserver`), continuation/query sufficiency and the observational quotient
(`ChargedContinuationQuotient`), and the dynamic profile-change measure (`ChargedDynamicQueryInnovation`).

**The reduction (this file).**  `charged_dynamic_notInP`: for *any* query-scheme assignment `S`, if the dynamic
query-profile innovation is super-polynomial on every charged machine deciding `L` (`SATLower`), then
`L ∉ InP` for the charged model.  The `PUpper` half is discharged unconditionally
(`dynamicQueryResource_polyBounded`: innovation `≤ clock`), so the entire content is the `SATLower` hypothesis.

**The two-horn boundary (why `SATLower` here is exactly the P-vs-NP obligation).**

* *Collapse horn* (`ChargedDynamicQueryCollapse.universal_dynamic_lower_impossible`): quantified over *all* valid
  schemes, `SATLower` is impossible — a time-invariant scheme (even a rich, input-separating one) has innovation
  `0`.  So `SATLower` must fix a canonical time-sensitive scheme.
* *Clock horn* (`ChargedCanonicalQueryAudit.canonical_schemeResource_eq_clock`): the maximally-rich canonical
  scheme's resource is *exactly* `M.clock`.  Its `SATLower` is precisely a charged-time lower bound for SAT.

**Padding-sensitivity (this file, `charged_dynamic_padding_sensitive`).**  The clock-horn measure is not a
language invariant: two charged machines deciding the *same* language have different canonical resource whenever
their clocks differ.  So a would-be separating invariant must additionally quotient harmless padding — i.e. take
the minimum over padding-equivalent machines, which is exactly the min-over-decompositions quantifier the
observer-boundary programme already isolates as the P-vs-NP frontier.

## Honest scope

A conditional reduction (`SATLower ⇒ L ∉ charged-P`) with `PUpper` discharged, plus machine-checked boundary
theorems showing both trivial extremes fail and the surviving canonical measure equals runtime and is
padding-sensitive.  No `SATLower` is proved; no complexity-class separation is established.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ChargedDynamicSPDPCapstone

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.ChargedHolographicMachine
open PallLean.Paper93.DeepMath.PathB.ChargedDynamicQueryInnovation
open PallLean.Paper93.DeepMath.PathB.ChargedCanonicalQueryAudit

/-! ## The reduction: `SATLower ⇒ L ∉ charged-P`, with `PUpper` free -/

/-- **The charged dynamic-SPDP reduction.**  If the dynamic query-profile innovation of the scheme assignment `S`
is not polynomially bounded on any charged machine deciding `L`, then `L` is outside the charged model's `P`.  The
polynomial upper bound holds automatically for every polynomial-time machine, so `SATLower` (the hypothesis) is
the only remaining content. -/
theorem charged_dynamic_notInP (S : ∀ M, QueryScheme M) (L : List Bool → Bool)
    (hLower : ∀ M : ChargedMachine, Decides M L → ¬ PolyBounded (schemeResource (S M))) :
    ¬ InP L := by
  rintro ⟨M, hpoly, hdec⟩
  exact hLower M hdec (dynamicQueryResource_polyBounded (S M) hpoly)

/-- The `PUpper` half, isolated: every polynomial-time charged machine has polynomial dynamic query innovation for
every scheme — discharged, no hypothesis. -/
theorem charged_dynamic_PUpper (S : ∀ M, QueryScheme M) (M : ChargedMachine) (hM : IsPolyTime M) :
    PolyBounded (schemeResource (S M)) :=
  dynamicQueryResource_polyBounded (S M) hM

/-! ## Padding-sensitivity: the clock-horn measure is not a language invariant -/

/-- A one-state machine that stays put and always rejects: it decides the constantly-`false` language under any
clock. -/
def constMachine (clk : Nat → Nat) : ChargedMachine where
  Q := 1
  start := ⟨0, by omega⟩
  delta := fun _ _ => (⟨0, by omega⟩, false, ⟨2, by omega⟩)
  accept := fun _ => false
  clock := clk

theorem constMachine_decides (clk : Nat → Nat) :
    Decides (constMachine clk) (fun _ => false) :=
  fun _ => rfl

/-- **The canonical dynamic measure is padding-sensitive.**  Two charged machines can decide the same language
yet have different canonical dynamic resource — so the measure is not a language invariant; it charges harmless
clock padding.  (Here both machines decide `fun _ => false`, with clocks `1` and `2`.) -/
theorem charged_dynamic_padding_sensitive :
    ∃ (L : List Bool → Bool) (M₁ M₂ : ChargedMachine),
      Decides M₁ L ∧ Decides M₂ L ∧
      ∃ n, dynamicQueryResource (canonicalRichSemantics M₁ n)
             ≠ dynamicQueryResource (canonicalRichSemantics M₂ n) := by
  refine ⟨fun _ => false, constMachine (fun _ => 1), constMachine (fun _ => 2),
    constMachine_decides _, constMachine_decides _, 0, ?_⟩
  rw [canonical_dynamicQueryResource_eq_clock, canonical_dynamicQueryResource_eq_clock]
  decide

end PallLean.Paper93.DeepMath.PathB.ChargedDynamicSPDPCapstone

#print axioms PallLean.Paper93.DeepMath.PathB.ChargedDynamicSPDPCapstone.charged_dynamic_notInP
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedDynamicSPDPCapstone.charged_dynamic_padding_sensitive
