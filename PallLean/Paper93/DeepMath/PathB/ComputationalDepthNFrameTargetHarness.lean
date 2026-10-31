import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameConditionalPvsNP
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMCSP

/-!
# N-Frame: the lower-bound target harness — what any admissible method must survive

The conditional theorem left one open premise: `NFrameCircuitLowerBoundTarget` (super-polynomial `cbudget` for SAT).
This file builds the **harness** around that target: it proves `cbudget` is an *instance* of the repo's MCSP framework,
so the barrier theorems formalized earlier in this arc apply to the circuit target *as theorems*, and any candidate
lower-bound method faces exactly these proven constraints:

  `cbudget_eq_mcsp` — **PROVED**: the circuit energy *is* the minimum-description-size invariant for the representation
        class `Rep = gate lists`, `size = length`.
  `output_surjective` — **PROVED**: every function has a circuit (via the verified compiler on the DNF transducer).
  `cbudget_gap_iff_not_sizeClass` — **PROVED, constraint #1 (circularity)**: `s < cbudget f ↔ f ∉ SIZE(s)`.  The target
        is *definitionally* class non-membership — so the "method" of directly establishing the gap has no independent
        content; a real method must derive the gap from some other structure of `f`.
  `target_iff_not_sizeClass` — **PROVED**: the family target restated: SAT eventually escapes every polynomial `SIZE`
        class — the naive reading and the honest reading agree exactly.
  `no_natural_method` — **PROVED, constraint #2 (anti-naturalness)**: under a Razborov–Rudich instance for `SIZE(s)`,
        any *large* property useful against `SIZE(s)` is non-constructive — a candidate method that is constructive and
        large cannot certify the target.

## Why restricted bounds exist and the general one does not — the harness's explanatory content

The two constraints calibrate exactly against the repo's real bounds.  **Restricted classes** (formulas, `AC⁰`,
`AC⁰[p]`, small-width boundaries) are too weak to compute pseudorandom functions, so the Razborov–Rudich premise *fails*
there and constructive-and-large methods are legitimate — which is precisely why the repo's Nečiporuk (`Ω(N²/log N)`
boundary tearing) and Razborov–Smolensky arcs *succeed*.  **General circuits** (`SIZE(poly)` = the conditional theorem's
class) plausibly do compute PRFs, so constraint #2 bites: an admissible method must be anti-natural, and by constraint #1
it must be non-circular — it must certify `s < cbudget f` without being the assertion itself.  No known method satisfies
both for general circuits; that conjunction is the precise, formalized reason the known toolbox stops at the target's
doorstep.  This file proves the constraints; it does **not** supply a method.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.NFrameAntiNatural (Useful Large)
open PallLean.Paper93.DeepMath.PathB.NFrameMCSP

variable {n : ℕ}

/-- The circuit size class: functions computed by at most `s` gates — the `SIZE(s)` of the boundary model. -/
def circuitSizeClass (s : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ c : List (CGate n), output c = f ∧ c.length ≤ s

/-- **Every function has a circuit (proved)** — the verified compiler applied to the DNF transducer. -/
theorem output_surjective (f : (Fin n → Bool) → Bool) :
    ∃ c : List (CGate n), output c = f := by
  refine ⟨compile 0 (dnfFor f), funext fun x => ?_⟩
  rw [compile_computes (dnfFor f) x]
  rw [eval_dnfFor f]

/-- **The circuit energy is an MCSP instance (proved)**: `cbudget = mcsp` for `Rep = gate lists`, `size = length`. -/
theorem cbudget_eq_mcsp (f : (Fin n → Bool) → Bool) :
    cbudget f = mcsp (fun c : List (CGate n) => output c) List.length f := by
  unfold cbudget mcsp
  congr 1
  ext s
  constructor
  · rintro ⟨c, hc, hl⟩
    exact ⟨c, funext hc, hl⟩
  · rintro ⟨c, hc, hl⟩
    exact ⟨c, fun x => congrFun hc x, hl⟩

/-- The size class agrees with the MCSP instance's. -/
theorem circuitSizeClass_eq_sizeClass (s : ℕ) (f : (Fin n → Bool) → Bool) :
    circuitSizeClass s f ↔ sizeClass (fun c : List (CGate n) => output c) List.length s f :=
  Iff.rfl

/-- **Constraint #1 — circularity (proved)**: the circuit-energy gap `s < cbudget f` is *identical* to `f ∉ SIZE(s)`.
Directly asserting the gap is asserting the conclusion; an admissible method must derive it from other structure. -/
theorem cbudget_gap_iff_not_sizeClass (s : ℕ) (f : (Fin n → Bool) → Bool) :
    s < cbudget f ↔ ¬ circuitSizeClass s f := by
  rw [cbudget_eq_mcsp]
  exact mcsp_gap_iff_not_sizeClass _ _ output_surjective s f

/-- **The family target, restated exactly (proved)**: super-polynomial `cbudget` for `F` is precisely "`F` eventually
escapes every polynomial `SIZE` class". -/
theorem target_iff_not_sizeClass (F : ∀ n : ℕ, (Fin n → Bool) → Bool) :
    NFrameCircuitLowerBoundTarget F ↔
      ∀ k, ∃ n, ¬ circuitSizeClass (n ^ k + k) (F n) := by
  unfold NFrameCircuitLowerBoundTarget SuperPolyCBudget
  exact forall_congr' fun k => exists_congr fun n => cbudget_gap_iff_not_sizeClass _ _

/-- **Constraint #2 — anti-naturalness (proved)**: under a Razborov–Rudich instance `rr` for `SIZE(s)` (no
constructive-and-large property is useful against it — the premise that holds when the class computes PRFs), any *large*
candidate method useful against `SIZE(s)` is non-constructive.  Constructive-and-large methods cannot certify the
target for classes above the PRF threshold; below it (formulas, `AC⁰`, `AC⁰[p]`) the premise fails and such methods are
legitimate — exactly where the repo's real restricted bounds live. -/
theorem no_natural_method {s : ℕ} {K : ℕ}
    {Φ : ((Fin n → Bool) → Bool) → Prop} {Constructive : (((Fin n → Bool) → Bool) → Prop) → Prop}
    (rr : Constructive Φ → Large Φ K → Useful Φ (circuitSizeClass s) → False)
    (hlarge : Large Φ K) (huseful : Useful Φ (circuitSizeClass s)) :
    ¬ Constructive Φ :=
  fun hc => rr hc hlarge huseful

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_eq_mcsp
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_gap_iff_not_sizeClass
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.target_iff_not_sizeClass
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.no_natural_method
