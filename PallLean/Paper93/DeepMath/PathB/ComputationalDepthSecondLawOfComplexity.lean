import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNaturalProofsObstruction

/-!
# The second law of complexity, as a face of the wall

Susskind–Brown's **second law of complexity**: the circuit complexity of a state grows (linearly,
with high probability) until it **saturates** at `C_max ~ exp(S)`, after which it plateaus.  It is
the dynamical engine behind `complexity = volume` — the reason the bulk volume keeps growing.  This
file formalises its literal shape and proves where it lands: the growth is a *counting/typical-case*
statement (the counting barrier) and any efficient per-state complexity test is a natural property
(the natural-proofs barrier).  Like the Bekenstein and CV forms, it renames the wall.

## The curve (proved)

`curve C_max t = min t C_max` is the second-law shape: linear rise, then a plateau at `C_max`.

* **`curve_monotone`** — complexity is non-decreasing in time (the "arrow of complexity").
* **`curve_saturates`** — it never exceeds `C_max` (the ceiling; in dS the cosmological horizon).
* **`curve_plateau`** — once `C_max ≤ t` it is pinned at `C_max` (saturation).

## The two walls (proved)

* **`second_law_saturates`** — the actual measure is bounded: `C s ≤ C_max`.  Growth stops.
* **`second_law_counting_not_sat`** — Wall A: the statistical second law ("a state of complexity
  `> k` exists" — the typical trajectory rises) is CONSISTENT with `C sat ≤ k`.  The arrow points
  toward the *typical* (maximal-complexity) state, and SAT is one specific, structured state that
  need not be typical.  Existence of hard states, never SAT-specific — the counting barrier.
* **`second_law_detector_breaks_crypto`** — Wall B: if `C` above threshold is efficiently testable
  and SAT is complex, the predicate `C s ≤ k` is a `ColossusRuler` (poly-checkable, true on all
  low-complexity states, false on SAT), hence a natural distinguisher, hence — via the reused
  Razborov–Rudich barrier — forces `¬ PRFExists`.

## The dichotomy, and the verdict

The two walls compose into a clean dichotomy: EITHER SAT is a low-complexity state (then the second
law's growth-to-typical says nothing about it — `second_law_counting_not_sat`) OR SAT is
high-complexity (then no efficient certificate of that can exist — `second_law_detector_breaks_crypto`).
Either way the second law does not deliver a SAT-specific circuit lower bound.  It is the *dynamics*
of the incompressibility wall — the arrow that fills the CV volume — not a way across it.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SecondLawOfComplexity

open PallLean.Paper93.DeepMath.PathB.NaturalProofsObstruction

/-! ### The second-law curve: growth then saturation -/

/-- The Brown–Susskind curve: complexity rises linearly with time, then plateaus at `Cmax`. -/
def curve (Cmax t : ℕ) : ℕ := min t Cmax

/-- **The arrow of complexity (proved).**  `curve` is non-decreasing in time. -/
theorem curve_monotone (Cmax a b : ℕ) (h : a ≤ b) : curve Cmax a ≤ curve Cmax b := by
  simp only [curve]; omega

/-- **Saturation ceiling (proved).**  `curve` never exceeds `Cmax` (the cosmological horizon in dS). -/
theorem curve_saturates (Cmax t : ℕ) : curve Cmax t ≤ Cmax := by
  simp only [curve]; omega

/-- **The plateau (proved).**  Past `t = Cmax` the complexity is pinned at `Cmax` — saturation. -/
theorem curve_plateau (Cmax t : ℕ) (h : Cmax ≤ t) : curve Cmax t = Cmax := by
  simp only [curve]; omega

/-! ### The dynamical world and its two walls -/

/-- A complexity-dynamics world: states with a complexity measure `C` bounded by the saturation
ceiling `Cmax`, a distinguished SAT state, and the crypto hypothesis. -/
structure SLWorld where
  /-- the state space -/
  State : Type
  /-- circuit complexity of a state -/
  C : State → ℕ
  /-- the saturation ceiling `~ exp(S)` -/
  Cmax : ℕ
  /-- complexity saturates: it never exceeds the ceiling -/
  bounded : ∀ s, C s ≤ Cmax
  /-- the SAT state -/
  sat : State
  /-- pseudorandom functions exist (the barrier's crypto hypothesis) -/
  PRFExists : Prop

/-- **Complexity saturates (proved).**  The measure is bounded by `Cmax` — the second law's growth
halts at the ceiling. -/
theorem second_law_saturates (W : SLWorld) (s : W.State) : W.C s ≤ W.Cmax := W.bounded s

/-- **Wall A — the arrow is typical-case, not SAT-specific (proved).**  The statistical second law
gives a state of complexity above any sub-maximal `k`; that is consistent with `C sat ≤ k`.  The
growth points at the typical (maximal) state, and SAT need not be typical — the counting barrier. -/
theorem second_law_counting_not_sat (W : SLWorld) (k : ℕ)
    (typical : ∃ s, k < W.C s) (sat_simple : W.C W.sat ≤ k) :
    (∃ s, k < W.C s) ∧ ¬ (k < W.C W.sat) :=
  ⟨typical, by omega⟩

/-- The `ComplexityWorld` induced at threshold `k`: `P/poly` = "complexity `≤ k`". -/
def toComplexityWorld (W : SLWorld) (k : ℕ) (Eff : (W.State → Bool) → Prop) : ComplexityWorld where
  Fn := W.State
  InPpoly := fun s => W.C s ≤ k
  PolyTimeComputable := Eff
  sat := W.sat
  PRFExists := W.PRFExists

/-- **The complexity threshold test IS a `ColossusRuler` (proved).**  `s ↦ (C s ≤ k)` is
poly-checkable (if `C` is efficiently testable), true on every low-complexity state, and false on a
high-complexity SAT. -/
def complexityRuler (W : SLWorld) (k : ℕ) (hsat : k < W.C W.sat)
    (Eff : (W.State → Bool) → Prop) (hEff : Eff (fun s => decide (W.C s ≤ k))) :
    ColossusRuler (toComplexityWorld W k Eff) where
  E := fun s => decide (W.C s ≤ k)
  poly := hEff
  closedOnPpoly := fun s hs => by
    have hcs : W.C s ≤ k := hs
    simp [hcs]
  failsSAT := by
    show decide (W.C W.sat ≤ k) = false
    have hn : ¬ (W.C W.sat ≤ k) := by omega
    simp [hn]

/-- **Wall B — an efficient complexity detector breaks crypto (proved).**  If complexity above
threshold is efficiently testable and SAT is complex, the detector is a natural distinguisher and,
via the Razborov–Rudich barrier, forces `¬ PRFExists`. -/
theorem second_law_detector_breaks_crypto (W : SLWorld) (k : ℕ) (hsat : k < W.C W.sat)
    (Eff : (W.State → Bool) → Prop) (hEff : Eff (fun s => decide (W.C s ≤ k)))
    (barrier : RazborovRudichBarrier (toComplexityWorld W k Eff)) :
    ¬ W.PRFExists :=
  ruler_needs_broken_crypto (toComplexityWorld W k Eff)
    (complexityRuler W k hsat Eff hEff) barrier

end PallLean.Paper93.DeepMath.PathB.SecondLawOfComplexity

#print axioms PallLean.Paper93.DeepMath.PathB.SecondLawOfComplexity.curve_monotone
#print axioms PallLean.Paper93.DeepMath.PathB.SecondLawOfComplexity.second_law_saturates
#print axioms PallLean.Paper93.DeepMath.PathB.SecondLawOfComplexity.second_law_counting_not_sat
#print axioms PallLean.Paper93.DeepMath.PathB.SecondLawOfComplexity.second_law_detector_breaks_crypto
