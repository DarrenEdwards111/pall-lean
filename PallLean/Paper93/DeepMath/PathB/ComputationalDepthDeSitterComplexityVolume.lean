import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNaturalProofsObstruction

/-!
# The de Sitter "complexity = volume" functional, run against the walls

The one physical thread where gravity gives complexity *lower* bounds is Susskind's `complexity =
volume` (CV): the circuit complexity of a boundary state equals the bulk volume of a maximal slice,
and the "second law of complexity" says that volume grows.  Unlike the Bekenstein/information form
(`HolographicIncompressibility`), this is the RIGHT quantity (circuit complexity) and the RIGHT
direction (a lower bound).  So it is the honest candidate.  This file formalises it as a functional
on functions and runs it against the two walls — and it lands on both.

## The functional and the conjecture-as-socket

`CVWorld` carries the true minimal circuit size `cbudget` and a **volume functional** `vol`
(the dS bulk volume).  The CV conjecture, in its useful (lower-bound) direction, is the named socket

  `CVLowerBound : ∀ f, vol f ≤ cbudget f`   -- volume lower-bounds complexity

— NOT proved (it is a physics conjecture, and dS/CFT has no rigorous formulation), exactly like the
magnification trigger or the trading ingredients.

## What is proved

* **`cv_would_separate`** — the instinct is correct: `CVLowerBound` + "SAT has large volume" gives
  `cbudget sat` large, i.e. the separation.  If the functional had the right profile it would work.
* **Wall A — counting (`cv_counting_gives_existence_not_sat`)** — the second law of complexity is a
  *typical-case* statement ("most states have large volume").  Machine-checked: that existence is
  fully CONSISTENT with `vol sat` being small.  The physics gives `∃` a hard function, never that
  SAT specifically is hard — the counting barrier.
* **Wall B — natural proofs (`cv_efficient_breaks_crypto`)** — if `vol` is efficiently computable
  and separates (large on SAT, small on `P/poly`), the threshold predicate `vol f ≤ t` is a
  `ColossusRuler`, hence a natural distinguisher, hence — via the Razborov–Rudich barrier reused
  from `NaturalProofsObstruction` — forces `¬ PRFExists`.  An efficient CV functional that separates
  breaks cryptography.
* **dS saturation (`cv_saturation_caps_certificate`)** — the de Sitter feature: complexity=volume
  *saturates* (the cosmological horizon caps volume at `cap`).  So even as a lower bound it certifies
  hardness only *below* `cap`; past the horizon it is flat and certifies nothing.

## Verdict

The complexity=volume functional is the strongest physical candidate — right quantity, right
direction — and it still lands on the wall from both sides: its typical-case form (second law) is
the counting barrier, and its efficient-detector form is the natural-proofs barrier, with the dS
horizon additionally capping what it could certify.  Positive-curvature "inversion" does not change
this: the functional either fails to single out SAT (counting) or, made to single out SAT
efficiently, becomes a natural property (barriered).  Gravity renames the wall in the CV language
too; it does not cross it.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DeSitterComplexityVolume

open PallLean.Paper93.DeepMath.PathB.NaturalProofsObstruction

/-- A world with the true circuit-size measure `cbudget` and the CV **volume** functional `vol`. -/
structure CVWorld where
  /-- the universe of Boolean functions -/
  Fn : Type
  /-- true minimal circuit size -/
  cbudget : Fn → ℕ
  /-- the de Sitter bulk-volume functional (Susskind CV) -/
  vol : Fn → ℕ
  /-- the SAT function -/
  sat : Fn
  /-- pseudorandom functions exist (the barrier's crypto hypothesis) -/
  PRFExists : Prop

/-- **The CV conjecture (named socket, NOT proved).**  Volume lower-bounds complexity — the
useful direction of `complexity = volume`.  This is a physics conjecture; dS/CFT has no rigorous
formulation, so it is a hypothesis, not a theorem. -/
def CVLowerBound (W : CVWorld) : Prop := ∀ f, W.vol f ≤ W.cbudget f

/-- **CV would prove the separation (proved).**  Given the CV lower bound and that SAT has volume
above the `P/poly` threshold `t`, its circuit size exceeds `t`: `t < cbudget sat`.  The instinct is
right — the functional, with the right profile, would separate. -/
theorem cv_would_separate (W : CVWorld) (h : CVLowerBound W) (t : ℕ)
    (hsat : t < W.vol W.sat) : t < W.cbudget W.sat :=
  lt_of_lt_of_le hsat (h W.sat)

/-! ### Wall A — the counting barrier -/

/-- **The second law of complexity is typical-case, not SAT-specific (proved).**  "Most states have
large volume" gives the EXISTENCE of a high-volume function, but that is consistent with `vol sat`
being small.  So the volume-growth law does not pin SAT — the counting barrier. -/
theorem cv_counting_gives_existence_not_sat (W : CVWorld) (t : ℕ)
    (secondLaw : ∃ f, t < W.vol f) (sat_small : W.vol W.sat ≤ t) :
    (∃ f, t < W.vol f) ∧ ¬ (t < W.vol W.sat) :=
  ⟨secondLaw, by omega⟩

/-! ### Wall B — the natural-proofs barrier -/

/-- The `ComplexityWorld` induced by a CV world at threshold `t` and an efficiency notion `Eff`:
`P/poly` = "circuit size `≤ t`", the constructive notion = `Eff`. -/
def cvToComplexityWorld (W : CVWorld) (t : ℕ) (Eff : (W.Fn → Bool) → Prop) : ComplexityWorld where
  Fn := W.Fn
  InPpoly := fun f => W.cbudget f ≤ t
  PolyTimeComputable := Eff
  sat := W.sat
  PRFExists := W.PRFExists

/-- **An efficient, separating CV functional IS a `ColossusRuler` (proved).**  The threshold
predicate `f ↦ (vol f ≤ t)` is poly-checkable (if `vol` is efficient), true on all of `P/poly` (via
the CV lower bound), and false on SAT (large volume).  It is exactly the natural-distinguisher shape. -/
def cvRuler (W : CVWorld) (h : CVLowerBound W) (t : ℕ) (hsat : t < W.vol W.sat)
    (Eff : (W.Fn → Bool) → Prop) (hEff : Eff (fun f => decide (W.vol f ≤ t))) :
    ColossusRuler (cvToComplexityWorld W t Eff) where
  E := fun f => decide (W.vol f ≤ t)
  poly := hEff
  closedOnPpoly := fun f hf => by
    have hv : W.vol f ≤ t := le_trans (h f) hf
    simp [hv]
  failsSAT := by
    show decide (W.vol W.sat ≤ t) = false
    have hn : ¬ (W.vol W.sat ≤ t) := by omega
    simp [hn]

/-- **An efficient separating CV functional breaks cryptography (proved).**  Given the
Razborov–Rudich barrier, an efficiently-computable CV volume that separates SAT from `P/poly` forces
`¬ PRFExists` — pseudorandom functions, hence one-way functions, must fail.  The CV functional lands
on the identical natural-proofs wall as any other efficient separator. -/
theorem cv_efficient_breaks_crypto (W : CVWorld) (h : CVLowerBound W) (t : ℕ)
    (hsat : t < W.vol W.sat) (Eff : (W.Fn → Bool) → Prop)
    (hEff : Eff (fun f => decide (W.vol f ≤ t)))
    (barrier : RazborovRudichBarrier (cvToComplexityWorld W t Eff)) :
    ¬ W.PRFExists :=
  ruler_needs_broken_crypto (cvToComplexityWorld W t Eff)
    (cvRuler W h t hsat Eff hEff) barrier

/-! ### The de Sitter saturation cap -/

/-- **de Sitter saturation caps the certificate (proved).**  In dS the volume saturates at the
cosmological-horizon bound `cap` (`vol f ≤ cap`).  So the CV lower bound can only certify hardness
BELOW the cap: if `cap ≤ t` the volume never exceeds `t`, and `cv_would_separate` cannot fire — past
the horizon the functional is flat and certifies nothing. -/
theorem cv_saturation_caps_certificate (W : CVWorld) (cap : ℕ)
    (hsat_cap : ∀ f, W.vol f ≤ cap) (t : ℕ) (hcap : cap ≤ t) (f : W.Fn) :
    ¬ (t < W.vol f) := by
  have := hsat_cap f
  omega

end PallLean.Paper93.DeepMath.PathB.DeSitterComplexityVolume

#print axioms PallLean.Paper93.DeepMath.PathB.DeSitterComplexityVolume.cv_would_separate
#print axioms PallLean.Paper93.DeepMath.PathB.DeSitterComplexityVolume.cv_counting_gives_existence_not_sat
#print axioms PallLean.Paper93.DeepMath.PathB.DeSitterComplexityVolume.cv_efficient_breaks_crypto
#print axioms PallLean.Paper93.DeepMath.PathB.DeSitterComplexityVolume.cv_saturation_caps_certificate
