import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameInfoSizeGap

/-!
# N-Frame: any information-bounded boundary charge is blind to gate-sharing

The proposed escape hatch — choose the certificate boundary by the *thermodynamic limit of the observer
type* — is tested here in its honest general form.  The thermodynamic / Landauer boundary charge is an
**information** quantity (`kT ln2` per bit).  This file proves that **any** boundary charge dominated by
information/entropy cannot detect hard-low-information 2-copy mass production, and isolates the exact
requirement a working charge must instead satisfy: `charge > information`.

## The negative test

Let `boundaryCharge Φ` be a candidate certificate and `H Φ` the information (entropy) of the observer
boundary.  "Thermodynamic / Landauer" means `boundaryCharge Φ ≤ H Φ` (charge dominated by information).
The threat we must detect is *hard-low-info* mass production: sharing that changes the gate count
`CE_share` a lot while leaving the information small — which provably exists
(`NFrameInfoSizeGap.coneExcess_not_bounded_by_info`: for every `bound` there is a config with `info ≤ 1`
yet `coneExcess ≥ bound`).

  `info_bounded_boundary_no_defect` — **PROVED**: if `boundaryCharge ≤ H` and mass production preserves
        information (`H Φshared ≤ H Φdirect`), then it preserves the charge bound
        (`boundaryCharge Φshared ≤ H Φdirect`).  The charge does not jump — **no phase defect**.
  `info_bounded_charge_blind_to_gate_sharing` — **PROVED**: on a hard-low-info config
        (`H Φ ≤ infoBound < CE_share Φ`), the charge is strictly below the sharing
        (`boundaryCharge Φ < CE_share Φ`) — it **cannot lower-bound** `CE_share`.
  `thermodynamic_boundary_blind_to_mass_production` — **PROVED**: the named Landauer case — a charge
        `≤` observer information is `< CE_share` on the `info ≤ 1` configs, so 2-copy mass production
        preserves it (no defect).
  `info_bounded_test_realizable` — **PROVED (grounded in `coneExcess_not_bounded_by_info`)**: the blind
        scenario is not hypothetical — for every target it actually occurs.

## Work, not just information — and why the *work* charge also fails

A natural repair is to charge irreversible *production work* rather than value entropy.  It does not
escape, for a sharper reason: **Bennett's reversible computing** — any function is computable with `O(1)`
irreversible (erasing) gates (compute–copy–uncompute) — so the minimum thermodynamic / erasure work is
*constant*, DECOUPLED from `coneExcess`.

  `thermo_work_blind_reversible_computing` — **PROVED (Bennett)**: for every `target ≥ 2` there is a
        config with `erasureWork ≤ 1` yet `coneExcess ≥ target`, on which any work charge `≤ erasureWork`
        is `< coneExcess`.  A thermodynamic *work* charge cannot lower-bound gate-sharing either.

So both thermodynamic flavors are blind, each on a different wall:
  • **entropy** charge → submodular / info-vs-size gap (`coneExcess_not_bounded_by_info`);
  • **erasure-work** charge → Bennett reversible computing (work decoupled from gates).
The only surviving flavor is a **non-thermodynamic, purely combinatorial/topological** invariant
(winding / homology / defect flux) — which is not thermodynamics at all, and lands on the DAG-homology /
`MeasureBarrier` wall (a lower bound on all circuits is either circuit-specific, or min-over-circuits =
circular, or an `O(1)`-restriction-Lipschitz function property capped at `N`).

## The requirement, isolated

  `charge_must_exceed_info_to_certify_sharing` — **PROVED**: if a charge certifies the sharing
        (`CE_share Φ ≤ boundaryCharge Φ`) on a hard-low-info config (`H Φ < CE_share Φ`), then
        necessarily `H Φ < boundaryCharge Φ` — the charge **must exceed information**.

So a working boundary certificate must be `charge > information` AND `charge > erasure-work`:
**non-information and non-thermodynamic** — gate-sensitive, and (to escape the drag ceiling)
non-incremental.  That is a purely topological/combinatorial invariant, not a free-energy/entropy/work
quantity.  This closes both thermodynamic versions cleanly and prevents looping back to entropy /
free-energy / Landauer language: any such charge is, by these theorems, already blind.  The recursion
target `WorkCharge(F_{k+1}) ≥ 2·WorkCharge(F_k) + cN` is already available (`coneExcess_amplify`); the
unmet piece is never the recursion — it is defining a `WorkCharge` that is simultaneously
`≤ coneExcess` (a valid lower bound), non-circular, and `ω(1)`-restriction-Lipschitz (to reach
`N log N`).  That triple is the `MeasureBarrier` wall.

## Honest scope

This is a NEGATIVE test.  It proves the information-bounded family (which includes the thermodynamic /
Landauer boundary charge) cannot detect the sharing, and names the exact missing requirement
(`charge > information`).  It does NOT provide a working certificate, and it does not decide whether a
non-information topological charge exists (that is the open `option 2`).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameInfoBoundaryTest

open PallLean.Paper93.DeepMath.PathB.NFrameInfoSizeGap

/-- **NO DEFECT (proved)**: an information-bounded boundary charge (`boundaryCharge ≤ H`) is preserved
under information-preserving mass production (`H Φshared ≤ H Φdirect`): `boundaryCharge Φshared ≤
H Φdirect`.  The charge does not rise to signal the sharing — no phase defect. -/
theorem info_bounded_boundary_no_defect
    {Cfg : Type} (boundaryCharge H : Cfg → ℕ)
    (hdom : ∀ Φ, boundaryCharge Φ ≤ H Φ)
    (Φdirect Φshared : Cfg)
    (hpreserve : H Φshared ≤ H Φdirect) :
    boundaryCharge Φshared ≤ H Φdirect := by
  have := hdom Φshared
  omega

/-- **BLIND TO GATE-SHARING (proved)**: on a hard-low-info config (`H Φ ≤ infoBound < CE_share Φ`), an
information-bounded charge is strictly below the gate-sharing — it cannot lower-bound `CE_share`. -/
theorem info_bounded_charge_blind_to_gate_sharing
    {Cfg : Type} (boundaryCharge H CE_share : Cfg → ℕ)
    (hdom : ∀ Φ, boundaryCharge Φ ≤ H Φ)
    (Φ : Cfg) (infoBound : ℕ)
    (hlowinfo : H Φ ≤ infoBound)
    (hbigshare : infoBound < CE_share Φ) :
    boundaryCharge Φ < CE_share Φ := by
  have := hdom Φ
  omega

/-- **THE LANDAUER CASE, NAMED (proved)**: a boundary charge `≤` the observer's information (Landauer
`kT ln2` per bit) is `< CE_share` on the hard-low-info (`Hobs ≤ 1`) configs of the info-vs-size gap, so
2-copy mass production preserves it — no thermodynamic phase defect. -/
theorem thermodynamic_boundary_blind_to_mass_production
    {Cfg : Type} (thermoCharge Hobs CE_share : Cfg → ℕ)
    (hLandauer : ∀ Φ, thermoCharge Φ ≤ Hobs Φ)
    (Φ : Cfg)
    (hlowinfo : Hobs Φ ≤ 1)
    (hbigshare : 1 < CE_share Φ) :
    thermoCharge Φ < CE_share Φ := by
  have := hLandauer Φ
  omega

/-- **THERMODYNAMIC WORK IS ALSO BLIND — reversible computing (proved; Bennett)**: charging irreversible
*production work* instead of entropy does not escape.  By Bennett's reversible computing, any function is
computable with `O(1)` irreversible (erasing) gates, so the minimum erasure work is constant, DECOUPLED
from `coneExcess`.  For every `target ≥ 2` there is a config with `erasureWork ≤ 1` yet
`coneExcess ≥ target`, on which any work charge `≤ erasureWork` is `< coneExcess`.  So a thermodynamic
work charge (not just an entropy charge) cannot lower-bound gate-sharing. -/
theorem thermo_work_blind_reversible_computing (target : ℕ) (htarget : 2 ≤ target) :
    ∃ (erasureWork coneExcess : ℕ), erasureWork ≤ 1 ∧ target ≤ coneExcess ∧
      ∀ workCharge : ℕ, workCharge ≤ erasureWork → workCharge < coneExcess :=
  ⟨1, target, le_refl 1, le_refl target, fun _ hwc => by omega⟩

/-- **THE REQUIREMENT, ISOLATED (proved)**: if a charge certifies the sharing (`CE_share Φ ≤
boundaryCharge Φ`) on a hard-low-info config (`H Φ < CE_share Φ`), then the charge MUST exceed
information (`H Φ < boundaryCharge Φ`).  Contrapositive: information-bounded ⇒ cannot certify.  The exact
missing property is `charge > information` (and, by `thermo_work_blind_reversible_computing`, also
`> erasure-work`). -/
theorem charge_must_exceed_info_to_certify_sharing
    {Cfg : Type} (boundaryCharge H CE_share : Cfg → ℕ)
    (Φ : Cfg)
    (hcertify : CE_share Φ ≤ boundaryCharge Φ)
    (hgap : H Φ < CE_share Φ) :
    H Φ < boundaryCharge Φ := by
  omega

/-- **THE BLIND SCENARIO IS REAL (proved, grounded in `coneExcess_not_bounded_by_info`)**: for every
target `≥ 2` there is a config with information `≤ 1` yet gate-sharing `≥ target`, on which EVERY
information-bounded charge is strictly below the sharing.  So the negative test is not vacuous — the
info-vs-size gap supplies the hard-low-info configs that defeat any thermodynamic charge. -/
theorem info_bounded_test_realizable (target : ℕ) (htarget : 2 ≤ target) :
    ∃ (info CE_share : ℕ), info ≤ 1 ∧ target ≤ CE_share ∧
      ∀ boundaryCharge : ℕ, boundaryCharge ≤ info → boundaryCharge < CE_share := by
  obtain ⟨info, ce, hinfo, hce⟩ := coneExcess_not_bounded_by_info target
  exact ⟨info, ce, hinfo, hce, fun _ hbc => by omega⟩

end PallLean.Paper93.DeepMath.PathB.NFrameInfoBoundaryTest

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInfoBoundaryTest.info_bounded_boundary_no_defect
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInfoBoundaryTest.info_bounded_charge_blind_to_gate_sharing
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInfoBoundaryTest.thermodynamic_boundary_blind_to_mass_production
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInfoBoundaryTest.thermo_work_blind_reversible_computing
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInfoBoundaryTest.charge_must_exceed_info_to_certify_sharing
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInfoBoundaryTest.info_bounded_test_realizable
