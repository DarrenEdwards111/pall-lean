import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeUVTransport
import PallLean.Paper93.DeepMath.PathB.ZeroGaugeNPIdentityMinorObstruction
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeNonzeroFrontier
import PallLean.PaperFaithfulCompilation

/-!
# Transporting the zero / constant projection to the flat SAT-decider gauge space

This file mirrors `SATDeciderGaugeUVTransport` for the **zero/constant
projection shortcut**.  Instead of transporting the paper-faithful `piPhi`
projection, we transport the candidate `Π⋆ = 0` (the zero linear map on the
UV ambient `PMnPoly`).  The resulting flat endomorphism is the zero linear
map on `SATDeciderGaugeSpace`.

The zero linear map is rank-monotone (its image always has SPDP rank `0`)
and idempotent (a projection gauge), so it discharges the structural
fields of `IsAmplituhedronGauge` trivially.  However, the same vanishing
that makes it rank-monotone collapses the projected NP-side lower bound
to `0`, which contradicts the positive identity-minor binomial bound at
the paper scale `n ≥ 2 ^ 804`.  In this sense the projected lower bound
becomes vacuous and the zero route cannot be a valid SAT-decider gauge.

For a "constant projection" — a linear map whose image is a single
polynomial — linearity forces the constant value to be `0`, so the
constant route reduces to the zero route by `LinearMap.map_zero`.

This file is kernel-only.  No `sorry`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine

/-! ### The zero candidate at the UV level -/

/-- The **zero / constant projection** candidate on the UV ambient space.

This is the structural counterpart of `piPhi (satDeciderGaugeUVSplit …)`
in `SATDeciderGaugeUVTransport`: a candidate linear endomorphism on the
UV polynomial space.  The zero linear map is the unique linear map that
collapses every input to a constant (necessarily `0`, by linearity). -/
noncomputable def satDeciderGaugeZeroProjectionUV
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    PMnPoly (satDeciderGaugeUVSplit M n hn2 htb hns) →ₗ[Rat]
      PMnPoly (satDeciderGaugeUVSplit M n hn2 htb hns) :=
  (0 : PMnPoly (satDeciderGaugeUVSplit M n hn2 htb hns) →ₗ[Rat]
        PMnPoly (satDeciderGaugeUVSplit M n hn2 htb hns))

/-- The UV zero projection sends every polynomial to `0`. -/
theorem satDeciderGaugeZeroProjectionUV_apply
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (q : PMnPoly (satDeciderGaugeUVSplit M n hn2 htb hns)) :
    satDeciderGaugeZeroProjectionUV M n hn2 htb hns q = 0 := by
  unfold satDeciderGaugeZeroProjectionUV
  exact LinearMap.zero_apply q

/-- The UV zero projection is idempotent: `0 ∘ 0 = 0`.

This is the structural shape of a projection gauge in the UV ambient. -/
theorem satDeciderGaugeZeroProjectionUV_idempotent
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeZeroProjectionUV M n hn2 htb hns ∘ₗ
        satDeciderGaugeZeroProjectionUV M n hn2 htb hns =
      satDeciderGaugeZeroProjectionUV M n hn2 htb hns := by
  apply LinearMap.ext
  intro q
  simp [satDeciderGaugeZeroProjectionUV_apply]

/-! ### Transporting the zero projection back to the flat gauge space -/

/-- Concrete flat SAT-decider gauge obtained by transporting the zero
projection through the same UV pipeline as `satDeciderGaugeUVTransport`,
but with `piPhi` replaced by the zero linear map. -/
noncomputable def satDeciderGaugeZeroProjectionTransport
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeMap M n hn2 htb hns :=
  satDeciderGaugeUVToFlat M n hn2 htb hns ∘ₗ
    satDeciderGaugeZeroProjectionUV M n hn2 htb hns ∘ₗ
      satDeciderGaugeFlatToUV M n hn2 htb hns

/-- Applying the transported zero projection to any flat polynomial yields
`0`.  The middle factor zeroes everything before the back-rename can
recover any nontrivial information. -/
theorem satDeciderGaugeZeroProjectionTransport_apply
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    satDeciderGaugeZeroProjectionTransport M n hn2 htb hns p = 0 := by
  unfold satDeciderGaugeZeroProjectionTransport
  simp only [LinearMap.comp_apply,
    satDeciderGaugeZeroProjectionUV_apply, map_zero]

/-- The transported zero projection is identically the zero linear map on
the flat SAT-decider polynomial space. -/
theorem satDeciderGaugeZeroProjectionTransport_eq_zero
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeZeroProjectionTransport M n hn2 htb hns =
      (0 : SATDeciderGaugeMap M n hn2 htb hns) := by
  apply LinearMap.ext
  intro p
  rw [satDeciderGaugeZeroProjectionTransport_apply]
  exact (LinearMap.zero_apply p).symm

/-! ### Structural fields the zero transport satisfies trivially -/

/-- The transported zero projection is idempotent, hence a
`GaugeMonotonicity.IsProjectionGauge`. -/
theorem satDeciderGaugeZeroProjectionTransport_isProjectionGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    GaugeMonotonicity.IsProjectionGauge
      (satDeciderGaugeZeroProjectionTransport M n hn2 htb hns) := by
  refine ⟨?_⟩
  apply LinearMap.ext
  intro p
  simp [satDeciderGaugeZeroProjectionTransport_apply]

/-- The transported zero projection is rank-monotone in the generic
`GaugeMonotonicity` vocabulary: its image is the zero polynomial, whose
SPDP rank is `0`, which is `≤` any natural number. -/
theorem satDeciderGaugeZeroProjectionTransport_isRankMonotoneGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    GaugeMonotonicity.IsRankMonotoneGauge
      (cook_levin_compilation M n hn2 htb hns).partition
      (satDeciderGaugeZeroProjectionTransport M n hn2 htb hns) := by
  intro κ ℓ p
  rw [satDeciderGaugeZeroProjectionTransport_apply,
      mlBlockedSpdpRank_zero]
  exact Nat.zero_le _

/-- Rank monotonicity for the transported zero projection, stated as the
SAT-decider gauge subgoal. -/
theorem satDeciderGaugeZeroProjectionTransport_rankMonotonicity
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (satDeciderGaugeZeroProjectionTransport M n hn2 htb hns) :=
  satDeciderGaugeZeroProjectionTransport_isRankMonotoneGauge
    M n hn2 htb hns

/-- The transported zero projection trivially satisfies the projected
P-side bound: any quantity is `≤` itself, and the projected polynomial is
`0`, so the bound `0 ≤ n ^ 200` is immediate. -/
theorem satDeciderGaugeZeroProjectionTransport_pSideBound
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (satDeciderGaugeZeroProjectionTransport M n hn2 htb hns) := by
  unfold SATDeciderGaugePSideBound
  rw [satDeciderGaugeZeroProjectionTransport_apply,
      mlBlockedSpdpRank_zero]
  exact Nat.zero_le _

/-! ### The structural obstruction: vacuous projected lower bound -/

/-- **Core obstruction.**  The transported zero projection cannot satisfy
the SAT-decider NP identity-minor preservation subgoal whenever the
binomial identity-minor lower bound is positive.

The image of `compiledPoly` under the transported zero gauge is `0`, so
the projected SPDP rank is `0`.  This makes the projected NP-side lower
bound vacuous: it asserts `Nat.choose (n/3) (Nat.log 2 n) ≤ 0`, which
contradicts `0 < Nat.choose (n/3) (Nat.log 2 n)`. -/
theorem satDeciderGaugeZeroProjectionTransport_not_npIdentityMinorPreservation
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (hbinom_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n)) :
    ¬ SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (satDeciderGaugeZeroProjectionTransport M n hn2 htb hns) := by
  rw [satDeciderGaugeZeroProjectionTransport_eq_zero]
  exact zeroGauge_not_npIdentityMinorPreservation_of_binomial_pos
    M n hn2 htb hns hdec hbinom_pos

/-- The transported zero projection cannot satisfy the full three-subgoal
package whenever the binomial identity-minor lower bound is positive. -/
theorem satDeciderGaugeZeroProjectionTransport_not_satDeciderGaugeSubgoals
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (hbinom_pos : 0 < Nat.choose (n / 3) (Nat.log 2 n)) :
    ¬ SATDeciderGaugeSubgoals M n hn2 htb hns
      (satDeciderGaugeZeroProjectionTransport M n hn2 htb hns) := by
  rw [satDeciderGaugeZeroProjectionTransport_eq_zero]
  exact zeroGauge_not_satDeciderGaugeSubgoals_of_binomial_pos
    M n hn2 htb hns hdec hbinom_pos

/-- At the paper scale `n ≥ 2 ^ 804`, the binomial identity-minor lower
bound is positive (via `arithmetic_gap_2pow804`), so the transported zero
projection cannot satisfy NP identity-minor preservation. -/
theorem satDeciderGaugeZeroProjectionTransport_not_npIdentityMinorPreservation_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ¬ SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (satDeciderGaugeZeroProjectionTransport M n hn2 htb hns) :=
  satDeciderGaugeZeroProjectionTransport_not_npIdentityMinorPreservation
    M n hn2 htb hns hdec
    (lt_of_le_of_lt (Nat.zero_le _)
      (PaperFaithfulCompilation.arithmetic_gap_2pow804 n hn))

/-- At the paper scale `n ≥ 2 ^ 804`, the transported zero projection
cannot satisfy the full SAT-decider three-subgoal package. -/
theorem satDeciderGaugeZeroProjectionTransport_not_satDeciderGaugeSubgoals_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ¬ SATDeciderGaugeSubgoals M n hn2 htb hns
      (satDeciderGaugeZeroProjectionTransport M n hn2 htb hns) :=
  satDeciderGaugeZeroProjectionTransport_not_satDeciderGaugeSubgoals
    M n hn2 htb hns hdec
    (lt_of_le_of_lt (Nat.zero_le _)
      (PaperFaithfulCompilation.arithmetic_gap_2pow804 n hn))

/-! ### Constant-projection collapse to the zero route

A "constant projection" — a linear endomorphism `L` whose image consists
of a single polynomial `c` — must satisfy `c = L 0 = 0` by linearity.  So
in linear-map land, the only constant projection is the zero map, and the
constant route is identical to the zero route. -/

/-- **Constant-projection collapse.**  Any linear endomorphism of the
SAT-decider gauge space whose image is a single polynomial `c` must have
`c = 0`. -/
theorem satDeciderGaugeMap_constant_image_eq_zero
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (c : SATDeciderGaugeSpace M n hn2 htb hns)
    (hconst : ∀ p : SATDeciderGaugeSpace M n hn2 htb hns, gauge p = c) :
    c = 0 := by
  have h0 : gauge 0 = c := hconst 0
  have hzero : gauge 0 = 0 := LinearMap.map_zero gauge
  exact h0 ▸ hzero.symm |>.symm

/-- **Constant-projection collapse, gauge form.**  Any linear endomorphism
whose image is a single polynomial is identically the zero linear map. -/
theorem satDeciderGaugeMap_constant_eq_zero
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (c : SATDeciderGaugeSpace M n hn2 htb hns)
    (hconst : ∀ p : SATDeciderGaugeSpace M n hn2 htb hns, gauge p = c) :
    gauge = 0 := by
  have hc : c = 0 :=
    satDeciderGaugeMap_constant_image_eq_zero
      M n hn2 htb hns gauge c hconst
  apply LinearMap.ext
  intro p
  simp [hconst p, hc]

/-- **Constant projection cannot be a SAT-decider gauge.**  Any constant
linear map fails NP identity-minor preservation at the paper scale, by
collapse to the zero route. -/
theorem satDeciderGaugeMap_constant_not_npIdentityMinorPreservation_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (c : SATDeciderGaugeSpace M n hn2 htb hns)
    (hconst : ∀ p : SATDeciderGaugeSpace M n hn2 htb hns, gauge p = c) :
    ¬ SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge := by
  have hgauge_zero : gauge = 0 :=
    satDeciderGaugeMap_constant_eq_zero
      M n hn2 htb hns gauge c hconst
  rw [hgauge_zero]
  exact zeroGauge_not_npIdentityMinorPreservation_at_large_n
    M n hn hn2 htb hns hdec

/-! ## Axiom audit anchors -/

#print axioms satDeciderGaugeZeroProjectionUV_apply
#print axioms satDeciderGaugeZeroProjectionUV_idempotent
#print axioms satDeciderGaugeZeroProjectionTransport_apply
#print axioms satDeciderGaugeZeroProjectionTransport_eq_zero
#print axioms satDeciderGaugeZeroProjectionTransport_isProjectionGauge
#print axioms satDeciderGaugeZeroProjectionTransport_isRankMonotoneGauge
#print axioms satDeciderGaugeZeroProjectionTransport_rankMonotonicity
#print axioms satDeciderGaugeZeroProjectionTransport_pSideBound
#print axioms satDeciderGaugeZeroProjectionTransport_not_npIdentityMinorPreservation
#print axioms satDeciderGaugeZeroProjectionTransport_not_satDeciderGaugeSubgoals
#print axioms satDeciderGaugeZeroProjectionTransport_not_npIdentityMinorPreservation_at_large_n
#print axioms satDeciderGaugeZeroProjectionTransport_not_satDeciderGaugeSubgoals_at_large_n
#print axioms satDeciderGaugeMap_constant_image_eq_zero
#print axioms satDeciderGaugeMap_constant_eq_zero
#print axioms satDeciderGaugeMap_constant_not_npIdentityMinorPreservation_at_large_n

end PallLean.Paper93.DeepMath.PathB
