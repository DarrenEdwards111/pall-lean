import PallLean.Paper93.DeepMath.PathC.PiPlusPayloadCloseout
import PallLean.Paper93.DeepMath.PathC.PiPlusRouteBOneWindowSupportObstruction
import PallLean.Paper93.DeepMath.PathB.ZeroProfileNormalFormInstantiationProgress

/-!
# One-window zero common-span obstruction

The current Route-C payload asks for an unprojected one-window zero-profile
common span.  This file proves that this target is too strong at paper scale:
the zero-profile shifted rows already contain all singleton-shift directions,
and those are linearly independent for the Cook--Levin base product because its
constant coefficient is nonzero.

So any unprojected common span must have dimension/cardinality at least the
ambient variable count `n`.  At `n = 2^804`, the one-window profile budget is
only `(806)^8`, far smaller than `n`.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000
set_option maxHeartbeats 1000000

/-- Any unprojected zero-profile common span whose shifted-row family includes
singleton shifts must pay at least the ambient dimension, provided the base
product has nonzero constant coefficient. -/
theorem ambient_le_zeroProfileShiftCommonSpan_budget_of_constCoeff_ne_zero
    {n L κ budget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hκ : 1 ≤ κ)
    (hp0 :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (Finset.univ.prod factors) ≠ 0)
    (hcommon :
      ∃ G : Finset (MvPolynomial (Fin n) ℚ),
        G.card ≤ budget ∧
        zeroProfileShiftImageSet κ factors ⊆
          Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))) :
    n ≤ budget := by
  classical
  rcases hcommon with ⟨G, hG_card, hG_span⟩
  let U : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))
  haveI hU_finite : Module.Finite ℚ ↥U :=
    Module.Finite.span_of_finite ℚ (Finset.finite_toSet G)
  have hrow_mem : ∀ i : Fin n,
      zeroProfileSingletonShiftRow (Finset.univ.prod factors) i ∈ U := by
    intro i
    exact hG_span
      (zeroProfileSingletonShiftRow_mem_shiftImageSet factors i hκ)
  let rowsInU : Fin n → U :=
    fun i => ⟨zeroProfileSingletonShiftRow (Finset.univ.prod factors) i,
      hrow_mem i⟩
  have hli :
      LinearIndependent ℚ
        (fun i : Fin n =>
          zeroProfileSingletonShiftRow (Finset.univ.prod factors) i) :=
    zeroProfileSingletonShiftRows_linearIndependent_of_constCoeff_ne_zero
      (Finset.univ.prod factors) hp0
  have hli_U : LinearIndependent ℚ rowsInU := by
    rw [linearIndependent_iff'] at hli ⊢
    intro s w hw i hi
    apply hli s w ?_ i hi
    have hval := congrArg
      (fun q : U => (q : MvPolynomial (Fin n) ℚ)) hw
    simpa [rowsInU] using hval
  have hcard_le_finrank : n ≤ Module.finrank ℚ ↥U := by
    simpa [Fintype.card_fin] using hli_U.fintype_card_le_finrank
  have hfinrank_le_card : Module.finrank ℚ ↥U ≤ G.card := by
    simpa [U] using
      (finrank_span_finset_le_card G :
        Module.finrank ℚ
          ↥(Submodule.span ℚ
            (↑G : Set (MvPolynomial (Fin n) ℚ))) ≤ G.card)
  exact hcard_le_finrank.trans (hfinrank_le_card.trans hG_card)

/-- The current one-window zero-profile common-span socket forces the ambient
variable count to fit inside the one-window within-profile budget. -/
theorem ambient_le_withinProfileBound_of_cookLevinOneWindowZeroCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hzero : CookLevinOneWindowZeroHistogramShiftCommonSpan M n hn htb hns) :
    n ≤ withinProfileBound (Nat.log 2 n + 1) := by
  apply ambient_le_zeroProfileShiftCommonSpan_budget_of_constCoeff_ne_zero
    (κ := Nat.log 2 n + 1)
    (factors := fun i => (cookLevinFactorList M n hn htb hns).get i)
  · omega
  · change MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (cookLevinZeroProfileBaseProduct M n hn htb hns) ≠ 0
    rw [cookLevinZeroProfileBaseProduct_coeff_zero M n hn htb hns]
    norm_num
  · simpa [CookLevinOneWindowZeroHistogramShiftCommonSpan] using hzero

/-- At paper scale the unprojected one-window zero-profile common span is
impossible: the budget is far below the ambient variable count. -/
theorem not_paperScale_cookLevinOneWindowZeroHistogramShiftCommonSpan
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    ¬ CookLevinOneWindowZeroHistogramShiftCommonSpan
        M (2 ^ 804) paperScale_ge_two htb hns := by
  intro hzero
  have hamb := ambient_le_withinProfileBound_of_cookLevinOneWindowZeroCommonSpan
    M (2 ^ 804) paperScale_ge_two htb hns hzero
  exact not_le_of_gt paperScale_oneWindow_withinProfileBound_lt_ambient hamb

/-- Consequently, the current payload package cannot be inhabited at paper scale
for any machine.  The zero-profile socket must be reformulated, e.g. as a
quotiented/projected zero-profile target, before the final endpoint can close. -/
theorem not_paperScalePiPlusPayloadData_current_zeroSocket
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    ¬ Nonempty (PaperScalePiPlusPayloadData M htb hns) := by
  rintro ⟨D⟩
  exact not_paperScale_cookLevinOneWindowZeroHistogramShiftCommonSpan
    M htb hns D.zero_common_span

/-! ## Axiom audit anchors -/

#print axioms ambient_le_zeroProfileShiftCommonSpan_budget_of_constCoeff_ne_zero
#print axioms ambient_le_withinProfileBound_of_cookLevinOneWindowZeroCommonSpan
#print axioms not_paperScale_cookLevinOneWindowZeroHistogramShiftCommonSpan
#print axioms not_paperScalePiPlusPayloadData_current_zeroSocket

end PallLean.Paper93.DeepMath.PathC
