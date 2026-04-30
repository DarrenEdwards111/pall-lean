import PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiExtraction
import PallLean.Paper93.Paper283.RouteBZeroProfileQuotientedCompressionProof
import PallLean.Paper93.DeepMath.PathB.ZeroProfileConcreteNormalFormProgress

/-!
# Strict `TΦ` singleton-quotient final hook

This file specializes the strict `TΦ` projected/log-window consumer to the
exact singleton-quotient zero-profile target.  It keeps the final proof gate
honest: the remaining assumptions are precisely the projected quotient budget
and the strict `TΦ` projected P-window containment.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler.Step252
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Strict `TΦ` contradiction from the exact singleton-quotient zero-profile
budget and strict projected P-window containment. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_projectedTypeBudget
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
        withinProfileBound (Nat.log 2 n))
    (hcontrol :
      RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_zeroProfileQuotientedShiftCommonSpan
    M n hn hn2 htb hns hdec
    (zeroProfileQuotientBySingletonShiftProjection
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
    (cookLevinZeroProfileQuotientedShiftCommonSpan_of_singletonQuotient_projectedTypeBudget
      M n hn2 htb hns hbudget)
    hcontrol

/-- Strict `TΦ` contradiction from the semantic singleton normalizer route.

This is the paper-facing replacement for the failed raw derivative
representative target: the zero-profile row and the extracted derivative row
are compared after the explicit normal-form projection, and the P-side budget
is paid on the normalizer image. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_commonSpan
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    {budget : Nat}
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileSingletonNormalFormProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        budget)
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormIdentity
        M n hn2 htb hns)
    (hbudget : budget <= n ^ 200) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm
    M n hn hn2 htb hns hdec hspan hnorm hbudget

/-- Strict `TΦ` contradiction from the semantic singleton normalizer route
with singleton residuals paid explicitly.

This is the proof-facing Route B hook after the raw derivative representative
obstruction: it only asks for normalized row equality, and budgets the
singleton-shift residual directions separately at cost `n`. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_commonSpan_normalizedRows
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    {budget : Nat}
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileSingletonNormalFormProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        budget)
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns)
    (hbudget : budget + n <= n ^ 200) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_normalizedRows
    M n hn hn2 htb hns hdec hspan hnorm hbudget

/-- Strict `TΦ` contradiction from the normalizer-image zero-profile common
span and the residual-balance row algebra.

This is the paper-facing target after removing the obstructed raw
`concreteW` row-embedding package from the singleton-normalizer branch.  The
P-side input is exactly the compressed normalizer-image span, and the row
algebra input is exactly the quotient/residual identity. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_commonSpan_residualBalance
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    {budget : Nat}
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileSingletonNormalFormProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        budget)
    (hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)))
    (hbudget : budget + n <= n ^ 200) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_commonSpan_normalizedRows
    M n hn hn2 htb hns hdec hspan
    ((routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_iff_singletonResidual
      M n hn2 htb hns).mpr
      (routeBPaperFaithfulTPhi_singletonResidual_of_restrictedResidualBalance
        M n hn2 htb hns hres))
    hbudget

/-- At paper scale, the singleton normal-form image budget plus the explicitly
paid ambient singleton residual still fits inside the strict `TΦ` `n^200`
P-side envelope. -/
theorem routeBPaperFaithfulTPhi_singletonNormalFormBudget_add_ambient_le_pow_200
    (n : Nat) (hn2 : n >= 2) :
    zeroProfileSymmetricProfileDim zeroProfileHistogram + n <= n ^ 200 := by
  rw [zeroProfileSymmetricProfileDim_zeroProfileHistogram]
  have hnpos : 0 < n := by omega
  have hquad : 1 + n <= n ^ 2 := by
    nlinarith [hn2]
  exact hquad.trans (Nat.pow_le_pow_right hnpos (by norm_num : 2 <= 200))

/-- At paper scale, the full within-profile zero-profile budget plus the
explicit singleton residual budget still fits inside `n^200`. -/
theorem routeBPaperFaithfulTPhi_withinProfileBound_add_ambient_le_pow_200
    (n : Nat) (hn2 : n >= 2) :
    withinProfileBound (Nat.log 2 n) + n <= n ^ 200 := by
  rw [WithinProfileBound.withinProfileBound_eq_pow8]
  have hnpos : 0 < n := by omega
  have hbase : Nat.log 2 n + 1 <= 2 * n := by
    have hlog : Nat.log 2 n <= n := Nat.log_le_self 2 n
    omega
  have hpow8 :
      (Nat.log 2 n + 1) ^ 8 <= (2 * n) ^ 8 :=
    Nat.pow_le_pow_left hbase 8
  have htwo_pow : (2 : Nat) ^ 8 <= n ^ 8 :=
    Nat.pow_le_pow_left hn2 8
  have hmul :
      (2 * n) ^ 8 <= n ^ 16 := by
    calc
      (2 * n) ^ 8 = 2 ^ 8 * n ^ 8 := by rw [Nat.mul_pow]
      _ <= n ^ 8 * n ^ 8 := Nat.mul_le_mul_right (n ^ 8) htwo_pow
      _ = n ^ 16 := by rw [← Nat.pow_add]
  have hwithin16 :
      (Nat.log 2 n + 1) ^ 8 <= n ^ 16 :=
    hpow8.trans hmul
  have hn16 : n <= n ^ 16 := by
    calc
      n = n ^ 1 := by rw [pow_one]
      _ <= n ^ 16 := Nat.pow_le_pow_right hnpos (by norm_num : 1 <= 16)
  have hsum16 :
      (Nat.log 2 n + 1) ^ 8 + n <= 2 * n ^ 16 := by
    have hsum :
        (Nat.log 2 n + 1) ^ 8 + n <= n ^ 16 + n ^ 16 :=
      Nat.add_le_add hwithin16 hn16
    simpa [two_mul] using hsum
  have htwo16_le_17 :
      2 * n ^ 16 <= n ^ 17 := by
    have hmul' : 2 * n ^ 16 <= n * n ^ 16 :=
      Nat.mul_le_mul_right (n ^ 16) hn2
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul'
  have h17_200 :
      n ^ 17 <= n ^ 200 :=
    Nat.pow_le_pow_right hnpos (by norm_num : 17 <= 200)
  exact hsum16.trans (htwo16_le_17.trans h17_200)

/-- A finite common span for the singleton quotient pushes through the
explicit singleton normalizer with no budget loss.

This is the direct projected/quotiented normalizer-image bridge: the quotient
is used only as a classifier, while the resulting basis is normalized by the
semantic normal-form projection. -/
theorem zeroProfileProjectedCommonSpanWithBudget_singletonNormalForm_of_singletonQuotient_commonSpan
    {n L κ budget : Nat}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hconst :
      MvPolynomial.coeff (0 : Fin n →₀ Nat)
        (Finset.univ.prod factors) = (1 : ℚ))
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget κ factors
        (zeroProfileQuotientBySingletonShiftProjection factors)
        budget) :
    ZeroProfileProjectedCommonSpanWithBudget κ factors
      (zeroProfileSingletonNormalFormProjection factors)
      budget := by
  classical
  rcases hspan with ⟨G, hG_card, hG_span⟩
  let N := zeroProfileSingletonNormalFormProjection factors
  let Q := zeroProfileQuotientBySingletonShiftProjection factors
  refine ⟨G.image N, ?_, ?_⟩
  · exact (Finset.card_image_le).trans hG_card
  · intro z hz
    rcases hz with ⟨row, hrow, rfl⟩
    have hQ_span :
        Q row ∈ Submodule.span ℚ
          (↑G : Set (MvPolynomial (Fin n) ℚ)) :=
      hG_span ⟨row, hrow, rfl⟩
    have hNQ_mem :
        N (Q row) ∈ Submodule.map N
          (Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))) :=
      ⟨Q row, hQ_span, rfl⟩
    have hNQ_span :
        N (Q row) ∈ Submodule.span ℚ
          (↑(G.image N) : Set (MvPolynomial (Fin n) ℚ)) := by
      rw [Submodule.map_span] at hNQ_mem
      simpa [N] using hNQ_mem
    have hN_eq :
        N row = N (Q row) := by
      exact
        zeroProfileSingletonNormalFormProjection_eq_of_sub_mem_singletonShiftSubspace
          factors hconst
          (zeroProfileQuotientBySingletonShiftProjection_residual_mem_singletonShiftSubspace
            factors row)
    change N row ∈ Submodule.span ℚ
      (↑(G.image N) : Set (MvPolynomial (Fin n) ℚ))
    rw [hN_eq]
    exact hNQ_span

/-- The exact singleton-quotient projected type budget supplies the
normalizer-image common span directly. -/
theorem zeroProfileProjectedCommonSpanWithBudget_singletonNormalForm_of_singletonQuotient_projectedTypeBudget
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      (zeroProfileSingletonNormalFormProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
      (zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) := by
  classical
  let factors :=
    fun i => (cookLevinFactorList M n hn2 htb hns).get i
  have hconst :
      MvPolynomial.coeff (0 : Fin n →₀ Nat)
        (Finset.univ.prod factors) = (1 : ℚ) := by
    simpa [factors, cookLevinZeroProfileBaseProduct] using
      cookLevinZeroProfileBaseProduct_coeff_zero M n hn2 htb hns
  exact
    zeroProfileProjectedCommonSpanWithBudget_singletonNormalForm_of_singletonQuotient_commonSpan
      factors hconst
      (zeroProfileProjectedCommonSpanWithBudget_singletonQuotient_projectedFinrank
        (Nat.log 2 n) factors)

/-- Strict `TΦ` contradiction from the projected singleton quotient type
budget and the residual-balance row algebra, routed through the explicit
normalizer image rather than the impossible unprojected zero-histogram span. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_residualBalance
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
        withinProfileBound (Nat.log 2 n))
    (hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_commonSpan_residualBalance
    M n hn hn2 htb hns hdec
    (zeroProfileProjectedCommonSpanWithBudget_singletonNormalForm_of_singletonQuotient_projectedTypeBudget
      M n hn2 htb hns)
    hres
    ((Nat.add_le_add_right hbudget n).trans
      (routeBPaperFaithfulTPhi_withinProfileBound_add_ambient_le_pow_200
        n hn2))

/-- Strict `TΦ` contradiction from the exact singleton-quotient projected type
budget and normalized row equality.

This is the paper-facing endpoint of the singleton-normalizer route: it uses
the quotient only to control the compressed normalizer image, then pays the
discarded singleton residual directions at ambient cost `n` inside the
`n^200` envelope.  It deliberately avoids requiring the raw derivative row to
be the arbitrary quotient representative. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_normalizedRows
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
        withinProfileBound (Nat.log 2 n))
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_commonSpan_normalizedRows
    M n hn hn2 htb hns hdec
    (zeroProfileProjectedCommonSpanWithBudget_singletonNormalForm_of_singletonQuotient_projectedTypeBudget
      M n hn2 htb hns)
    hnorm
    ((Nat.add_le_add_right hbudget n).trans
      (routeBPaperFaithfulTPhi_withinProfileBound_add_ambient_le_pow_200
        n hn2))

/-- Strict `TΦ` contradiction from the exact singleton-quotient projected type
budget and the normalized non-singleton coefficient computation.

The singleton coordinates are erased by the explicit normalizer on both sides,
so this is the smallest coefficient-level row-algebra input needed by the
normalizer route. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_normalizedCoeff
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
        withinProfileBound (Nat.log 2 n))
    (hcoeff :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_normalizedRows
    M n hn hn2 htb hns hdec hbudget
    ((routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_iff_singletonResidual
      M n hn2 htb hns).mpr
      (routeBPaperFaithfulTPhi_singletonResidual_of_normalized_nonSingleton_coeff
        M n hn2 htb hns hcoeff))

/-- Expanded coefficient-balance form of the exact projected-budget strict
`TΦ` route. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_normalizedCoeffBalance
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
        withinProfileBound (Nat.log 2 n))
    (hbalance :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_normalizedCoeff
    M n hn hn2 htb hns hdec hbudget
    (routeBPaperFaithfulTPhi_normalizedNonSingletonCoeffIdentity_of_coeffBalance
      M n hn2 htb hns hbalance)

/-- Strict `TΦ` contradiction from the exact projected singleton quotient
budget, normalized row equality, and the derivative fixed-representative
condition.

This is the fully semantic decomposition of the direct residual-balance gate:
normalized row equality supplies the singleton-residual algebra, and the
fixed-representative condition is exactly what upgrades quotient equality to
the raw residual-balance consumer. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_normalizedRows_fixedDerivative
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
        withinProfileBound (Nat.log 2 n))
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns)
    (hfix :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_residualBalance
    M n hn hn2 htb hns hdec hbudget
    (routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientResidualBalance_of_normalizedRows_derivativeFixed
      M n hn2 htb hns hnorm hfix)

/-- The exact zero-histogram shifted common span pushes through the singleton
normalizer image, with the same `withinProfileBound` budget. -/
theorem zeroProfileProjectedCommonSpanWithBudget_singletonNormalForm_of_zeroHistogramShiftCommonSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hzero :
      CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns) :
    ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      (zeroProfileSingletonNormalFormProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
      (withinProfileBound (Nat.log 2 n)) := by
  classical
  rcases hzero with ⟨G, hG_card, hG_span⟩
  have hid :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (LinearMap.id :
          MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
        (withinProfileBound (Nat.log 2 n)) := by
    refine ⟨G, hG_card, ?_⟩
    intro q hq
    rcases hq with ⟨row, hrow, rfl⟩
    simpa using hG_span hrow
  exact
    zeroProfileProjectedCommonSpanWithBudget_of_id_projectedCommonSpan
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      (zeroProfileSingletonNormalFormProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
      hid

/-- Strict `TΦ` contradiction from the exact zero-histogram common span and
the residual-balance row algebra.

This closes the singleton-normalizer common-span gate from the older
`CookLevinZeroHistogramShiftCommonSpan` package, while keeping the remaining
row algebra as the corrected residual-balance statement. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_zeroHistogramShiftCommonSpan_residualBalance
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hzero :
      CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_commonSpan_residualBalance
    M n hn hn2 htb hns hdec
    (zeroProfileProjectedCommonSpanWithBudget_singletonNormalForm_of_zeroHistogramShiftCommonSpan
      M n hn2 htb hns hzero)
    hres
    (routeBPaperFaithfulTPhi_withinProfileBound_add_ambient_le_pow_200
      n hn2)

/-- Concrete `concreteW` row embeddings supply the singleton-normalizer image
common span.  The proof first obtains the identity-projected zero-profile
profile/symmetric-power span, then pushes it through the explicit normalizer. -/
theorem zeroProfileProjectedCommonSpanWithBudget_singletonNormalForm_concreteW_of_rowEmbeddings
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4) :
    ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      (zeroProfileSingletonNormalFormProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) :=
  zeroProfileProjectedCommonSpanWithBudget_of_id_projectedCommonSpan
    (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
    (zeroProfileSingletonNormalFormProjection
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
    (zeroProfileProjectedCommonSpanWithBudget_id_concreteW_of_rowEmbeddings
      M n hn2 htb hns hn4 hRowEmbeddings)

/-- Semantic replacement for the arbitrary singleton-complement classifier.

The hard-coded quotient
`zeroProfileQuotientBySingletonShiftProjection` projects to an arbitrary
`Classical.choose` complement, so it should not be asked to preserve the
paper's canonical local chart.  The paper-faithful object is the explicit
singleton normalizer.  Concrete `concreteW` row embeddings give a budgeted
common span for that normalizer image directly, with the singleton
zero-profile budget. -/
theorem cookLevinZeroProfileSingletonNormalizerCommonSpanObligation_of_concreteW_rowEmbeddings
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4) :
    ∃ budget : Nat,
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileSingletonNormalFormProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        budget ∧
      budget <= withinProfileBound (Nat.log 2 n) := by
  refine
    ⟨zeroProfileSymmetricProfileDim zeroProfileHistogram,
      zeroProfileProjectedCommonSpanWithBudget_singletonNormalForm_concreteW_of_rowEmbeddings
        M n hn2 htb hns hn4 hRowEmbeddings,
      ?_⟩
  exact zeroProfileSymmetricProfileDim_zeroProfileHistogram_le_withinProfileBound
    (Nat.log 2 n)

/-- Strict `TΦ` contradiction from concrete zero-profile row embeddings and
normalized singleton-normalizer row equality.

This closes the new normalizer-image common-span and `budget + n` arithmetic
gates; the remaining row algebra is exactly the normalized equality
`normalForm(q) = normalForm(d)`. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_concreteW_rowEmbeddings_normalizedRows
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (hnorm :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_commonSpan_normalizedRows
    M n hn hn2 htb hns hdec
    (zeroProfileProjectedCommonSpanWithBudget_singletonNormalForm_concreteW_of_rowEmbeddings
      M n hn2 htb hns hn4 hRowEmbeddings)
    hnorm
    (routeBPaperFaithfulTPhi_singletonNormalFormBudget_add_ambient_le_pow_200
      n hn2)

/-- Strict `TΦ` contradiction from concrete zero-profile row embeddings and
the normalized non-singleton coefficient computation.  Singleton coefficients
are handled by the normalizer/residual bridge, so no derivative
fixed-representative condition is required. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeff
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (hcoeff :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_concreteW_rowEmbeddings_normalizedRows
    M n hn hn2 htb hns hdec hn4 hRowEmbeddings
    ((routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_iff_singletonResidual
      M n hn2 htb hns).mpr
      (routeBPaperFaithfulTPhi_singletonResidual_of_normalized_nonSingleton_coeff
        M n hn2 htb hns hcoeff))

/-- Strict `TΦ` contradiction from concrete zero-profile row embeddings and
the expanded normalized coefficient-balance computation.

This is the proof-facing algebraic target after unfolding the singleton
normalizer: the remaining Cook-Levin calculation may be supplied in the
balanced coefficient form, and the named non-singleton identity is derived
internally. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeffBalance
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (hbalance :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeff
    M n hn hn2 htb hns hdec hn4 hRowEmbeddings
    (routeBPaperFaithfulTPhi_normalizedNonSingletonCoeffIdentity_of_coeffBalance
      M n hn2 htb hns hbalance)

/-- Strict `TΦ` contradiction from concrete row embeddings and the residual
balance row algebra, without requiring derivative singleton coefficients to
vanish or the raw derivative row to be a fixed quotient representative. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_concreteW_rowEmbeddings_residualBalance
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeffBalance
    M n hn hn2 htb hns hdec hn4 hRowEmbeddings
    (routeBPaperFaithfulTPhi_coeffBalance_of_restrictedResidualBalance
      M n hn2 htb hns hres)

/-- Strict `TΦ` contradiction from a concrete singleton-quotient normal-form
classifier plus the exact strict-FOB derivative-erasure row identity. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_concreteSingletonQuotient_strictFOB
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    {typeBudget : Nat}
    (D :
      ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget)
    (hmap :
      ZeroProfileConcreteNormalFormRowMap
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        D)
    (hbudget : typeBudget <= withinProfileBound (Nat.log 2 n))
    (herase :
      RouteBPaperFaithfulTPhiProjectedPWindowStrictFOBDerivativeErasure
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_projectedTypeBudget
    M n hn hn2 htb hns hdec
    (zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_concreteRowMap
      M n hn2 htb hns D hmap hbudget)
    (routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_strictFOBDerivativeErasure
      M n hn2 htb hns
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
      herase)

/-- Strict `TΦ` contradiction from a concrete singleton-quotient normal-form
classifier plus the corrected range-only row identity.

This is the proof-facing quotient/classifier hook: it avoids the refuted raw
derivative representative target and compares only after the selected
singleton-quotient projection. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_concreteSingletonQuotient_rangeRestrictedRowIdentity
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    {typeBudget : Nat}
    (D :
      ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget)
    (hmap :
      ZeroProfileConcreteNormalFormRowMap
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        D)
    (hbudget : typeBudget <= withinProfileBound (Nat.log 2 n))
    (hrow :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_zeroProfileQuotientedShiftCommonSpan_rangeRestrictedRowIdentity
    M n hn hn2 htb hns hdec
    (zeroProfileQuotientBySingletonShiftProjection
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
    (cookLevinZeroProfileQuotientedShiftCommonSpan_of_concreteSingletonQuotientRowMap
      M n hn2 htb hns D hmap hbudget)
    hrow

/-- Strict `TΦ` singleton-quotient contradiction from concrete `concreteW`
row embeddings and the corrected range-only residual-balance equality.

The concrete row-embedding package now discharges the projected quotient
budget.  The remaining strict-`TΦ` input is exactly the range-only residual
balance; off-range rows are not part of this target. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_rangeRestrictedResidualBalance
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (hres :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_projectedTypeBudget
    M n hn hn2 htb hns hdec
    (cookLevinZeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_concreteW_rowEmbeddings
      M n hn2 htb hns hn4 hRowEmbeddings)
    (routeBPaperFaithfulTPhi_projectedPWindowControlledByZeroProfileProjection_of_rangeRestrictedRowIdentity
      M n hn2 htb hns
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
      (routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_of_restrictedResidualBalance
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        hres))

/-- Strict `TΦ` singleton-quotient contradiction from concrete `concreteW`
row embeddings and the concrete quotient-decomposition form of the residual
gate. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_residualDecomposition
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (hdecomp :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientResidualDecomposition
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_rangeRestrictedResidualBalance
    M n hn hn2 htb hns hdec hn4 hRowEmbeddings
    (routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientResidualBalance_of_decomposition
      M n hn2 htb hns hdecomp)

/-- Strict `TΦ` singleton-quotient contradiction from concrete `concreteW`
row embeddings, quotient-level row equality, and the explicit condition that
each derivative row is already the selected singleton-quotient representative. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_quotientRows_fixedDerivative
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (hquot :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientRowIdentity
        M n hn2 htb hns)
    (hfix :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_rangeRestrictedResidualBalance
    M n hn hn2 htb hns hdec hn4 hRowEmbeddings
    ((routeBPaperFaithfulTPhi_rangePWindowRestrictedSingletonQuotientRowIdentity_iff_restrictedResidualBalance
      M n hn2 htb hns).mp
      (routeBPaperFaithfulTPhi_rangePWindowRestrictedZeroProfileRowIdentity_of_singletonQuotientRowIdentity_fixedDerivative
        M n hn2 htb hns hquot hfix))

/-- Strict `TΦ` singleton-quotient contradiction from concrete `concreteW`
row embeddings, the normalized non-singleton coefficient identity, and the
explicit fixed-representative condition for derivative rows. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_normalizedCoeff_fixedDerivative
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (hcoeff :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
        M n hn2 htb hns)
    (hfix :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_quotientRows_fixedDerivative
    M n hn hn2 htb hns hdec hn4 hRowEmbeddings
    (routeBPaperFaithfulTPhi_singletonQuotientRowIdentity_of_singletonResidual
      M n hn2 htb hns
      (routeBPaperFaithfulTPhi_singletonResidual_of_normalized_nonSingleton_coeff
        M n hn2 htb hns hcoeff))
    hfix

/-- Strict `TΦ` singleton-quotient contradiction from the expanded corrected
coefficient balance.  This is the proof-facing final hook for the actual
Cook-Levin coefficient computation after unfolding the singleton normalizer. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_coeffBalance_fixedDerivative
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (hbalance :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
        M n hn2 htb hns)
    (hfix :
      RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_normalizedCoeff_fixedDerivative
    M n hn hn2 htb hns hdec hn4 hRowEmbeddings
    (routeBPaperFaithfulTPhi_normalizedNonSingletonCoeffIdentity_of_coeffBalance
      M n hn2 htb hns hbalance)
    hfix

/-- Uniform strict `TΦ` singleton-quotient projected gates rule out bounded SAT
deciders at paper scale. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_projectedTypeBudget
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
          M n hn2 htb hns
          (zeroProfileQuotientBySingletonShiftProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_projectedTypeBudget
      M n hn hn2 htb hns hdec
      (hcert M n hn hn2 htb hns hdec).1
      (hcert M n hn hn2 htb hns hdec).2

/-- Uniform strict `TΦ` singleton-normalizer gates rule out bounded SAT
deciders at paper scale.  This exposes the remaining proof target without the
non-faithful derivative fixed-representative condition. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_commonSpan
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists budget : Nat,
          ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            (zeroProfileSingletonNormalFormProjection
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
            budget ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormIdentity
            M n hn2 htb hns ∧
          budget <= n ^ 200) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨budget, hspan, hnorm, hbudget⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_commonSpan
      M n hn hn2 htb hns hdec hspan hnorm hbudget

/-- Uniform strict `TΦ` singleton-normalizer gates rule out bounded SAT
deciders at paper scale with singleton residuals paid explicitly.  This is the
normalized-row version of the semantic hook and does not require derivative
rows to be fixed representatives. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_commonSpan_normalizedRows
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists budget : Nat,
          ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            (zeroProfileSingletonNormalFormProjection
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
            budget ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
            M n hn2 htb hns ∧
          budget + n <= n ^ 200) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨budget, hspan, hnorm, hbudget⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_commonSpan_normalizedRows
      M n hn hn2 htb hns hdec hspan hnorm hbudget

/-- Uniform normalizer-image common span plus residual-balance row algebra
rules out bounded SAT deciders at paper scale.  This branch does not consume
the obstructed raw `concreteW` row-embedding package. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_commonSpan_residualBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists budget : Nat,
          ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            (zeroProfileSingletonNormalFormProjection
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
            budget ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
            M n hn2 htb hns
            (zeroProfileQuotientBySingletonShiftProjection
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) ∧
          budget + n <= n ^ 200) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨budget, hspan, hres, hbudget⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_commonSpan_residualBalance
      M n hn hn2 htb hns hdec hspan hres hbudget

/-- Uniform singleton-quotient projected type budget plus residual-balance row
algebra rule out bounded SAT deciders through the explicit normalizer image.
This is the direct projected/quotiented zero-profile route; it does not ask
for the impossible full zero-histogram common span. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_residualBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
          M n hn2 htb hns
          (zeroProfileQuotientBySingletonShiftProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨hbudget, hres⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_residualBalance
      M n hn hn2 htb hns hdec hbudget hres

/-- Uniform exact projected quotient budget plus normalized row equality rule
out bounded SAT deciders at paper scale, without any fixed-representative
condition on the raw derivative row. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedRows
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨hbudget, hnorm⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_normalizedRows
      M n hn hn2 htb hns hdec hbudget hnorm

/-- Uniform exact projected quotient budget plus normalized non-singleton
coefficient equality rule out bounded SAT deciders at paper scale. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedCoeff
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨hbudget, hcoeff⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_normalizedCoeff
      M n hn hn2 htb hns hdec hbudget hcoeff

/-- Uniform exact projected quotient budget plus expanded coefficient balance
rule out bounded SAT deciders at paper scale. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedCoeffBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨hbudget, hbalance⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_normalizedCoeffBalance
      M n hn hn2 htb hns hdec hbudget hbalance

/-- Uniform exact projected quotient budget plus the semantic normalized-row
residual decomposition rule out bounded SAT deciders at paper scale. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedRows_fixedDerivative
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
          M n hn2 htb hns ∧
        RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨hbudget, hnorm, hfix⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_normalizedRows_fixedDerivative
      M n hn hn2 htb hns hdec hbudget hnorm hfix

/-- Uniform singleton-quotient certificate close-out from the corrected
semantic coefficient target and the selected derivative representative
condition.  This is the projected/quotient branch: it does not assert a raw
range-wide row identity. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_projectedTypeBudget_normalizedCoeff_fixedDerivative
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
          M n hn2 htb hns ∧
        RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨hbudget, hcoeff, hfix⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_normalizedRows_fixedDerivative
      M n hn hn2 htb hns hdec hbudget
      (routeBPaperFaithfulTPhi_singletonNormalizedRowIdentity_of_normalizedNonSingletonCoeff
        M n hn2 htb hns hcoeff)
      hfix

/-- Uniform concrete singleton-quotient close-out with the projected type
budget discharged by the existing `concreteW` row embeddings.  The remaining
live assumptions are exactly the normalized non-singleton coefficient identity
and the derivative fixed-representative condition. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_projectedTypeBudget_normalizedCoeff_fixedDerivative
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
            M n hn2 htb hns ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
            M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_projectedTypeBudget_normalizedCoeff_fixedDerivative
    (fun M n hn hn2 htb hns hdec => by
      rcases hcert M n hn hn2 htb hns hdec with
        ⟨hn4, hRowEmbeddings, hcoeff, hfix⟩
      exact
        ⟨cookLevinZeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_concreteW_rowEmbeddings
            M n hn2 htb hns hn4 hRowEmbeddings,
          hcoeff,
          hfix⟩)

/-- Uniform concrete row embeddings plus normalized singleton-normalizer row
identity rule out bounded SAT deciders at paper scale.  The normalizer common
span and `+ n` singleton residual budget are discharged internally. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedRows
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
            M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨hn4, hrows, hnorm⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_concreteW_rowEmbeddings_normalizedRows
      M n hn hn2 htb hns hdec hn4 hrows hnorm

/-- Uniform concrete row embeddings plus the normalized non-singleton
coefficient identity rule out bounded SAT deciders at paper scale. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeff
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
            M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨hn4, hrows, hcoeff⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeff
      M n hn hn2 htb hns hdec hn4 hrows hcoeff

/-- Uniform concrete row embeddings plus the expanded normalized coefficient
balance rule out bounded SAT deciders at paper scale.  This is the corrected
semantic singleton-normalizer close-out: no fixed representative for the raw
derivative row is required. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeffBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
            M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨hn4, hrows, hbalance⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeffBalance
      M n hn hn2 htb hns hdec hn4 hrows hbalance

/-- The broad concreteW + normalized-coefficient-balance certificate cannot
be the final paper-faithful close-out whenever the two-differentiated strict
tag obstruction is present.  The corrected route must use the narrowed
canonical/profile row family instead of a range-wide coefficient balance. -/
theorem routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeffBalance_certificate_noGo_of_twoDifferentiatedStrictTags_even
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
            M n hn2 htb hns)
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (T : Finset (Fin (n / 3))) (j k : Fin (n / 3))
    (hTcard : T.card = Nat.log 2 n)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (T.toList.map (cookLevinStrictFOBFlatMap n)))
    (hj : j ∈ T) (hk : k ∈ T) (hjk : j ≠ k)
    (hEvenT : Even T.card)
    (hα :
      ∀ i : Fin n,
        SymmetricPower.tagMonomial
          (({j, k} : Finset (Fin (n / 3))).map
            ⟨cookLevinStrictFOBFlatMap n,
              cookLevinStrictFOBFlatMap_injective n⟩) ≠
          Finsupp.single i 1) :
    False := by
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨_hn4, _hrows, hbalance⟩
  exact
    routeBPaperFaithfulTPhi_not_normalizedCoeffBalance_of_twoDifferentiatedStrictTags_even
      M n hn2 htb hns T j k hTcard hadm hj hk hjk hEvenT hα hbalance

/-- The same obstruction rules out the compact broad non-singleton coefficient
identity.  The compact form is just the singleton-normalizer projection
equality; after unfolding the normalizer it is equivalent to the expanded
balance refuted above. -/
theorem routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedNonSingletonCoeff_certificate_noGo_of_twoDifferentiatedStrictTags_even
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
            M n hn2 htb hns)
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (T : Finset (Fin (n / 3))) (j k : Fin (n / 3))
    (hTcard : T.card = Nat.log 2 n)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition
        (T.toList.map (cookLevinStrictFOBFlatMap n)))
    (hj : j ∈ T) (hk : k ∈ T) (hjk : j ≠ k)
    (hEvenT : Even T.card)
    (hα :
      ∀ i : Fin n,
        SymmetricPower.tagMonomial
          (({j, k} : Finset (Fin (n / 3))).map
            ⟨cookLevinStrictFOBFlatMap n,
              cookLevinStrictFOBFlatMap_injective n⟩) ≠
          Finsupp.single i 1) :
    False := by
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨_hn4, _hrows, hcoeff⟩
  exact
    routeBPaperFaithfulTPhi_not_normalizedNonSingletonCoeffIdentity_of_twoDifferentiatedStrictTags_even
      M n hn2 htb hns T j k hTcard hadm hj hk hjk hEvenT hα hcoeff

/-- Paper-faithful strict `TΦ` close-out from concrete row embeddings plus the
narrowed canonical/profile residual-balance package.

This is the replacement for the refuted range-wide normalized coefficient
balance certificate.  The coefficient calculation is consumed only through the
canonical/profile row family selected by the strict normal-form data. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_canonicalProfileResidualBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          Nonempty
            (RouteBPaperFaithfulTPhiCanonicalProfileResidualBalance
              M n hn2 htb hns)) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨hn4, hrows, ⟨hprofile⟩⟩
  have _hrestricted :
      RouteBPaperFaithfulTPhiCanonicalProfileRestrictedNormalizedCoeffIdentity
        M n hn2 htb hns hprofile.canonicalRow :=
    routeBPaperFaithfulTPhi_canonicalProfileRestrictedNormalizedCoeffIdentity_of_residualBalance
      M n hn2 htb hns hprofile
  exact
    false_of_routeBPaperFaithfulTPhi_canonical_from_concreteW_rowEmbeddings
      M n hn hn2 htb hns hdec hn4 hrows

/-- The proved strict paper-faithful canonical/profile coefficient theorem
supplies the narrowed residual-balance package for the concreteW close-out. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_strictPaperFaithfulCanonicalProfile
    (hrows :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_canonicalProfileResidualBalance
    (fun M n hn hn2 htb hns hdec => by
      rcases hrows M n hn hn2 htb hns hdec with ⟨hn4, hrow⟩
      exact
        ⟨hn4, hrow,
          ⟨routeBPaperFaithfulTPhi_canonicalProfileResidualBalance_strictPaperFaithful_proved
            M n hn2 htb hns⟩⟩)

/-- Legacy strict paper-faithful canonical/profile close-out from the imported
canonical `concreteW` row-embedding frontier.

This names the exact upstream concreteW input surface: direct Cook-Levin
branch shapes, canonical-row transport, canonical H4, and the concrete I1/I2/I3
local algebra.  This is retained as a diagnostic bridge only: the live
paper-faithful route below replaces the raw canonical H4 field by the
endpoint/profile-aware charged profile cover. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_importedConcreteW_strictPaperFaithfulCanonicalProfile
    (hShape :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        CookLevinDirectBranchShapeWitnesses M n hn2 htb hns hn4)
    (hTransport :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        CookLevinConcreteWCanonicalRowTransport M n hn2 htb hns hn4)
    (hDeriv :
      forall (n : Nat) (hn4 : n >= 4),
        PallLean.Paper93.Spanning.DerivClosurePerType (n := n)
          (fun tau =>
            PallLean.Paper93.Wiring.concreteW n hn4
              (Fin.castLEEmb hn4) tau))
    (hI1 :
      forall (n : Nat) (hn4 : n >= 4),
        ConcreteWProductGrouping n hn4)
    (hI2 :
      forall (n : Nat) (hn4 : n >= 4),
        ConcreteWShiftClosure n hn4)
    (hI3 :
      forall (n : Nat) (hn4 : n >= 4),
        ConcreteWMlprojClosure n hn4) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_strictPaperFaithfulCanonicalProfile
    (fun M n hn hn2 htb hns _hdec => by
      let hn4 : n >= 4 := routeB_paperScale_ge_four hn
      exact
        ⟨hn4,
          CookLevinPerTypeRowEmbeddings_concreteW_of_directBranchShapes_transport_H4_I123
            M n hn2 htb hns hn4
            (hShape M n hn2 hn4 htb hns)
            (hTransport M n hn2 hn4 htb hns)
            (hDeriv n hn4)
            (hI1 n hn4)
            (hI2 n hn4)
            (hI3 n hn4)⟩)

/-- Paper-faithful strict `TΦ` contradiction from the §9 profile/orbit
assembly.

This is the replacement for the overstrong same-budget endpoint charged cover:
the paper's load-bearing Route B object is canonical-window/profile
compression, giving a global profile-orbit span bound.  Once that assembly is
available, the existing strict ambient gauge P-side bound contradicts the
projected/log-window NP lower side. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_strictPaperProfileOrbitGlobalAssembly
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hassembly :
      RouteBPaperFaithfulTPhiStrictPaperProfileOrbitGlobalAssembly
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow
    M n hn hn2 htb hns hdec
    (routeBPaperFaithfulTPhi_pSideBound_of_strictPaperProfileOrbitGlobalAssembly
      M n hn2 htb hns hassembly)

/-- Final paper-faithful Route B close-out through canonical-window/profile
compression and global profile-orbit assembly.

Compared with the endpoint charged-cover hooks below, this states the remaining
mathematical obligation at the paper level: prove the strict profile/orbit
assembly for every SAT-decider instance. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly
    (hassembly :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictPaperProfileOrbitGlobalAssembly
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_strictPaperProfileOrbitGlobalAssembly
      M n hn hn2 htb hns hdec
      (hassembly M n hn hn2 htb hns hdec)

/-- Paper-faithful strict `TΦ` contradiction from the actual
canonical-window local-monoid/profile analysis.

This is the corrected final hook for §9.3--§9.4: canonical windows select
finite interface-anonymous local profiles, each range row lands in its selected
profile span, the finite union over profiles bounds the ambient strict `TΦ`
rank, and the combined profile budget fits below `n^200`. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_strictCanonicalWindowLocalMonoidProfileAnalysis
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hanalysis :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileAnalysis
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow
    M n hn hn2 htb hns hdec
    (routeBPaperFaithfulTPhi_pSideBound_of_strictCanonicalWindowLocalMonoidProfileAnalysis
      M n hn2 htb hns hanalysis)

/-- Final close-out from the paper-shaped canonical-window local-monoid/profile
analysis, without routing through broad coefficient identities, derivative-fixed
representatives, or a one-profile classifier. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileAnalysis
    (hanalysis :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileAnalysis
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_strictCanonicalWindowLocalMonoidProfileAnalysis
      M n hn hn2 htb hns hdec
      (hanalysis M n hn hn2 htb hns hdec)

/-- Paper-faithful strict `TΦ` contradiction from the separated
local-monoid profile data: Lemma 29 profile count, Lemma 31 local span
dimension, and canonical range-row membership. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_strictCanonicalWindowLocalMonoidProfileData
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hdata :
      RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileData
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow
    M n hn hn2 htb hns hdec
    (routeBPaperFaithfulTPhi_pSideBound_of_strictCanonicalWindowLocalMonoidProfileData
      M n hn2 htb hns hdata)

/-- Final close-out from the paper's separated local-monoid/profile facts. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileData
    (hdata :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileData
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_strictCanonicalWindowLocalMonoidProfileData
      M n hn hn2 htb hns hdec
      (hdata M n hn hn2 htb hns hdec)

/-- Final close-out from literal paper §9.3 interface-anonymous local-monoid
profile data.

This is the tightest row-cover input surface: a finite local normal-form
alphabet, realizable interface-anonymous profile histograms, Lemma 29 profile
count, Lemma 31 local basis dimension, and selected canonical row membership.
-/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictInterfaceAnonymousLocalMonoidProfileData
    (hdata :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictInterfaceAnonymousLocalMonoidProfileData
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileData
    (fun M n hn hn2 htb hns hdec =>
      routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileData_of_interfaceAnonymousLocalMonoidProfileData
        M n hn2 htb hns
        (hdata M n hn hn2 htb hns hdec))

/-- Final close-out from the bounded finite-normal-form alphabet version of
the paper §9.3 interface-anonymous local-monoid data.  Here Lemma 29's profile
count is derived from `Fintype.card Σ^{≤q} ≤ 4`, not accepted as a direct
profile-count field. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictBoundedInterfaceAnonymousLocalMonoidProfileData
    (hdata :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictBoundedInterfaceAnonymousLocalMonoidProfileData
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictInterfaceAnonymousLocalMonoidProfileData
    (fun M n hn hn2 htb hns hdec =>
      routeBPaperFaithfulTPhi_strictInterfaceAnonymousLocalMonoidProfileData_of_boundedInterfaceAnonymousLocalMonoidProfileData
        M n hn2 htb hns
        (hdata M n hn hn2 htb hns hdec))

/-- Final close-out from the actual four-valued Cook-Levin interface alphabet
version of the strict `TΦ` interface-anonymous local-monoid profile data. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfileData
    (hdata :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictConstraintTypeInterfaceProfileData
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictBoundedInterfaceAnonymousLocalMonoidProfileData
    (fun M n hn hn2 htb hns hdec =>
      routeBPaperFaithfulTPhi_strictBoundedInterfaceAnonymousLocalMonoidProfileData_of_constraintTypeInterfaceProfileData
        M n hn2 htb hns
        (hdata M n hn hn2 htb hns hdec))

/-- Final close-out from strict `ConstraintType` profile-subspace data.  The
finite local bases are chosen mechanically from the supplied subspaces rather
than accepted as an input field. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceData
    (hdata :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfileData
    (fun M n hn hn2 htb hns hdec =>
      routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfileData_of_profileSubspaceData
        M n hn2 htb hns
        (hdata M n hn hn2 htb hns hdec))

/-- Paper-faithful strict `TΦ` contradiction from the corrected range-row
profile cover data and its actual range-row global span theorem.

This is the non-shortcut row-cover endpoint: the data carries the separated
profile count/local dimension budget through `combinedProfileBound`, and
`hrange` is the literal strict range-row assembled-profile cover for the same
data. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_strictPaperRangeRowsGlobalProfileSpanCover
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (D :
      RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
        M n hn2 htb hns)
    (hrange :
      RouteBPaperFaithfulTPhiStrictPaperRangeRowsGlobalProfileSpanCover D) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow
    M n hn hn2 htb hns hdec
    (routeBPaperFaithfulTPhi_pSideBound_of_strictPaperRangeRowsGlobalProfileSpanCover
      M n hn2 htb hns D hrange)

/-- Final close-out from the corrected paper-shaped strict range-row cover
surface.

This is the exact §9.3--§9.4 shape: construct the finite local-monoid profile
data `D`, prove the range rows land in the assembled profile span for that same
`D`, then use the combined profile budget. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictPaperRangeRowsGlobalProfileSpanCover
    (hcover :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists D :
          RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
            M n hn2 htb hns,
          RouteBPaperFaithfulTPhiStrictPaperRangeRowsGlobalProfileSpanCover D) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcover M n hn hn2 htb hns hdec with ⟨D, hrange⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_strictPaperRangeRowsGlobalProfileSpanCover
      M n hn hn2 htb hns hdec D hrange

/-- Final close-out from corrected paper-shaped range-row profile-cover data.

Unlike the legacy `RouteBPaperFaithfulTPhiStrictRangeRowProfileCoverData`
consumer below, this theorem uses the corrected combined profile budget and the
finite union over interface-anonymous local-monoid profiles. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictPaperRangeRowProfileCoverData
    (hdata :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictPaperRangeRowsGlobalProfileSpanCover
    (fun M n hn hn2 htb hns hdec =>
      let D := hdata M n hn hn2 htb hns hdec
      ⟨D,
        routeBPaperFaithfulTPhi_strictPaperRangeRowsGlobalProfileSpanCover_of_paperRangeRowProfileCoverData
          M n hn2 htb hns D⟩)

/-- Paper-faithful strict `TΦ` contradiction from the actual
local-monoid/profile analysis, through the separated Lemma 29/Lemma 31 data
surface. -/
theorem false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_strictLocalMonoidProfileAnalysis
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804)
    (hn2 : n >= 2) (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (hanalysis :
      RouteBPaperFaithfulTPhiStrictLocalMonoidProfileAnalysis
        M n hn2 htb hns) :
    False :=
  false_of_routeBPaperFaithfulTPhi_projectedLogWindow
    M n hn hn2 htb hns hdec
    (routeBPaperFaithfulTPhi_pSideBound_of_strictLocalMonoidProfileAnalysis
      M n hn2 htb hns hanalysis)

/-- Final close-out from the actual local-monoid/profile row analysis.  This
keeps the paper's logical shape explicit: canonical-window profile selection,
separate profile-count and local-dimension bounds, and row membership in the
selected profile span. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictLocalMonoidProfileAnalysis
    (hanalysis :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictLocalMonoidProfileAnalysis
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_strictLocalMonoidProfileAnalysis
      M n hn hn2 htb hns hdec
      (hanalysis M n hn hn2 htb hns hdec)

/-- Final paper-shaped close-out from canonical-window orbit/profile data plus
the exact range-row assembled-profile cover.

This mirrors the paper's §9.3--§9.4 chain: canonical windows are assigned
interface-anonymous profiles, rows are covered by bounded profile/orbit bases,
and the strict range rows assemble into the global profile span.  It avoids the
refuted broad coefficient identity and does not require a raw derivative-fixed
representative condition. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictCanonicalWindowOrbitProfile_rangeRows
    (hprofile :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists D :
          RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
            M n hn2 htb hns,
          RouteBPaperFaithfulTPhiStrictRangeRowsGlobalProfileSpanCover D) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly
    (fun M n hn hn2 htb hns hdec => by
      rcases hprofile M n hn hn2 htb hns hdec with ⟨D, hrows⟩
      exact
        routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly_of_rangeRows
          D hrows)

/-- Final paper-faithful close-out from the actual local-monoid/profile
range-row cover data.

This is the concrete row-cover theorem surface: provide the finite profile
cover data for strict range rows, and the existing Route B chain assembles it
into the global profile/orbit rank bound. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictRangeRowProfileCoverData
    (hcover :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictRangeRowProfileCoverData
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictCanonicalWindowOrbitProfile_rangeRows
    (fun M n hn hn2 htb hns hdec =>
      routeBPaperFaithfulTPhi_strictCanonicalWindowOrbitRankData_exists_rangeRowsGlobalProfileSpanCover_of_rangeRowProfileCoverData
        M n hn2 htb hns
        (hcover M n hn hn2 htb hns hdec))

/-- Final paper-faithful close-out from the strict profile-subspace classifier
obligation.

This names the current mathematical frontier directly: prove the
local-monoid/profile classifier for strict `TΦ` range rows, and the final
projected/log-window contradiction follows. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation
    (hclassifier :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifierObligation
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly
    (fun M n hn hn2 htb hns hdec =>
      routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly_of_profileSubspaceClassifierObligation
        M n hn2 htb hns
        (hclassifier M n hn hn2 htb hns hdec))

/-- Final paper-faithful close-out from projected profile compression plus
restricted strict-row identity.

This is the quotient/profile-aware route to the strict classifier obligation:
the projected normal-form analysis supplies the bounded common span, and the
remaining row algebra is only the source-coordinate restricted projected
identity. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_restrictedRowIdentity_projectedCommonSpan
    (hprojected :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists project :
          MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ,
          ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            project (withinProfileBound (Nat.log 2 n)) ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
            M n hn2 htb hns project) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation
    (fun M n hn hn2 htb hns hdec => by
      rcases hprojected M n hn hn2 htb hns hdec with
        ⟨project, hspan, hrow⟩
      exact
        routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation_of_restrictedRowIdentity_projectedCommonSpan
          M n hn2 htb hns project hspan hrow)

/-- Final paper-faithful close-out from quotient certificate data and the
semantic restricted residual-balance row algebra for the selected projection.

This is the corrected projected/quotient branch: the certificate supplies the
bounded projected profile span, and residual balance supplies the restricted
row identity after projection. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_quotientTypeCertificate_restrictedResidualBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists typeBudget : Nat,
        exists cert :
          ZeroProfileQuotientTypeSpaceCertificate (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            typeBudget,
          typeBudget <= withinProfileBound (Nat.log 2 n) ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
            M n hn2 htb hns cert.project) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation
    (fun M n hn hn2 htb hns hdec => by
      rcases hcert M n hn hn2 htb hns hdec with
        ⟨typeBudget, cert, hbudget, hres⟩
      exact
        routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation_of_quotientTypeCertificate_restrictedResidualBalance
          M n hn2 htb hns cert hres hbudget)

/-- Obligation-level version of the quotient semantic residual-balance
close-out. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_quotientTypeNormalFormObligation_restrictedResidualBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists typeBudget : Nat,
          CookLevinZeroProfileQuotientTypeNormalFormObligation
            M n hn2 htb hns typeBudget ∧
          (∀ cert :
            ZeroProfileQuotientTypeSpaceCertificate (Nat.log 2 n)
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
              typeBudget,
            RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
              M n hn2 htb hns cert.project) ∧
          typeBudget <= withinProfileBound (Nat.log 2 n)) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation
    (fun M n hn hn2 htb hns hdec => by
      rcases hcert M n hn hn2 htb hns hdec with
        ⟨typeBudget, hquot, hres, hbudget⟩
      exact
        routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation_of_quotientTypeNormalFormObligation_restrictedResidualBalance
          M n hn2 htb hns hquot hres hbudget)

/-- Final strict paper-faithful close-out through the endpoint/profile-aware
replacement for canonical `concreteW` H4.

This route does not ask for the refuted canonical H4 field.  Direct branch
shapes plus canonical-row transport supply endpoint-augmented H3, the
endpoint-augmented H4 proof is internal to the charged target-cover consumer,
and the concrete endpoint charge discharges charged shift. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_endpointAugmented_directBranchTransport_concreteEndpointCharge_chargedTargetCover
    (hzero :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hShape :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        CookLevinDirectBranchShapeWitnesses M n hn2 htb hns hn4)
    (hTransport :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        CookLevinConcreteWCanonicalRowTransport M n hn2 htb hns hn4)
    (hI1_univ : PallLean.Paper93.Wiring.PerTypeProductGrouping_universal)
    (hI3_univ : PallLean.Paper93.Wiring.PerTypeMlprojClosure_universal)
    (hCover :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        forall (h : ProfileHistogram)
          (hadm : ProfileAdmissible (Nat.log 2 n) h),
            h ConstraintType.transitionRight = 0 ->
              h ≠ zeroProfileHistogram ->
                ActiveProfileSupport h ->
                  CookLevinEndpointChargedTargetProfileCoverAt
                    M n hn2 htb hns
                    (concreteWEndpointSpanOneStepCharge n hn4) h hadm) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_endpointAugmented_concreteEndpointCharge_chargedTargetCover
    hzero
    (fun M n hn2 hn4 htb hns =>
      CookLevinFactorMemPerType_endpointAugmentedConcreteW_of_directBranchShapes_transport
        M n hn2 htb hns hn4
        (hShape M n hn2 hn4 htb hns)
        (hTransport M n hn2 hn4 htb hns))
    (fun n hn4 => hI1_univ n (endpointAugmentedConcreteW n hn4))
    (fun n hn4 => hI3_univ n (endpointAugmentedConcreteW n hn4))
    hCover

/-- Same endpoint/profile-aware close-out, but with the remaining obligation
stated at generator level: every source post-span generator must charge into
one admissible active target profile. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_endpointAugmented_directBranchTransport_concreteEndpointCharge_chargedGeneratorCover
    (hzero :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hShape :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        CookLevinDirectBranchShapeWitnesses M n hn2 htb hns hn4)
    (hTransport :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        CookLevinConcreteWCanonicalRowTransport M n hn2 htb hns hn4)
    (hI1_univ : PallLean.Paper93.Wiring.PerTypeProductGrouping_universal)
    (hI3_univ : PallLean.Paper93.Wiring.PerTypeMlprojClosure_universal)
    (hCover :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        forall (h : ProfileHistogram)
          (hadm : ProfileAdmissible (Nat.log 2 n) h),
            h ConstraintType.transitionRight = 0 ->
              h ≠ zeroProfileHistogram ->
                ActiveProfileSupport h ->
                  CookLevinEndpointChargedTargetGeneratorCoverAt
                    M n hn2 htb hns
                    (concreteWEndpointSpanOneStepCharge n hn4) h hadm) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_endpointAugmented_directBranchTransport_concreteEndpointCharge_chargedTargetCover
      hzero hShape hTransport hI1_univ hI3_univ
    (fun M n hn2 hn4 htb hns h hadm htr hne hactive =>
      CookLevinEndpointChargedTargetProfileCoverAt_of_generatorCover
        M n hn2 htb hns (concreteWEndpointSpanOneStepCharge n hn4) h hadm
        (hCover M n hn2 hn4 htb hns h hadm htr hne hactive))

/-- Uniform concrete row embeddings plus the range-only residual balance rule
out bounded SAT deciders through the semantic singleton normalizer. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_residualBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
            M n hn2 htb hns
            (zeroProfileQuotientBySingletonShiftProjection
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨hn4, hrows, hres⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_concreteW_rowEmbeddings_residualBalance
      M n hn hn2 htb hns hdec hn4 hrows hres

/-- Uniform concrete normal-form classifiers plus strict-FOB row erasure rule
out bounded SAT deciders at paper scale through the strict `TΦ` route. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteSingletonQuotient_strictFOB
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists typeBudget : Nat,
        exists D :
          ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget,
        exists _ :
          ZeroProfileConcreteNormalFormRowMap
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
              (zeroProfileQuotientBySingletonShiftProjection
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
              D,
            typeBudget <= withinProfileBound (Nat.log 2 n) ∧
            RouteBPaperFaithfulTPhiProjectedPWindowStrictFOBDerivativeErasure
              M n hn2 htb hns
              (zeroProfileQuotientBySingletonShiftProjection
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨typeBudget, D, hmap, hbudget, herase⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_concreteSingletonQuotient_strictFOB
      M n hn hn2 htb hns hdec D hmap hbudget herase

/-- Uniform concrete singleton-quotient classifiers plus the corrected
range-only row identity rule out bounded SAT deciders through the strict
`TΦ` quotient route. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteSingletonQuotient_rangeRestrictedRowIdentity
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists typeBudget : Nat,
        exists D :
          ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget,
        exists _ :
          ZeroProfileConcreteNormalFormRowMap
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
              (zeroProfileQuotientBySingletonShiftProjection
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
              D,
            typeBudget <= withinProfileBound (Nat.log 2 n) ∧
            RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
              M n hn2 htb hns
              (zeroProfileQuotientBySingletonShiftProjection
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨typeBudget, D, hmap, hbudget, hrow⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_concreteSingletonQuotient_rangeRestrictedRowIdentity
      M n hn hn2 htb hns hdec D hmap hbudget hrow

/-- Uniform strict `TΦ` route after the concreteW projected-budget close:
only the range-only residual-balance equality remains as the strict extraction
input. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_rangeRestrictedResidualBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
            M n hn2 htb hns
            (zeroProfileQuotientBySingletonShiftProjection
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨hn4, hRowEmbeddings, hres⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_rangeRestrictedResidualBalance
      M n hn hn2 htb hns hdec hn4 hRowEmbeddings hres

/-- Uniform strict `TΦ` singleton-quotient route through the concrete
decomposition form of the residual gate. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_residualDecomposition
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientResidualDecomposition
            M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨hn4, hRowEmbeddings, hdecomp⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_residualDecomposition
      M n hn hn2 htb hns hdec hn4 hRowEmbeddings hdecomp

/-- Uniform strict `TΦ` singleton-quotient route through quotient row equality
plus the fixed-representative derivative-row condition. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_quotientRows_fixedDerivative
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientRowIdentity
            M n hn2 htb hns ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
            M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨hn4, hRowEmbeddings, hquot, hfix⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_quotientRows_fixedDerivative
      M n hn hn2 htb hns hdec hn4 hRowEmbeddings hquot hfix

/-- Uniform strict `TΦ` singleton-quotient route through normalized
non-singleton coefficient equality plus fixed derivative representatives. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_normalizedCoeff_fixedDerivative
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
            M n hn2 htb hns ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
            M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨hn4, hRowEmbeddings, hcoeff, hfix⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_normalizedCoeff_fixedDerivative
      M n hn hn2 htb hns hdec hn4 hRowEmbeddings hcoeff hfix

/-- Uniform strict `TΦ` singleton-quotient route from the expanded corrected
coefficient balance plus fixed derivative representatives. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_coeffBalance_fixedDerivative
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
            M n hn2 htb hns ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
            M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  rcases hcert M n hn hn2 htb hns hdec with
    ⟨hn4, hRowEmbeddings, hbalance, hfix⟩
  exact
    false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_coeffBalance_fixedDerivative
      M n hn hn2 htb hns hdec hn4 hRowEmbeddings hbalance hfix

/-- Legacy rich-projection discharge from the strict `TΦ` singleton-quotient
projected route, mediated only by the no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_projectedTypeBudget
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulTPhiProjectedPWindowControlledByZeroProfileProjection
          M n hn2 htb hns
          (zeroProfileQuotientBySingletonShiftProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_projectedTypeBudget
      hcert)

/-- Legacy rich-projection discharge from the semantic singleton-normalizer
strict `TΦ` route, mediated only by the no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_commonSpan
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists budget : Nat,
          ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            (zeroProfileSingletonNormalFormProjection
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
            budget ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalFormIdentity
            M n hn2 htb hns ∧
          budget <= n ^ 200) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_commonSpan
      hcert)

/-- Legacy rich-projection discharge from the normalized singleton-normalizer
strict `TΦ` route, with singleton residuals paid at cost `n`. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_commonSpan_normalizedRows
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists budget : Nat,
          ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            (zeroProfileSingletonNormalFormProjection
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
            budget ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
            M n hn2 htb hns ∧
          budget + n <= n ^ 200) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_commonSpan_normalizedRows
      hcert)

/-- Legacy rich-projection discharge from the paper-facing normalizer-image
common span plus residual-balance row algebra. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_commonSpan_residualBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists budget : Nat,
          ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            (zeroProfileSingletonNormalFormProjection
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
            budget ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
            M n hn2 htb hns
            (zeroProfileQuotientBySingletonShiftProjection
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) ∧
          budget + n <= n ^ 200) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_commonSpan_residualBalance
      hcert)

/-- Rich-projection discharge from the direct projected/quotiented
singleton-normalizer zero-profile route and residual-balance row algebra. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_residualBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
          M n hn2 htb hns
          (zeroProfileQuotientBySingletonShiftProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_residualBalance
      hcert)

/-- Rich-projection discharge from exact projected quotient budget plus
normalized row equality, using the singleton-normalizer residual payment
rather than a raw derivative representative condition. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedRows
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedRows
      hcert)

/-- Rich-projection discharge from exact projected quotient budget plus the
normalized non-singleton coefficient computation. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedCoeff
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedCoeff
      hcert)

/-- Rich-projection discharge from exact projected quotient budget plus the
expanded normalized coefficient-balance computation. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedCoeffBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedCoeffBalance
      hcert)

/-- Rich-projection discharge from the exact projected quotient budget and
the semantic normalized-row decomposition of strict residual balance. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedRows_fixedDerivative
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
          M n hn2 htb hns ∧
        RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedRows_fixedDerivative
      hcert)

/-- Rich-projection discharge through the concrete singleton quotient
certificate, using the corrected semantic coefficient target plus fixed
derivative representatives. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_projectedTypeBudget_normalizedCoeff_fixedDerivative
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
          M n hn2 htb hns ∧
        RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_projectedTypeBudget_normalizedCoeff_fixedDerivative
      hcert)

/-- Rich-projection discharge with the singleton-quotient projected type budget
discharged by concrete `concreteW` row embeddings. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_projectedTypeBudget_normalizedCoeff_fixedDerivative
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
            M n hn2 htb hns ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
            M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_projectedTypeBudget_normalizedCoeff_fixedDerivative
      hcert)

/-- Legacy rich-projection discharge from concrete row embeddings and
normalized singleton-normalizer row identity. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedRows
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonNormalizedRowIdentity
            M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedRows
      hcert)

/-- Legacy rich-projection discharge from concrete row embeddings and the
normalized non-singleton coefficient identity. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeff
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
            M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeff
      hcert)

/-- Rich-projection discharge from concrete row embeddings and the expanded
normalized coefficient balance, via the semantic singleton-normalizer route. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeffBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
            M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeffBalance
      hcert)

/-- Rich-projection discharge from concrete row embeddings plus the narrowed
canonical/profile residual-balance package.  This is the paper-faithful
replacement for the refuted broad range-wide coefficient-balance close-out. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_canonicalProfileResidualBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          Nonempty
            (RouteBPaperFaithfulTPhiCanonicalProfileResidualBalance
              M n hn2 htb hns)) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_canonicalProfileResidualBalance
      hcert)

/-- Rich-projection discharge using the proved strict paper-faithful
canonical/profile coefficient package. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_strictPaperFaithfulCanonicalProfile
    (hrows :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_strictPaperFaithfulCanonicalProfile
      hrows)

/-- Rich-projection discharge from the imported canonical `concreteW`
row-embedding frontier and the proved strict paper-faithful canonical/profile
coefficient package. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_importedConcreteW_strictPaperFaithfulCanonicalProfile
    (hShape :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        CookLevinDirectBranchShapeWitnesses M n hn2 htb hns hn4)
    (hTransport :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        CookLevinConcreteWCanonicalRowTransport M n hn2 htb hns hn4)
    (hDeriv :
      forall (n : Nat) (hn4 : n >= 4),
        PallLean.Paper93.Spanning.DerivClosurePerType (n := n)
          (fun tau =>
            PallLean.Paper93.Wiring.concreteW n hn4
              (Fin.castLEEmb hn4) tau))
    (hI1 :
      forall (n : Nat) (hn4 : n >= 4),
        ConcreteWProductGrouping n hn4)
    (hI2 :
      forall (n : Nat) (hn4 : n >= 4),
        ConcreteWShiftClosure n hn4)
    (hI3 :
      forall (n : Nat) (hn4 : n >= 4),
        ConcreteWMlprojClosure n hn4) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_importedConcreteW_strictPaperFaithfulCanonicalProfile
      hShape hTransport hDeriv hI1 hI2 hI3)

/-- Rich-projection discharge through the paper-faithful strict
canonical-window/profile-orbit assembly. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly
    (hassembly :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictPaperProfileOrbitGlobalAssembly
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly
      hassembly)

/-- Rich-projection discharge through the actual canonical-window
local-monoid/profile analysis. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileAnalysis
    (hanalysis :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileAnalysis
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileAnalysis
      hanalysis)

/-- Rich-projection discharge from the separated paper local-monoid/profile
data. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileData
    (hdata :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictCanonicalWindowLocalMonoidProfileData
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileData
      hdata)

/-- Rich-projection discharge from literal interface-anonymous local-monoid
profile data, matching paper §9.3 Definition 21/Lemma 29 and Lemma 31. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictInterfaceAnonymousLocalMonoidProfileData
    (hdata :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictInterfaceAnonymousLocalMonoidProfileData
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictInterfaceAnonymousLocalMonoidProfileData
      hdata)

/-- Rich-projection discharge from the bounded finite-normal-form alphabet
version of the literal interface-anonymous local-monoid profile data. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictBoundedInterfaceAnonymousLocalMonoidProfileData
    (hdata :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictBoundedInterfaceAnonymousLocalMonoidProfileData
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictBoundedInterfaceAnonymousLocalMonoidProfileData
      hdata)

/-- Rich-projection discharge from the actual four-valued Cook-Levin
interface-alphabet version of strict interface-anonymous profile data. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfileData
    (hdata :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictConstraintTypeInterfaceProfileData
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfileData
      hdata)

/-- Rich-projection discharge from strict `ConstraintType` profile-subspace
data, with local bases generated from the profile subspaces. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceData
    (hdata :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceData
      hdata)

/-- Rich-projection discharge from the corrected paper-shaped strict range-row
cover theorem.

This is the discharge analogue of
`noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictPaperRangeRowsGlobalProfileSpanCover`:
the input is not a broad classifier or quotient identity, but the actual
finite local-monoid profile data together with the strict range-row global
cover for that same data. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictPaperRangeRowsGlobalProfileSpanCover
    (hcover :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists D :
          RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
            M n hn2 htb hns,
          RouteBPaperFaithfulTPhiStrictPaperRangeRowsGlobalProfileSpanCover D) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictPaperRangeRowsGlobalProfileSpanCover
      hcover)

/-- Rich-projection discharge from corrected paper-shaped range-row profile
cover data with the combined profile budget. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictPaperRangeRowProfileCoverData
    (hdata :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictPaperRangeRowProfileCoverData
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictPaperRangeRowProfileCoverData
      hdata)

/-- Rich-projection discharge from the actual local-monoid/profile analysis,
routed through the separated paper data surface. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictLocalMonoidProfileAnalysis
    (hanalysis :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictLocalMonoidProfileAnalysis
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictLocalMonoidProfileAnalysis
      hanalysis)

/-- Rich-projection discharge from canonical-window orbit/profile data plus
the exact range-row assembled-profile cover. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictCanonicalWindowOrbitProfile_rangeRows
    (hprofile :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists D :
          RouteBPaperFaithfulTPhiStrictCanonicalWindowOrbitRankData
            M n hn2 htb hns,
          RouteBPaperFaithfulTPhiStrictRangeRowsGlobalProfileSpanCover D) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictCanonicalWindowOrbitProfile_rangeRows
      hprofile)

/-- Rich-projection discharge from strict range-row profile-cover data. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictRangeRowProfileCoverData
    (hcover :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictRangeRowProfileCoverData
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictRangeRowProfileCoverData
      hcover)

/-- Rich-projection discharge from the strict profile-subspace classifier
obligation. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation
    (hclassifier :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBPaperFaithfulTPhiStrictProfileSubspaceClassifierObligation
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation
      hclassifier)

/-- Rich-projection discharge from projected profile compression plus
restricted strict-row identity. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_restrictedRowIdentity_projectedCommonSpan
    (hprojected :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists project :
          MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ,
          ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            project (withinProfileBound (Nat.log 2 n)) ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
            M n hn2 htb hns project) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_restrictedRowIdentity_projectedCommonSpan
      hprojected)

/-- Rich-projection discharge from quotient certificate data and semantic
restricted residual balance. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_quotientTypeCertificate_restrictedResidualBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists typeBudget : Nat,
        exists cert :
          ZeroProfileQuotientTypeSpaceCertificate (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            typeBudget,
          typeBudget <= withinProfileBound (Nat.log 2 n) ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
            M n hn2 htb hns cert.project) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_quotientTypeCertificate_restrictedResidualBalance
      hcert)

/-- Rich-projection discharge from quotient normal-form obligation data and
semantic restricted residual balance. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_quotientTypeNormalFormObligation_restrictedResidualBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists typeBudget : Nat,
          CookLevinZeroProfileQuotientTypeNormalFormObligation
            M n hn2 htb hns typeBudget ∧
          (∀ cert :
            ZeroProfileQuotientTypeSpaceCertificate (Nat.log 2 n)
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
              typeBudget,
            RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
              M n hn2 htb hns cert.project) ∧
          typeBudget <= withinProfileBound (Nat.log 2 n)) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_quotientTypeNormalFormObligation_restrictedResidualBalance
      hcert)

/-- Rich-projection discharge through the endpoint/profile-aware replacement
for canonical `concreteW` H4. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_endpointAugmented_directBranchTransport_concreteEndpointCharge_chargedTargetCover
    (hzero :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hShape :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        CookLevinDirectBranchShapeWitnesses M n hn2 htb hns hn4)
    (hTransport :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        CookLevinConcreteWCanonicalRowTransport M n hn2 htb hns hn4)
    (hI1_univ : PallLean.Paper93.Wiring.PerTypeProductGrouping_universal)
    (hI3_univ : PallLean.Paper93.Wiring.PerTypeMlprojClosure_universal)
    (hCover :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        forall (h : ProfileHistogram)
          (hadm : ProfileAdmissible (Nat.log 2 n) h),
            h ConstraintType.transitionRight = 0 ->
              h ≠ zeroProfileHistogram ->
                ActiveProfileSupport h ->
                  CookLevinEndpointChargedTargetProfileCoverAt
                    M n hn2 htb hns
                    (concreteWEndpointSpanOneStepCharge n hn4) h hadm) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_endpointAugmented_directBranchTransport_concreteEndpointCharge_chargedTargetCover
      hzero hShape hTransport hI1_univ hI3_univ hCover)

/-- Rich-projection discharge through the concrete endpoint charge with the
remaining target-profile cover stated at generator level. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_endpointAugmented_directBranchTransport_concreteEndpointCharge_chargedGeneratorCover
    (hzero :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hShape :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        CookLevinDirectBranchShapeWitnesses M n hn2 htb hns hn4)
    (hTransport :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        CookLevinConcreteWCanonicalRowTransport M n hn2 htb hns hn4)
    (hI1_univ : PallLean.Paper93.Wiring.PerTypeProductGrouping_universal)
    (hI3_univ : PallLean.Paper93.Wiring.PerTypeMlprojClosure_universal)
    (hCover :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        forall (h : ProfileHistogram)
          (hadm : ProfileAdmissible (Nat.log 2 n) h),
            h ConstraintType.transitionRight = 0 ->
              h ≠ zeroProfileHistogram ->
                ActiveProfileSupport h ->
                  CookLevinEndpointChargedTargetGeneratorCoverAt
                    M n hn2 htb hns
                    (concreteWEndpointSpanOneStepCharge n hn4) h hadm) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_endpointAugmented_directBranchTransport_concreteEndpointCharge_chargedGeneratorCover
      hzero hShape hTransport hI1_univ hI3_univ hCover)

/-- Rich-projection discharge from concrete row embeddings and range-only
residual balance through the semantic singleton normalizer. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_residualBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
            M n hn2 htb hns
            (zeroProfileQuotientBySingletonShiftProjection
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_residualBalance
      hcert)

/-- Legacy rich-projection discharge from concrete singleton-quotient
normal-form classifiers and strict-FOB row erasure, mediated only by the
no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_concreteSingletonQuotient_strictFOB
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists typeBudget : Nat,
        exists D :
          ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget,
        exists _ :
          ZeroProfileConcreteNormalFormRowMap
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
              (zeroProfileQuotientBySingletonShiftProjection
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
              D,
            typeBudget <= withinProfileBound (Nat.log 2 n) ∧
            RouteBPaperFaithfulTPhiProjectedPWindowStrictFOBDerivativeErasure
              M n hn2 htb hns
              (zeroProfileQuotientBySingletonShiftProjection
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteSingletonQuotient_strictFOB
      hcert)

/-- Legacy rich-projection discharge from concrete singleton-quotient
normal-form classifiers and the corrected range-only row identity, mediated
only by the no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_concreteSingletonQuotient_rangeRestrictedRowIdentity
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists typeBudget : Nat,
        exists D :
          ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget,
        exists _ :
          ZeroProfileConcreteNormalFormRowMap
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
              (zeroProfileQuotientBySingletonShiftProjection
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
              D,
            typeBudget <= withinProfileBound (Nat.log 2 n) ∧
            RouteBPaperFaithfulTPhiRangePWindowRestrictedZeroProfileRowIdentity
              M n hn2 htb hns
              (zeroProfileQuotientBySingletonShiftProjection
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteSingletonQuotient_rangeRestrictedRowIdentity
      hcert)

/-- Legacy rich-projection discharge from the corrected range-only strict
`TΦ` singleton-quotient route, mediated only by the no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_rangeRestrictedResidualBalance
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedResidualBalance
            M n hn2 htb hns
            (zeroProfileQuotientBySingletonShiftProjection
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_rangeRestrictedResidualBalance
      hcert)

/-- Legacy rich-projection discharge from the strict `TΦ` singleton-quotient
residual-decomposition route, mediated only by the no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_residualDecomposition
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientResidualDecomposition
            M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_residualDecomposition
      hcert)

/-- Legacy rich-projection discharge from quotient row equality plus the
fixed-representative derivative-row condition, mediated only by the no-decider
equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_quotientRows_fixedDerivative
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientRowIdentity
            M n hn2 htb hns ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
            M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_quotientRows_fixedDerivative
      hcert)

/-- Legacy rich-projection discharge from normalized non-singleton coefficient
equality plus fixed derivative representatives, mediated only by the no-decider
equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_normalizedCoeff_fixedDerivative
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedNonSingletonCoeffIdentity
            M n hn2 htb hns ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
            M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_normalizedCoeff_fixedDerivative
      hcert)

/-- Legacy rich-projection discharge from the expanded corrected coefficient
balance, mediated only by the no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_coeffBalance_fixedDerivative
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedNormalizedCoeffBalance
            M n hn2 htb hns ∧
          RouteBPaperFaithfulTPhiRangePWindowRestrictedSingletonQuotientDerivativeFixed
            M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_coeffBalance_fixedDerivative
      hcert)

/-! ## Axiom audit anchors -/

#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_projectedTypeBudget
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_commonSpan
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_commonSpan_normalizedRows
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_commonSpan_residualBalance
#print axioms routeBPaperFaithfulTPhi_singletonNormalFormBudget_add_ambient_le_pow_200
#print axioms routeBPaperFaithfulTPhi_withinProfileBound_add_ambient_le_pow_200
#print axioms zeroProfileProjectedCommonSpanWithBudget_singletonNormalForm_of_singletonQuotient_commonSpan
#print axioms zeroProfileProjectedCommonSpanWithBudget_singletonNormalForm_of_singletonQuotient_projectedTypeBudget
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_residualBalance
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_normalizedRows
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_normalizedCoeff
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_normalizedCoeffBalance
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_projectedTypeBudget_normalizedRows_fixedDerivative
#print axioms zeroProfileProjectedCommonSpanWithBudget_singletonNormalForm_of_zeroHistogramShiftCommonSpan
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_zeroHistogramShiftCommonSpan_residualBalance
#print axioms zeroProfileProjectedCommonSpanWithBudget_singletonNormalForm_concreteW_of_rowEmbeddings
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_concreteW_rowEmbeddings_normalizedRows
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeff
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeffBalance
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonNormalForm_concreteW_rowEmbeddings_residualBalance
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_concreteSingletonQuotient_strictFOB
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_rangeRestrictedResidualBalance
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_residualDecomposition
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_quotientRows_fixedDerivative
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_normalizedCoeff_fixedDerivative
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_singletonQuotient_concreteW_rowEmbeddings_coeffBalance_fixedDerivative
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_projectedTypeBudget
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_commonSpan
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_commonSpan_normalizedRows
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_commonSpan_residualBalance
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_residualBalance
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedRows
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedCoeff
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedCoeffBalance
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedRows_fixedDerivative
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_projectedTypeBudget_normalizedCoeff_fixedDerivative
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_projectedTypeBudget_normalizedCoeff_fixedDerivative
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedRows
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeff
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeffBalance
#print axioms routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeffBalance_certificate_noGo_of_twoDifferentiatedStrictTags_even
#print axioms routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedNonSingletonCoeff_certificate_noGo_of_twoDifferentiatedStrictTags_even
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_canonicalProfileResidualBalance
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_strictPaperFaithfulCanonicalProfile
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_importedConcreteW_strictPaperFaithfulCanonicalProfile
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_strictPaperProfileOrbitGlobalAssembly
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_strictCanonicalWindowLocalMonoidProfileAnalysis
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileAnalysis
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_strictCanonicalWindowLocalMonoidProfileData
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileData
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictInterfaceAnonymousLocalMonoidProfileData
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictBoundedInterfaceAnonymousLocalMonoidProfileData
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfileData
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceData
#print axioms false_of_routeBPaperFaithfulTPhi_projectedLogWindow_of_strictLocalMonoidProfileAnalysis
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictLocalMonoidProfileAnalysis
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictCanonicalWindowOrbitProfile_rangeRows
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictRangeRowProfileCoverData
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_restrictedRowIdentity_projectedCommonSpan
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_quotientTypeCertificate_restrictedResidualBalance
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_quotientTypeNormalFormObligation_restrictedResidualBalance
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_endpointAugmented_directBranchTransport_concreteEndpointCharge_chargedTargetCover
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_endpointAugmented_directBranchTransport_concreteEndpointCharge_chargedGeneratorCover
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_residualBalance
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_concreteSingletonQuotient_strictFOB
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_rangeRestrictedResidualBalance
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_residualDecomposition
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_quotientRows_fixedDerivative
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_normalizedCoeff_fixedDerivative
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_coeffBalance_fixedDerivative
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_projectedTypeBudget
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_commonSpan
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_commonSpan_normalizedRows
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_commonSpan_residualBalance
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_residualBalance
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedRows
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedCoeff
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedCoeffBalance
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedRows_fixedDerivative
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_projectedTypeBudget_normalizedCoeff_fixedDerivative
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_projectedTypeBudget_normalizedCoeff_fixedDerivative
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedRows
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeff
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeffBalance
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_canonicalProfileResidualBalance
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_strictPaperFaithfulCanonicalProfile
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_importedConcreteW_strictPaperFaithfulCanonicalProfile
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictPaperProfileOrbitGlobalAssembly
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileAnalysis
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileData
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictInterfaceAnonymousLocalMonoidProfileData
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictBoundedInterfaceAnonymousLocalMonoidProfileData
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfileData
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceData
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictLocalMonoidProfileAnalysis
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictCanonicalWindowOrbitProfile_rangeRows
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictRangeRowProfileCoverData
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_strictProfileSubspaceClassifierObligation
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_restrictedRowIdentity_projectedCommonSpan
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_quotientTypeCertificate_restrictedResidualBalance
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_quotientTypeNormalFormObligation_restrictedResidualBalance
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_endpointAugmented_directBranchTransport_concreteEndpointCharge_chargedTargetCover
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_endpointAugmented_directBranchTransport_concreteEndpointCharge_chargedGeneratorCover
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_residualBalance
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_concreteSingletonQuotient_strictFOB
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_rangeRestrictedResidualBalance
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_residualDecomposition
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_quotientRows_fixedDerivative
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_normalizedCoeff_fixedDerivative
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_coeffBalance_fixedDerivative

end PallLean.Paper93.Paper283
