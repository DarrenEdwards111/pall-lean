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
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedRows_fixedDerivative
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedRows
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeff
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
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_projectedTypeBudget_normalizedRows_fixedDerivative
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedRows
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonNormalForm_concreteW_rowEmbeddings_normalizedCoeff
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_concreteSingletonQuotient_strictFOB
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_rangeRestrictedResidualBalance
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_residualDecomposition
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_quotientRows_fixedDerivative
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_normalizedCoeff_fixedDerivative
#print axioms cookLevinRichProjectionDischarge_of_routeBPaperFaithfulTPhi_singletonQuotient_concreteW_rowEmbeddings_coeffBalance_fixedDerivative

end PallLean.Paper93.Paper283
