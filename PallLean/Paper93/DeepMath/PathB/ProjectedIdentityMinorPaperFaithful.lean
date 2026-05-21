import PallLean.Step4Compiler

/-!
# Paper-faithful projected identity-minor frontier

The flat SAT-decider gauge field used by `GlobalGodMoveGauge` asks for both
the P-side upper bound and the NP identity-minor lower bound on the same
polynomial `gauge (compiledPoly ...)`.  That is the right contradiction once
all paper hypotheses are assembled, but it is not the paper's intermediate
object language.

This file records the paper-faithful formulation used by Path A / Lemma 205:

* the NP identity minor is first a lower bound on the coupled sheet
  `Q : CoupledSheetPoly σ` over the `u` variables;
* the projected/compiler-side hard object is `Π P = embed σ Q`;
* the lower bound is transported through the `embed` rank-preservation theorem.

So the identity-minor preservation surface is stated on the projected extracted
object `Π P`, not directly on the flat Cook-Levin `compiledPoly`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulCompilation

/-- A Kronecker-dual family certifies linear independence of the primal family.

This is the abstract bridge needed for the projected identity-minor basis: once
`projectedIdentityMinorDual_basis_apply` gives the delta evaluation
`dual i (basis j) = if i = j then 1 else 0`, the primal projected basis is
linearly independent by applying this theorem with `b := projectedIdentityMinorBasis`
and `dual := projectedIdentityMinorDual`. -/
theorem linearIndependent_of_dual_kronecker
    {ι K E : Type*} [DecidableEq ι] [Field K] [AddCommGroup E] [Module K E]
    (b : ι → E) (dual : ι → E →ₗ[K] K)
    (hdual : ∀ i j, dual i (b j) = if i = j then (1 : K) else 0) :
    LinearIndependent K b := by
  rw [linearIndependent_iff]
  intro l hl
  ext i
  have hi_eval : dual i (Finsupp.linearCombination K b l) = l i := by
    rw [LinearMap.map_finsupp_linearCombination]
    rw [Finsupp.linearCombination_apply]
    calc
      (Finsupp.sum l fun j a => a • (dual i ∘ b) j)
          = Finsupp.sum l fun j a => a * (if i = j then (1 : K) else 0) := by
            apply Finsupp.sum_congr
            intro j hj
            simp [hdual]
      _ = Finsupp.sum l fun j a => if i = j then a else 0 := by
            apply Finsupp.sum_congr
            intro j hj
            by_cases hij : i = j <;> simp [hij]
      _ = l i := by
            rw [Finsupp.sum_eq_single i]
            · simp
            · intro j _ hji
              simp [show i ≠ j from hji.symm]
            · intro hi
              simp
  rw [← hi_eval, hl]
  simp

/-- A signed/nonzero-diagonal Kronecker-dual family certifies linear
independence of the primal family.

This is the form needed by the concrete identity-minor construction in
`IdentityMinorReal`: its coefficient matrix has diagonal entries `±1`, not
necessarily definitionally `1`.  The only algebra needed is that every diagonal
entry is nonzero. -/
theorem linearIndependent_of_dual_kronecker_nonzero_diag
    {ι K E : Type*} [DecidableEq ι] [Field K] [AddCommGroup E] [Module K E]
    (b : ι → E) (dual : ι → E →ₗ[K] K) (diag : ι → K)
    (hdiag : ∀ i, diag i ≠ 0)
    (hdual : ∀ i j, dual i (b j) = if i = j then diag i else 0) :
    LinearIndependent K b := by
  rw [linearIndependent_iff]
  intro l hl
  ext i
  have hi_eval : dual i (Finsupp.linearCombination K b l) = l i * diag i := by
    rw [LinearMap.map_finsupp_linearCombination]
    rw [Finsupp.linearCombination_apply]
    calc
      (Finsupp.sum l fun j a => a • (dual i ∘ b) j)
          = Finsupp.sum l fun j a => a * (if i = j then diag i else 0) := by
            apply Finsupp.sum_congr
            intro j hj
            simp [hdual]
      _ = Finsupp.sum l fun j a => if i = j then a * diag i else 0 := by
            apply Finsupp.sum_congr
            intro j hj
            by_cases hij : i = j <;> simp [hij]
      _ = l i * diag i := by
            rw [Finsupp.sum_eq_single i]
            · simp
            · intro j _ hji
              simp [show i ≠ j from hji.symm]
            · intro hi
              simp
  have hzero : l i * diag i = 0 := by
    rw [← hi_eval, hl]
    simp
  exact (mul_eq_zero.mp hzero).resolve_right (hdiag i)

/-- A Kronecker-dual family forces the span of the primal vectors to have
rank at least the index cardinality.  This is the rank-lower-bound form used
for projected identity-minor bases before moving into a concrete SPDP row
subspace. -/
theorem fintype_card_le_finrank_span_of_dual_kronecker
    {ι K E : Type*} [DecidableEq ι] [Fintype ι]
    [Field K] [AddCommGroup E] [Module K E]
    (b : ι → E) (dual : ι → E →ₗ[K] K)
    (hdual : ∀ i j, dual i (b j) = if i = j then (1 : K) else 0) :
    Fintype.card ι ≤ (Set.range b).finrank K := by
  rw [← linearIndependent_iff_card_le_finrank_span]
  exact linearIndependent_of_dual_kronecker b dual hdual

/-- Ambient finite-dimensional version of
`fintype_card_le_finrank_span_of_dual_kronecker`. -/
theorem fintype_card_le_finrank_of_dual_kronecker
    {ι K E : Type*} [DecidableEq ι] [Fintype ι]
    [Field K] [AddCommGroup E] [Module K E] [Module.Finite K E]
    (b : ι → E) (dual : ι → E →ₗ[K] K)
    (hdual : ∀ i j, dual i (b j) = if i = j then (1 : K) else 0) :
    Fintype.card ι ≤ Module.finrank K E := by
  exact (linearIndependent_of_dual_kronecker b dual hdual).fintype_card_le_finrank

/-- If the Kronecker-certified primal vectors all lie in a submodule, then that
submodule has rank at least the index cardinality.  This is the composition
step from projected identity-minor basis vectors into the concrete row/SPDP
subspace containing them. -/
theorem fintype_card_le_submodule_finrank_of_dual_kronecker
    {ι K E : Type*} [DecidableEq ι] [Fintype ι]
    [Field K] [AddCommGroup E] [Module K E]
    (U : Submodule K E) [Module.Finite K U]
    (b : ι → E) (dual : ι → E →ₗ[K] K)
    (hmem : ∀ i, b i ∈ U)
    (hdual : ∀ i j, dual i (b j) = if i = j then (1 : K) else 0) :
    Fintype.card ι ≤ Module.finrank K U := by
  let bU : ι → U := fun i => ⟨b i, hmem i⟩
  let dualU : ι → U →ₗ[K] K := fun i => (dual i).comp U.subtype
  have hdualU : ∀ i j, dualU i (bU j) = if i = j then (1 : K) else 0 := by
    intro i j
    exact hdual i j
  exact (linearIndependent_of_dual_kronecker bU dualU hdualU).fintype_card_le_finrank

/-- Submodule rank lower bound from a signed/nonzero-diagonal Kronecker dual
certificate. -/
theorem fintype_card_le_submodule_finrank_of_dual_kronecker_nonzero_diag
    {ι K E : Type*} [DecidableEq ι] [Fintype ι]
    [Field K] [AddCommGroup E] [Module K E]
    (U : Submodule K E) [Module.Finite K U]
    (b : ι → E) (dual : ι → E →ₗ[K] K) (diag : ι → K)
    (hmem : ∀ i, b i ∈ U)
    (hdiag : ∀ i, diag i ≠ 0)
    (hdual : ∀ i j, dual i (b j) = if i = j then diag i else 0) :
    Fintype.card ι ≤ Module.finrank K U := by
  let bU : ι → U := fun i => ⟨b i, hmem i⟩
  let dualU : ι → U →ₗ[K] K := fun i => (dual i).comp U.subtype
  have hdualU : ∀ i j, dualU i (bU j) = if i = j then diag i else 0 := by
    intro i j
    exact hdual i j
  exact (linearIndependent_of_dual_kronecker_nonzero_diag
    bU dualU diag hdiag hdualU).fintype_card_le_finrank

/-- Concrete SPDP-rank form of the Kronecker-dual lower bound.

If the projected identity-minor basis vectors are actual multilinear SPDP rows
for `p`, the Kronecker dual certificate gives the desired rank lower bound
immediately: the SPDP row subspace contains a linearly independent family of
size `Fintype.card ι`. -/
theorem fintype_card_le_mlBlockedSpdpRank_of_dual_kronecker
    {n : ℕ} {ι K : Type*} [DecidableEq ι] [Fintype ι]
    [Field K]
    (B : SPDP.BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) K)
    (b : ι → MvPolynomial (Fin n) K)
    (dual : ι → MvPolynomial (Fin n) K →ₗ[K] K)
    (hmem : ∀ i, b i ∈ mlBlockedSpdpSubspace B κ ℓ p)
    (hdual : ∀ i j, dual i (b j) = if i = j then (1 : K) else 0) :
    Fintype.card ι ≤ mlBlockedSpdpRank B κ ℓ p := by
  unfold mlBlockedSpdpRank
  exact fintype_card_le_submodule_finrank_of_dual_kronecker
    (mlBlockedSpdpSubspace B κ ℓ p) b dual hmem hdual

/-- Blocked-SPDP-rank version: after the multilinear row-space lower bound,
compose with `mlBlockedSpdpRank_le_blocked`. -/
theorem fintype_card_le_blockedSpdpRank_of_dual_kronecker
    {n : ℕ} {ι K : Type*} [DecidableEq ι] [Fintype ι]
    [Field K]
    (B : SPDP.BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) K)
    (b : ι → MvPolynomial (Fin n) K)
    (dual : ι → MvPolynomial (Fin n) K →ₗ[K] K)
    (hmem : ∀ i, b i ∈ mlBlockedSpdpSubspace B κ ℓ p)
    (hdual : ∀ i j, dual i (b j) = if i = j then (1 : K) else 0) :
    Fintype.card ι ≤ SPDP.blockedSpdpRank B κ ℓ p := by
  exact (fintype_card_le_mlBlockedSpdpRank_of_dual_kronecker
    B κ ℓ p b dual hmem hdual).trans (mlBlockedSpdpRank_le B κ ℓ p)

/-- Multilinear SPDP-rank lower bound from a signed/nonzero-diagonal
Kronecker dual certificate. -/
theorem fintype_card_le_mlBlockedSpdpRank_of_dual_kronecker_nonzero_diag
    {n : ℕ} {ι K : Type*} [DecidableEq ι] [Fintype ι]
    [Field K]
    (B : SPDP.BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) K)
    (b : ι → MvPolynomial (Fin n) K)
    (dual : ι → MvPolynomial (Fin n) K →ₗ[K] K) (diag : ι → K)
    (hmem : ∀ i, b i ∈ mlBlockedSpdpSubspace B κ ℓ p)
    (hdiag : ∀ i, diag i ≠ 0)
    (hdual : ∀ i j, dual i (b j) = if i = j then diag i else 0) :
    Fintype.card ι ≤ mlBlockedSpdpRank B κ ℓ p := by
  unfold mlBlockedSpdpRank
  exact fintype_card_le_submodule_finrank_of_dual_kronecker_nonzero_diag
    (mlBlockedSpdpSubspace B κ ℓ p) b dual diag hmem hdiag hdual

/-- Blocked-SPDP-rank lower bound from a signed/nonzero-diagonal Kronecker
dual certificate. -/
theorem fintype_card_le_blockedSpdpRank_of_dual_kronecker_nonzero_diag
    {n : ℕ} {ι K : Type*} [DecidableEq ι] [Fintype ι]
    [Field K]
    (B : SPDP.BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) K)
    (b : ι → MvPolynomial (Fin n) K)
    (dual : ι → MvPolynomial (Fin n) K →ₗ[K] K) (diag : ι → K)
    (hmem : ∀ i, b i ∈ mlBlockedSpdpSubspace B κ ℓ p)
    (hdiag : ∀ i, diag i ≠ 0)
    (hdual : ∀ i j, dual i (b j) = if i = j then diag i else 0) :
    Fintype.card ι ≤ SPDP.blockedSpdpRank B κ ℓ p := by
  exact (fintype_card_le_mlBlockedSpdpRank_of_dual_kronecker_nonzero_diag
    B κ ℓ p b dual diag hmem hdiag hdual).trans
      (mlBlockedSpdpRank_le B κ ℓ p)

/-- Cardinality-indexed lower-bound transport for multilinear SPDP rank.

This is the final arithmetic composition used when the identity-minor index set
has already been counted: any explicit lower bound on `Fintype.card ι` transfers
to the SPDP rank once the Kronecker rows lie in the SPDP row space.  In the
projected NP application, instantiate `N` with the identity-minor size such as
`Nat.choose (n / 3) (Nat.log 2 n)`. -/
theorem nat_le_mlBlockedSpdpRank_of_card_le_of_dual_kronecker
    {n : ℕ} {ι K : Type*} [DecidableEq ι] [Fintype ι]
    [Field K]
    (N : ℕ) (hcard : N ≤ Fintype.card ι)
    (B : SPDP.BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) K)
    (b : ι → MvPolynomial (Fin n) K)
    (dual : ι → MvPolynomial (Fin n) K →ₗ[K] K)
    (hmem : ∀ i, b i ∈ mlBlockedSpdpSubspace B κ ℓ p)
    (hdual : ∀ i j, dual i (b j) = if i = j then (1 : K) else 0) :
    N ≤ mlBlockedSpdpRank B κ ℓ p :=
  hcard.trans
    (fintype_card_le_mlBlockedSpdpRank_of_dual_kronecker B κ ℓ p b dual hmem hdual)

/-- Cardinality-indexed lower-bound transport for ordinary blocked SPDP rank. -/
theorem nat_le_blockedSpdpRank_of_card_le_of_dual_kronecker
    {n : ℕ} {ι K : Type*} [DecidableEq ι] [Fintype ι]
    [Field K]
    (N : ℕ) (hcard : N ≤ Fintype.card ι)
    (B : SPDP.BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) K)
    (b : ι → MvPolynomial (Fin n) K)
    (dual : ι → MvPolynomial (Fin n) K →ₗ[K] K)
    (hmem : ∀ i, b i ∈ mlBlockedSpdpSubspace B κ ℓ p)
    (hdual : ∀ i j, dual i (b j) = if i = j then (1 : K) else 0) :
    N ≤ SPDP.blockedSpdpRank B κ ℓ p :=
  hcard.trans
    (fintype_card_le_blockedSpdpRank_of_dual_kronecker B κ ℓ p b dual hmem hdual)

/-- Cardinality-indexed lower-bound transport for multilinear SPDP rank from a
signed/nonzero-diagonal Kronecker certificate. -/
theorem nat_le_mlBlockedSpdpRank_of_card_le_of_dual_kronecker_nonzero_diag
    {n : ℕ} {ι K : Type*} [DecidableEq ι] [Fintype ι]
    [Field K]
    (N : ℕ) (hcard : N ≤ Fintype.card ι)
    (B : SPDP.BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) K)
    (b : ι → MvPolynomial (Fin n) K)
    (dual : ι → MvPolynomial (Fin n) K →ₗ[K] K) (diag : ι → K)
    (hmem : ∀ i, b i ∈ mlBlockedSpdpSubspace B κ ℓ p)
    (hdiag : ∀ i, diag i ≠ 0)
    (hdual : ∀ i j, dual i (b j) = if i = j then diag i else 0) :
    N ≤ mlBlockedSpdpRank B κ ℓ p :=
  hcard.trans
    (fintype_card_le_mlBlockedSpdpRank_of_dual_kronecker_nonzero_diag
      B κ ℓ p b dual diag hmem hdiag hdual)

/-- Cardinality-indexed lower-bound transport for ordinary blocked SPDP rank
from a signed/nonzero-diagonal Kronecker certificate. -/
theorem nat_le_blockedSpdpRank_of_card_le_of_dual_kronecker_nonzero_diag
    {n : ℕ} {ι K : Type*} [DecidableEq ι] [Fintype ι]
    [Field K]
    (N : ℕ) (hcard : N ≤ Fintype.card ι)
    (B : SPDP.BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) K)
    (b : ι → MvPolynomial (Fin n) K)
    (dual : ι → MvPolynomial (Fin n) K →ₗ[K] K) (diag : ι → K)
    (hmem : ∀ i, b i ∈ mlBlockedSpdpSubspace B κ ℓ p)
    (hdiag : ∀ i, diag i ≠ 0)
    (hdual : ∀ i j, dual i (b j) = if i = j then diag i else 0) :
    N ≤ SPDP.blockedSpdpRank B κ ℓ p :=
  hcard.trans
    (fintype_card_le_blockedSpdpRank_of_dual_kronecker_nonzero_diag
      B κ ℓ p b dual diag hmem hdiag hdual)

/-- Consume the concrete coefficient-space Kronecker system from
`IdentityMinorReal` as an SPDP-rank lower bound.

The diagonal entries in `IdentityMinorReal.KroneckerDeltaSystem` are signs
`±1`; the nonzero-diagonal bridge above turns that coefficient minor directly
into a multilinear SPDP-rank lower bound once the rows are known to lie in the
SPDP row space. -/
theorem nat_le_mlBlockedSpdpRank_of_kroneckerDeltaSystem_rows
    {n N : ℕ} {K : Type*} [Field K]
    (B : SPDP.BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) K)
    (sys : IdentityMinorReal.KroneckerDeltaSystem K n N)
    (hmem : ∀ i, sys.rows i ∈ mlBlockedSpdpSubspace B κ ℓ p) :
    N ≤ mlBlockedSpdpRank B κ ℓ p := by
  have hcard : N ≤ Fintype.card (Fin N) := by simp
  refine nat_le_mlBlockedSpdpRank_of_card_le_of_dual_kronecker_nonzero_diag
    N hcard B κ ℓ p sys.rows
    (fun i => IdentityMinorReal.coeffLinearMap K (sys.cols i))
    sys.signs hmem ?_ ?_
  · intro i
    rcases sys.signs_unit i with h | h <;> simp [h]
  · intro i j
    exact sys.kronecker i j

/-- The built identity-minor system from a disjoint-clause family gives the
expected `Nat.choose m κ` SPDP-rank lower bound, provided its gadget-product
rows are actual rows of the target SPDP space. -/
theorem choose_le_mlBlockedSpdpRank_of_disjointClauseSystem_rows
    {K : Type*} [Field K]
    (sys : IdentityMinorReal.DisjointClauseSystem K) (κ ℓ : ℕ)
    (B : SPDP.BlockPartition sys.numVars)
    (p : MvPolynomial (Fin sys.numVars) K)
    (hmem : ∀ i,
      IdentityMinorReal.gadgetProd sys (IdentityMinorReal.getClauseSubset sys κ i) ∈
        mlBlockedSpdpSubspace B κ ℓ p) :
    Nat.choose sys.numClauses κ ≤ mlBlockedSpdpRank B κ ℓ p := by
  exact nat_le_mlBlockedSpdpRank_of_kroneckerDeltaSystem_rows
    B κ ℓ p (IdentityMinorReal.buildKroneckerSystem sys κ) hmem

/-- A paper-faithful projection over the `u/v` split ambient polynomial space. -/
abbrev PaperFaithfulProjection (σ : UVSplit) : Type :=
  PMnPoly σ →ₗ[ℚ] PMnPoly σ

/-- Source-side identity-minor lower bound on the coupled sheet `Q`.

This is the paper §18 / §40.3 object: the rank is measured before embedding,
against the pulled-back block partition on the `u` variables. -/
def SourceIdentityMinorLowerBound
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) : Prop :=
  Nat.choose (n / 3) (Nat.log 2 n) ≤
    mlBlockedSpdpRank (pullbackPartition B σ.inlU) κ ℓ Q

/-- Source identity-minor lower bound from explicit projected rows and their
Kronecker duals.

This is the Property-3 local closure in its useful form: once the projected
identity-minor row family lies in the pulled-back multilinear SPDP row space of
`Q`, and the dual functionals evaluate as a Kronecker delta, the usual
`Nat.choose (n / 3) (Nat.log 2 n)` lower bound follows from the independent
row count. -/
theorem sourceIdentityMinorLowerBound_of_dual_kronecker_rows
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ)
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : ι → CoupledSheetPoly σ)
    (dual : ι → CoupledSheetPoly σ →ₗ[ℚ] ℚ)
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ Fintype.card ι)
    (hmem : ∀ i, b i ∈ mlBlockedSpdpSubspace (pullbackPartition B σ.inlU) κ ℓ Q)
    (hdual : ∀ i j, dual i (b j) = if i = j then (1 : ℚ) else 0) :
    SourceIdentityMinorLowerBound n σ B κ ℓ Q := by
  unfold SourceIdentityMinorLowerBound
  exact nat_le_mlBlockedSpdpRank_of_card_le_of_dual_kronecker
    (Nat.choose (n / 3) (Nat.log 2 n)) hcard
    (pullbackPartition B σ.inlU) κ ℓ Q b dual hmem hdual

/-- Source identity-minor lower bound from explicit projected rows and a
signed/nonzero-diagonal Kronecker dual certificate.

This matches the concrete identity-minor coefficient calculation where the
diagonal coefficient is usually a sign (`±1`) rather than literally `1`. -/
theorem sourceIdentityMinorLowerBound_of_dual_kronecker_rows_nonzero_diag
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ)
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : ι → CoupledSheetPoly σ)
    (dual : ι → CoupledSheetPoly σ →ₗ[ℚ] ℚ) (diag : ι → ℚ)
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ Fintype.card ι)
    (hmem : ∀ i, b i ∈ mlBlockedSpdpSubspace (pullbackPartition B σ.inlU) κ ℓ Q)
    (hdiag : ∀ i, diag i ≠ 0)
    (hdual : ∀ i j, dual i (b j) = if i = j then diag i else 0) :
    SourceIdentityMinorLowerBound n σ B κ ℓ Q := by
  unfold SourceIdentityMinorLowerBound
  exact nat_le_mlBlockedSpdpRank_of_card_le_of_dual_kronecker_nonzero_diag
    (Nat.choose (n / 3) (Nat.log 2 n)) hcard
    (pullbackPartition B σ.inlU) κ ℓ Q b dual diag hmem hdiag hdual

/-- Source lower bound from an already-built coefficient-space Kronecker
system over the coupled-sheet variables.

This consumes the exact object constructed in `IdentityMinorReal`: rows,
columns, and signed diagonal coefficients.  The only remaining local proof
obligations are the row-space membership and the comparison between the paper's
`Nat.choose (n / 3) (Nat.log 2 n)` size and the minor size `N`. -/
theorem sourceIdentityMinorLowerBound_of_kroneckerDeltaSystem_rows
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) {N : ℕ}
    (sys : IdentityMinorReal.KroneckerDeltaSystem ℚ σ.numU N)
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ N)
    (hmem : ∀ i, sys.rows i ∈
      mlBlockedSpdpSubspace (pullbackPartition B σ.inlU) κ ℓ Q) :
    SourceIdentityMinorLowerBound n σ B κ ℓ Q := by
  unfold SourceIdentityMinorLowerBound
  exact hcard.trans
    (nat_le_mlBlockedSpdpRank_of_kroneckerDeltaSystem_rows
      (pullbackPartition B σ.inlU) κ ℓ Q sys hmem)

/-- Source lower bound from the concrete disjoint-clause identity-minor
construction, in a split whose `u` variables are exactly the clause-system
variables.

For a disjoint clause system over the coupled-sheet variables, the built
Kronecker system has exactly `Nat.choose sys.numClauses κ` rows.  Thus a
clause-count/cardinality comparison plus row-space membership gives the paper
source identity-minor bound.  This version avoids any equality transport in the
variable count by building the `UVSplit` with `numU := sys.numVars`. -/
theorem sourceIdentityMinorLowerBound_of_disjointClauseSystem_rows
    (n numV : ℕ) (sys : IdentityMinorReal.DisjointClauseSystem ℚ)
    (B : SPDP.BlockPartition ({ numU := sys.numVars, numV := numV } : UVSplit).total)
    (κ ℓ : ℕ)
    (Q : CoupledSheetPoly ({ numU := sys.numVars, numV := numV } : UVSplit))
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ Nat.choose sys.numClauses κ)
    (hmem : ∀ i,
      IdentityMinorReal.gadgetProd sys (IdentityMinorReal.getClauseSubset sys κ i) ∈
        mlBlockedSpdpSubspace
          (pullbackPartition B ({ numU := sys.numVars, numV := numV } : UVSplit).inlU)
          κ ℓ Q) :
    SourceIdentityMinorLowerBound n
      ({ numU := sys.numVars, numV := numV } : UVSplit) B κ ℓ Q := by
  exact sourceIdentityMinorLowerBound_of_kroneckerDeltaSystem_rows
    n ({ numU := sys.numVars, numV := numV } : UVSplit) B κ ℓ Q
    (IdentityMinorReal.buildKroneckerSystem sys κ) hcard hmem

/-- Projected identity-minor lower bound on the embedded hard object.

Unlike `SATDeciderGaugeNPIdentityMinorPreservation`, this formulation does not
mention the flat `compiledPoly`.  It asks whether the projection preserves the
embedded coupled-sheet obstruction. -/
def PaperFaithfulProjectedIdentityMinorLowerBound
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ)
    (Pi : PaperFaithfulProjection σ) : Prop :=
  Nat.choose (n / 3) (Nat.log 2 n) ≤
    mlBlockedSpdpRank B κ ℓ (Pi (CoupledSheetPoly.embed σ Q))

/-- Projected compiler-side identity-minor lower bound.

This is the paper Lemma 205 shape: a compiler polynomial `P` extracts to the
embedded hard object under the projection, and that projected image carries the
identity-minor lower bound. -/
def PaperFaithfulProjectedCompilerIdentityMinorLowerBound
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) (P : PMnPoly σ)
    (Pi : PaperFaithfulProjection σ) : Prop :=
  Pi P = CoupledSheetPoly.embed σ Q ∧
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank B κ ℓ (Pi P)

/-- The projected identity-minor lower bound follows from the source lower
bound when the projection fixes the embedded hard object. -/
theorem projectedIdentityMinorLowerBound_of_source_of_fixed_embed
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ)
    (Pi : PaperFaithfulProjection σ)
    (hfix : Pi (CoupledSheetPoly.embed σ Q) = CoupledSheetPoly.embed σ Q)
    (hsource : SourceIdentityMinorLowerBound n σ B κ ℓ Q) :
    PaperFaithfulProjectedIdentityMinorLowerBound n σ B κ ℓ Q Pi := by
  unfold PaperFaithfulProjectedIdentityMinorLowerBound
  rw [hfix]
  exact le_trans hsource (embed_rank_preservation σ B κ ℓ Q)

/-- The compiler-side projected lower bound follows from the extraction
identity `Π P = embed σ Q` and the source identity-minor lower bound. -/
theorem projectedCompilerIdentityMinorLowerBound_of_extraction_and_source
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) (P : PMnPoly σ)
    (Pi : PaperFaithfulProjection σ)
    (hExtract : Pi P = CoupledSheetPoly.embed σ Q)
    (hsource : SourceIdentityMinorLowerBound n σ B κ ℓ Q) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound n σ B κ ℓ Q P Pi := by
  refine ⟨hExtract, ?_⟩
  rw [hExtract]
  exact le_trans hsource (embed_rank_preservation σ B κ ℓ Q)

/-- Compiler-side projected identity-minor lower bound from explicit projected
rows, their Kronecker duals, and an extraction identity.

This packages the whole local route: count rows, prove the delta evaluation,
show row membership in the pulled-back SPDP space, then compose with
`Pi P = embed Q`. -/
theorem projectedCompilerIdentityMinorLowerBound_of_extraction_dual_kronecker_rows
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) (P : PMnPoly σ)
    (Pi : PaperFaithfulProjection σ)
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : ι → CoupledSheetPoly σ)
    (dual : ι → CoupledSheetPoly σ →ₗ[ℚ] ℚ)
    (hExtract : Pi P = CoupledSheetPoly.embed σ Q)
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ Fintype.card ι)
    (hmem : ∀ i, b i ∈ mlBlockedSpdpSubspace (pullbackPartition B σ.inlU) κ ℓ Q)
    (hdual : ∀ i j, dual i (b j) = if i = j then (1 : ℚ) else 0) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound n σ B κ ℓ Q P Pi := by
  exact projectedCompilerIdentityMinorLowerBound_of_extraction_and_source
    n σ B κ ℓ Q P Pi hExtract
    (sourceIdentityMinorLowerBound_of_dual_kronecker_rows
      n σ B κ ℓ Q b dual hcard hmem hdual)

/-- Compiler-side projected lower bound from explicit rows with a signed
nonzero-diagonal Kronecker certificate. -/
theorem projectedCompilerIdentityMinorLowerBound_of_extraction_dual_kronecker_rows_nonzero_diag
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) (P : PMnPoly σ)
    (Pi : PaperFaithfulProjection σ)
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : ι → CoupledSheetPoly σ)
    (dual : ι → CoupledSheetPoly σ →ₗ[ℚ] ℚ) (diag : ι → ℚ)
    (hExtract : Pi P = CoupledSheetPoly.embed σ Q)
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ Fintype.card ι)
    (hmem : ∀ i, b i ∈ mlBlockedSpdpSubspace (pullbackPartition B σ.inlU) κ ℓ Q)
    (hdiag : ∀ i, diag i ≠ 0)
    (hdual : ∀ i j, dual i (b j) = if i = j then diag i else 0) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound n σ B κ ℓ Q P Pi := by
  exact projectedCompilerIdentityMinorLowerBound_of_extraction_and_source
    n σ B κ ℓ Q P Pi hExtract
    (sourceIdentityMinorLowerBound_of_dual_kronecker_rows_nonzero_diag
      n σ B κ ℓ Q b dual diag hcard hmem hdiag hdual)

/-- Compiler-side projected lower bound from an `IdentityMinorReal`
coefficient-space Kronecker system over the coupled-sheet variables. -/
theorem projectedCompilerIdentityMinorLowerBound_of_extraction_kroneckerDeltaSystem_rows
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) (P : PMnPoly σ)
    (Pi : PaperFaithfulProjection σ) {N : ℕ}
    (sys : IdentityMinorReal.KroneckerDeltaSystem ℚ σ.numU N)
    (hExtract : Pi P = CoupledSheetPoly.embed σ Q)
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ N)
    (hmem : ∀ i, sys.rows i ∈
      mlBlockedSpdpSubspace (pullbackPartition B σ.inlU) κ ℓ Q) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound n σ B κ ℓ Q P Pi := by
  exact projectedCompilerIdentityMinorLowerBound_of_extraction_and_source
    n σ B κ ℓ Q P Pi hExtract
    (sourceIdentityMinorLowerBound_of_kroneckerDeltaSystem_rows
      n σ B κ ℓ Q sys hcard hmem)

/-- Compiler-side projected lower bound from the concrete disjoint-clause
identity-minor construction, for a split whose `u` variables are exactly the
clause-system variables. -/
theorem projectedCompilerIdentityMinorLowerBound_of_extraction_disjointClauseSystem_rows
    (n numV : ℕ) (sys : IdentityMinorReal.DisjointClauseSystem ℚ)
    (B : SPDP.BlockPartition ({ numU := sys.numVars, numV := numV } : UVSplit).total)
    (κ ℓ : ℕ)
    (Q : CoupledSheetPoly ({ numU := sys.numVars, numV := numV } : UVSplit))
    (P : PMnPoly ({ numU := sys.numVars, numV := numV } : UVSplit))
    (Pi : PaperFaithfulProjection ({ numU := sys.numVars, numV := numV } : UVSplit))
    (hExtract : Pi P =
      CoupledSheetPoly.embed ({ numU := sys.numVars, numV := numV } : UVSplit) Q)
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ Nat.choose sys.numClauses κ)
    (hmem : ∀ i,
      IdentityMinorReal.gadgetProd sys (IdentityMinorReal.getClauseSubset sys κ i) ∈
        mlBlockedSpdpSubspace
          (pullbackPartition B ({ numU := sys.numVars, numV := numV } : UVSplit).inlU)
          κ ℓ Q) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound n
      ({ numU := sys.numVars, numV := numV } : UVSplit) B κ ℓ Q P Pi := by
  exact projectedCompilerIdentityMinorLowerBound_of_extraction_and_source
    n ({ numU := sys.numVars, numV := numV } : UVSplit) B κ ℓ Q P Pi hExtract
    (sourceIdentityMinorLowerBound_of_disjointClauseSystem_rows
      n numV sys B κ ℓ Q hcard hmem)

/-- The concrete `piPhi` projection preserves the embedded identity-minor
obstruction whenever the source coupled sheet has the lower bound. -/
theorem piPhi_projectedIdentityMinorLowerBound_of_source
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ)
    (hsource : SourceIdentityMinorLowerBound n σ B κ ℓ Q) :
    PaperFaithfulProjectedIdentityMinorLowerBound n σ B κ ℓ Q (piPhi σ) :=
  projectedIdentityMinorLowerBound_of_source_of_fixed_embed
    n σ B κ ℓ Q (piPhi σ) (piPhi_embed_eq σ Q) hsource

/-- The paper Lemma 205 extraction identity plus the source lower bound gives
the projected compiler-side identity-minor lower bound for `piPhi`. -/
theorem piPhi_projectedCompilerIdentityMinorLowerBound_of_extraction
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) (P : PMnPoly σ)
    (hExtract : piPhi σ P = CoupledSheetPoly.embed σ Q)
    (hsource : SourceIdentityMinorLowerBound n σ B κ ℓ Q) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound n σ B κ ℓ Q P (piPhi σ) :=
  projectedCompilerIdentityMinorLowerBound_of_extraction_and_source
    n σ B κ ℓ Q P (piPhi σ) hExtract hsource

/-- The explicit paper extraction operator `T_Φ` preserves the embedded
identity-minor obstruction when the source coupled sheet has the lower bound.

This uses the actual factorized extraction map from `Step4Compiler`:
`T_Φ = basis ∘ affine relabel ∘ restriction ∘ projection`, which reduces to
`piPhi` in the canonical Cook-Levin basis. -/
theorem T_Phi_projectedIdentityMinorLowerBound_of_source
    (n : ℕ) (σ : UVSplit) (Φ : Finset σ.Idx)
    (B : SPDP.BlockPartition σ.total) (κ ℓ : ℕ)
    (Q : CoupledSheetPoly σ)
    (hsource : SourceIdentityMinorLowerBound n σ B κ ℓ Q) :
    PaperFaithfulProjectedIdentityMinorLowerBound
      n σ B κ ℓ Q (Step4Compiler.T_Phi σ Φ) := by
  apply projectedIdentityMinorLowerBound_of_source_of_fixed_embed
  · rw [Step4Compiler.T_Phi_eq_piPhi σ Φ]
    exact piPhi_embed_eq σ Q
  · exact hsource

/-- The paper Lemma 205 extraction equation for `T_Φ`, plus the source
identity-minor lower bound on the coupled sheet, gives the projected compiler
identity-minor lower bound on the extracted image. -/
theorem T_Phi_projectedCompilerIdentityMinorLowerBound_of_extraction
    (n : ℕ) (σ : UVSplit) (Φ : Finset σ.Idx)
    (B : SPDP.BlockPartition σ.total) (κ ℓ : ℕ)
    (Q : CoupledSheetPoly σ) (P : PMnPoly σ)
    (hExtract : piPhi σ P = CoupledSheetPoly.embed σ Q)
    (hsource : SourceIdentityMinorLowerBound n σ B κ ℓ Q) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound
      n σ B κ ℓ Q P (Step4Compiler.T_Phi σ Φ) :=
  projectedCompilerIdentityMinorLowerBound_of_extraction_and_source
    n σ B κ ℓ Q P (Step4Compiler.T_Phi σ Φ)
    (Step4Compiler.T_Phi_image_of_PMn_real_embed σ Φ P Q hExtract)
    hsource

/-- Projected identity-minor lower bound for a paper §40 partitioned output.

This is the direct `Step241.PartitionedCompilerOutput` formulation: once the
embedded verifier sheet has the identity-minor lower bound, the projected full
compiler output has the same lower bound because `piPhi` extracts exactly
`embedded_Q`. -/
def PartitionedOutputProjectedIdentityMinorLowerBound
    (n : ℕ) (W : Step4Compiler.Step241.PartitionedCompilerOutput)
    (B : SPDP.BlockPartition W.σ.total) (κ ℓ : ℕ) : Prop :=
  Nat.choose (n / 3) (Nat.log 2 n) ≤
    mlBlockedSpdpRank B κ ℓ (piPhi W.σ W.full_output)

/-- If the embedded verifier sheet has the identity-minor lower bound, then
the projected full partitioned output has it too. -/
theorem partitionedOutput_projectedIdentityMinorLowerBound_of_embedded
    (n : ℕ) (W : Step4Compiler.Step241.PartitionedCompilerOutput)
    (B : SPDP.BlockPartition W.σ.total) (κ ℓ : ℕ)
    (hembedded :
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        mlBlockedSpdpRank B κ ℓ W.embedded_Q) :
    PartitionedOutputProjectedIdentityMinorLowerBound n W B κ ℓ := by
  unfold PartitionedOutputProjectedIdentityMinorLowerBound
  rw [Step4Compiler.Step241.partitioned_output_piPhi_extracts W]
  exact hembedded

/-- Source-side identity-minor lower bound on `W.Q_verifier` lifts to the
projected full partitioned output. -/
theorem partitionedOutput_projectedIdentityMinorLowerBound_of_source
    (n : ℕ) (W : Step4Compiler.Step241.PartitionedCompilerOutput)
    (B : SPDP.BlockPartition W.σ.total) (κ ℓ : ℕ)
    (hsource : SourceIdentityMinorLowerBound n W.σ B κ ℓ W.Q_verifier) :
    PartitionedOutputProjectedIdentityMinorLowerBound n W B κ ℓ := by
  apply partitionedOutput_projectedIdentityMinorLowerBound_of_embedded
  change Nat.choose (n / 3) (Nat.log 2 n) ≤
    mlBlockedSpdpRank B κ ℓ (CoupledSheetPoly.embed W.σ W.Q_verifier)
  exact le_trans hsource (embed_rank_preservation W.σ B κ ℓ W.Q_verifier)

/-- The partitioned output directly satisfies the paper-faithful projected
compiler-side identity-minor field. -/
theorem partitionedOutput_projectedCompilerIdentityMinorLowerBound_of_source
    (n : ℕ) (W : Step4Compiler.Step241.PartitionedCompilerOutput)
    (B : SPDP.BlockPartition W.σ.total) (κ ℓ : ℕ)
    (hsource : SourceIdentityMinorLowerBound n W.σ B κ ℓ W.Q_verifier) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound
      n W.σ B κ ℓ W.Q_verifier W.full_output (piPhi W.σ) := by
  apply projectedCompilerIdentityMinorLowerBound_of_extraction_and_source
  · simpa [Step4Compiler.Step241.PartitionedCompilerOutput.embedded_Q] using
      Step4Compiler.Step241.partitioned_output_piPhi_extracts W
  · exact hsource

/-- Partitioned-output form for the actual `T_Φ` extraction pipeline.  The
same source lower bound survives the basis/relabel/restrict/project composite
because the full compiler output extracts to the embedded verifier sheet. -/
theorem partitionedOutput_T_Phi_projectedCompilerIdentityMinorLowerBound_of_source
    (n : ℕ) (W : Step4Compiler.Step241.PartitionedCompilerOutput)
    (Φ : Finset W.σ.Idx)
    (B : SPDP.BlockPartition W.σ.total) (κ ℓ : ℕ)
    (hsource : SourceIdentityMinorLowerBound n W.σ B κ ℓ W.Q_verifier) :
    PaperFaithfulProjectedCompilerIdentityMinorLowerBound
      n W.σ B κ ℓ W.Q_verifier W.full_output
        (Step4Compiler.T_Phi W.σ Φ) := by
  apply T_Phi_projectedCompilerIdentityMinorLowerBound_of_extraction
  · simpa [Step4Compiler.Step241.PartitionedCompilerOutput.embedded_Q] using
      Step4Compiler.Step241.partitioned_output_piPhi_extracts W
  · exact hsource

/-- Paper-faithful P-side upper bound: the small-rank statement belongs to
the compiler polynomial `P`, while the lower bound belongs to its projected
extracted image. -/
def PaperFaithfulCompilerPSideBound
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (P : PMnPoly σ) : Prop :=
  mlBlockedSpdpRank B κ ℓ P ≤ n ^ 200

/-- The paper-faithful projected contradiction package.

This is the precise non-flat formulation: source `Q` has the identity-minor
lower bound, `P` extracts to `embed Q` through `piPhi`, and `P` has the P-side
rank bound. -/
def PaperFaithfulProjectedContradictionPackage
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) (P : PMnPoly σ) : Prop :=
  SourceIdentityMinorLowerBound n σ B κ ℓ Q ∧
    piPhi σ P = CoupledSheetPoly.embed σ Q ∧
      PaperFaithfulCompilerPSideBound n σ B κ ℓ P

/-- Build the projected contradiction package from a coefficient-space
Kronecker system over the coupled-sheet variables.

This is the exact paper-faithful clash constructor: the NP side is supplied by
the identity-minor coefficient system, while the P side remains a separate
small-rank hypothesis about the unprojected compiler polynomial. -/
theorem paperFaithfulProjectedContradictionPackage_of_kroneckerDeltaSystem_rows
    (n : ℕ) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) (P : PMnPoly σ) {N : ℕ}
    (sys : IdentityMinorReal.KroneckerDeltaSystem ℚ σ.numU N)
    (hExtract : piPhi σ P = CoupledSheetPoly.embed σ Q)
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ N)
    (hmem : ∀ i, sys.rows i ∈
      mlBlockedSpdpSubspace (pullbackPartition B σ.inlU) κ ℓ Q)
    (hP : PaperFaithfulCompilerPSideBound n σ B κ ℓ P) :
    PaperFaithfulProjectedContradictionPackage n σ B κ ℓ Q P := by
  refine ⟨?_, hExtract, hP⟩
  exact sourceIdentityMinorLowerBound_of_kroneckerDeltaSystem_rows
    n σ B κ ℓ Q sys hcard hmem

/-- Build the projected contradiction package from a concrete disjoint-clause
identity-minor system. -/
theorem paperFaithfulProjectedContradictionPackage_of_disjointClauseSystem_rows
    (n numV : ℕ) (sys : IdentityMinorReal.DisjointClauseSystem ℚ)
    (B : SPDP.BlockPartition ({ numU := sys.numVars, numV := numV } : UVSplit).total)
    (κ ℓ : ℕ)
    (Q : CoupledSheetPoly ({ numU := sys.numVars, numV := numV } : UVSplit))
    (P : PMnPoly ({ numU := sys.numVars, numV := numV } : UVSplit))
    (hExtract : piPhi ({ numU := sys.numVars, numV := numV } : UVSplit) P =
      CoupledSheetPoly.embed ({ numU := sys.numVars, numV := numV } : UVSplit) Q)
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ Nat.choose sys.numClauses κ)
    (hmem : ∀ i,
      IdentityMinorReal.gadgetProd sys (IdentityMinorReal.getClauseSubset sys κ i) ∈
        mlBlockedSpdpSubspace
          (pullbackPartition B ({ numU := sys.numVars, numV := numV } : UVSplit).inlU)
          κ ℓ Q)
    (hP : PaperFaithfulCompilerPSideBound n
      ({ numU := sys.numVars, numV := numV } : UVSplit) B κ ℓ P) :
    PaperFaithfulProjectedContradictionPackage n
      ({ numU := sys.numVars, numV := numV } : UVSplit) B κ ℓ Q P := by
  refine ⟨?_, hExtract, hP⟩
  exact sourceIdentityMinorLowerBound_of_disjointClauseSystem_rows
    n numV sys B κ ℓ Q hcard hmem

/-- Consuming the paper-faithful projected formulation gives the same final
rank contradiction, but without asking the raw flat `compiledPoly` to carry
both sides of the argument. -/
theorem false_of_paperFaithfulProjectedContradictionPackage
    (n : ℕ) (hn : n ≥ 2 ^ 804)
    (σ : UVSplit) (hV : 0 < σ.numV)
    (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) (P : PMnPoly σ)
    (hpack : PaperFaithfulProjectedContradictionPackage n σ B κ ℓ Q P) :
    False :=
  pathA_general_separation n hn hV B Q P κ ℓ
    hpack.2.1 hpack.1 hpack.2.2

/-- Direct final contradiction from a coefficient-space Kronecker identity
minor plus the paper-faithful extraction and P-side rank bound. -/
theorem false_of_kroneckerDeltaSystem_rows_paperFaithfulProjected
    (n : ℕ) (hn : n ≥ 2 ^ 804)
    (σ : UVSplit) (hV : 0 < σ.numV)
    (B : SPDP.BlockPartition σ.total)
    (κ ℓ : ℕ) (Q : CoupledSheetPoly σ) (P : PMnPoly σ) {N : ℕ}
    (sys : IdentityMinorReal.KroneckerDeltaSystem ℚ σ.numU N)
    (hExtract : piPhi σ P = CoupledSheetPoly.embed σ Q)
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ N)
    (hmem : ∀ i, sys.rows i ∈
      mlBlockedSpdpSubspace (pullbackPartition B σ.inlU) κ ℓ Q)
    (hP : PaperFaithfulCompilerPSideBound n σ B κ ℓ P) :
    False :=
  false_of_paperFaithfulProjectedContradictionPackage n hn σ hV B κ ℓ Q P
    (paperFaithfulProjectedContradictionPackage_of_kroneckerDeltaSystem_rows
      n σ B κ ℓ Q P sys hExtract hcard hmem hP)

/-- Direct final contradiction from a concrete disjoint-clause identity minor
plus extraction and the P-side rank bound. -/
theorem false_of_disjointClauseSystem_rows_paperFaithfulProjected
    (n numV : ℕ) (hn : n ≥ 2 ^ 804) (hV : 0 < numV)
    (sys : IdentityMinorReal.DisjointClauseSystem ℚ)
    (B : SPDP.BlockPartition ({ numU := sys.numVars, numV := numV } : UVSplit).total)
    (κ ℓ : ℕ)
    (Q : CoupledSheetPoly ({ numU := sys.numVars, numV := numV } : UVSplit))
    (P : PMnPoly ({ numU := sys.numVars, numV := numV } : UVSplit))
    (hExtract : piPhi ({ numU := sys.numVars, numV := numV } : UVSplit) P =
      CoupledSheetPoly.embed ({ numU := sys.numVars, numV := numV } : UVSplit) Q)
    (hcard : Nat.choose (n / 3) (Nat.log 2 n) ≤ Nat.choose sys.numClauses κ)
    (hmem : ∀ i,
      IdentityMinorReal.gadgetProd sys (IdentityMinorReal.getClauseSubset sys κ i) ∈
        mlBlockedSpdpSubspace
          (pullbackPartition B ({ numU := sys.numVars, numV := numV } : UVSplit).inlU)
          κ ℓ Q)
    (hP : PaperFaithfulCompilerPSideBound n
      ({ numU := sys.numVars, numV := numV } : UVSplit) B κ ℓ P) :
    False :=
  false_of_paperFaithfulProjectedContradictionPackage n hn
    ({ numU := sys.numVars, numV := numV } : UVSplit) hV B κ ℓ Q P
    (paperFaithfulProjectedContradictionPackage_of_disjointClauseSystem_rows
      n numV sys B κ ℓ Q P hExtract hcard hmem hP)

/-! ## Axiom audit anchors -/

#print axioms linearIndependent_of_dual_kronecker
#print axioms linearIndependent_of_dual_kronecker_nonzero_diag
#print axioms fintype_card_le_finrank_span_of_dual_kronecker
#print axioms fintype_card_le_finrank_of_dual_kronecker
#print axioms fintype_card_le_submodule_finrank_of_dual_kronecker
#print axioms fintype_card_le_submodule_finrank_of_dual_kronecker_nonzero_diag
#print axioms fintype_card_le_mlBlockedSpdpRank_of_dual_kronecker
#print axioms fintype_card_le_blockedSpdpRank_of_dual_kronecker
#print axioms fintype_card_le_mlBlockedSpdpRank_of_dual_kronecker_nonzero_diag
#print axioms fintype_card_le_blockedSpdpRank_of_dual_kronecker_nonzero_diag
#print axioms nat_le_mlBlockedSpdpRank_of_card_le_of_dual_kronecker
#print axioms nat_le_blockedSpdpRank_of_card_le_of_dual_kronecker
#print axioms nat_le_mlBlockedSpdpRank_of_card_le_of_dual_kronecker_nonzero_diag
#print axioms nat_le_blockedSpdpRank_of_card_le_of_dual_kronecker_nonzero_diag
#print axioms nat_le_mlBlockedSpdpRank_of_kroneckerDeltaSystem_rows
#print axioms choose_le_mlBlockedSpdpRank_of_disjointClauseSystem_rows
#print axioms sourceIdentityMinorLowerBound_of_dual_kronecker_rows
#print axioms sourceIdentityMinorLowerBound_of_dual_kronecker_rows_nonzero_diag
#print axioms sourceIdentityMinorLowerBound_of_kroneckerDeltaSystem_rows
#print axioms sourceIdentityMinorLowerBound_of_disjointClauseSystem_rows
#print axioms projectedIdentityMinorLowerBound_of_source_of_fixed_embed
#print axioms projectedCompilerIdentityMinorLowerBound_of_extraction_and_source
#print axioms projectedCompilerIdentityMinorLowerBound_of_extraction_dual_kronecker_rows
#print axioms projectedCompilerIdentityMinorLowerBound_of_extraction_dual_kronecker_rows_nonzero_diag
#print axioms projectedCompilerIdentityMinorLowerBound_of_extraction_kroneckerDeltaSystem_rows
#print axioms projectedCompilerIdentityMinorLowerBound_of_extraction_disjointClauseSystem_rows
#print axioms piPhi_projectedIdentityMinorLowerBound_of_source
#print axioms piPhi_projectedCompilerIdentityMinorLowerBound_of_extraction
#print axioms T_Phi_projectedIdentityMinorLowerBound_of_source
#print axioms T_Phi_projectedCompilerIdentityMinorLowerBound_of_extraction
#print axioms partitionedOutput_projectedIdentityMinorLowerBound_of_embedded
#print axioms partitionedOutput_projectedIdentityMinorLowerBound_of_source
#print axioms partitionedOutput_projectedCompilerIdentityMinorLowerBound_of_source
#print axioms partitionedOutput_T_Phi_projectedCompilerIdentityMinorLowerBound_of_source
#print axioms paperFaithfulProjectedContradictionPackage_of_kroneckerDeltaSystem_rows
#print axioms paperFaithfulProjectedContradictionPackage_of_disjointClauseSystem_rows
#print axioms false_of_paperFaithfulProjectedContradictionPackage
#print axioms false_of_kroneckerDeltaSystem_rows_paperFaithfulProjected
#print axioms false_of_disjointClauseSystem_rows_paperFaithfulProjected

end PallLean.Paper93.DeepMath.PathB
