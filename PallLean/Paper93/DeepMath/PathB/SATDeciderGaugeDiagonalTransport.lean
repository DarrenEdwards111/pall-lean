import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeDischargeSubgoals
import PallLean.PaperFaithfulCompilation

/-!
# Transporting a diagonal candidate to the flat SAT-decider gauge space

This file rules out the **diagonal-only shortcut** for the SAT-decider gauge.
The intuition is structural: if `Π⋆` is forced to be a diagonal matrix on the
flat ambient (i.e. it acts on each variable independently as a single scalar),
then on the polynomial space it must take the form `c • id` for some `c : ℚ`.

We show:

* The "all-ones diagonal" collapses literally to the identity gauge
  (`satDeciderGaugeDiagonal 1 = LinearMap.id`).
* Any scalar diagonal `c • id` is **rank monotone** for the SPDP rank, since
  scalar multiplication contracts the SPDP subspace and hence cannot increase
  finrank. This holds even when `c ≠ 1`.
* Idempotence (the `IsProjectionGauge` requirement) forces `c = 0` or `c = 1`,
  i.e. the only diagonal candidates that can serve as projection gauges are
  the zero map and the identity. In particular, no rank-strict, non-trivial
  `Π⋆` can be realised as a diagonal candidate.

Together, these statements certify that the diagonal-only shortcut collapses
to either the identity or a non-rank-reducing scalar map, and so cannot be
the nontrivial richer projection that the paper requires.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open SPDP
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine

/-! ## Section 1: The diagonal candidate -/

/-- The **diagonal candidate** for a SAT-decider gauge: the linear endomorphism
that scales every polynomial by a fixed scalar `c : ℚ`. This is the polynomial
incarnation of "Π⋆ is a diagonal matrix with all diagonal entries equal to
`c`". When `c = 1` it is the identity; when `c = 0` it is the zero map. -/
noncomputable def satDeciderGaugeDiagonal
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (c : ℚ) :
    SATDeciderGaugeMap M n hn2 htb hns :=
  c • (LinearMap.id : SATDeciderGaugeSpace M n hn2 htb hns →ₗ[Rat]
      SATDeciderGaugeSpace M n hn2 htb hns)

/-- Applying the diagonal candidate to a polynomial multiplies it by `c`. -/
theorem satDeciderGaugeDiagonal_apply
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (c : ℚ)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    satDeciderGaugeDiagonal M n hn2 htb hns c p = c • p := by
  unfold satDeciderGaugeDiagonal
  simp

/-! ## Section 2: All-ones diagonal collapses to the identity -/

/-- The all-ones diagonal candidate is literally the identity gauge.
This is the algebraic reflection of "diagonal with all entries equal to 1
is the identity matrix". -/
theorem satDeciderGaugeDiagonal_one_eq_id
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeDiagonal M n hn2 htb hns 1 = LinearMap.id := by
  unfold satDeciderGaugeDiagonal
  ext p
  simp

/-- Pointwise restatement: the all-ones diagonal fixes every polynomial. -/
theorem satDeciderGaugeDiagonal_one_apply
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    satDeciderGaugeDiagonal M n hn2 htb hns 1 p = p := by
  rw [satDeciderGaugeDiagonal_apply]
  simp

/-! ## Section 3: Scalar multiplication does not enlarge the SPDP subspace -/

/-- Scalar multiplication contracts the SPDP subspace: every generator of
`mlBlockedSpdpSubspace B κ ℓ (c • p)` is `c` times a generator of
`mlBlockedSpdpSubspace B κ ℓ p`, hence lies in the latter. -/
theorem mlBlockedSpdpSubspace_smul_le
    {N : ℕ} (B : BlockPartition N) (κ ℓ : ℕ) (c : ℚ)
    (p : MvPolynomial (Fin N) ℚ) :
    mlBlockedSpdpSubspace B κ ℓ (c • p) ≤
      mlBlockedSpdpSubspace B κ ℓ p := by
  apply Submodule.span_le.mpr
  rintro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
  -- Rewrite the generator using `iterDerivList_smul` and `mlProj` linearity.
  have hderiv : iterDerivList S (c • p) = c • iterDerivList S p :=
    GaugeMonotonicity.iterDerivList_smul S c p
  have hmul : m * iterDerivList S (c • p) = c • (m * iterDerivList S p) := by
    rw [hderiv, mul_smul_comm]
  have hproj :
      mlProj (m * iterDerivList S (c • p)) = c • mlProj (m * iterDerivList S p) := by
    rw [hmul]
    exact mlProj_smul c (m * iterDerivList S p)
  -- The generator of `c • p` equals `c • (a generator of p)`.
  have hq' : q = c • mlProj (m * iterDerivList S p) := by
    rw [hq, hproj]
  rw [hq']
  -- A scalar multiple of a generator lives in the span of generators.
  refine Submodule.smul_mem _ c ?_
  exact Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩

/-- SPDP rank is monotone under scalar multiplication: scaling `p` by any
scalar `c : ℚ` cannot increase its multilinear-blocked SPDP rank. -/
theorem mlBlockedSpdpRank_smul_le
    {N : ℕ} (B : BlockPartition N) (κ ℓ : ℕ) (c : ℚ)
    (p : MvPolynomial (Fin N) ℚ) :
    mlBlockedSpdpRank B κ ℓ (c • p) ≤ mlBlockedSpdpRank B κ ℓ p := by
  unfold mlBlockedSpdpRank
  exact Submodule.finrank_mono (mlBlockedSpdpSubspace_smul_le B κ ℓ c p)

/-! ## Section 4: Rank monotonicity for the diagonal candidate -/

/-- The diagonal candidate is a rank-monotone gauge, in the generic
`GaugeMonotonicity` vocabulary, for every scalar `c : ℚ`. -/
theorem satDeciderGaugeDiagonal_isRankMonotoneGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (c : ℚ) :
    GaugeMonotonicity.IsRankMonotoneGauge
      (cook_levin_compilation M n hn2 htb hns).partition
      (satDeciderGaugeDiagonal M n hn2 htb hns c) := by
  intro κ ℓ p
  rw [satDeciderGaugeDiagonal_apply]
  exact mlBlockedSpdpRank_smul_le _ κ ℓ c p

/-- Rank monotonicity for the diagonal candidate, stated as the SAT-decider
gauge subgoal `SATDeciderGaugeRankMonotonicity`. -/
theorem satDeciderGaugeDiagonal_rankMonotonicity
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (c : ℚ) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (satDeciderGaugeDiagonal M n hn2 htb hns c) :=
  satDeciderGaugeDiagonal_isRankMonotoneGauge M n hn2 htb hns c

/-! ## Section 5: All-ones diagonal is a projection gauge -/

/-- The all-ones diagonal candidate is a projection gauge — because it equals
the identity. This is the only "real" projection a diagonal candidate can
provide. -/
theorem satDeciderGaugeDiagonal_one_isProjectionGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    GaugeMonotonicity.IsProjectionGauge
      (satDeciderGaugeDiagonal M n hn2 htb hns 1) := by
  rw [satDeciderGaugeDiagonal_one_eq_id]
  exact GaugeMonotonicity.IsProjectionGauge.id

/-- Rank monotonicity for the all-ones diagonal in the generic
`GaugeMonotonicity` vocabulary, stated by collapsing to the identity. -/
theorem satDeciderGaugeDiagonal_one_isRankMonotoneGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    GaugeMonotonicity.IsRankMonotoneGauge
      (cook_levin_compilation M n hn2 htb hns).partition
      (satDeciderGaugeDiagonal M n hn2 htb hns 1) := by
  rw [satDeciderGaugeDiagonal_one_eq_id]
  exact GaugeMonotonicity.IsRankMonotoneGauge.id
    (cook_levin_compilation M n hn2 htb hns).partition

/-! ## Section 6: Idempotence forces `c ∈ {0, 1}`

The `IsProjectionGauge` requirement is `g ∘ₗ g = g`. For the diagonal
candidate `c • id`, this becomes `c^2 • id = c • id`, which on the
multivariate polynomial ring `MvPolynomial (Fin _) ℚ` (which is nontrivial)
forces `c^2 = c`, i.e. `c = 0` or `c = 1`. So the only diagonal candidates
that can be projection gauges are the trivial ones; no nontrivial richer
projection (with `c ≠ 1` and `c ≠ 0`) can hide inside the diagonal-only
shortcut. -/

/-- A nonzero polynomial witness in the SAT-decider polynomial space:
the constant `1`. The Cook-Levin compilation has at least one variable when
`n ≥ 2`, so the polynomial ring is nontrivial. -/
theorem satDeciderGaugeSpace_one_ne_zero
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    (1 : SATDeciderGaugeSpace M n hn2 htb hns) ≠ 0 := by
  intro h
  have h' :=
    congrArg (fun p => MvPolynomial.coeff (0 : Fin (cook_levin_compilation M n hn2 htb hns).numVars →₀ ℕ) p) h
  simp [MvPolynomial.coeff_one] at h'

/-- If the diagonal candidate `c • id` is a projection gauge, then
`c^2 = c`. -/
theorem satDeciderGaugeDiagonal_isProjectionGauge_implies_idempotent_scalar
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (c : ℚ)
    (h : GaugeMonotonicity.IsProjectionGauge
      (satDeciderGaugeDiagonal M n hn2 htb hns c)) :
    c * c = c := by
  -- The idempotence equation, applied to `1 : SATDeciderGaugeSpace`, says
  -- `c • (c • 1) = c • 1`, i.e. `(c * c) • 1 = c • 1`.
  have hap :
      satDeciderGaugeDiagonal M n hn2 htb hns c
          (satDeciderGaugeDiagonal M n hn2 htb hns c
            (1 : SATDeciderGaugeSpace M n hn2 htb hns)) =
        satDeciderGaugeDiagonal M n hn2 htb hns c
          (1 : SATDeciderGaugeSpace M n hn2 htb hns) :=
    h.apply_apply (1 : SATDeciderGaugeSpace M n hn2 htb hns)
  -- The three diagonal applications collapse via `simp` to scalar smul.
  simp only [satDeciderGaugeDiagonal_apply, smul_smul] at hap
  -- Now `hap : (c * c) • 1 = c • 1`. Use that `1 ≠ 0` to cancel.
  have hone_ne : (1 : SATDeciderGaugeSpace M n hn2 htb hns) ≠ 0 :=
    satDeciderGaugeSpace_one_ne_zero M n hn2 htb hns
  -- Subtract: `((c * c) - c) • 1 = 0`.
  have hsub :
      ((c * c) - c) • (1 : SATDeciderGaugeSpace M n hn2 htb hns) = 0 := by
    rw [sub_smul, hap, sub_self]
  -- In the ℚ-module `MvPolynomial`, `r • x = 0` with `x ≠ 0` forces `r = 0`.
  have hcc : (c * c) - c = 0 := by
    rcases (smul_eq_zero.mp hsub) with hr | hx
    · exact hr
    · exact absurd hx hone_ne
  linarith

/-- If the diagonal candidate `c • id` is a projection gauge, then `c = 0`
or `c = 1`. So a diagonal candidate can serve as a projection gauge **only**
in the trivial cases — it cannot be a non-trivial richer projection. -/
theorem satDeciderGaugeDiagonal_isProjectionGauge_iff_trivial
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (c : ℚ)
    (h : GaugeMonotonicity.IsProjectionGauge
      (satDeciderGaugeDiagonal M n hn2 htb hns c)) :
    c = 0 ∨ c = 1 := by
  have hcc : c * c = c :=
    satDeciderGaugeDiagonal_isProjectionGauge_implies_idempotent_scalar
      M n hn2 htb hns c h
  -- `c^2 = c` factors as `c * (c - 1) = 0` in ℚ (a field, no zero divisors).
  have hfact : c * (c - 1) = 0 := by linarith
  rcases mul_eq_zero.mp hfact with hc | hc
  · exact Or.inl hc
  · exact Or.inr (by linarith)

/-! ## Section 7: Diagonal-only shortcut summary -/

/-- **Diagonal-only shortcut summary.** Any diagonal candidate
`satDeciderGaugeDiagonal c` either:

  (a) fails to be a projection gauge (`c ≠ 0` and `c ≠ 1`); or
  (b) is a projection gauge but with `c ∈ {0, 1}`, in which case it is the
      zero map (`c = 0`) or the identity (`c = 1`).

Either way, the diagonal-only candidate cannot serve as a non-trivial richer
projection: in case (a) the projection requirement of `IsAmplituhedronGauge`
fails outright, and in case (b) the candidate collapses to the identity (or
the trivial zero map) which makes no rank reduction. -/
theorem satDeciderGaugeDiagonal_collapses
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (c : ℚ) :
    (¬ GaugeMonotonicity.IsProjectionGauge
        (satDeciderGaugeDiagonal M n hn2 htb hns c)) ∨
      (satDeciderGaugeDiagonal M n hn2 htb hns c = 0) ∨
      (satDeciderGaugeDiagonal M n hn2 htb hns c = LinearMap.id) := by
  by_cases h : GaugeMonotonicity.IsProjectionGauge
      (satDeciderGaugeDiagonal M n hn2 htb hns c)
  · right
    rcases satDeciderGaugeDiagonal_isProjectionGauge_iff_trivial
        M n hn2 htb hns c h with hc | hc
    · left
      unfold satDeciderGaugeDiagonal
      rw [hc]
      ext p
      simp
    · right
      rw [hc]
      exact satDeciderGaugeDiagonal_one_eq_id M n hn2 htb hns
  · exact Or.inl h

/-! ## Axiom audit anchors -/

#print axioms satDeciderGaugeDiagonal_apply
#print axioms satDeciderGaugeDiagonal_one_eq_id
#print axioms satDeciderGaugeDiagonal_one_apply
#print axioms mlBlockedSpdpSubspace_smul_le
#print axioms mlBlockedSpdpRank_smul_le
#print axioms satDeciderGaugeDiagonal_isRankMonotoneGauge
#print axioms satDeciderGaugeDiagonal_rankMonotonicity
#print axioms satDeciderGaugeDiagonal_one_isProjectionGauge
#print axioms satDeciderGaugeDiagonal_one_isRankMonotoneGauge
#print axioms satDeciderGaugeSpace_one_ne_zero
#print axioms satDeciderGaugeDiagonal_isProjectionGauge_implies_idempotent_scalar
#print axioms satDeciderGaugeDiagonal_isProjectionGauge_iff_trivial
#print axioms satDeciderGaugeDiagonal_collapses

end PallLean.Paper93.DeepMath.PathB
