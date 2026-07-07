import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameInducedMatch

/-!
# N-Frame: the base case — two disjoint rigidities add (detection level), and the Uhlig gap

The recursion `coneExcess(f_{2N}) ≥ 2·coneExcess(f_N) + cN` needs its `2·` term: two copies of
the rigid mixing on DISJOINT inputs must have `coneExcess` that ADDS.  This file proves the base
case AT THE DETECTION/RIGIDITY LEVEL — two disjoint copies' detection matrices form a
BLOCK-DIAGONAL identity, so their detectable ranks add — and locates precisely where the lift to
`coneExcess` (the direct-sum problem) breaks.

  `bilinSym_cross_zero` — **PROVED**: coordinates in different blocks do not cross-detect —
        `A_{ab} + A_{ba} = 0` ⟹ `bilinSym A (e_a)(e_b) = 0`.  (Block-diagonal `A` = two disjoint
        copies.)
  `combined_detection_identity` — **PROVED, THE DETECTION-LEVEL DIRECT SUM**: two induced
        matchings on disjoint blocks (block-internal identities, cross-detection zero) combine to
        a SINGLE induced matching over `Fin r₁ ⊕ Fin r₂` with identity detection.  So (with
        `induced_matching_distinct`) the two rigidities give `2^{r₁+r₂}` distinguished rows —
        cut-rank adds, `rank(F) ≥ r₁ + r₂`.

## Honest scope — the base case holds at DETECTION; the CONE-level lift is the Uhlig gap

The detection-level direct sum is PROVED: disjoint rigidities do not interfere (block-diagonal
identity), so their ranks add.  But this gives a LINEAR bound — `rank(F) ≥ r₁ + r₂ ≤ (#inputs of
F)` — via cut capacity, exactly the `log|Y| ≤ N` regime.

The recursion needs the CONE-level direct sum: `coneExcess(f_{2N}) ≥ 2·coneExcess(f_N)`, where
`coneExcess(f_N)` is SUPER-LINEAR (by induction).  Cut capacity CANNOT supply this — its bound is
`≤ #inputs = 2N < 2·coneExcess(f_N)`.  It requires the two `f_N` sub-CONES of a MINIMAL circuit
to be DISJOINT.  And that is exactly the DIRECT SUM problem, which is OPEN — and worse, Uhlig's
mass-production theorem shows the direct sum for circuit SIZE is FALSE in general (some functions
compute many copies in `(1+o(1))×` the cost of one, by sharing a universal part).  So cone
disjointness cannot be assumed; the base case at the DETECTION level (proved here) does NOT lift
to the CONE level without a proof that the specific rigid `g` admits NO mass-production sharing —
a direct-sum-hardness statement for an explicit function, which is open.

So: the base case is TRUE and proved where it is provable (detection/rigidity direct sum), and the
gap to the recursion is now exactly named — the cone-level direct sum.

**UPDATE (see `ComputationalDepthNFrameUhligCheck.lean`)**: the "guarded by the Uhlig barrier"
framing above is IMPRECISE and is corrected there.  Uhlig mass production only helps
near-maximally-hard functions (`C(f) ~ 2^n/n`); our `g` is easy (`O(dN)`) and `f_N` quasi-linear
(`O(N log N)`), so Uhlig does NOT apply here.  The cone-level direct sum remains OPEN, but for the
general (weaker) reason, not the Uhlig obstruction.  This is the honest boundary of the arc.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameDirectSum

open PallLean.Paper93.DeepMath.PathB.NFrameQuadForm
open PallLean.Paper93.DeepMath.PathB.NFrameEpsBias
open PallLean.Paper93.DeepMath.PathB.NFrameInducedMatch

variable {N : ℕ}

/-- **THE CROSS-ZERO ATOM (proved)**: coordinates whose symmetric `M`-entry is `0` do not
cross-detect — block-diagonal `A` (two disjoint copies) has no cross-detection. -/
theorem bilinSym_cross_zero (A : Fin N → Fin N → ZMod 2) (a b : Fin N)
    (h : A a b + A b a = 0) :
    bilinSym A (unitDir a) (unitDir b) = 0 := by
  unfold unitDir
  rw [bilinSym_units]
  exact h

/-- **THE DETECTION-LEVEL DIRECT SUM (proved)**: two induced matchings on disjoint blocks
(block-internal identity detection, zero cross-detection) combine to one induced matching over
`Fin r₁ ⊕ Fin r₂` with identity detection.  So the two rigidities ADD (`rank ≥ r₁ + r₂`). -/
theorem combined_detection_identity {r₁ r₂ : ℕ} (A : Fin N → Fin N → ZMod 2)
    (s₁ t₁ : Fin r₁ → Fin N) (s₂ t₂ : Fin r₂ → Fin N)
    (hid₁ : ∀ k l, bilinSym A (unitDir (t₁ k)) (unitDir (s₁ l)) = if k = l then 1 else 0)
    (hid₂ : ∀ k l, bilinSym A (unitDir (t₂ k)) (unitDir (s₂ l)) = if k = l then 1 else 0)
    (hcross₁₂ : ∀ k l, bilinSym A (unitDir (t₁ k)) (unitDir (s₂ l)) = 0)
    (hcross₂₁ : ∀ k l, bilinSym A (unitDir (t₂ k)) (unitDir (s₁ l)) = 0) :
    ∀ k l : Fin r₁ ⊕ Fin r₂,
      bilinSym A (unitDir (Sum.elim t₁ t₂ k)) (unitDir (Sum.elim s₁ s₂ l))
        = if k = l then 1 else 0 := by
  intro k l
  cases k with
  | inl k =>
    cases l with
    | inl l =>
      simp only [Sum.elim_inl]
      rw [hid₁]
      by_cases h : k = l <;> simp [h, Sum.inl.injEq]
    | inr l =>
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [hcross₁₂]
      simp
  | inr k =>
    cases l with
    | inl l =>
      simp only [Sum.elim_inr, Sum.elim_inl]
      rw [hcross₂₁]
      simp
    | inr l =>
      simp only [Sum.elim_inr]
      rw [hid₂]
      by_cases h : k = l <;> simp [h, Sum.inr.injEq]

end PallLean.Paper93.DeepMath.PathB.NFrameDirectSum

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameDirectSum.bilinSym_cross_zero
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameDirectSum.combined_detection_identity
