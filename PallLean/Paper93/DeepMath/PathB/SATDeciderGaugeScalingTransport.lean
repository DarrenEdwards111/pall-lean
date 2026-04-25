import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeDischargeSubgoals
import PallLean.PaperFaithfulCompilation

/-!
# Trivial-scaling shortcut closes to identity-or-zero

This file mirrors `SATDeciderGaugeUVTransport.lean` for a different
"obvious" route to a richer projection: pick a scalar `c : ℚ` and let the
candidate gauge be `c • LinearMap.id` on the flat SAT-decider polynomial
space.

The point of this file is the **negative** result.  We show that the
trivial-scaling family

  `satDeciderGaugeScalingTransport M n hn2 htb hns c := c • LinearMap.id`

is a `GaugeMonotonicity.IsProjectionGauge` if and only if the scalar
satisfies `c * c = c`, equivalently `c = 0` or `c = 1`.  Both endpoints
are degenerate:

* at `c = 1`, the gauge equals `LinearMap.id`, exactly the identity case
  already handled by `SATDeciderGaugeUVTransport`;
* at `c = 0`, the gauge equals `0`, so it sends every polynomial to the
  zero polynomial and cannot preserve any nonzero rank quantity.

In particular, the trivial-scaling shortcut **cannot** produce a richer
projection beyond what the identity already gives.  This rules out one
plausible "free upgrade" path Codex might attempt and forces any
honest richer-projection construction to introduce truly nonscalar
linear structure.

The file is kernel-only: all proofs reduce to algebra of linear maps and
polynomials over `ℚ` plus the existing rank-zero lemma for the zero
polynomial.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine

/-- Trivial scaling candidate gauge: scale every entry of the flat
SAT-decider polynomial space by a fixed scalar `c : ℚ`. -/
noncomputable def satDeciderGaugeScalingTransport
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : ℚ) :
    SATDeciderGaugeMap M n hn2 htb hns :=
  c • (LinearMap.id : SATDeciderGaugeSpace M n hn2 htb hns →ₗ[ℚ]
    SATDeciderGaugeSpace M n hn2 htb hns)

/-- Pointwise behaviour of the scaling candidate. -/
theorem satDeciderGaugeScalingTransport_apply
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : ℚ) (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    satDeciderGaugeScalingTransport M n hn2 htb hns c p = c • p := by
  unfold satDeciderGaugeScalingTransport
  simp [LinearMap.smul_apply]

/-- Composing the scaling candidate with itself multiplies the scalars. -/
theorem satDeciderGaugeScalingTransport_comp
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : ℚ) :
    satDeciderGaugeScalingTransport M n hn2 htb hns c ∘ₗ
        satDeciderGaugeScalingTransport M n hn2 htb hns c =
      satDeciderGaugeScalingTransport M n hn2 htb hns (c * c) := by
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply,
    satDeciderGaugeScalingTransport_apply, smul_smul]

/-- At `c = 1` the scaling candidate is exactly the identity gauge —
the same endomorphism produced by the UV-transport shortcut. -/
theorem satDeciderGaugeScalingTransport_one_eq_id
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeScalingTransport M n hn2 htb hns 1 = LinearMap.id := by
  apply LinearMap.ext
  intro p
  rw [satDeciderGaugeScalingTransport_apply]
  simp

/-- At `c = 0` the scaling candidate is the zero map. -/
theorem satDeciderGaugeScalingTransport_zero_eq_zero
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeScalingTransport M n hn2 htb hns 0 = 0 := by
  apply LinearMap.ext
  intro p
  rw [satDeciderGaugeScalingTransport_apply]
  simp

/-- Idempotency of a scalar gauge forces `c * c = c`.  This is the
algebraic core of the closure: the only scalars that can give a
projection gauge are roots of `c² = c`. -/
theorem satDeciderGaugeScalingTransport_idempotent_forces_sq
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : ℚ)
    (hidem : satDeciderGaugeScalingTransport M n hn2 htb hns c ∘ₗ
        satDeciderGaugeScalingTransport M n hn2 htb hns c =
      satDeciderGaugeScalingTransport M n hn2 htb hns c) :
    c * c = c := by
  -- Apply both sides to the constant polynomial 1.
  have hpt :
      (satDeciderGaugeScalingTransport M n hn2 htb hns c ∘ₗ
          satDeciderGaugeScalingTransport M n hn2 htb hns c)
          (1 : SATDeciderGaugeSpace M n hn2 htb hns) =
        satDeciderGaugeScalingTransport M n hn2 htb hns c
          (1 : SATDeciderGaugeSpace M n hn2 htb hns) := by
    rw [hidem]
  rw [satDeciderGaugeScalingTransport_comp,
      satDeciderGaugeScalingTransport_apply,
      satDeciderGaugeScalingTransport_apply] at hpt
  -- `(c * c) • 1 = c • 1` in the polynomial ring.
  have hsub : (c * c - c) •
      (1 : SATDeciderGaugeSpace M n hn2 htb hns) = 0 := by
    rw [sub_smul, hpt, sub_self]
  -- Polynomial `1` is nonzero, so the scalar must be zero.
  rcases smul_eq_zero.mp hsub with hcc | hone
  · linarith
  · exact absurd hone one_ne_zero

/-- A scalar gauge is a projection gauge precisely when its scalar
satisfies `c² = c`. -/
theorem satDeciderGaugeScalingTransport_isProjectionGauge_iff_sq
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : ℚ) :
    GaugeMonotonicity.IsProjectionGauge
        (satDeciderGaugeScalingTransport M n hn2 htb hns c) ↔
      c * c = c := by
  constructor
  · intro hproj
    exact satDeciderGaugeScalingTransport_idempotent_forces_sq
      M n hn2 htb hns c hproj.idempotent
  · intro hsq
    refine ⟨?_⟩
    rw [satDeciderGaugeScalingTransport_comp]
    -- `(c*c) • id = c • id` because `c*c = c`.
    unfold satDeciderGaugeScalingTransport
    rw [hsq]

/-- Over `ℚ`, the equation `c² = c` admits only the two solutions
`c = 0` and `c = 1`. -/
theorem rat_sq_eq_self_iff (c : ℚ) : c * c = c ↔ c = 0 ∨ c = 1 := by
  constructor
  · intro h
    have h' : c * (c - 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp h' with hc | hcm1
    · exact Or.inl hc
    · right; linarith
  · rintro (rfl | rfl) <;> ring

/-- The scalar gauge is a projection gauge iff `c ∈ {0, 1}`. -/
theorem satDeciderGaugeScalingTransport_isProjectionGauge_iff
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : ℚ) :
    GaugeMonotonicity.IsProjectionGauge
        (satDeciderGaugeScalingTransport M n hn2 htb hns c) ↔
      c = 0 ∨ c = 1 := by
  rw [satDeciderGaugeScalingTransport_isProjectionGauge_iff_sq]
  exact rat_sq_eq_self_iff c

/-- **Closure theorem (collapse to identity-or-zero).**  Every
trivial-scaling candidate that is actually a projection gauge equals
either the identity gauge or the zero gauge. -/
theorem satDeciderGaugeScalingTransport_collapse
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : ℚ)
    (hproj : GaugeMonotonicity.IsProjectionGauge
        (satDeciderGaugeScalingTransport M n hn2 htb hns c)) :
    satDeciderGaugeScalingTransport M n hn2 htb hns c = LinearMap.id ∨
      satDeciderGaugeScalingTransport M n hn2 htb hns c = 0 := by
  have hcases :=
    (satDeciderGaugeScalingTransport_isProjectionGauge_iff
      M n hn2 htb hns c).mp hproj
  rcases hcases with h0 | h1
  · right
    rw [h0]
    exact satDeciderGaugeScalingTransport_zero_eq_zero M n hn2 htb hns
  · left
    rw [h1]
    exact satDeciderGaugeScalingTransport_one_eq_id M n hn2 htb hns

/-- The zero scaling gauge sends the compiled SAT-decider polynomial to
the zero polynomial.  This makes its multilinear blocked SPDP rank
identically zero, regardless of `(κ, ℓ)`. -/
theorem satDeciderGaugeScalingTransport_zero_compiled_zero
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeScalingTransport M n hn2 htb hns 0
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) = 0 := by
  rw [satDeciderGaugeScalingTransport_apply]
  simp

/-- Rank-monotonicity for the trivial-scaling gauge at the two
projection scalars `c ∈ {0, 1}`.  The `c = 1` case literally collapses
to the identity, matching `satDeciderGaugeUVTransport_isRankMonotoneGauge`,
and the `c = 0` case is rank-monotone because it sends every polynomial
to zero (rank `0`, which is `≤` everything). -/
theorem satDeciderGaugeScalingTransport_isRankMonotoneGauge_of_proj
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : ℚ) (hproj : c = 0 ∨ c = 1) :
    GaugeMonotonicity.IsRankMonotoneGauge
      (cook_levin_compilation M n hn2 htb hns).partition
      (satDeciderGaugeScalingTransport M n hn2 htb hns c) := by
  rcases hproj with h0 | h1
  · -- c = 0: the gauge is the zero map.
    intro κ ℓ p
    have happ : satDeciderGaugeScalingTransport M n hn2 htb hns c p = 0 := by
      rw [h0, satDeciderGaugeScalingTransport_apply]; simp
    rw [happ, MultilinearSPDP.mlBlockedSpdpRank_zero]
    exact Nat.zero_le _
  · -- c = 1: collapses to identity exactly as in UV transport.
    rw [h1]
    rw [satDeciderGaugeScalingTransport_one_eq_id]
    exact GaugeMonotonicity.IsRankMonotoneGauge.id _

/-- **Main negative result.**  Any trivial-scaling candidate Π⋆ that is
a projection gauge is *strictly* not richer than the identity: it is
either the identity itself (already covered by `SATDeciderGaugeUVTransport`)
or the zero map (which annihilates the compiled polynomial and hence
its rank).  In symbols, projection-gauge scalings live in the doubleton
`{LinearMap.id, 0}`. -/
theorem satDeciderGaugeScalingTransport_not_richer
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : ℚ)
    (hproj : GaugeMonotonicity.IsProjectionGauge
        (satDeciderGaugeScalingTransport M n hn2 htb hns c)) :
    satDeciderGaugeScalingTransport M n hn2 htb hns c ∈
      ({LinearMap.id, 0} :
        Set (SATDeciderGaugeMap M n hn2 htb hns)) := by
  rcases satDeciderGaugeScalingTransport_collapse M n hn2 htb hns c hproj
    with hid | hzero
  · exact Or.inl hid
  · exact Or.inr (by simpa using hzero)

/-! ## Axiom audit anchors -/

#print axioms satDeciderGaugeScalingTransport_apply
#print axioms satDeciderGaugeScalingTransport_comp
#print axioms satDeciderGaugeScalingTransport_one_eq_id
#print axioms satDeciderGaugeScalingTransport_zero_eq_zero
#print axioms satDeciderGaugeScalingTransport_idempotent_forces_sq
#print axioms satDeciderGaugeScalingTransport_isProjectionGauge_iff_sq
#print axioms rat_sq_eq_self_iff
#print axioms satDeciderGaugeScalingTransport_isProjectionGauge_iff
#print axioms satDeciderGaugeScalingTransport_collapse
#print axioms satDeciderGaugeScalingTransport_zero_compiled_zero
#print axioms satDeciderGaugeScalingTransport_isRankMonotoneGauge_of_proj
#print axioms satDeciderGaugeScalingTransport_not_richer

end PallLean.Paper93.DeepMath.PathB
