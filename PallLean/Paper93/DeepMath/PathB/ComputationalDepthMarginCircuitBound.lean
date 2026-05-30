import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMarginFreeUPP
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSignApproxMargin
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthForsterUPP

/-!
# Circuit-level sign-rank bound from bottom margins (steps 2–3)

Cashing the margin-controlled sign approximation
(`SignApproxMargin.exists_sign_approx_margin_coeffs`) into the depth-2 circuit
bridge (`MarginFreeUPP.wholeCircuit_signRankBound_ofPolyApprox`):

  **bottom gates with margin `γ_k`  ⇒  degree `D_k ≈ 1/γ_k²` polynomial
  approximations  ⇒  weighted-approx realizers  ⇒  whole-circuit sign-rank
  bound `1 + ∑_k (D_k+1)²`**,

provided the total approximation error stays below the top-gate margin.

This is the circuit-level statement, with the margin dependence visible: the
per-gate transcript cost `(D_k+1)²` is governed by `D_k`, the degree from
`exists_sign_approx_margin` — which blows up as the bottom margin `γ_k → 0`.

Modulo `CentralBinomGF` (carried from `SignApproxMargin`).
-/

namespace PallLean.Paper93.DeepMath.PathB.MarginCircuit

open scoped BigOperators
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.MarginFreeUPP
open PallLean.Paper93.DeepMath.PathB.SignApproxMargin
open PallLean.Paper93.DeepMath.PathB.ForsterUnconditional
open PallLean.Paper93.DeepMath.PathB.ForsterUPP

variable {m n : ℕ}

/-- `sgn` of a bottom halfspace gate is the real sign of its argument. -/
theorem sgn_bottomGate (C : Depth2Threshold m n) (k : Fin C.s) (i : Fin m) (j : Fin n) :
    sgn (C.bottomGate k i j) = if 0 < C.α k i + C.β k j then (1 : ℝ) else -1 := by
  unfold Depth2Threshold.bottomGate bipartiteHalfspace
  by_cases h : 0 < C.α k i + C.β k j <;> simp [sgn, h]

/-- **Whole-circuit sign-rank bound from bottom margins (steps 2–3).**  If every
bottom `LTF` gate of `C` is normalised with margin `γ_k` (i.e.
`γ_k ≤ |α_k i + β_k j| ≤ 1`), and per-gate approximation errors `ε_k` are chosen so
their `w`-weighted total stays below the top-gate margin everywhere, then the
whole `THR∘LTF` circuit has sign rank `≤ 1 + ∑_k (D_k+1)²`, where `D_k` is the
degree from the margin approximation (so `D_k ≈ 1/γ_k²`).  The bound's dependence
on the margins is exactly this `D_k`. -/
theorem wholeCircuit_signRank_of_bottomMargin
    (C : Depth2Threshold m n) (hGF : CentralBinomGF)
    (γ ε' : Fin C.s → ℝ) (hγ0 : ∀ k, 0 < γ k) (hγ1 : ∀ k, γ k ≤ 1)
    (hε' : ∀ k, 0 < ε' k)
    (hbandlo : ∀ k i j, γ k ≤ |C.α k i + C.β k j|)
    (hbandhi : ∀ k i j, |C.α k i + C.β k j| ≤ 1)
    (htop : ∀ i j, (∑ k, |C.w k| * ε' k) < |Depth2Threshold.topArgument C i j|) :
    ∃ D : Fin C.s → ℕ,
      Depth2Threshold.WholeCircuitSignRankBound C
        (Fintype.card (Option (Σ k, Fin (D k + 1) × Fin (D k + 1)))) := by
  choose D a ha using fun k =>
    exists_sign_approx_margin_coeffs hGF (hγ0 k) (hγ1 k) (hε' k)
  refine ⟨D, ?_⟩
  -- per-gate weighted approximation in the bridge's `∑_b c_b (α+β)^b` form
  have happrox : ∀ k (i : Fin m) (j : Fin n),
      |(∑ b ∈ Finset.range (D k + 1), (C.w k * a k b) * (C.α k i + C.β k j) ^ b)
        - C.w k * sgn (C.bottomGate k i j)| ≤ |C.w k| * ε' k := by
    intro k i j
    have hfac : (∑ b ∈ Finset.range (D k + 1), (C.w k * a k b) * (C.α k i + C.β k j) ^ b)
        = C.w k * ∑ b ∈ Finset.range (D k + 1), a k b * (C.α k i + C.β k j) ^ b := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [hfac, sgn_bottomGate, ← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (ha k _ (hbandlo k i j) (hbandhi k i j)) (abs_nonneg _)
  -- assemble via the bridge; the top-margin hypothesis discharges the composition
  refine wholeCircuit_signRankBound_ofPolyApprox C D (fun k b => C.w k * a k b)
    (fun k => |C.w k| * ε' k) (fun k => mul_nonneg (abs_nonneg _) (le_of_lt (hε' k)))
    happrox (fun i j => ?_)
  exact htop i j

/-- The margin-realization cost is `1 + ∑_k (D_k+1)²`. -/
theorem card_cost {s : ℕ} (D : Fin s → ℕ) :
    Fintype.card (Option (Σ k, Fin (D k + 1) × Fin (D k + 1))) = 1 + ∑ k, (D k + 1) ^ 2 := by
  rw [Fintype.card_option, Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin, sq]
  rw [add_comm]

/-! ### (c) The margin-blowup no-go

The margin route's cost is bounded *below* by the sign-rank lower bound of the
function being computed.  So a high-sign-rank function cannot be a small-cost
margin-`THR∘LTF`: either the gate count or the approximation degrees (governed by
`1/γ_k`) must be large.  This makes the wall precise — and it is *not* a barrier:
it follows from the margin upper bound (`wholeCircuit_signRank_of_bottomMargin`)
meeting the Forster lower bound. -/

/-- **Margin cost ≥ Forster bound.**  If `C.eval` has Forster sign-rank lower
bound `B`, then any margin realization of `C` (with the usual band/top-margin
hypotheses) costs `1 + ∑_k (D_k+1)² ≥ B`.  Hard functions force large margin-degree. -/
theorem margin_cost_ge_forster
    (C : Depth2Threshold m n) (hGF : CentralBinomGF)
    (γ ε' : Fin C.s → ℝ) (hγ0 : ∀ k, 0 < γ k) (hγ1 : ∀ k, γ k ≤ 1) (hε' : ∀ k, 0 < ε' k)
    (hbandlo : ∀ k i j, γ k ≤ |C.α k i + C.β k j|)
    (hbandhi : ∀ k i j, |C.α k i + C.β k j| ≤ 1)
    (htop : ∀ i j, (∑ k, |C.w k| * ε' k) < |Depth2Threshold.topArgument C i j|)
    {B : ℕ} (hForster : ForsterLowerBound C.eval B) :
    ∃ D : Fin C.s → ℕ, B ≤ 1 + ∑ k, (D k + 1) ^ 2 := by
  obtain ⟨D, hbound⟩ :=
    wholeCircuit_signRank_of_bottomMargin C hGF γ ε' hγ0 hγ1 hε' hbandlo hbandhi htop
  exact ⟨D, by rw [← card_cost D]; exact hForster _ hbound⟩

/-- **Walsh margin-blowup (concrete).**  Any `THR∘LTF` circuit whose evaluation is
the `2^{2j} × 2^{2j}` Walsh–Hadamard matrix, realized with bottom margins and a
top margin, must have `1 + ∑_k (D_k+1)² ≥ 2^j`.  Since `D_k ≈ 1/γ_k²`, computing
Walsh forces exponentially many gates *or* exponentially small margins — the
quantitative wall, concrete. -/
theorem walsh_margin_blowup {m' j : ℕ} (hmk : m' + 1 = 2 ^ (2 * j))
    (C : Depth2Threshold (m' + 1) (m' + 1)) (hCeval : C.eval = walshMatrix hmk)
    (hGF : CentralBinomGF)
    (γ ε' : Fin C.s → ℝ) (hγ0 : ∀ k, 0 < γ k) (hγ1 : ∀ k, γ k ≤ 1) (hε' : ∀ k, 0 < ε' k)
    (hbandlo : ∀ k i j, γ k ≤ |C.α k i + C.β k j|)
    (hbandhi : ∀ k i j, |C.α k i + C.β k j| ≤ 1)
    (htop : ∀ i j, (∑ k, |C.w k| * ε' k) < |Depth2Threshold.topArgument C i j|) :
    ∃ D : Fin C.s → ℕ, 2 ^ j ≤ 1 + ∑ k, (D k + 1) ^ 2 := by
  have hForster : ForsterLowerBound C.eval (2 ^ j) := by
    rw [hCeval]; exact walsh_forsterLowerBound hmk
  exact margin_cost_ge_forster C hGF γ ε' hγ0 hγ1 hε' hbandlo hbandhi htop hForster

end PallLean.Paper93.DeepMath.PathB.MarginCircuit

#print axioms PallLean.Paper93.DeepMath.PathB.MarginCircuit.wholeCircuit_signRank_of_bottomMargin
#print axioms PallLean.Paper93.DeepMath.PathB.MarginCircuit.margin_cost_ge_forster
#print axioms PallLean.Paper93.DeepMath.PathB.MarginCircuit.walsh_margin_blowup
