import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMarginCircuitBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCentralBinomGF

/-!
# Unconditional headline theorems (caveat removed)

With `CentralBinomGF` now a theorem (`CentralBinomGFProof.centralBinomGF`), the
margin arc is fully unconditional.  This file restates the headline results with
no carried hypothesis, by discharging `hGF := centralBinomGF`.  All depend only on
`[propext, Classical.choice, Quot.sound]`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MarginUnconditional

open scoped BigOperators
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ForsterUnconditional

/-- **Unconditional** margin-controlled sign approximation. -/
theorem exists_sign_approx_margin {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ z : ℝ, γ ≤ |z| → |z| ≤ 1 →
      |z * (∑ i ∈ Finset.range (N + 1), (Nat.centralBinom i / 4 ^ i : ℝ) * (1 - z ^ 2) ^ i)
          - (if 0 < z then (1 : ℝ) else -1)| ≤ ε :=
  SignApproxMargin.exists_sign_approx_margin CentralBinomGFProof.centralBinomGF hγ0 hγ1 hε

/-- **Unconditional** whole-circuit sign-rank bound from bottom margins. -/
theorem wholeCircuit_signRank_of_bottomMargin {m n : ℕ}
    (C : Depth2Threshold m n)
    (γ ε' : Fin C.s → ℝ) (hγ0 : ∀ k, 0 < γ k) (hγ1 : ∀ k, γ k ≤ 1) (hε' : ∀ k, 0 < ε' k)
    (hbandlo : ∀ k i j, γ k ≤ |C.α k i + C.β k j|)
    (hbandhi : ∀ k i j, |C.α k i + C.β k j| ≤ 1)
    (htop : ∀ i j, (∑ k, |C.w k| * ε' k) < |Depth2Threshold.topArgument C i j|) :
    ∃ D : Fin C.s → ℕ,
      Depth2Threshold.WholeCircuitSignRankBound C
        (Fintype.card (Option (Σ k, Fin (D k + 1) × Fin (D k + 1)))) :=
  MarginCircuit.wholeCircuit_signRank_of_bottomMargin C CentralBinomGFProof.centralBinomGF
    γ ε' hγ0 hγ1 hε' hbandlo hbandhi htop

/-- **Unconditional** Walsh size–margin tradeoff: any `THR∘LTF` computing the
`2^{2j}` Walsh matrix with margins has `2^j ≤ 1 + s·(Δ+1)²` (`s` = #gates,
`Δ = max_k D_k`).  No carried hypothesis. -/
theorem walsh_gates_degree_tradeoff {m' j : ℕ} (hmk : m' + 1 = 2 ^ (2 * j))
    (C : Depth2Threshold (m' + 1) (m' + 1)) (hCeval : C.eval = walshMatrix hmk)
    (γ ε' : Fin C.s → ℝ) (hγ0 : ∀ k, 0 < γ k) (hγ1 : ∀ k, γ k ≤ 1) (hε' : ∀ k, 0 < ε' k)
    (hbandlo : ∀ k i j, γ k ≤ |C.α k i + C.β k j|)
    (hbandhi : ∀ k i j, |C.α k i + C.β k j| ≤ 1)
    (htop : ∀ i j, (∑ k, |C.w k| * ε' k) < |Depth2Threshold.topArgument C i j|) :
    ∃ D : Fin C.s → ℕ,
      2 ^ j ≤ 1 + Fintype.card (Fin C.s) * (Finset.univ.sup D + 1) ^ 2 :=
  MarginCircuit.walsh_gates_degree_tradeoff hmk C hCeval CentralBinomGFProof.centralBinomGF
    γ ε' hγ0 hγ1 hε' hbandlo hbandhi htop

end PallLean.Paper93.DeepMath.PathB.MarginUnconditional

#print axioms PallLean.Paper93.DeepMath.PathB.MarginUnconditional.walsh_gates_degree_tradeoff
#print axioms PallLean.Paper93.DeepMath.PathB.MarginUnconditional.exists_sign_approx_margin
