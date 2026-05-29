import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUPPBridge
import Mathlib.Data.Nat.Choose.Sum

/-!
# Toward the margin-free UPP protocol: polynomial approximation ⇒ cheap bottom realizer

The composition theorem `wholeCircuitUPPRealizer_of_weightedApproxBottomOutputs`
(in `ComputationalDepthUPPBridge.lean`) already turns *cheap, error-controlled*
`WeightedApproxBottomRealizer`s for the bottom `LTF` gates into a whole-circuit
realizer — provided the total error beats the top margin.  The missing piece (the
genuine open "margin-free UPP protocol" step) is producing those cheap bottom
realizers.

This file builds the **algebraic core** of that step, isolating the remaining
analytic input cleanly:

* `weightedApproxRealizer_ofPolyApprox` — *any* degree-`d` polynomial that
  approximates the weighted bottom sign `w_k · sgn⟨α_k,β_k⟩` to error `ε`
  yields a `WeightedApproxBottomRealizer` of cost `(d+1)²`.  The construction is
  the binomial expansion `(α_i+β_j)^b = ∑_a C(b,a) α_i^a β_j^{b-a}`, which makes
  a degree-`d` polynomial in `α_i+β_j` a rank-`≤(d+1)²` bipartite transcript
  matrix.

Consequently the **entire** cheap-protocol question reduces to a single analytic
statement: *does the sign function admit a low-degree polynomial approximation,
to small `ε`, on the range of `α_i+β_j`?*  With a bottom-gate margin `γ`
(`|α_i+β_j| ≥ γ`) this is the classical Chebyshev approximation of `sign`, with
degree `O((1/γ) log(1/ε))` — but for a *general* circuit the margins can be
exponentially small, which is exactly why the route is hard.  This file does NOT
assert the analytic bound; it proves the reduction, so the open input is now a
precise, self-contained lemma rather than a vague "protocol".
-/

namespace PallLean.Paper93.DeepMath.PathB.MarginFreeUPP

open scoped BigOperators
open PallLean.Paper93.DeepMath.PathB

variable {m n : ℕ}

/-- **Binomial identity, range-extended.**  For `b ≤ d`, summing the binomial
terms over the full `range (d+1)` (the extra terms vanish since `C(b,a) = 0` for
`a > b`) recovers `(x+y)^b`. -/
lemma choose_sum_eq_add_pow (x y : ℝ) {b d : ℕ} (hbd : b ≤ d) :
    (∑ a ∈ Finset.range (d + 1), (b.choose a : ℝ) * x ^ a * y ^ (b - a)) = (x + y) ^ b := by
  have hsub : Finset.range (b + 1) ⊆ Finset.range (d + 1) := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.succ_le_succ hbd))
  rw [← Finset.sum_subset hsub (fun a _ ha => by
        rw [Finset.mem_range, not_lt] at ha
        rw [Nat.choose_eq_zero_of_lt (by omega)]; simp), add_pow]
  exact Finset.sum_congr rfl (fun a _ => by ring)

/-- **Polynomial approximation ⇒ weighted-approx bottom realizer.**  If the
degree-`d` polynomial with coefficients `c` approximates the weighted bottom sign
`w_k · sgn(bottomGate k i j)` to error `ε` at every input, then the bottom gate
has a `WeightedApproxBottomRealizer` indexed by `Fin (d+1) × Fin (d+1)` — i.e. of
transcript cost `(d+1)²`.

The realizer is the binomial expansion of the polynomial in `α_i + β_j`:
`alice (a,b) i = c_b · C(b,a) · α_i^a`, `bob (a,b) j = β_j^{b-a}`, so
`∑_{(a,b)} alice·bob = ∑_b c_b (α_i+β_j)^b`. -/
noncomputable def weightedApproxRealizer_ofPolyApprox (C : Depth2Threshold m n) (k : Fin C.s)
    (d : ℕ) (c : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (happrox : ∀ i j,
      |(∑ b ∈ Finset.range (d + 1), c b * (C.α k i + C.β k j) ^ b)
        - C.w k * sgn (C.bottomGate k i j)| ≤ ε) :
    WeightedApproxBottomRealizer C k (Fin (d + 1) × Fin (d + 1)) where
  alice p i := c (p.2 : ℕ) * ((p.2 : ℕ).choose (p.1 : ℕ) : ℝ) * (C.α k i) ^ (p.1 : ℕ)
  bob p j := (C.β k j) ^ ((p.2 : ℕ) - (p.1 : ℕ))
  ε := ε
  eps_nonneg := hε
  approx := by
    intro i j
    have hkey :
        (∑ p : Fin (d + 1) × Fin (d + 1),
            (c (p.2 : ℕ) * ((p.2 : ℕ).choose (p.1 : ℕ) : ℝ) * (C.α k i) ^ (p.1 : ℕ))
              * (C.β k j) ^ ((p.2 : ℕ) - (p.1 : ℕ)))
          = ∑ b ∈ Finset.range (d + 1), c b * (C.α k i + C.β k j) ^ b := by
      rw [Fintype.sum_prod_type_right]
      rw [Fin.sum_univ_eq_sum_range
        (fun b => ∑ a : Fin (d + 1),
          (c b * ((b : ℕ).choose a : ℝ) * (C.α k i) ^ (a : ℕ)) * (C.β k j) ^ ((b : ℕ) - a)) (d + 1)]
      refine Finset.sum_congr rfl (fun b hb => ?_)
      rw [Finset.mem_range] at hb
      rw [Fin.sum_univ_eq_sum_range
        (fun a => (c b * ((b : ℕ).choose a : ℝ) * (C.α k i) ^ a) * (C.β k j) ^ (b - a)) (d + 1)]
      rw [Finset.sum_congr rfl (fun a _ =>
        show (c b * ((b : ℕ).choose a : ℝ) * (C.α k i) ^ a) * (C.β k j) ^ (b - a)
          = c b * (((b : ℕ).choose a : ℝ) * (C.α k i) ^ a * (C.β k j) ^ (b - a)) by ring)]
      rw [← Finset.mul_sum, choose_sum_eq_add_pow (C.α k i) (C.β k j) (by omega : b ≤ d)]
    rw [hkey]
    exact happrox i j

/-- **The reduction, made precise.**  Suppose every bottom gate admits a
degree-`d` polynomial approximation of its weighted sign to error `ε k`, and the
total error `∑ ε k` is strictly below the top-gate margin everywhere.  Then the
whole `THR∘LTF` circuit has a transcript realizer of cost
`1 + ∑_k (d_k+1)²` — hence `WholeCircuitSignRankBound`.

This packages the algebraic core: the only remaining (open, analytic) inputs are
the per-gate polynomial approximations and the global margin condition. -/
theorem wholeCircuit_signRankBound_ofPolyApprox (C : Depth2Threshold m n)
    (d : Fin C.s → ℕ) (c : Fin C.s → ℕ → ℝ) (ε : Fin C.s → ℝ)
    (hε : ∀ k, 0 ≤ ε k)
    (happrox : ∀ k i j,
      |(∑ b ∈ Finset.range (d k + 1), c k b * (C.α k i + C.β k j) ^ b)
        - C.w k * sgn (C.bottomGate k i j)| ≤ ε k)
    (hmargin : ∀ i j,
      Depth2Threshold.weightedApproxError C
        (fun k => weightedApproxRealizer_ofPolyApprox C k (d k) (c k) (ε k) (hε k) (happrox k))
        < |Depth2Threshold.topArgument C i j|) :
    Depth2Threshold.WholeCircuitSignRankBound C
      (Fintype.card (Option (Σ k, Fin (d k + 1) × Fin (d k + 1)))) :=
  hasSignRankLE_of_uppTranscriptRealizer
    (Depth2Threshold.wholeCircuitUPPRealizer_of_weightedApproxBottomOutputs C
      (fun k => weightedApproxRealizer_ofPolyApprox C k (d k) (c k) (ε k) (hε k) (happrox k))
      hmargin)

end PallLean.Paper93.DeepMath.PathB.MarginFreeUPP

#print axioms PallLean.Paper93.DeepMath.PathB.MarginFreeUPP.choose_sum_eq_add_pow
#print axioms PallLean.Paper93.DeepMath.PathB.MarginFreeUPP.weightedApproxRealizer_ofPolyApprox
#print axioms PallLean.Paper93.DeepMath.PathB.MarginFreeUPP.wholeCircuit_signRankBound_ofPolyApprox
