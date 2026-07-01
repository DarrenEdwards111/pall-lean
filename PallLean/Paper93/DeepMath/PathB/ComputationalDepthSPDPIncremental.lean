import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSPDPDynamic

/-!
# Dynamic SPDP, candidate 2: per-step incremental rank also fails (proved)

Continuing the honest exploration of a dynamic SPDP invariant (`…SPDPDynamic` proved the "max rank across states"
candidate fails).  Here the candidate cost is the **per-step incremental rank**: for a trace of polynomials
`p 0, p 1, …, p T`, the increments `spdpRank(p (k+1)) − spdpRank(p k)`.

The sum of increments **telescopes** to the final minus initial rank, so it inherits `∏Xᵢ`'s exponential rank:

  `incrementalSum_ge` — `spdpRank(p T) − spdpRank(p 0) ≤ incrementalSum κ T p` (telescoping inequality, always).
  `spdpRank_one_eq_zero` — `spdpRank κ 0 (1) = 0` for `κ ≥ 1` (derivatives of a constant vanish).
  `fullProd_incrementalSum_ge` — any trace from `1` to `∏ᵢ Xᵢ` has `incrementalSum ≥ C(n, κ)` (exponential at `κ=n/2`).

The only escape is to make each increment small — but then the trace must be **exponentially long**:

  `fullProd_length_mul_maxInc_ge` — if every per-step increment is `≤ B`, then `T · B ≥ C(n, κ)`.  So a trace of
        `∏ᵢ Xᵢ` with polynomially-bounded per-step increments must have super-polynomial length.

**Conclusion.** Per-step incremental rank fails for the same fundamental reason as max-rank: the exponential final
`spdpRank` of `∏Xᵢ` must be *generated*, and generation = sum of increments = final − initial.  No rank-accumulation
measure (max, sum, or bounded-increment) escapes this; a useful dynamic SPDP for ACC must measure something that is
**not** the accumulated derivative-span rank at all (trace length alone = circuit size, which does not track hardness;
a genuinely different *restricted/transfer* rank is the open design problem).  This is a second proved no-go pinning
down the obstruction.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

open MvPolynomial SPDP Module

variable {n : ℕ} {F : Type*} [Field F]

-- spdpRank of the constant 1 is 0 for κ ≥ 1
theorem iterDerivList_one_of_ne_nil : ∀ (S : List (Fin n)), S ≠ [] →
    iterDerivList S (1 : MvPolynomial (Fin n) F) = 0
  | [], h => absurd rfl h
  | k :: rest, _ => by
    show iterDerivList rest (pderiv k 1) = 0
    rw [pderiv_one, iterDerivList_zero]
theorem spdpSubspace_one_eq_bot (κ : ℕ) (hκ : 1 ≤ κ) :
    spdpSubspace κ 0 (1 : MvPolynomial (Fin n) F) = ⊥ := by
  rw [spdpSubspace, Submodule.span_eq_bot]
  rintro _ ⟨S, m, hSlen, hmdeg, rfl⟩
  have hne : S ≠ [] := by intro h; simp only [h, List.length_nil] at hSlen; omega
  rw [iterDerivList_one_of_ne_nil S hne, mul_zero]
theorem spdpRank_one_eq_zero (κ : ℕ) (hκ : 1 ≤ κ) :
    spdpRank κ 0 (1 : MvPolynomial (Fin n) F) = 0 := by
  unfold spdpRank; rw [spdpSubspace_one_eq_bot κ hκ, finrank_bot]
-- telescoping: sum of per-step increments ≥ final - initial
noncomputable def incrementalSum (κ T : ℕ) (p : ℕ → MvPolynomial (Fin n) F) : ℕ :=
  ∑ k ∈ Finset.range T, (spdpRank κ 0 (p (k+1)) - spdpRank κ 0 (p k))
theorem incrementalSum_ge (κ T : ℕ) (p : ℕ → MvPolynomial (Fin n) F) :
    spdpRank κ 0 (p T) - spdpRank κ 0 (p 0) ≤ incrementalSum κ T p := by
  unfold incrementalSum
  induction T with
  | zero => simp
  | succ T ih => rw [Finset.sum_range_succ]; omega
-- the no-go for incremental-sum on ∏Xᵢ
theorem fullProd_incrementalSum_ge (κ : ℕ) (hκ : 1 ≤ κ) (T : ℕ) (p : ℕ → MvPolynomial (Fin n) F)
    (h0 : p 0 = 1) (hT : p T = fullProd) : n.choose κ ≤ incrementalSum κ T p := by
  have hge := incrementalSum_ge κ T p
  rw [h0, hT, spdpRank_one_eq_zero κ hκ, Nat.sub_zero] at hge
  exact le_trans (spdpRank_fullProd_choose_ge κ) hge

theorem fullProd_length_mul_maxInc_ge (κ : ℕ) (hκ : 1 ≤ κ) (T : ℕ)
    (p : ℕ → MvPolynomial (Fin n) F) (h0 : p 0 = 1) (hT : p T = fullProd) (B : ℕ)
    (hB : ∀ k < T, spdpRank κ 0 (p (k+1)) - spdpRank κ 0 (p k) ≤ B) :
    n.choose κ ≤ T * B := by
  have hsum : incrementalSum κ T p ≤ T * B := by
    unfold incrementalSum
    calc ∑ k ∈ Finset.range T, (spdpRank κ 0 (p (k+1)) - spdpRank κ 0 (p k))
        ≤ ∑ _k ∈ Finset.range T, B :=
          Finset.sum_le_sum (fun k hk => hB k (Finset.mem_range.mp hk))
      _ = T * B := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  exact le_trans (fullProd_incrementalSum_ge κ hκ T p h0 hT) hsum


end PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.fullProd_incrementalSum_ge
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.fullProd_length_mul_maxInc_ge
