import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDegreeChar
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSPDPBridge

/-!
# The multilinearization `mlPoly`: closing the proxy → literal-`spdpRank` bridge at the function level

`…NFrameSPDPBridge` bounded `spdpRank` by *polynomial* degree.  This file lifts that to the *function* level by
constructing the literal multilinear `MvPolynomial` of a cube function and showing it both represents the function
and has the right degree:

* `mlPoly Q = ∑_S (Q S)·∏_{i∈S} Xᵢ` — the multilinear `MvPolynomial` with coefficient family `Q`;
* `mlPoly_eval` — it represents the function: `eval (boolToField∘x) (mlPoly Q) = Multilinear.eval Q x`;
* `mlPoly_totalDegree_le` — `Q` supported on `|S| ≤ D` ⇒ `(mlPoly Q).totalDegree ≤ D`.

Combined with `nframeComplexity_le_iff_exists_lowdeg` (proxy = minimal multilinear degree) and
`spdpRank_le_of_totalDegree_le` (degree caps SPDP rank), this gives the end-to-end safe-direction bridge:

  `nframeComplexity_le_imp_spdpRank_le` — `NFrameComplexity f ≤ D` ⇒ there is a multilinear `MvPolynomial p`
        representing `f` (`∀ x, f x = eval (boolToField∘x) p`) with
        `spdpRank κ ℓ p ≤ finrank(restrictTotalDegree (Fin n) F (ℓ + D))`.

So a function of low N-Frame complexity has a literal multilinear representative whose literal `SPDP.spdpRank` is
bounded — the proxy and the repo's actual SPDP object, joined at the function level.

## Honest scope

Still the **safe** half (low complexity ⇒ bounded SPDP rank).  The hard direction (an SPDP rank *lower* bound for an
explicit family) is the barriered A3 hard-survival, untouched.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameSPDPBridge

open MvPolynomial SPDP
open PallLean.Paper93.DeepMath.PathB.Layer4 (boolToField)
open PallLean.Paper93.DeepMath.PathB.NFrameACC0 (NFrameComplexity nframeComplexity_le_iff_exists_lowdeg)

variable {n : ℕ} {F : Type*} [Field F]

/-- The multilinear `MvPolynomial` with coefficient family `Q`: `∑_S (Q S)·∏_{i∈S} Xᵢ`. -/
noncomputable def mlPoly (Q : Finset (Fin n) → F) : MvPolynomial (Fin n) F :=
  ∑ S : Finset (Fin n), C (Q S) * ∏ i ∈ S, X i

/-- **`mlPoly Q` represents the multilinear function (proved).**  Evaluating at the Boolean point `boolToField∘x`
returns `Multilinear.eval Q x`. -/
theorem mlPoly_eval (Q : Finset (Fin n) → F) (x : Fin n → Bool) :
    eval (fun i => boolToField F (x i)) (mlPoly Q) = Multilinear.eval Q x := by
  rw [mlPoly, map_sum, Multilinear.eval]
  apply Finset.sum_congr rfl
  intro S _
  rw [map_mul, eval_C, map_prod]
  congr 1
  rw [Multilinear.monomialFn]
  apply Finset.prod_congr rfl
  intro i _
  rw [eval_X, boolToField]

/-- **`mlPoly` of a degree-`≤D` coefficient family has total degree `≤ D` (proved).** -/
theorem mlPoly_totalDegree_le {D : ℕ} (Q : Finset (Fin n) → F)
    (hQ : ∀ S, D < S.card → Q S = 0) : (mlPoly Q).totalDegree ≤ D := by
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le ?_)
  intro S _
  by_cases hS : S.card ≤ D
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_finset_prod _ _).trans ?_
    have : ∑ i ∈ S, (X i : MvPolynomial (Fin n) F).totalDegree = S.card := by
      simp [totalDegree_X]
    rw [this]
    exact hS
  · rw [hQ S (by omega), map_zero, zero_mul, totalDegree_zero]
    exact Nat.zero_le D

/-- **End-to-end safe bridge (proved).**  A function of N-Frame complexity `≤ D` has a literal multilinear
`MvPolynomial` representative whose literal `SPDP.spdpRank` is bounded by `finrank(restrictTotalDegree (ℓ+D))`. -/
theorem nframeComplexity_le_imp_spdpRank_le [Fintype F] [DecidableEq F] {D : ℕ} (κ ℓ : ℕ)
    (f : (Fin n → Bool) → F) (hf : NFrameComplexity F f ≤ D) :
    ∃ p : MvPolynomial (Fin n) F,
      (∀ x, f x = eval (fun i => boolToField F (x i)) p) ∧
      spdpRank κ ℓ p ≤ Module.finrank F (restrictTotalDegree (Fin n) F (ℓ + D)) := by
  obtain ⟨Q, hQ, hfQ⟩ := (nframeComplexity_le_iff_exists_lowdeg f D).mp hf
  refine ⟨mlPoly Q, ?_, spdpRank_le_of_totalDegree_le κ ℓ (mlPoly Q) (mlPoly_totalDegree_le Q hQ)⟩
  intro x
  rw [mlPoly_eval, ← hfQ]

end PallLean.Paper93.DeepMath.PathB.NFrameSPDPBridge

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSPDPBridge.nframeComplexity_le_imp_spdpRank_le
