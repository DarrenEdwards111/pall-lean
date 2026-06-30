import PallLean.SPDPDefs

/-!
# Degree caps the literal SPDP rank: connecting `NFrameComplexity` to `SPDP.spdpRank` (safe direction)

`…NFrameDegreeChar` pinned the N-Frame proxy: `NFrameComplexity f` is exactly the minimal degree of a multilinear
polynomial representing `f`.  This file connects that **degree** invariant to the repo's literal **`SPDP.spdpRank`**
(`= finrank(span{ m·∂_S p : |S|=κ, deg m ≤ ℓ })`) in the non-barriered direction:

  `spdpRank_le_of_totalDegree_le` — if `p.totalDegree ≤ D` then
        `spdpRank κ ℓ p ≤ finrank(restrictTotalDegree (Fin n) F (ℓ + D))`.

So **low degree caps the SPDP rank**: a degree-`≤D` polynomial's SPDP subspace lives inside the (finite-dimensional)
space of degree-`≤ ℓ+D` polynomials, because each generator `m·∂_S p` has degree `≤ deg m + deg(∂_S p) ≤ ℓ + D`
(differentiation never raises degree).  Composed with `nframeComplexity_le_iff_exists_lowdeg` (the proxy = minimal
multilinear degree), this is the genuine link **`NFrameComplexity f ≤ D ⟹ spdpRank` of any degree-`≤D` multilinear
representative of `f` is bounded** — the two literal invariants, connected.

## Honest scope

This is the **safe** half of the bridge: low degree *upper-bounds* the SPDP rank.  The hard direction — a *lower*
bound on SPDP rank for an explicit family (`A3` hard-survival, the genuine SPDP rank lower bound) — is barriered
short of `P/poly` per the repo's own `…SPDPFeatureProjection` / `…NFrameHypercubeConstraint` docstrings, and is not
touched here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameSPDPBridge

open MvPolynomial SPDP

variable {n : ℕ} {F : Type*}

/-- The degree (sum of exponents) does not increase under truncated subtraction of a single exponent. -/
theorem degSub_le (s : Fin n →₀ ℕ) (i : Fin n) :
    (s - Finsupp.single i 1).sum (fun _ e => e) ≤ s.sum (fun _ e => e) := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.sum_fintype _ _ (fun _ => rfl)]
  exact Finset.sum_le_sum (fun a _ => by rw [Finsupp.tsub_apply]; exact tsub_le_self)

/-- **Differentiation does not raise total degree (proved).**  `totalDegree (∂_i p) ≤ totalDegree p` — the
matrix-calculus fact underlying the SPDP-from-degree bound. -/
theorem pderiv_totalDegree_le [CommRing F] (i : Fin n) (p : MvPolynomial (Fin n) F) :
    (pderiv i p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le ?_)
  intro s hs
  rw [pderiv_monomial]
  exact (totalDegree_monomial_le _ _).trans ((degSub_le s i).trans (MvPolynomial.le_totalDegree hs))

/-- **Iterated differentiation does not raise total degree (proved).** -/
theorem iterDerivList_totalDegree_le [CommRing F] (indices : List (Fin n))
    (p : MvPolynomial (Fin n) F) : (iterDerivList indices p).totalDegree ≤ p.totalDegree := by
  unfold iterDerivList
  induction indices generalizing p with
  | nil => simp
  | cons i is ih =>
    simp only [List.foldl_cons]
    exact (ih (pderiv i p)).trans (pderiv_totalDegree_le i p)

/-- `restrictTotalDegree` is monotone in the degree bound. -/
theorem restrictTotalDegree_mono [CommRing F] {a b : ℕ} (h : a ≤ b) :
    restrictTotalDegree (Fin n) F a ≤ restrictTotalDegree (Fin n) F b := by
  intro p hp
  rw [mem_restrictTotalDegree] at hp ⊢
  exact hp.trans h

/-- **The SPDP subspace of a polynomial lives in bounded-degree polynomials (proved).**  Every generator
`m·∂_S p` has degree `≤ deg m + deg(∂_S p) ≤ ℓ + totalDegree p`. -/
theorem spdpSubspace_le_restrictTotalDegree [CommRing F] (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    spdpSubspace κ ℓ p ≤ restrictTotalDegree (Fin n) F (ℓ + p.totalDegree) := by
  rw [spdpSubspace, Submodule.span_le]
  rintro q ⟨S, m, _, hmdeg, rfl⟩
  rw [SetLike.mem_coe, mem_restrictTotalDegree]
  calc (m * iterDerivList S p).totalDegree
      ≤ m.totalDegree + (iterDerivList S p).totalDegree := totalDegree_mul m _
    _ ≤ ℓ + p.totalDegree := Nat.add_le_add hmdeg (iterDerivList_totalDegree_le S p)

/-- **Low degree caps the literal SPDP rank (proved).**  If `p.totalDegree ≤ D` then
`spdpRank κ ℓ p ≤ finrank(restrictTotalDegree (Fin n) F (ℓ + D))` — the safe-direction bridge from the degree
invariant (`= NFrameComplexity`) to `SPDP.spdpRank`. -/
theorem spdpRank_le_of_totalDegree_le [Field F] {D : ℕ} (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F) (hp : p.totalDegree ≤ D) :
    spdpRank κ ℓ p ≤ Module.finrank F (restrictTotalDegree (Fin n) F (ℓ + D)) := by
  have hle : spdpSubspace κ ℓ p ≤ restrictTotalDegree (Fin n) F (ℓ + D) :=
    le_trans (spdpSubspace_le_restrictTotalDegree κ ℓ p)
      (restrictTotalDegree_mono (Nat.add_le_add_left hp ℓ))
  exact Submodule.finrank_mono hle

end PallLean.Paper93.DeepMath.PathB.NFrameSPDPBridge

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSPDPBridge.spdpRank_le_of_totalDegree_le
