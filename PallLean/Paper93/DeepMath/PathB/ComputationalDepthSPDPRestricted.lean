import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSPDPFullProdLB

/-!
# Restricted rank separates `∏Xᵢ` from `MOD_q` (where raw rank cannot)

Raw `SPDP.spdpRank` is exponential for BOTH `∏Xᵢ` and `MOD_q`, so it cannot tell them apart.  The reason `MOD_q` looks
identical is structural: its multilinear polynomial is itself a **product** — of *affine* forms:

  `MOD_q`'s polynomial `= ∏ᵢ (1 + (ω-1)·Xᵢ)`   (because `ω^{xᵢ} = 1 + (ω-1)xᵢ` on `{0,1}`).

But the two products differ under **restriction** (fixing variables to `0/1`):

  `fullProd_restrict_zero` — fixing one variable to `0` makes `∏ᵢ Xᵢ = 0` (the factor `Xⱼ` vanishes).  So its
        restricted rank can drop to `0` — `∏Xᵢ` is *fragile*.
  `modqPoly_restrict_ne_zero` — no `0/1` restriction makes `∏ᵢ(1 + c·Xᵢ)` zero (each affine factor evaluates to
        `1` or `1+c = ω`, both nonzero for `1+c ≠ 0`).  So `MOD_q` is never trivialised — it is *robust*.

So a **restriction-based** rank distinguishes the fragile `∏Xᵢ` (restricted rank `→ 0`) from the robust `MOD_q`
(restricted polynomial always nonzero), exactly where raw rank fails.  This is the qualitative reason restriction is
the right refinement — restriction-robustness of a nonvanishing-product structure is precisely why `MOD_q` is hard for
`AC⁰` (the switching-lemma intuition), captured algebraically.

## Honest scope

This is the **qualitative** separation (`∏Xᵢ` killable, `MOD_q` not).  The **quantitative** version — `MOD_q`'s
restricted rank stays *high* (`≥ C(n-B, κ)` under `≤ B` restrictions) — needs a `spdpRank` lower bound for the affine
product `∏(1+cXᵢ)` (a triangular / affine-automorphism argument, feasible and NOT barriered, mirroring
`spdpRank_fullProd_choose_ge`).  Whether restriction-robust rank is low for *all* of `ACC⁰` is the open barrier.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

open MvPolynomial SPDP

variable {n : ℕ} {F : Type*} [Field F]

-- MOD_q's multilinear polynomial: a product of affine forms
noncomputable def modqPoly (c : F) : MvPolynomial (Fin n) F := ∏ i : Fin n, (1 + C c * X i)
-- restriction: fix some variables to 0/1, leave others free
noncomputable def restrictPoly (r : Fin n → Option Bool) (p : MvPolynomial (Fin n) F) :
    MvPolynomial (Fin n) F :=
  aeval (fun i => (r i).elim (X i) (fun b => C (if b then (1 : F) else 0))) p
-- ∏Xᵢ is KILLABLE: fixing one variable to 0 makes it 0
theorem fullProd_restrict_zero (j : Fin n) :
    restrictPoly (fun i => if i = j then some false else none) (fullProd : MvPolynomial (Fin n) F) = 0 := by
  unfold restrictPoly fullProd
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp
-- MOD_q is UNKILLABLE: no 0/1 restriction makes it 0
theorem modqPoly_restrict_ne_zero (c : F) (hc1 : (1 : F) + c ≠ 0)
    (r : Fin n → Option Bool) : restrictPoly r (modqPoly c) ≠ 0 := by
  unfold restrictPoly modqPoly
  rw [map_prod, Finset.prod_ne_zero_iff]
  intro i _ h
  have h0 := congrArg (eval (fun _ => (0 : F))) h
  rw [map_zero] at h0
  rcases hri : r i with _ | b
  · simp [hri] at h0
  · cases b <;> simp [hri, hc1] at h0

end PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.fullProd_restrict_zero
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.modqPoly_restrict_ne_zero
