import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDimensionFullRank

/-!
# A charged tensor model and a restricted entanglement lower bound

This is the productive, non-socket version of the black-hole/MERA route.  The admissibility audit
(`ComputationalDepthBlackHoleMERAAdmissibilityAudit`) showed the fatal flaw of the uncharged model: the encoder can
oracle-load the answer bit, so exactness+isometry force *nothing*.  The measure that is immune to that flaw is the
**entanglement (bond dimension / Schmidt rank) across a fixed cut**, because the cross-cut rank of a function is an
*intrinsic* property — you cannot precompute it away.

A bond-`χ` tensor factorization of `f` across a cut `S` is a Schmidt/MPS decomposition
`f(x) = Σ_{a<χ} left_a(x|_S) · right_a(x|_Sᶜ)` — `χ` is the bond dimension crossing the cut.  We prove:

* `finrank_residualSpan_le_bond` — a bond-`χ` factorization forces `χ ≥ dim(residual span) = ` the cross-cut rank;
* `eqFun_tensor_bond_ge` — the **equality** function (a structured family, the canonical maximally-entangled
  function) requires bond dimension `χ ≥ 2^k` across its block cut — **exponential** in the block length.

The equality residuals are the standard basis (`DimensionFullRank.eqFun_dim_ge`), so the cross-cut rank is full
(`2^k`), and no bond-`χ` tensor with `χ < 2^k` can represent it.  This is exactly what the oracle-loading flaw
*cannot* defeat: bond `1` would mean the function is a product across the cut, but equality has rank `2^k`.

## Honest scope

A restricted lower bound: a *fixed* family (equality) at a *fixed* cut requires exponential bond dimension in a
tensor-network model.  No representation-invariance ("every encoding"), so no collapse and no machine-completeness
gap — and correspondingly, no separation.  A genuine tensor-network entanglement bound, presented as such.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TensorEntanglement

open PallLean.Paper93.DeepMath.PathB.DimensionFullRank

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The residual (subfunction) of `f` on the free block `S` at outside setting `α`. -/
def residualOf (S : Finset ι) (f : (ι → Bool) → K) (α : ι → Bool) : (ι → Bool) → K :=
  fun x => f (fun i => if i ∈ S then x i else α i)

/-- A **bond-`χ` tensor factorization** of `f` across the cut `S`: a Schmidt/MPS decomposition
`f(x) = Σ_{a<χ} left_a(x|_S) · right_a(x|_Sᶜ)` with `χ` the bond dimension crossing the cut.  `left_indep`/
`right_indep` pin the halves to their sides of the cut. -/
structure TensorFactorization (S : Finset ι) (f : (ι → Bool) → K) (χ : ℕ) where
  /-- Left tensors (the `S`-side legs). -/
  left : Fin χ → (ι → Bool) → K
  /-- Right tensors (the `Sᶜ`-side legs). -/
  right : Fin χ → (ι → Bool) → K
  /-- Each left leg depends only on the `S`-variables. -/
  left_indep : ∀ (a : Fin χ) (x y : ι → Bool), (∀ i ∈ S, x i = y i) → left a x = left a y
  /-- Each right leg depends only on the `Sᶜ`-variables. -/
  right_indep : ∀ (a : Fin χ) (x y : ι → Bool), (∀ i, i ∉ S → x i = y i) → right a x = right a y
  /-- The tensors contract to `f`. -/
  factors : ∀ x, f x = ∑ a, left a x * right a x

variable {S : Finset ι} {f : (ι → Bool) → K} {χ : ℕ}

/-- Each residual is a linear combination of the left legs: `res_α = Σ_a right_a(α) • left_a`. -/
theorem residualOf_eq_sum (T : TensorFactorization S f χ) (α : ι → Bool) :
    residualOf S f α = ∑ a, (T.right a α) • T.left a := by
  funext x
  simp only [residualOf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [T.factors]
  apply Finset.sum_congr rfl
  intro a _
  rw [T.left_indep a (fun i => if i ∈ S then x i else α i) x (fun i hi => if_pos hi),
    T.right_indep a (fun i => if i ∈ S then x i else α i) α (fun i hi => if_neg hi), mul_comm]

/-- Hence every residual lies in the span of the `χ` left legs. -/
theorem residualOf_mem_span (T : TensorFactorization S f χ) (α : ι → Bool) :
    residualOf S f α ∈ Submodule.span K (Set.range T.left) := by
  rw [residualOf_eq_sum T]
  exact Submodule.sum_mem _
    (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

/-- **Bond dimension lower-bounds the cross-cut rank.**  A bond-`χ` factorization forces the residual-span
dimension (the Schmidt rank across the cut) to be at most `χ`. -/
theorem finrank_residualSpan_le_bond (T : TensorFactorization S f χ) :
    Module.finrank K (Submodule.span K (Set.range (residualOf S f))) ≤ χ := by
  classical
  haveI : FiniteDimensional K ((ι → Bool) → K) := inferInstance
  have hsub : Submodule.span K (Set.range (residualOf S f))
      ≤ Submodule.span K (Set.range T.left) := by
    rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    exact residualOf_mem_span T α
  have hle : Module.finrank K (Submodule.span K (Set.range T.left)) ≤ χ := by
    have h1 := finrank_span_le_card (R := K) (Set.range T.left)
    rw [Set.toFinset_range] at h1
    calc Module.finrank K (Submodule.span K (Set.range T.left))
        ≤ (Finset.univ.image T.left).card := h1
      _ ≤ (Finset.univ : Finset (Fin χ)).card := Finset.card_image_le
      _ = χ := by rw [Finset.card_univ, Fintype.card_fin]
  exact le_trans (Submodule.finrank_mono hsub) hle

/-! ## The restricted entanglement lower bound: equality needs exponential bond dimension -/

/-- **Equality requires exponential bond dimension.**  Any bond-`χ` tensor factorization of the equality function
across its block cut has `χ ≥ 2^k` — the cross-cut rank is full, so no low-bond tensor represents it.  This is the
entanglement lower bound the oracle-loading flaw cannot defeat: bond `1` would make equality a product across the
cut, but its rank is `2^k`. -/
theorem eqFun_tensor_bond_ge {k χ : ℕ}
    (T : TensorFactorization (blockS k) (eqFun K k) χ) :
    2 ^ k ≤ χ := by
  have hres : residualOf (blockS k) (eqFun K k) = resVec K k := rfl
  have h1 : (2 : ℕ) ^ k
      ≤ Module.finrank K (Submodule.span K (Set.range (residualOf (blockS k) (eqFun K k)))) := by
    rw [hres]; exact eqFun_dim_ge
  exact le_trans h1 (finrank_residualSpan_le_bond T)

/-- **No cheap tensor for equality.**  For `1 ≤ k`, equality has no bond-`1` factorization — it is not a product
across the cut, so an oracle-loaded single-bit boundary cannot represent it. -/
theorem eqFun_no_bond_one {k : ℕ} (hk : 1 ≤ k)
    (T : TensorFactorization (blockS k) (eqFun K k) 1) : False := by
  have h := eqFun_tensor_bond_ge T
  have : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

end PallLean.Paper93.DeepMath.PathB.TensorEntanglement

#print axioms PallLean.Paper93.DeepMath.PathB.TensorEntanglement.finrank_residualSpan_le_bond
#print axioms PallLean.Paper93.DeepMath.PathB.TensorEntanglement.eqFun_tensor_bond_ge
#print axioms PallLean.Paper93.DeepMath.PathB.TensorEntanglement.eqFun_no_bond_one
