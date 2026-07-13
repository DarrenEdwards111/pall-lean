import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTensorEntanglementLowerBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukHardFunctionLB

/-!
# Exponential bond dimension for `hardF`'s address blocks

`TensorEntanglementLowerBound` proved a bond lower bound (bond `≥` cross-cut rank) and instantiated it for the
equality function.  This file extends it to the addressing family `hardF`: on any address block, the cross-cut
rank is `2^b − 1`, so any tensor factorization needs bond dimension `≥ 2^b − 1` — **exponential** in the block
length.

The mechanism upgrades `hardF`'s existing *count* bound to a *rank* bound.  Driving block `k` to address `c'`
(via `wit`) with data table `t` and the other blocks reading the reserved cell `c0`, `hardF_merge` gives residual
value `t[c']`.  So the residual for table `t` *is the table itself* as a function of the address.  Taking
`t = indicator_c` for each `c ≠ c0` yields the standard basis vectors `e_c` — `Dsize b − 1` linearly independent
residuals — so the residual-span rank is `≥ 2^b − 1`.

Note the coincidence: `hardF`'s log-count boundary is also `2^b − 1` (`card_blockResiduals_hardF_ge` gives
`2^{2^b − 1}` distinct residuals), and the *rank* here is `2^b − 1` too — the `2^{2^b−1}` residuals live in a
`(2^b − 1)`-dimensional space, achieving all `0/1` vectors of it.

## Honest scope

A restricted entanglement lower bound: a *fixed* family (`hardF`) at a *fixed* address-block cut needs exponential
bond dimension in a tensor-network model.  No representation-invariance, so no collapse and no separation.  A
genuine tensor-network bound, presented as such.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TensorEntanglementHardF

open PallLean.Paper93.DeepMath.PathB.NecHard
open PallLean.Paper93.DeepMath.PathB.TensorEntanglement

variable {K : Type*} [Field K] {b m : ℕ}

/-- The `K`-valued embedding of `hardF`. -/
noncomputable def hardFK (K : Type*) [Field K] (b m : ℕ) (x : Fin (nn b m) → Bool) : K :=
  if hardF x then 1 else 0

/-- The data table that is the indicator of a single address `c`. -/
def indicatorTable {b : ℕ} (c : Fin (Dsize b)) : Fin (Dsize b) → Bool := fun d => decide (d = c)

/-- The residual family: for each address `c ≠ c0`, the subfunction obtained with data table `indicator_c`
(others reading `c0`).  Indexed by the `2^b − 1` addresses other than `c0`. -/
noncomputable def gFam (K : Type*) [Field K] {b m : ℕ} (k : Fin m)
    (c : {c : Fin (Dsize b) // c ≠ c0}) : (Fin (nn b m) → Bool) → K :=
  residualOf (blockS k) (hardFK K b m) (mkt (indicatorTable c.val))

/-- **The standard-basis identity.**  `gFam k c` evaluated at the address `c'` is `[c' = c]` — the residuals are
the standard basis vectors. -/
theorem gFam_apply (k : Fin m) (c c' : {c : Fin (Dsize b) // c ≠ c0}) :
    gFam K k c (wit k c'.val) = if c'.val = c.val then (1 : K) else 0 := by
  have hc0 : indicatorTable c.val c0 = false := by
    simp only [indicatorTable]
    exact decide_eq_false (fun h => c.property h.symm)
  show hardFK K b m (fun i => if i ∈ blockS k then wit k c'.val i else mkt (indicatorTable c.val) i) = _
  unfold hardFK
  rw [hardF_merge k c'.val (indicatorTable c.val) hc0]
  simp only [indicatorTable]
  by_cases h : c'.val = c.val <;> simp [h]

/-- **The residuals are linearly independent** (`Dsize b − 1` of them). -/
theorem gFam_linearIndependent (k : Fin m) : LinearIndependent K (gFam K (b := b) (m := m) k) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a hsum c'
  have hpt := congrFun hsum (wit k c'.val)
  simp only [Finset.sum_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at hpt
  rw [Finset.sum_eq_single c'] at hpt
  · rw [gFam_apply, if_pos rfl] at hpt; simpa using hpt
  · intro c _ hc
    rw [gFam_apply, if_neg (fun h => hc (Subtype.ext h.symm)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ c') h

/-- **Cross-cut rank `≥ 2^b − 1`.**  The residual-span dimension of `hardF` on an address block is at least
`Dsize b − 1`. -/
theorem hardF_dimResiduals_ge (k : Fin m) :
    Dsize b - 1 ≤ Module.finrank K (Submodule.span K (Set.range (residualOf (blockS k) (hardFK K b m)))) := by
  classical
  haveI : FiniteDimensional K ((Fin (nn b m) → Bool) → K) := inferInstance
  have hcard : Module.finrank K (Submodule.span K (Set.range (gFam K (b := b) (m := m) k)))
      = Dsize b - 1 := by
    rw [finrank_span_eq_card (gFam_linearIndependent k)]
    simp only [ne_eq]
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  have hsub : Submodule.span K (Set.range (gFam K (b := b) (m := m) k))
      ≤ Submodule.span K (Set.range (residualOf (blockS k) (hardFK K b m))) := by
    apply Submodule.span_mono
    rintro _ ⟨c, rfl⟩
    exact ⟨mkt (indicatorTable c.val), rfl⟩
  rw [← hcard]
  exact Submodule.finrank_mono hsub

/-- **Exponential bond dimension for `hardF`'s address blocks.**  Any bond-`χ` tensor factorization of `hardF`
across an address block has `χ ≥ 2^b − 1` — exponential in the block length, coinciding with `hardF`'s log-count
boundary. -/
theorem hardF_tensor_bond_ge (k : Fin m) {χ : ℕ}
    (T : TensorFactorization (blockS k) (hardFK K b m) χ) :
    Dsize b - 1 ≤ χ :=
  le_trans (hardF_dimResiduals_ge k) (finrank_residualSpan_le_bond T)

end PallLean.Paper93.DeepMath.PathB.TensorEntanglementHardF

#print axioms PallLean.Paper93.DeepMath.PathB.TensorEntanglementHardF.gFam_linearIndependent
#print axioms PallLean.Paper93.DeepMath.PathB.TensorEntanglementHardF.hardF_tensor_bond_ge
