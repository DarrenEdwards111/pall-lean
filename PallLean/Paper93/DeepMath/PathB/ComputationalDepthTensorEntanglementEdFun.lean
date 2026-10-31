import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTensorEntanglementLowerBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukElementDistinctness

/-!
# Exponential bond dimension for element distinctness

Element distinctness `edFun` is genuinely different from the addressing families (`hardF`/`orMux`): it has no
data cells, and its residuals are set-indicators `a ↦ [a ∉ T]`, not standard basis vectors.  We treat the two-block
case (`m = 2`), where `edFun = [addr₀ ≠ addr₁]` — the residual on block `0` at outside address `c` is `[a ≠ c] =
1 − e_c`.

The residuals are not a basis, but their **differences** are: `res_{c₀} − res_{c'} = e_{c'} − e_{c₀}`, and the
`2^b − 1` vectors `{e_{c'} − e_{c₀} : c' ≠ c₀}` are linearly independent over *any* field (char-independent, unlike
the full-rank `J − I` argument which needs `2^b − 1 ≠ 0`).  So the cross-cut rank is `≥ 2^b − 1`, hence any tensor
factorization needs bond dimension `≥ 2^b − 1` — exponential.

Contrast: `edFun`'s formula/BP boundary is only `m − 1` (log of the pair-encoding count), but its *entanglement*
boundary is `2^b − 1` — the tensor bond is much larger, because the `[a ∉ T]` residuals, while few in log-count,
span a large space.

## Honest scope

A restricted entanglement lower bound for a *fixed* family (`edFun`, two blocks) at a *fixed* cut.  No
representation-invariance, no collapse, no separation.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TensorEntanglementEdFun

open PallLean.Paper93.DeepMath.PathB.NecHard
open PallLean.Paper93.DeepMath.PathB.NecHardED
open PallLean.Paper93.DeepMath.PathB.TensorEntanglement

variable {K : Type*} [Field K] {b : ℕ}

/-- The `K`-valued embedding of `edFun`. -/
noncomputable def edFunK (K : Type*) [Field K] (b : ℕ) (x : Fin (nn b 2) → Bool) : K :=
  if edFun x then 1 else 0

/-- **Two-block merge.**  With block `0` at address `a` and block `1` at address `c`, element distinctness is
`[a ≠ c]`. -/
theorem edFun_merge_m2 (a c : Fin (Dsize b)) :
    edFun (fun i => if i ∈ blockS (0 : Fin 2) then wit 0 a i else wit 1 c i) = decide (a ≠ c) := by
  set M : Fin (nn b 2) → Bool :=
    (fun i => if i ∈ blockS (0 : Fin 2) then wit 0 a i else wit 1 c i) with hM
  have haddr0 : addr M 0 = a := by
    unfold addr
    have he : (fun j => M (addrBitVar (0 : Fin 2) j)) = (e b).symm a := by
      funext j; rw [hM]; simp only [if_pos (addrBitVar_mem 0 j)]; exact wit_addrBitVar 0 a j
    rw [he, Equiv.apply_symm_apply]
  have haddr1 : addr M 1 = c := by
    unfold addr
    have he : (fun j => M (addrBitVar (1 : Fin 2) j)) = (e b).symm c := by
      funext j; rw [hM]
      simp only [if_neg (addrBitVar_ne_mem (show (1 : Fin 2) ≠ 0 by decide) j)]
      exact wit_addrBitVar 1 c j
    rw [he, Equiv.apply_symm_apply]
  unfold edFun
  by_cases hac : a = c
  · have hcol : ¬ (∀ k1 k2 : Fin 2, k1 ≠ k2 → addr M k1 ≠ addr M k2) := by
      push_neg
      exact ⟨0, 1, by decide, by rw [haddr0, haddr1]; exact hac⟩
    rw [decide_eq_false hcol, hac]; simp
  · have hall : ∀ k1 k2 : Fin 2, k1 ≠ k2 → addr M k1 ≠ addr M k2 := by
      rw [Fin.forall_fin_two]
      refine ⟨?_, ?_⟩
      · rw [Fin.forall_fin_two]
        exact ⟨fun h => absurd rfl h, fun _ => by rw [haddr0, haddr1]; exact hac⟩
      · rw [Fin.forall_fin_two]
        exact ⟨fun _ => by rw [haddr0, haddr1]; exact fun h => hac h.symm, fun h => absurd rfl h⟩
    rw [decide_eq_true hall]; simp [hac]

/-- The residual on block `0` with block `1` set to address `c`. -/
noncomputable def resAt (K : Type*) [Field K] {b : ℕ} (c : Fin (Dsize b)) : (Fin (nn b 2) → Bool) → K :=
  residualOf (blockS (0 : Fin 2)) (edFunK K b) (wit 1 c)

theorem resAt_apply (a c : Fin (Dsize b)) : resAt K c (wit 0 a) = if a ≠ c then (1 : K) else 0 := by
  show edFunK K b (fun i => if i ∈ blockS (0 : Fin 2) then wit 0 a i else wit 1 c i) = _
  unfold edFunK
  rw [edFun_merge_m2]
  by_cases h : a = c <;> simp [h]

/-- The difference family `d_{c'} = res_{c₀} − res_{c'}`, indexed by addresses `c' ≠ c₀` — the `2^b − 1`
independent vectors `e_{c'} − e_{c₀}`. -/
noncomputable def dFam (K : Type*) [Field K] {b : ℕ}
    (c' : {c : Fin (Dsize b) // c ≠ c0}) : (Fin (nn b 2) → Bool) → K :=
  resAt K c0 - resAt K c'.val

theorem dFam_apply (c' c'' : {c : Fin (Dsize b) // c ≠ c0}) :
    dFam K c' (wit 0 c''.val) = if c''.val = c'.val then (1 : K) else 0 := by
  simp only [dFam, Pi.sub_apply, resAt_apply]
  rw [if_pos c''.property]
  by_cases h : c''.val = c'.val <;> simp [h]

theorem dFam_linearIndependent : LinearIndependent K (dFam K (b := b)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a hsum c''
  have hpt := congrFun hsum (wit 0 c''.val)
  simp only [Finset.sum_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at hpt
  rw [Finset.sum_eq_single c''] at hpt
  · rw [dFam_apply, if_pos rfl] at hpt; simpa using hpt
  · intro c' _ hc
    rw [dFam_apply, if_neg (fun h => hc (Subtype.ext h.symm)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ c'') h

/-- **Cross-cut rank `≥ 2^b − 1`** for element distinctness on block `0`. -/
theorem edFun_dimResiduals_ge :
    Dsize b - 1
      ≤ Module.finrank K (Submodule.span K (Set.range (residualOf (blockS (0 : Fin 2)) (edFunK K b)))) := by
  classical
  haveI : FiniteDimensional K ((Fin (nn b 2) → Bool) → K) := inferInstance
  have hcard : Module.finrank K (Submodule.span K (Set.range (dFam K (b := b)))) = Dsize b - 1 := by
    rw [finrank_span_eq_card dFam_linearIndependent]
    simp only [ne_eq]
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  have hsub : Submodule.span K (Set.range (dFam K (b := b)))
      ≤ Submodule.span K (Set.range (residualOf (blockS (0 : Fin 2)) (edFunK K b))) := by
    rw [Submodule.span_le]
    rintro _ ⟨c', rfl⟩
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨wit 1 c0, rfl⟩)
      (Submodule.subset_span ⟨wit 1 c'.val, rfl⟩)
  rw [← hcard]
  exact Submodule.finrank_mono hsub

/-- **Exponential bond dimension for element distinctness.**  Any bond-`χ` tensor factorization of `edFun` (two
blocks) across block `0` has `χ ≥ 2^b − 1`. -/
theorem edFun_tensor_bond_ge {χ : ℕ}
    (T : TensorFactorization (blockS (0 : Fin 2)) (edFunK K b) χ) :
    Dsize b - 1 ≤ χ :=
  le_trans edFun_dimResiduals_ge (finrank_residualSpan_le_bond T)

end PallLean.Paper93.DeepMath.PathB.TensorEntanglementEdFun

#print axioms PallLean.Paper93.DeepMath.PathB.TensorEntanglementEdFun.edFun_merge_m2
#print axioms PallLean.Paper93.DeepMath.PathB.TensorEntanglementEdFun.edFun_tensor_bond_ge
