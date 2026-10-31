import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTensorEntanglementLowerBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukOrMultiplexer

/-!
# Exponential bond dimension for the OR-multiplexer's address blocks

The OR-multiplexer `orMux` shares `hardF`'s addressing structure — its merge identity `orMux_merge` reads the
same as `hardF_merge` when the other blocks read the reserved cell `c0`.  So the same rank argument applies: on
any address block the cross-cut rank is `2^b − 1`, hence any tensor factorization needs bond dimension `≥ 2^b − 1`
— exponential.

## Honest scope

A restricted entanglement lower bound for a *fixed* family (`orMux`) at a *fixed* address-block cut.  No
representation-invariance, no collapse, no separation.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TensorEntanglementOrMux

open PallLean.Paper93.DeepMath.PathB.NecHard
open PallLean.Paper93.DeepMath.PathB.NecHardOr
open PallLean.Paper93.DeepMath.PathB.TensorEntanglement

variable {K : Type*} [Field K] {b m : ℕ}

/-- The `K`-valued embedding of `orMux`. -/
noncomputable def orMuxK (K : Type*) [Field K] (b m : ℕ) (x : Fin (nn b m) → Bool) : K :=
  if orMux x then 1 else 0

/-- The data table that is the indicator of a single address `c`. -/
def indicatorTable {b : ℕ} (c : Fin (Dsize b)) : Fin (Dsize b) → Bool := fun d => decide (d = c)

/-- The residual family: for each address `c ≠ c0`, the subfunction with data table `indicator_c`. -/
noncomputable def gFam (K : Type*) [Field K] {b m : ℕ} (k : Fin m)
    (c : {c : Fin (Dsize b) // c ≠ c0}) : (Fin (nn b m) → Bool) → K :=
  residualOf (blockS k) (orMuxK K b m) (mkt (indicatorTable c.val))

theorem gFam_apply (k : Fin m) (c c' : {c : Fin (Dsize b) // c ≠ c0}) :
    gFam K k c (wit k c'.val) = if c'.val = c.val then (1 : K) else 0 := by
  have hc0 : indicatorTable c.val c0 = false := by
    simp only [indicatorTable]
    exact decide_eq_false (fun h => c.property h.symm)
  show orMuxK K b m (fun i => if i ∈ blockS k then wit k c'.val i else mkt (indicatorTable c.val) i) = _
  unfold orMuxK
  rw [orMux_merge k c'.val (indicatorTable c.val) hc0]
  simp only [indicatorTable]
  by_cases h : c'.val = c.val <;> simp [h]

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

/-- **Cross-cut rank `≥ 2^b − 1`** for `orMux` on an address block. -/
theorem orMux_dimResiduals_ge (k : Fin m) :
    Dsize b - 1 ≤ Module.finrank K (Submodule.span K (Set.range (residualOf (blockS k) (orMuxK K b m)))) := by
  classical
  haveI : FiniteDimensional K ((Fin (nn b m) → Bool) → K) := inferInstance
  have hcard : Module.finrank K (Submodule.span K (Set.range (gFam K (b := b) (m := m) k)))
      = Dsize b - 1 := by
    rw [finrank_span_eq_card (gFam_linearIndependent k)]
    simp only [ne_eq]
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  have hsub : Submodule.span K (Set.range (gFam K (b := b) (m := m) k))
      ≤ Submodule.span K (Set.range (residualOf (blockS k) (orMuxK K b m))) := by
    apply Submodule.span_mono
    rintro _ ⟨c, rfl⟩
    exact ⟨mkt (indicatorTable c.val), rfl⟩
  rw [← hcard]
  exact Submodule.finrank_mono hsub

/-- **Exponential bond dimension for `orMux`'s address blocks.**  Any bond-`χ` tensor factorization of `orMux`
across an address block has `χ ≥ 2^b − 1`. -/
theorem orMux_tensor_bond_ge (k : Fin m) {χ : ℕ}
    (T : TensorFactorization (blockS k) (orMuxK K b m) χ) :
    Dsize b - 1 ≤ χ :=
  le_trans (orMux_dimResiduals_ge k) (finrank_residualSpan_le_bond T)

end PallLean.Paper93.DeepMath.PathB.TensorEntanglementOrMux

#print axioms PallLean.Paper93.DeepMath.PathB.TensorEntanglementOrMux.orMux_tensor_bond_ge
