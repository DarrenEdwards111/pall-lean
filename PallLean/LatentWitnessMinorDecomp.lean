import PallLean.LatentCompiler
import PallLean.ProductDeriv
import Mathlib.Tactic

/-!
# LatentWitnessMinorDecomp

Direct NP-side lower bound on latentCompiledPoly via identity-minor
construction on the selConSheet component.

Key insight: derivatives at selSlot positions kill machCopySheet and copyConSheet
(they contain no selSlot variables), so SPDP generators from selSlot-admissible
lists depend only on selConSheet. The selConSheet product structure then provides
a Kronecker-delta identity for linear independence.
-/

namespace LatentWitnessMinorDecomp

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open LatentCompiler

/-- Admissibility of selector-slot witness lists under latentPartition. -/
theorem witness_selector_list_admissible (M : DTM) (n : ℕ)
    (S : List (Fin (latentBaseVars M n))) (hnd : S.Nodup) :
    isBlockAdmissible (latentPartition M n) (S.map (selSlot M n)) :=
  selSlotList_admissible M n S hnd

/-! ## Structural: selSlot derivatives isolate selConSheet -/

/-- machCopyGadget has no selSlot variables (uses machSlot and copySlot only).
Therefore pderiv at any selSlot position gives 0. -/
theorem selSlot_ne_machSlot (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n)) :
    selSlot M n j ≠ machSlot M n i := by
  simp [selSlot, machSlot, slot, Fin.ext_iff]; omega

theorem selSlot_ne_copySlot (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n)) :
    selSlot M n j ≠ copySlot M n i := by
  simp [selSlot, copySlot, slot, Fin.ext_iff]; omega

theorem selSlot_ne_conSlot (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n)) :
    selSlot M n j ≠ conSlot M n i := by
  simp [selSlot, conSlot, slot, Fin.ext_iff]; omega

/-- machCopyGadget has no selSlot variables (uses machSlot and copySlot only).
Therefore pderiv at any selSlot position gives 0. -/
theorem pderiv_selSlot_machCopyGadget (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n)) :
    pderiv (selSlot M n j) (machCopyGadget M n i) = 0 := by
  unfold machCopyGadget Xmach Xcopy
  have hm := selSlot_ne_machSlot M n i j
  have hc := selSlot_ne_copySlot M n i j
  -- machCopyGadget = 1 - X_mach * X_copy
  -- pderiv kills both X_mach and X_copy since selSlot ≠ machSlot, copySlot
  -- Use ProductDeriv.pderiv_one_sub_mul_ne
  exact ProductDeriv.pderiv_one_sub_mul_ne hm (by
    rw [MvPolynomial.vars_X]; simp; exact hc)

/-- copyConGadget has no selSlot variables. -/
theorem pderiv_selSlot_copyConGadget (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n)) :
    pderiv (selSlot M n j) (copyConGadget M n i) = 0 := by
  unfold copyConGadget Xcopy Xcon
  have hcp := selSlot_ne_copySlot M n i j
  have hcn := selSlot_ne_conSlot M n i j
  exact ProductDeriv.pderiv_one_sub_mul_ne hcp (by
    rw [MvPolynomial.vars_X]; simp; exact hcn)

private theorem foldl_pderiv_zero_sel {n : ℕ} (l : List (Fin n)) :
    l.foldl (fun q i => pderiv i q) (0 : MvPolynomial (Fin n) ℚ) = 0 := by
  induction l with
  | nil => simp
  | cons a rest ih => simpa [List.foldl] using ih

private theorem pderiv_selSlot_prod_machCopy_zero (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n))
    (t : Finset (Fin (latentBaseVars M n))) :
    pderiv (selSlot M n j) (∏ i ∈ t, machCopyGadget M n i) = 0 := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      simp [Finset.prod_insert, ha, MvPolynomial.pderiv_mul,
        pderiv_selSlot_machCopyGadget, ih]

private theorem pderiv_selSlot_prod_copyCon_zero (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n))
    (t : Finset (Fin (latentBaseVars M n))) :
    pderiv (selSlot M n j) (∏ i ∈ t, copyConGadget M n i) = 0 := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      simp [Finset.prod_insert, ha, MvPolynomial.pderiv_mul,
        pderiv_selSlot_copyConGadget, ih]

/-- Any nonempty iterated selSlot-derivative kills machCopySheet. -/
theorem iterDerivList_selSlot_machCopySheet_zero (M : DTM) (n : ℕ)
    (S : List (Fin (latentBaseVars M n))) (hS : S ≠ []) :
    iterDerivList (S.map (selSlot M n)) (machCopySheet M n) = 0 := by
  cases S with
  | nil => contradiction
  | cons a rest =>
      unfold machCopySheet
      simp only [iterDerivList, List.map, List.foldl]
      rw [pderiv_selSlot_prod_machCopy_zero M n a Finset.univ]
      exact foldl_pderiv_zero_sel (rest.map (selSlot M n))

/-- Any nonempty iterated selSlot-derivative kills copyConSheet. -/
theorem iterDerivList_selSlot_copyConSheet_zero (M : DTM) (n : ℕ)
    (S : List (Fin (latentBaseVars M n))) (hS : S ≠ []) :
    iterDerivList (S.map (selSlot M n)) (copyConSheet M n) = 0 := by
  cases S with
  | nil => contradiction
  | cons a rest =>
      unfold copyConSheet
      simp only [iterDerivList, List.map, List.foldl]
      rw [pderiv_selSlot_prod_copyCon_zero M n a Finset.univ]
      exact foldl_pderiv_zero_sel (rest.map (selSlot M n))

/-- For nonempty selector-derivative lists, latentCompiledPoly derivatives reduce to selConSheet. -/
theorem iterDerivList_selSlot_latentCompiled_eq_selCon (M : DTM) (n : ℕ)
    (S : List (Fin (latentBaseVars M n))) (hS : S ≠ []) :
    iterDerivList (S.map (selSlot M n)) (latentCompiledPoly M n) =
      iterDerivList (S.map (selSlot M n)) (selConSheet M n) := by
  unfold latentCompiledPoly
  rw [iterDerivList_add, iterDerivList_add,
    iterDerivList_selSlot_machCopySheet_zero M n S hS,
    iterDerivList_selSlot_copyConSheet_zero M n S hS,
    zero_add, zero_add]

/-! ## selConSheet identity-minor core lemmas -/

private theorem selSlot_not_in_Xcon_vars (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n)) :
    selSlot M n j ∉ (Xcon M n i).vars := by
  unfold Xcon
  rw [MvPolynomial.vars_X]
  simp [selSlot_ne_conSlot M n i j]

/-- Derivative of selConGadget at its own selector slot. -/
theorem pderiv_selSlot_selConGadget_eq (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    pderiv (selSlot M n i) (selConGadget M n i) = -(Xcon M n i) := by
  unfold selConGadget Xsel
  exact ProductDeriv.pderiv_one_sub_mul (selSlot_not_in_Xcon_vars M n i i)

/-- Derivative of selConGadget at a different selector slot is zero. -/
theorem pderiv_selSlot_selConGadget_ne (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n)) (hij : i ≠ j) :
    pderiv (selSlot M n j) (selConGadget M n i) = 0 := by
  unfold selConGadget Xsel
  have hneq : selSlot M n j ≠ selSlot M n i := by
    intro h
    have hji : j = i := selSlot_injective M n h
    exact hij hji.symm
  exact ProductDeriv.pderiv_one_sub_mul_ne hneq (selSlot_not_in_Xcon_vars M n i j)

/-- Selector derivative on a finite selCon product (hit case). -/
theorem pderiv_selSlot_selConProd_of_mem (M : DTM) (n : ℕ)
    (T : Finset (Fin (latentBaseVars M n)))
    (j : Fin (latentBaseVars M n)) (hj : j ∈ T) :
    pderiv (selSlot M n j) (∏ i ∈ T, selConGadget M n i) =
      (-(Xcon M n j)) * (∏ i ∈ (T.erase j), selConGadget M n i) := by
  rw [ProductDeriv.pderiv_prod_single
      (s := T)
      (f := fun i => selConGadget M n i)
      (i := selSlot M n j)
      (k := j)
      (hk := hj)]
  · simpa [pderiv_selSlot_selConGadget_eq]
  · intro i hi hij
    exact pderiv_selSlot_selConGadget_ne M n i j hij

/-- Selector derivative on a finite selCon product (miss case). -/
theorem pderiv_selSlot_selConProd_of_not_mem (M : DTM) (n : ℕ)
    (T : Finset (Fin (latentBaseVars M n)))
    (j : Fin (latentBaseVars M n)) (hj : j ∉ T) :
    pderiv (selSlot M n j) (∏ i ∈ T, selConGadget M n i) = 0 := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
      have hja : j ≠ a := by
        intro h
        apply hj
        simp [h, ha]
      have hjT : j ∉ T := by
        intro h
        apply hj
        simp [h, ha]
      rw [Finset.prod_insert ha, MvPolynomial.pderiv_mul]
      simp [pderiv_selSlot_selConGadget_ne M n a j (by simpa [eq_comm] using hja), ih hjT]

/-- Single selector derivative of selConSheet isolates one factor by product rule. -/
theorem pderiv_selSlot_selConSheet (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n)) :
    pderiv (selSlot M n j) (selConSheet M n) =
      (-(Xcon M n j)) * (∏ i ∈ (Finset.univ.erase j), selConGadget M n i) := by
  unfold selConSheet
  exact pderiv_selSlot_selConProd_of_mem M n Finset.univ j (by simp)

/-! ## κ-level iterated derivative assembly for selCon products -/

private theorem iterDerivList_mul_const_left
    {n : ℕ} (indices : List (Fin n))
    (f g : MvPolynomial (Fin n) ℚ)
    (hf : ∀ i ∈ indices, pderiv i f = 0) :
    iterDerivList indices (f * g) = f * iterDerivList indices g := by
  induction indices generalizing g with
  | nil => simp [iterDerivList]
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl]
    have hi : pderiv i f = 0 := hf i (by simp)
    rw [MvPolynomial.pderiv_mul, hi, zero_mul, zero_add]
    exact ih _ (fun j hj => hf j (by simp [hj]))

/-- Full κ-level selector-derivative formula on a finite selCon product.
For a nodup selector list `ks`, differentiating a selCon product over `s` gives:
`(-1)^|ks| * (∏_{k∈ks} Xcon(k)) * (∏_{i∈s\ks} selConGadget(i))`. -/
theorem iterDeriv_selConProd_eq (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n))) (hnd : ks.Nodup)
    (s : Finset (Fin (latentBaseVars M n))) (hks : ∀ k ∈ ks, k ∈ s) :
    iterDerivList (ks.map (selSlot M n)) (∏ i ∈ s, selConGadget M n i) =
      C ((-1 : ℚ)^ks.length) * (ks.map (Xcon M n)).prod *
        (∏ i ∈ (s \ ks.toFinset), selConGadget M n i) := by
  induction ks generalizing s with
  | nil =>
      simp [iterDerivList]
  | cons k rest ih =>
      simp only [List.map_cons]
      rw [show iterDerivList (selSlot M n k :: rest.map (selSlot M n)) (∏ i ∈ s, selConGadget M n i) =
          iterDerivList (rest.map (selSlot M n))
            (pderiv (selSlot M n k) (∏ i ∈ s, selConGadget M n i))
        from by unfold iterDerivList; simp [List.foldl]]
      have hk_mem : k ∈ s := hks k (by simp)
      rw [pderiv_selSlot_selConProd_of_mem M n s k hk_mem]

      have hconst : ∀ i ∈ rest.map (selSlot M n), pderiv i (-(Xcon M n k)) = 0 := by
        intro i hi
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hi
        have hnot : selSlot M n c ∉ (Xcon M n k).vars := selSlot_not_in_Xcon_vars M n k c
        rw [map_neg, MvPolynomial.pderiv_eq_zero_of_notMem_vars hnot, neg_zero]

      rw [iterDerivList_mul_const_left _ _ _ hconst]

      have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hk_not : k ∉ rest := (List.nodup_cons.mp hnd).1
      have hrest_in : ∀ j ∈ rest, j ∈ s.erase k := by
        intro j hj
        exact Finset.mem_erase.mpr ⟨fun h => hk_not (h ▸ hj), hks j (by simp [hj])⟩

      rw [ih hnd' (s.erase k) hrest_in]
      have hset : s.erase k \ rest.toFinset = s \ (k :: rest).toFinset := by
        ext x
        simp [Finset.mem_sdiff, Finset.mem_erase, List.toFinset_cons]
        tauto
      rw [hset]
      simp only [List.length_cons, List.prod_cons]
      rw [pow_succ, map_mul, map_neg, map_one]
      ring

/-! ## Direct NP lower bound -/

/-- NP-side lower bound at contradiction scale — DIRECT on latentCompiledPoly.
No bridge needed: identity minor on selConSheet inside latentCompiledPoly
gives C(baseVars, κ) linearly independent generators directly.

Proof sketch (paper-faithful, Section 18 style):
1. Derivatives at selSlot positions kill machCopySheet and copyConSheet
2. Remaining selConSheet = ∏(1 - Xsel_i · Xcon_i) has product structure
3. Tag monomials τ_S = ∏_{j∈S} e_{conSlot j} give Kronecker delta
4. Linear independence → rank ≥ C(baseVars, κ) ≥ n^(κ/4) -/
def latent_hard_witness_logscale (M : DTM) (n : ℕ) (_hn804 : n ≥ 2 ^ 804) : Prop :=
  n ^ (Nat.log 2 n / 4) ≤
    mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (latentCompiledPoly M n)

/-- Alias: "Obligation 1" in the current route is the direct NP lower bound. -/
def obligation1_np_logscale (M : DTM) (n : ℕ) (hn804 : n ≥ 2 ^ 804) : Prop :=
  latent_hard_witness_logscale M n hn804

end LatentWitnessMinorDecomp
