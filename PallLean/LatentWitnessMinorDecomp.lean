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

/-- Machine slots are injective on base indices. -/
theorem machSlot_injective (M : DTM) (n : ℕ) : Function.Injective (machSlot M n) := by
  intro a b hab
  simp [machSlot, slot] at hab
  exact Fin.ext (by omega)

/-- Copy slots are injective on base indices. -/
theorem copySlot_injective (M : DTM) (n : ℕ) : Function.Injective (copySlot M n) := by
  intro a b hab
  simp [copySlot, slot] at hab
  exact Fin.ext (by omega)

/-- Admissibility of machine-slot witness lists under latentPartition. -/
theorem witness_mach_list_admissible (M : DTM) (n : ℕ)
    (S : List (Fin (latentBaseVars M n))) (hnd : S.Nodup) :
    isBlockAdmissible (latentPartition M n) (S.map (machSlot M n)) := by
  constructor
  · exact hnd.map (machSlot_injective M n)
  · intro b
    by_contra hgt
    push_neg at hgt
    set filt := (S.map (machSlot M n)).filter (fun j => (latentPartition M n).assign j = b)
    have hmap_nd : (S.map (machSlot M n)).Nodup := hnd.map (machSlot_injective M n)
    have hfilt_nd : filt.Nodup := hmap_nd.filter _
    have h0 : 0 < filt.length := by omega
    have h1 : 1 < filt.length := by omega
    have hx_mem : filt[0] ∈ filt := List.getElem_mem h0
    have hy_mem : filt[1] ∈ filt := List.getElem_mem h1
    rw [List.mem_filter] at hx_mem hy_mem
    obtain ⟨hx_in, hx_bl⟩ := hx_mem
    obtain ⟨hy_in, hy_bl⟩ := hy_mem
    rw [List.mem_map] at hx_in hy_in
    obtain ⟨a, _, ha⟩ := hx_in
    obtain ⟨c, _, hc⟩ := hy_in
    have hx_eq : (latentPartition M n).assign filt[0] = b := by exact (decide_eq_true_eq.mp hx_bl)
    have hy_eq : (latentPartition M n).assign filt[1] = b := by exact (decide_eq_true_eq.mp hy_bl)
    have ha_bl : a = b := by
      have h2 : (latentPartition M n).assign filt[0] = a := by
        rw [show filt[0] = machSlot M n a from ha.symm]
        exact latentPartition_assign_machSlot M n a
      exact h2.symm.trans hx_eq
    have hc_bl : c = b := by
      have h2 : (latentPartition M n).assign filt[1] = c := by
        rw [show filt[1] = machSlot M n c from hc.symm]
        exact latentPartition_assign_machSlot M n c
      exact h2.symm.trans hy_eq
    have hac : a = c := ha_bl.trans hc_bl.symm
    exact absurd (hfilt_nd.getElem_inj_iff.mp (by show filt[0] = filt[1]; rw [← ha, ← hc, hac])) (by omega)

/-- Admissibility of copy-slot witness lists under latentPartition. -/
theorem witness_copy_list_admissible (M : DTM) (n : ℕ)
    (S : List (Fin (latentBaseVars M n))) (hnd : S.Nodup) :
    isBlockAdmissible (latentPartition M n) (S.map (copySlot M n)) := by
  constructor
  · exact hnd.map (copySlot_injective M n)
  · intro b
    by_contra hgt
    push_neg at hgt
    set filt := (S.map (copySlot M n)).filter (fun j => (latentPartition M n).assign j = b)
    have hmap_nd : (S.map (copySlot M n)).Nodup := hnd.map (copySlot_injective M n)
    have hfilt_nd : filt.Nodup := hmap_nd.filter _
    have h0 : 0 < filt.length := by omega
    have h1 : 1 < filt.length := by omega
    have hx_mem : filt[0] ∈ filt := List.getElem_mem h0
    have hy_mem : filt[1] ∈ filt := List.getElem_mem h1
    rw [List.mem_filter] at hx_mem hy_mem
    obtain ⟨hx_in, hx_bl⟩ := hx_mem
    obtain ⟨hy_in, hy_bl⟩ := hy_mem
    rw [List.mem_map] at hx_in hy_in
    obtain ⟨a, _, ha⟩ := hx_in
    obtain ⟨c, _, hc⟩ := hy_in
    have hx_eq : (latentPartition M n).assign filt[0] = b := by exact (decide_eq_true_eq.mp hx_bl)
    have hy_eq : (latentPartition M n).assign filt[1] = b := by exact (decide_eq_true_eq.mp hy_bl)
    have ha_bl : a = b := by
      have h2 : (latentPartition M n).assign filt[0] = a := by
        rw [show filt[0] = copySlot M n a from ha.symm]
        exact latentPartition_assign_copySlot M n a
      exact h2.symm.trans hx_eq
    have hc_bl : c = b := by
      have h2 : (latentPartition M n).assign filt[1] = c := by
        rw [show filt[1] = copySlot M n c from hc.symm]
        exact latentPartition_assign_copySlot M n c
      exact h2.symm.trans hy_eq
    have hac : a = c := ha_bl.trans hc_bl.symm
    exact absurd (hfilt_nd.getElem_inj_iff.mp (by show filt[0] = filt[1]; rw [← ha, ← hc, hac])) (by omega)

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

/-- Derivative of machCopyGadget at its own machine slot. -/
theorem pderiv_machSlot_machCopyGadget_eq (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    pderiv (machSlot M n i) (machCopyGadget M n i) = -(Xcopy M n i) := by
  unfold machCopyGadget Xmach
  have hnot : machSlot M n i ∉ (Xcopy M n i).vars := by
    rw [MvPolynomial.vars_X]
    simp [machSlot, copySlot, slot, Fin.ext_iff]
  exact ProductDeriv.pderiv_one_sub_mul hnot

/-- Derivative of machCopyGadget at a different machine slot is zero. -/
theorem pderiv_machSlot_machCopyGadget_ne (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n)) (hij : i ≠ j) :
    pderiv (machSlot M n j) (machCopyGadget M n i) = 0 := by
  unfold machCopyGadget Xmach
  have hneq : machSlot M n j ≠ machSlot M n i := by
    intro h
    exact hij ((machSlot_injective M n) h).symm
  have hnot : machSlot M n j ∉ (Xcopy M n i).vars := by
    rw [MvPolynomial.vars_X]
    simp [machSlot, copySlot, slot, Fin.ext_iff]
  exact ProductDeriv.pderiv_one_sub_mul_ne hneq hnot

/-- Machine-slot derivative on a finite machCopy product (hit case). -/
theorem pderiv_machSlot_machCopyProd_of_mem (M : DTM) (n : ℕ)
    (T : Finset (Fin (latentBaseVars M n)))
    (j : Fin (latentBaseVars M n)) (hj : j ∈ T) :
    pderiv (machSlot M n j) (∏ i ∈ T, machCopyGadget M n i) =
      (-(Xcopy M n j)) * (∏ i ∈ (T.erase j), machCopyGadget M n i) := by
  rw [ProductDeriv.pderiv_prod_single
      (s := T)
      (f := fun i => machCopyGadget M n i)
      (i := machSlot M n j)
      (k := j)
      (hk := hj)]
  · simpa [pderiv_machSlot_machCopyGadget_eq]
  · intro i hi hij
    exact pderiv_machSlot_machCopyGadget_ne M n i j hij

/-- Machine-slot derivative on a finite machCopy product (miss case). -/
theorem pderiv_machSlot_machCopyProd_of_not_mem (M : DTM) (n : ℕ)
    (T : Finset (Fin (latentBaseVars M n)))
    (j : Fin (latentBaseVars M n)) (hj : j ∉ T) :
    pderiv (machSlot M n j) (∏ i ∈ T, machCopyGadget M n i) = 0 := by
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
      simp [pderiv_machSlot_machCopyGadget_ne M n a j (by simpa [eq_comm] using hja), ih hjT]

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

/-- κ-level iterated derivative closed form specialized to full selConSheet. -/
theorem iterDeriv_selConSheet_eq (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n))) (hnd : ks.Nodup) :
    iterDerivList (ks.map (selSlot M n)) (selConSheet M n) =
      C ((-1 : ℚ)^ks.length) * (ks.map (Xcon M n)).prod *
        (∏ i ∈ (Finset.univ \ ks.toFinset), selConGadget M n i) := by
  unfold selConSheet
  exact iterDeriv_selConProd_eq M n ks hnd Finset.univ (by intro k hk; simp)

/-- Kronecker matrix data at logscale: choose-many independent generators
inside the blocked SPDP subspace of latentCompiledPoly. -/
def selCon_kronecker_matrix_logscale (M : DTM) (n : ℕ)
    (_hn804 : n ≥ 2 ^ 804) : Prop :=
  let K := Nat.choose (latentBaseVars M n) (Nat.log 2 n)
  ∃ (R : Fin K →
      ↥(mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n))),
    LinearIndependent ℚ (Subtype.val ∘ R)

/-- Row polynomial built from a selector-subset witness list. -/
noncomputable def selCon_rowPoly (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n))) :
    MvPolynomial (Fin (latentNumVars M n)) ℚ :=
  mlProj (iterDerivList (ks.map (selSlot M n)) (latentCompiledPoly M n))

/-- Any logscale selector-list derivative row lies in the blocked SPDP subspace. -/
theorem selCon_row_in_subspace_from_list (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n)))
    (hnd : ks.Nodup)
    (hlen : ks.length = Nat.log 2 n) :
    selCon_rowPoly M n ks ∈
      mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n) := by
  unfold selCon_rowPoly mlBlockedSpdpSubspace
  apply Submodule.subset_span
  refine ⟨ks.map (selSlot M n), 1, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [List.length_map] using hlen
  · -- totalDegree(1) = 0 ≤ log₂ n
    simp
  · -- vars(1)=∅ ⊆ S.toFinset
    simp
  · exact witness_selector_list_admissible M n ks hnd
  · simp [iterDerivList]

/-- Choose-indexed selector-list data used to build Kronecker row families. -/
def selCon_kronecker_rows_data_logscale (M : DTM) (n : ℕ)
    (_hn804 : n ≥ 2 ^ 804) : Prop :=
  let K := Nat.choose (latentBaseVars M n) (Nat.log 2 n)
  ∃ (idxList : Fin K → List (Fin (latentBaseVars M n))),
    (∀ i, (idxList i).Nodup) ∧
    (∀ i, (idxList i).length = Nat.log 2 n)

/-- Kronecker rows at logscale (candidate independent family). -/
def selCon_kronecker_rows_logscale (M : DTM) (n : ℕ)
    (_hn804 : n ≥ 2 ^ 804) : Prop :=
  let K := Nat.choose (latentBaseVars M n) (Nat.log 2 n)
  ∃ (R : Fin K →
      ↥(mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n))), True

/-- Construct row-family witness from choose-indexed selector-list data. -/
theorem selCon_kronecker_rows_logscale_from_index_lists (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804)
    (hRows : selCon_kronecker_rows_data_logscale M n hn804) :
    selCon_kronecker_rows_logscale M n hn804 := by
  rcases hRows with ⟨idxList, hnd, hlen⟩
  let K := Nat.choose (latentBaseVars M n) (Nat.log 2 n)
  refine ⟨(fun i : Fin K =>
    ⟨selCon_rowPoly M n (idxList i),
      selCon_row_in_subspace_from_list M n (idxList i) (hnd i) (hlen i)⟩), trivial⟩

/-- Canonical sign attached to a selector list: (-1)^(length). -/
noncomputable def selCon_signOfList {α : Type*} (ks : List α) : ℚ :=
  if Even ks.length then 1 else -1

theorem selCon_signOfList_pm1 {α : Type*} (ks : List α) :
    selCon_signOfList ks = 1 ∨ selCon_signOfList ks = -1 := by
  unfold selCon_signOfList
  by_cases h : Even ks.length
  · left; simp [h]
  · right; simp [h]

/-- Tag monomial for a selector-list index set: τ = ∑ e_{conSlot(k)}. -/
noncomputable def selCon_tagMono (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n))) :
    (Fin (latentNumVars M n)) →₀ ℕ :=
  (ks.map (conSlot M n)).foldr (fun j acc => acc + Finsupp.single j 1) 0

/-- Kronecker signs at logscale (±1 diagonal values). -/
def selCon_kronecker_signs_logscale (M : DTM) (n : ℕ)
    (_hn804 : n ≥ 2 ^ 804) : Prop :=
  let K := Nat.choose (latentBaseVars M n) (Nat.log 2 n)
  ∃ (signs : Fin K → ℚ), ∀ i, signs i = 1 ∨ signs i = -1

/-- Build ±1 sign witnesses canonically from choose-indexed selector lists. -/
theorem selCon_kronecker_signs_logscale_from_index_lists (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804)
    (hRows : selCon_kronecker_rows_data_logscale M n hn804) :
    selCon_kronecker_signs_logscale M n hn804 := by
  rcases hRows with ⟨idxList, _hnd, _hlen⟩
  let K := Nat.choose (latentBaseVars M n) (Nat.log 2 n)
  refine ⟨fun i : Fin K => selCon_signOfList (idxList i), ?_⟩
  intro i
  exact selCon_signOfList_pm1 (idxList i)

/-- Kronecker coefficient law at logscale, parameterized by row/tag/sign witnesses. -/
def selCon_kronecker_coeff_law_logscale (M : DTM) (n : ℕ)
    (_hn804 : n ≥ 2 ^ 804) : Prop :=
  let K := Nat.choose (latentBaseVars M n) (Nat.log 2 n)
  ∃ (R : Fin K →
      ↥(mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n)))
    (τ : Fin K → ((Fin (latentNumVars M n)) →₀ ℕ))
    (signs : Fin K → ℚ),
      (∀ i, signs i = 1 ∨ signs i = -1) ∧
      (∀ i j, MvPolynomial.coeff (τ i) (R j).val = if i = j then signs i else 0)

/-- Construct the Kronecker coefficient-law package from index-list data,
plus explicit diagonal/off-diagonal coefficient equations.

This isolates the remaining NP hard core to two concrete coefficient lemmas. -/
theorem selCon_kronecker_coeff_law_logscale_from_index_lists
    (M : DTM) (n : ℕ) (hn804 : n ≥ 2 ^ 804)
    (idxList : Fin (Nat.choose (latentBaseVars M n) (Nat.log 2 n)) →
      List (Fin (latentBaseVars M n)))
    (hnd : ∀ i, (idxList i).Nodup)
    (hlen : ∀ i, (idxList i).length = Nat.log 2 n)
    (hdiag : ∀ i : Fin (Nat.choose (latentBaseVars M n) (Nat.log 2 n)),
      MvPolynomial.coeff (selCon_tagMono M n (idxList i))
        (selCon_rowPoly M n (idxList i)) = selCon_signOfList (idxList i))
    (hoff : ∀ i j : Fin (Nat.choose (latentBaseVars M n) (Nat.log 2 n)), i ≠ j →
      MvPolynomial.coeff (selCon_tagMono M n (idxList i))
        (selCon_rowPoly M n (idxList j)) = 0) :
    selCon_kronecker_coeff_law_logscale M n hn804 := by
  let K := Nat.choose (latentBaseVars M n) (Nat.log 2 n)
  let R : Fin K →
      ↥(mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n)) :=
    fun i => ⟨selCon_rowPoly M n (idxList i),
      selCon_row_in_subspace_from_list M n (idxList i) (hnd i) (hlen i)⟩
  let τ : Fin K → ((Fin (latentNumVars M n)) →₀ ℕ) :=
    fun i => selCon_tagMono M n (idxList i)
  let signs : Fin K → ℚ :=
    fun i => selCon_signOfList (idxList i)
  refine ⟨R, τ, signs, ?_, ?_⟩
  · intro i
    exact selCon_signOfList_pm1 (idxList i)
  · intro i j
    by_cases hij : i = j
    · subst hij
      simpa [R, τ, signs] using hdiag i
    · have h0 := hoff i j hij
      simpa [R, τ, signs, hij] using h0

/-- Stronger Kronecker witness data (paper identity-minor form) at logscale. -/
def selCon_kronecker_data_logscale (M : DTM) (n : ℕ)
    (_hn804 : n ≥ 2 ^ 804) : Prop :=
  selCon_kronecker_coeff_law_logscale M n _hn804

/-- Assemble Kronecker data from explicit parts (paper-faithful decomposition). -/
theorem selCon_kronecker_data_logscale_from_parts (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804)
    (_hRows : selCon_kronecker_rows_logscale M n hn804)
    (_hSigns : selCon_kronecker_signs_logscale M n hn804)
    (hCoeff : selCon_kronecker_coeff_law_logscale M n hn804) :
    selCon_kronecker_data_logscale M n hn804 :=
  hCoeff

private theorem linearIndependent_from_kronecker
    (M : DTM) (n : ℕ) (K : ℕ)
    (R : Fin K →
      ↥(mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n)))
    (τ : Fin K → ((Fin (latentNumVars M n)) →₀ ℕ))
    (signs : Fin K → ℚ)
    (hsigns : ∀ i, signs i = 1 ∨ signs i = -1)
    (hkronecker : ∀ i j, MvPolynomial.coeff (τ i) (R j).val = if i = j then signs i else 0) :
    LinearIndependent ℚ (Subtype.val ∘ R) := by
  rw [linearIndependent_iff']
  intro S g hg a ha
  have h0 : (Tseitin.coeffLin ℚ (τ a)) (∑ j ∈ S, g j • (Subtype.val ∘ R) j) = 0 := by
    rw [hg]
    exact map_zero _
  simp only [map_sum, LinearMap.map_smul, Function.comp, smul_eq_mul] at h0
  simp only [Tseitin.coeffLin, LinearMap.coe_mk, AddHom.coe_mk] at h0
  have hsub : ∀ j ∈ S, g j * MvPolynomial.coeff (τ a) (R j).val =
      if j = a then g j * signs a else 0 := by
    intro j _
    rw [hkronecker a j]
    by_cases h : a = j
    · subst h
      simp
    · simp [h, show j ≠ a from fun h' => h (h' ▸ rfl)]
  rw [Finset.sum_congr rfl hsub, Finset.sum_ite_eq' S a, if_pos ha] at h0
  rcases hsigns a with hs | hs <;> simp [hs] at h0 <;> exact h0

/-- Build matrix-level closure from explicit Kronecker coefficient data. -/
theorem selCon_kronecker_matrix_logscale_from_data (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804)
    (hData : selCon_kronecker_data_logscale M n hn804) :
    selCon_kronecker_matrix_logscale M n hn804 := by
  rcases hData with ⟨R, τ, signs, hsigns, hkronecker⟩
  refine ⟨R, linearIndependent_from_kronecker M n _ R τ signs hsigns hkronecker⟩

/-- Kronecker/identity-minor choose-rank closure at logscale.
This is the linear-independence matrix claim after κ-level derivative expansion. -/
def selCon_choose_rank_logscale (M : DTM) (n : ℕ)
    (_hn804 : n ≥ 2 ^ 804) : Prop :=
  Nat.choose (latentBaseVars M n) (Nat.log 2 n) ≤
    mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (latentCompiledPoly M n)

private theorem finrank_submodule_ge_card
    (M : DTM) (n : ℕ) (K : ℕ)
    (R : Fin K →
      ↥(mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n)))
    (hlin : LinearIndependent ℚ (Subtype.val ∘ R)) :
    K ≤ Module.finrank ℚ
      (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n)) := by
  have hrange : ∀ i, (Subtype.val ∘ R) i ∈
      mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n) := fun i => (R i).2
  have hspan : Submodule.span ℚ (Set.range (Subtype.val ∘ R)) ≤
      mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n) :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hrange)
  have hcard := finrank_span_eq_card hlin
  haveI : Module.Finite ℚ
      (Submodule.span ℚ (Set.range (Subtype.val ∘ R))) :=
    Module.Finite.span_of_finite ℚ (Set.finite_range _)
  have hmono := Submodule.finrank_mono hspan
  simp [Fintype.card_fin] at hcard
  omega

/-- Rank closure from explicit Kronecker matrix linear-independence data. -/
theorem selCon_choose_rank_logscale_from_matrix (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804)
    (hMat : selCon_kronecker_matrix_logscale M n hn804) :
    selCon_choose_rank_logscale M n hn804 := by
  rcases hMat with ⟨R, hlin⟩
  unfold selCon_choose_rank_logscale mlBlockedSpdpRank
  exact finrank_submodule_ge_card M n _ R hlin

/-- Rank closure directly from explicit Kronecker coefficient data. -/
theorem selCon_choose_rank_logscale_from_data (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804)
    (hData : selCon_kronecker_data_logscale M n hn804) :
    selCon_choose_rank_logscale M n hn804 := by
  exact selCon_choose_rank_logscale_from_matrix M n hn804
    (selCon_kronecker_matrix_logscale_from_data M n hn804 hData)

/-- Base numeric lower bound at logscale for choose(n, log₂ n), uniform from n ≥ 2^40.
Paper-faithful combinatorial step (same arithmetic backbone as BinomialBound2). -/
theorem choose_numeric_logscale_base (n : ℕ) (hn40 : 2 ^ 40 ≤ n) :
    n ^ (Nat.log 2 n / 4) ≤ Nat.choose n (Nat.log 2 n) := by
  set k := Nat.log 2 n
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hq4 : (n / (30 * k)) ^ 4 ≥ n := by
      -- quotient_pow4_ge in BinomialBound is parameterized by log₂ n; rewrite k
      have := BinomialBound.quotient_pow4_ge n hn40
      simpa [k] using this
    have hq1 : 1 ≤ n / (30 * k) := by
      apply Nat.div_pos
      · calc
          30 * k ≤ 2 ^ (k / 2) := BinomialBound.thirty_k_le_pow_half k (by
            have h40 : 40 ≤ k := by
              have h1 : Nat.log 2 (2 ^ 40) = 40 := Nat.log_pow (by norm_num) 40
              have h2 : Nat.log 2 (2 ^ 40) ≤ k := by
                simpa [k] using Nat.log_mono (by norm_num) le_rfl hn40
              omega
            omega)
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ n := by
            have hn_ne : n ≠ 0 := by omega
            simpa [k] using (Nat.pow_log_le_self 2 hn_ne)
      · omega
    have hpow40 : (n / (30 * k)) ^ k ≥ n ^ (k / 4) :=
      BinomialBound.pow_lift_four (n / (30 * k)) n k hq4 hq1
    have hchoose_div : Nat.choose n k ≥ (n / k) ^ k :=
      BinomialBound.choose_ge_div_pow n k hkpos
    have hdiv_mono : n / (30 * k) ≤ n / k := by
      -- larger denominator gives smaller quotient
      exact Nat.div_le_div_left (by omega) hkpos
    have hpow_mono : (n / (30 * k)) ^ k ≤ (n / k) ^ k :=
      Nat.pow_le_pow_left hdiv_mono k
    have hchoose40 : Nat.choose n k ≥ n ^ (k / 4) := by
      exact le_trans hpow40 (le_trans hpow_mono hchoose_div)
    simpa [k] using hchoose40

/-- Numeric choose-vs-n closure at logscale (combinatorial side). -/
def selCon_choose_numeric_logscale (M : DTM) (n : ℕ)
    (_hn804 : n ≥ 2 ^ 804) : Prop :=
  n ^ (Nat.log 2 n / 4) ≤ Nat.choose (latentBaseVars M n) (Nat.log 2 n)

/-- Numeric closure proved from base choose bound + latentBaseVars monotonicity. -/
theorem selCon_choose_numeric_logscale_proved (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804) :
    selCon_choose_numeric_logscale M n hn804 := by
  unfold selCon_choose_numeric_logscale
  have hpow : (2 : ℕ) ^ 40 ≤ 2 ^ 804 := by
    exact Nat.pow_le_pow_right (by norm_num) (by decide : 40 ≤ 804)
  have hn40 : 2 ^ 40 ≤ n := le_trans hpow hn804
  have hbase : n ^ (Nat.log 2 n / 4) ≤ Nat.choose n (Nat.log 2 n) :=
    choose_numeric_logscale_base n hn40
  have hmon : Nat.choose n (Nat.log 2 n) ≤
      Nat.choose (latentBaseVars M n) (Nat.log 2 n) := by
    apply Nat.choose_le_choose
    exact latentBaseVars_ge_n M n
  exact le_trans hbase hmon

/-- Final κ-level NP closure package.
Split into:
1) choose-rank (Kronecker linear independence)
2) choose numeric lower bound -/
def selCon_kronecker_linear_independence_logscale (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804) : Prop :=
  selCon_choose_rank_logscale M n hn804 ∧
  selCon_choose_numeric_logscale M n hn804

/-- Assemble NP package from explicit Kronecker data + numeric choose closure. -/
theorem selCon_kronecker_linear_independence_logscale_from_data_numeric
    (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804)
    (hData : selCon_kronecker_data_logscale M n hn804)
    (hNum : selCon_choose_numeric_logscale M n hn804) :
    selCon_kronecker_linear_independence_logscale M n hn804 := by
  refine ⟨selCon_choose_rank_logscale_from_data M n hn804 hData, hNum⟩

/-- Numeric closure is now proved internally; NP package can be assembled from data only. -/
theorem selCon_kronecker_linear_independence_logscale_from_data
    (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804)
    (hData : selCon_kronecker_data_logscale M n hn804) :
    selCon_kronecker_linear_independence_logscale M n hn804 := by
  exact selCon_kronecker_linear_independence_logscale_from_data_numeric
    M n hn804 hData (selCon_choose_numeric_logscale_proved M n hn804)

/-- Closing theorem for NP side from the two logscale closures. -/
theorem latent_hard_witness_logscale_from_kronecker (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804)
    (hK : selCon_kronecker_linear_independence_logscale M n hn804) :
    n ^ (Nat.log 2 n / 4) ≤
      mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n) := by
  rcases hK with ⟨hRank, hNum⟩
  exact le_trans hNum hRank

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
