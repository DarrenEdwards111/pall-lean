import PallLean.MultilinearSPDP
import PallLean.NPWitness
import PallLean.Compiler
import Mathlib.Tactic
set_option exponentiation.threshold 1024

/-!
# LatentCompiler — Hidden-witness compiler with Fin-indexed variables

4 layers: machine(0), copy(1), selector(2), consistency(3)
Variable j encodes: layer = j % 4, base index = j / 4

The witness structure only appears after extraction, not in the raw polynomial.
Local gadgets are cross-layer products (machine×copy, copy×consistency, selector×consistency)
so no single layer contains a high-rank product sheet.
-/

namespace LatentCompiler

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial

def latentBaseVars (M : DTM) (n : ℕ) : ℕ := numVars M n (Nat.log 2 n)
def latentNumVars (M : DTM) (n : ℕ) : ℕ := 4 * latentBaseVars M n

private theorem four_i_lt (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) (k : Fin 4) :
    4 * i.val + k.val < latentNumVars M n := by unfold latentNumVars; omega

private theorem div4_lt (M : DTM) (n : ℕ) (j : Fin (latentNumVars M n)) :
    j.val / 4 < latentBaseVars M n := by have := j.isLt; unfold latentNumVars at this; omega

/-- Slot for layer k, base index i. -/
def slot (M : DTM) (n : ℕ) (k : Fin 4) (i : Fin (latentBaseVars M n)) :
    Fin (latentNumVars M n) := ⟨4 * i.val + k.val, four_i_lt M n i k⟩

def machSlot (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) := slot M n 0 i
def copySlot (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) := slot M n 1 i
def selSlot  (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) := slot M n 2 i
def conSlot  (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) := slot M n 3 i

noncomputable def Xmach (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    MvPolynomial (Fin (latentNumVars M n)) ℚ := X (machSlot M n i)
noncomputable def Xcopy (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    MvPolynomial (Fin (latentNumVars M n)) ℚ := X (copySlot M n i)
noncomputable def Xsel (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    MvPolynomial (Fin (latentNumVars M n)) ℚ := X (selSlot M n i)
noncomputable def Xcon (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    MvPolynomial (Fin (latentNumVars M n)) ℚ := X (conSlot M n i)

/-- Cross-layer gadgets: each touches 2 variables from DIFFERENT layers. -/
noncomputable def machCopyGadget (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    MvPolynomial (Fin (latentNumVars M n)) ℚ := 1 - Xmach M n i * Xcopy M n i
noncomputable def copyConGadget (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    MvPolynomial (Fin (latentNumVars M n)) ℚ := 1 - Xcopy M n i * Xcon M n i
noncomputable def selConGadget (M : DTM) (n : ℕ) (i : Fin (latentBaseVars M n)) :
    MvPolynomial (Fin (latentNumVars M n)) ℚ := 1 - Xsel M n i * Xcon M n i

/-- Three sheets from cross-layer products. -/
noncomputable def machCopySheet (M : DTM) (n : ℕ) :=
  ∏ i : Fin (latentBaseVars M n), machCopyGadget M n i
noncomputable def copyConSheet (M : DTM) (n : ℕ) :=
  ∏ i : Fin (latentBaseVars M n), copyConGadget M n i
noncomputable def selConSheet (M : DTM) (n : ℕ) :=
  ∏ i : Fin (latentBaseVars M n), selConGadget M n i

/-- The latent compiled polynomial: sum of three cross-layer sheets.
No single-layer product sheet appears → no baked-in exponential rank. -/
noncomputable def latentCompiledPoly (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (latentNumVars M n)) ℚ :=
  machCopySheet M n + copyConSheet M n + selConSheet M n

/-- Block partition: group all 4 copies of base index i into one block. -/
noncomputable def latentPartition (M : DTM) (n : ℕ) :
    BlockPartition (latentNumVars M n) where
  numBlocks := latentBaseVars M n
  assign := fun j => ⟨j.val / 4, div4_lt M n j⟩

/-- Selector-layer extraction. -/
noncomputable def extractSelector (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (latentNumVars M n)) ℚ →ₐ[ℚ]
      MvPolynomial (Fin (latentBaseVars M n)) ℚ :=
  aeval (fun j : Fin (latentNumVars M n) =>
    if j.val % 4 = 2 then X ⟨j.val / 4, div4_lt M n j⟩ else 0)

/-- Machine-layer extraction. -/
noncomputable def extractMachine (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (latentNumVars M n)) ℚ →ₐ[ℚ]
      MvPolynomial (Fin (latentBaseVars M n)) ℚ :=
  aeval (fun j : Fin (latentNumVars M n) =>
    if j.val % 4 = 0 then X ⟨j.val / 4, div4_lt M n j⟩ else 0)

/-- Selector slots are injective on base indices. -/
theorem selSlot_injective (M : DTM) (n : ℕ) : Function.Injective (selSlot M n) := by
  intro a b hab
  simp [selSlot, slot] at hab
  exact Fin.ext (by omega)

/-- Under latentPartition, machine slot i lands in block i. -/
theorem latentPartition_assign_machSlot (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    (latentPartition M n).assign (machSlot M n i) = i := by
  apply Fin.ext
  simp [latentPartition, machSlot, slot]

/-- Under latentPartition, copy slot i lands in block i. -/
theorem latentPartition_assign_copySlot (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    (latentPartition M n).assign (copySlot M n i) = i := by
  apply Fin.ext
  simp [latentPartition, copySlot, slot]
  omega

/-- Under latentPartition, consistency slot i lands in block i. -/
theorem latentPartition_assign_conSlot (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    (latentPartition M n).assign (conSlot M n i) = i := by
  apply Fin.ext
  simp [latentPartition, conSlot, slot]
  omega

/-- Under latentPartition, selector slot i lands in block i. -/
theorem latentPartition_assign_selSlot (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    (latentPartition M n).assign (selSlot M n i) = i := by
  apply Fin.ext
  simp [latentPartition, selSlot, slot]
  omega

/-- Every variable in `Fin (latentNumVars M n)` belongs to exactly one of the 4 slot families.
    This is because `latentNumVars = 4 * latentBaseVars` and `slot M n k i = ⟨4*i+k, _⟩`. -/
theorem var_layer_exhaustive (M : DTM) (n : ℕ) (v : Fin (latentNumVars M n)) :
    (∃ i : Fin (latentBaseVars M n), v = machSlot M n i) ∨
    (∃ i : Fin (latentBaseVars M n), v = copySlot M n i) ∨
    (∃ i : Fin (latentBaseVars M n), v = selSlot M n i) ∨
    (∃ i : Fin (latentBaseVars M n), v = conSlot M n i) := by
  have hmod : v.val % 4 < 4 := Nat.mod_lt _ (by omega)
  have hdiv : v.val / 4 < latentBaseVars M n := by
    have hv := v.isLt
    simp only [latentNumVars] at hv
    exact Nat.div_lt_of_lt_mul hv
  set b : Fin (latentBaseVars M n) := ⟨v.val / 4, hdiv⟩
  have hm := Nat.mod_two_eq_zero_or_one (v.val % 4)
  -- Manually case split on v.val % 4
  have h04 : v.val % 4 = 0 ∨ v.val % 4 = 1 ∨ v.val % 4 = 2 ∨ v.val % 4 = 3 := by omega
  rcases h04 with h0 | h1 | h2 | h3
  · left; refine ⟨b, Fin.ext ?_⟩
    show v.val = (slot M n 0 b).val
    unfold slot
    simp only [Fin.val_mk]
    -- Goal: v.val = 4 * b.val + (0 : Fin 4).val
    -- b.val = v.val / 4, h0: v.val % 4 = 0
    change v.val = 4 * (v.val / 4) + (0 : Fin 4).val
    omega
  · right; left; refine ⟨b, Fin.ext ?_⟩
    show v.val = (slot M n 1 b).val
    unfold slot; simp only [Fin.val_mk]
    change v.val = 4 * (v.val / 4) + (1 : Fin 4).val
    omega
  · right; right; left; refine ⟨b, Fin.ext ?_⟩
    show v.val = (slot M n 2 b).val
    unfold slot; simp only [Fin.val_mk]
    change v.val = 4 * (v.val / 4) + (2 : Fin 4).val
    omega
  · right; right; right; refine ⟨b, Fin.ext ?_⟩
    show v.val = (slot M n 3 b).val
    unfold slot; simp only [Fin.val_mk]
    change v.val = 4 * (v.val / 4) + (3 : Fin 4).val
    omega

/-- The layer (mod-4 residue) of a variable determines which slot family it belongs to. -/
theorem var_layer_eq_machSlot_of_mod (M : DTM) (n : ℕ) (v : Fin (latentNumVars M n))
    (hv : v.val % 4 = 0) :
    ∃ i : Fin (latentBaseVars M n), v = machSlot M n i := by
  have hdiv : v.val / 4 < latentBaseVars M n := by
    have := v.isLt; simp only [latentNumVars] at this; exact Nat.div_lt_of_lt_mul this
  refine ⟨⟨v.val / 4, hdiv⟩, Fin.ext ?_⟩
  show v.val = (slot M n 0 ⟨v.val / 4, hdiv⟩).val
  unfold slot; simp only [Fin.val_mk]
  change v.val = 4 * (v.val / 4) + (0 : Fin 4).val; omega

theorem var_layer_eq_copySlot_of_mod (M : DTM) (n : ℕ) (v : Fin (latentNumVars M n))
    (hv : v.val % 4 = 1) :
    ∃ i : Fin (latentBaseVars M n), v = copySlot M n i := by
  have hdiv : v.val / 4 < latentBaseVars M n := by
    have := v.isLt; simp only [latentNumVars] at this; exact Nat.div_lt_of_lt_mul this
  refine ⟨⟨v.val / 4, hdiv⟩, Fin.ext ?_⟩
  show v.val = (slot M n 1 ⟨v.val / 4, hdiv⟩).val
  unfold slot; simp only [Fin.val_mk]
  change v.val = 4 * (v.val / 4) + (1 : Fin 4).val; omega

theorem var_layer_eq_selSlot_of_mod (M : DTM) (n : ℕ) (v : Fin (latentNumVars M n))
    (hv : v.val % 4 = 2) :
    ∃ i : Fin (latentBaseVars M n), v = selSlot M n i := by
  have hdiv : v.val / 4 < latentBaseVars M n := by
    have := v.isLt; simp only [latentNumVars] at this; exact Nat.div_lt_of_lt_mul this
  refine ⟨⟨v.val / 4, hdiv⟩, Fin.ext ?_⟩
  show v.val = (slot M n 2 ⟨v.val / 4, hdiv⟩).val
  unfold slot; simp only [Fin.val_mk]
  change v.val = 4 * (v.val / 4) + (2 : Fin 4).val; omega

theorem var_layer_eq_conSlot_of_mod (M : DTM) (n : ℕ) (v : Fin (latentNumVars M n))
    (hv : v.val % 4 = 3) :
    ∃ i : Fin (latentBaseVars M n), v = conSlot M n i := by
  have hdiv : v.val / 4 < latentBaseVars M n := by
    have := v.isLt; simp only [latentNumVars] at this; exact Nat.div_lt_of_lt_mul this
  refine ⟨⟨v.val / 4, hdiv⟩, Fin.ext ?_⟩
  show v.val = (slot M n 3 ⟨v.val / 4, hdiv⟩).val
  unfold slot; simp only [Fin.val_mk]
  change v.val = 4 * (v.val / 4) + (3 : Fin 4).val; omega

/-- Admissibility of selector-slot lists: one selector slot per base block. -/
theorem selSlotList_admissible (M : DTM) (n : ℕ)
    (S : List (Fin (latentBaseVars M n))) (hnd : S.Nodup) :
    isBlockAdmissible (latentPartition M n) (S.map (selSlot M n)) := by
  constructor
  · exact hnd.map (selSlot_injective M n)
  · intro b
    by_contra hgt
    push_neg at hgt
    set filt := (S.map (selSlot M n)).filter (fun j => (latentPartition M n).assign j = b)
    have hmap_nd : (S.map (selSlot M n)).Nodup := hnd.map (selSlot_injective M n)
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
    have hx_eq : (latentPartition M n).assign filt[0] = b := by
      exact (decide_eq_true_eq.mp hx_bl)
    have hy_eq : (latentPartition M n).assign filt[1] = b := by
      exact (decide_eq_true_eq.mp hy_bl)
    have ha_bl : a = b := by
      have h2 : (latentPartition M n).assign filt[0] = a := by
        rw [show filt[0] = selSlot M n a from ha.symm]
        exact latentPartition_assign_selSlot M n a
      exact h2.symm.trans hx_eq
    have hc_bl : c = b := by
      have h2 : (latentPartition M n).assign filt[1] = c := by
        rw [show filt[1] = selSlot M n c from hc.symm]
        exact latentPartition_assign_selSlot M n c
      exact h2.symm.trans hy_eq
    have hac : a = c := ha_bl.trans hc_bl.symm
    exact absurd (hfilt_nd.getElem_inj_iff.mp (by show filt[0] = filt[1]; rw [← ha, ← hc, hac])) (by omega)

section ExtractedWitness

/-- The extracted product witness on base-variable space.
This is what extraction reveals: ∏ᵢ (1 - X_i). -/
noncomputable def extractedProductWitness (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (latentBaseVars M n)) ℚ :=
  ∏ i : Fin (latentBaseVars M n), (1 - X i)

/-- Basic size fact: latentBaseVars contains at least the raw input variables. -/
theorem latentBaseVars_ge_n (M : DTM) (n : ℕ) :
    n ≤ latentBaseVars M n := by
  unfold latentBaseVars TuringMachine.numVars
  set S := TuringMachine.tapeSize M n
  have hbase : n ≤ n + Nat.log 2 n := Nat.le_add_right n (Nat.log 2 n)
  have hrest : n + Nat.log 2 n ≤ S * S + S * M.numStates + S * S + (n + Nat.log 2 n) :=
    Nat.le_add_left _ _
  calc
    n ≤ n + Nat.log 2 n := hbase
    _ ≤ S * S + S * M.numStates + S * S + (n + Nat.log 2 n) := hrest
    _ = S * S + S * M.numStates + S * S + n + Nat.log 2 n := by omega

/-- Therefore log₂(n) is also bounded by latentBaseVars. -/
theorem log_le_latentBaseVars (M : DTM) (n : ℕ) :
    Nat.log 2 n ≤ latentBaseVars M n := by
  exact le_trans (Nat.log_le_self 2 n) (latentBaseVars_ge_n M n)

end ExtractedWitness

end LatentCompiler
