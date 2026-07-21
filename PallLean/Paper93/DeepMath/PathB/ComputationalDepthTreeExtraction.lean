import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFloorFanout
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDAGTwoKill

/-!
# Tree extraction: the first above-floor lower bound — `cbudget allEq3Fin ≥ 6`

The final assembly of the floor-attainment structure theorem, cashed out on the
slack seed.  A 5-gate circuit for `AllEqual₃` (three dependent variables, cone
floor `2·3 − 1 = 5`) is pinned by census + fanout into a read-once tree:

* the output is a binary gate; exactly two binary gates exist; the three `var`
  gates carry the three distinct variables (`var_position_exists` + injectivity);
* the second binary gate sits at the arithmetically-identified position
  `p = 6 − (w₀+w₁+w₂)`; the **capacity partition** (four wires, each read at least
  once in range, fanout at most one, at most two reads per gate) forces the two
  gates' read-sets to partition `{0,1,2,3}` exactly — junk references, double
  reads, and self-loops all die by cardinality;
* the output therefore reads the second gate and one lone variable `x_t`, whose
  gate nobody else reads — so the other operand wire is **blind** to `x_t`
  (`wire_inv`), extracting `allEq3Fin = op' (x_t, u)` with `u` free of `x_t`;
* `allEq3_no_split_a/b/c` refute all three cases.

Hence **`cbudget_allEq3Fin : 6 ≤ cbudget allEq3Fin` (proved)** — the model's first
lower bound strictly above the cone floor.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- Every dependent variable owns a cone `var` gate. -/
theorem var_position_exists {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hs : 0 < c.length) (i : Fin n) (hi : i ∈ depSet f) :
    ∃ w, w ∈ cone c ∧ c.getD w (.cst false) = CGate.var i := by
  obtain ⟨x, b, hxb⟩ := mem_depSet.mp hi
  by_contra hno
  push_neg at hno
  have hnv : ∀ w, InCone c w → c.getD w (.cst false) ≠ CGate.var i := fun w hw he =>
    hno w (mem_cone.mpr ⟨inCone_lt hs hw, hw⟩) he
  refine hxb ?_
  rw [← hcomp (Function.update x i b), ← hcomp x, output_eq_wire, output_eq_wire]
  exact cone_wire_agree c i x b hs hnv _ InCone.root

/-- The seed as a slice function. -/
def allEq3Fin : (Fin 3 → Bool) → Bool := fun x => allEq3 (x 0) (x 1) (x 2)

theorem depSet_allEq3Fin : depSet allEq3Fin = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro j
  fin_cases j
  · exact mem_depSet.mpr ⟨fun _ => true, false, by decide⟩
  · exact mem_depSet.mpr ⟨fun _ => true, false, by decide⟩
  · exact mem_depSet.mpr ⟨fun _ => true, false, by decide⟩

theorem depSet_allEq3Fin_card : (depSet allEq3Fin).card = 3 := by
  rw [depSet_allEq3Fin, Finset.card_univ, Fintype.card_fin]

/-- **No 5-gate circuit computes AllEqual₃.** -/
theorem no_five_gate_allEq3 (c : List (CGate 3)) (hcomp : computes c allEq3Fin)
    (hlen5 : c.length = 5) : False := by
  classical
  have hs : 0 < c.length := by omega
  obtain ⟨hconeC, hvarsC, hbins⟩ := floor_census allEq3Fin c hcomp
    (by rw [hlen5, depSet_allEq3Fin_card])
  rw [depSet_allEq3Fin_card] at hvarsC
  -- the cone is all of range 5
  have hconeAll : cone c = Finset.range c.length :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      (by rw [Finset.card_range, hconeC])
  have hmemc : ∀ q, q < 5 → q ∈ cone c := by
    intro q hq
    rw [hconeAll, Finset.mem_range]
    omega
  -- var positions for the three variables
  obtain ⟨w₀, hw₀c, hg₀⟩ := var_position_exists allEq3Fin c hcomp hs 0
    (by rw [depSet_allEq3Fin]; exact Finset.mem_univ _)
  obtain ⟨w₁, hw₁c, hg₁⟩ := var_position_exists allEq3Fin c hcomp hs 1
    (by rw [depSet_allEq3Fin]; exact Finset.mem_univ _)
  obtain ⟨w₂, hw₂c, hg₂⟩ := var_position_exists allEq3Fin c hcomp hs 2
    (by rw [depSet_allEq3Fin]; exact Finset.mem_univ _)
  have hw₀5 : w₀ < 5 := by have := (mem_cone.mp hw₀c).1; omega
  have hw₁5 : w₁ < 5 := by have := (mem_cone.mp hw₁c).1; omega
  have hw₂5 : w₂ < 5 := by have := (mem_cone.mp hw₂c).1; omega
  have hne01 : w₀ ≠ w₁ := by
    intro he
    rw [he, hg₁] at hg₀
    exact absurd (CGate.var.inj hg₀) (by decide)
  have hne02 : w₀ ≠ w₂ := by
    intro he
    rw [he, hg₂] at hg₀
    exact absurd (CGate.var.inj hg₀) (by decide)
  have hne12 : w₁ ≠ w₂ := by
    intro he
    rw [he, hg₂] at hg₁
    exact absurd (CGate.var.inj hg₁) (by decide)
  -- the output gate
  have h4c : (4 : ℕ) ∈ cone c := hmemc 4 (by omega)
  cases hg4 : c.getD 4 (.cst false) with
  | var i =>
    have hout : ∀ x : Fin 3 → Bool, allEq3Fin x = x i := by
      intro x
      have h1 := hcomp x
      rw [output_eq_wire, show c.length - 1 = 4 from by omega,
        wire_eq c x (show (4 : ℕ) < c.length by omega), hg4] at h1
      exact h1.symm
    have := hout (fun _ => false)
    revert this
    decide
  | cst v =>
    have hb := hbins 4 h4c (by rw [hg4]; rintro ⟨i', hi'⟩; simp at hi')
    rw [hg4] at hb
    simp [inSlots] at hb
  | un op j =>
    have hb := hbins 4 h4c (by rw [hg4]; rintro ⟨i', hi'⟩; simp at hi')
    rw [hg4] at hb
    simp [inSlots] at hb
  | bin op j k =>
  -- var positions avoid the output
  have hw₀4 : w₀ ≠ 4 := by
    intro he
    rw [he, hg4] at hg₀
    simp at hg₀
  have hw₁4 : w₁ ≠ 4 := by
    intro he
    rw [he, hg4] at hg₁
    simp at hg₁
  have hw₂4 : w₂ ≠ 4 := by
    intro he
    rw [he, hg4] at hg₂
    simp at hg₂
  -- the second binary position, arithmetically
  set p := 6 - (w₀ + w₁ + w₂) with hpdef
  have hw₀3 : w₀ ≤ 3 := by omega
  have hw₁3 : w₁ ≤ 3 := by omega
  have hw₂3 : w₂ ≤ 3 := by omega
  have hp_le : p ≤ 3 := by omega
  have hp0 : p ≠ w₀ := by omega
  have hp1 : p ≠ w₁ := by omega
  have hp2 : p ≠ w₂ := by omega
  have hclass : ∀ q, q < 4 → q = w₀ ∨ q = w₁ ∨ q = w₂ ∨ q = p := by
    intro q hq
    omega
  -- p's gate is binary: otherwise four var positions
  have hgp_notvar : ¬ ∃ i' : Fin 3, c.getD p (.cst false) = CGate.var i' := by
    rintro ⟨i', hi'⟩
    have hsub4 : ({w₀, w₁, w₂, p} : Finset ℕ) ⊆ coneVars c := by
      intro q hq
      rw [coneVars, Finset.mem_filter]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact ⟨hw₀c, ⟨0, hg₀⟩⟩
      · exact ⟨hw₁c, ⟨1, hg₁⟩⟩
      · exact ⟨hw₂c, ⟨2, hg₂⟩⟩
      · exact ⟨hmemc p (by omega), ⟨i', hi'⟩⟩
    have hcard4 : ({w₀, w₁, w₂, p} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have := Finset.card_le_card hsub4
    omega
  have hgp_slots := hbins p (hmemc p (by omega)) hgp_notvar
  -- reader classification for positions below the output
  have hreader : ∀ s, s < 4 →
      (s ∈ gateReads (c.getD p (.cst false)) ∧ s < p)
        ∨ s ∈ gateReads (c.getD 4 (.cst false)) := by
    intro s hs4
    have hsc : s ∈ cone c := hmemc s (by omega)
    obtain ⟨hslt, hscone⟩ := mem_cone.mp hsc
    cases hscone with
    | root => omega
    | step hw hjm hjw =>
      rename_i w'
      have hw5 : w' < c.length := inCone_lt hs hw
      have hw_notvar : ∀ (i' : Fin 3), c.getD w' (.cst false) ≠ CGate.var i' := by
        intro i' he
        rw [he] at hjm
        simp [gateReads] at hjm
      have hwne0 : w' ≠ w₀ := fun he => hw_notvar 0 (by rw [he]; exact hg₀)
      have hwne1 : w' ≠ w₁ := fun he => hw_notvar 1 (by rw [he]; exact hg₁)
      have hwne2 : w' ≠ w₂ := fun he => hw_notvar 2 (by rw [he]; exact hg₂)
      have : w' = p ∨ w' = 4 := by omega
      rcases this with rfl | rfl
      · exact Or.inl ⟨hjm, hjw⟩
      · exact Or.inr hjm
  -- the capacity partition
  have hAcard : (gateReads (c.getD p (.cst false))).card ≤ 2 :=
    le_trans (gateReads_card_le _) (le_of_eq hgp_slots)
  have hBcard : (gateReads (c.getD 4 (.cst false))).card ≤ 2 := by
    rw [hg4]
    exact le_trans (gateReads_card_le _) (inSlots_le_two _)
  have hSsub : (Finset.range 4)
      ⊆ gateReads (c.getD p (.cst false)) ∪ gateReads (c.getD 4 (.cst false)) := by
    intro s hsr
    rw [Finset.mem_range] at hsr
    rw [Finset.mem_union]
    rcases hreader s hsr with ⟨hA, -⟩ | hB
    · exact Or.inl hA
    · exact Or.inr hB
  have hSeq : (Finset.range 4)
      = gateReads (c.getD p (.cst false)) ∪ gateReads (c.getD 4 (.cst false)) := by
    refine Finset.eq_of_subset_of_card_le hSsub ?_
    rw [Finset.card_range]
    exact le_trans (Finset.card_union_le _ _) (by omega)
  have hinter : (gateReads (c.getD p (.cst false)) ∩ gateReads (c.getD 4 (.cst false))).card
      = 0 := by
    have hu := Finset.card_union_add_card_inter (gateReads (c.getD p (.cst false)))
      (gateReads (c.getD 4 (.cst false)))
    have h4' : (gateReads (c.getD p (.cst false)) ∪ gateReads (c.getD 4 (.cst false))).card
        = 4 := by
      rw [← hSeq, Finset.card_range]
    omega
  have hdisj : ∀ s, s ∈ gateReads (c.getD p (.cst false)) →
      s ∈ gateReads (c.getD 4 (.cst false)) → False := by
    intro s hsA hsB
    have : s ∈ gateReads (c.getD p (.cst false)) ∩ gateReads (c.getD 4 (.cst false)) :=
      Finset.mem_inter.mpr ⟨hsA, hsB⟩
    rw [Finset.card_eq_zero] at hinter
    rw [hinter] at this
    exact absurd this (Finset.notMem_empty _)
  -- p is read by the output
  have hpB : p ∈ gateReads (c.getD 4 (.cst false)) := by
    rcases hreader p (by omega) with ⟨-, hlt⟩ | hB
    · omega
    · exact hB
  -- the output's other source t is a var position, unread by p
  have hBset : gateReads (c.getD (4:ℕ) (.cst false)) = {j, k} := by rw [hg4]; rfl
  have hjk_ne : j ≠ k := by
    intro he
    have : ({j, k} : Finset ℕ).card ≤ 1 := by
      rw [he]
      simp
    have hB2 : (gateReads (c.getD (4:ℕ) (.cst false))).card = 2 := by
      have hu := Finset.card_union_add_card_inter (gateReads (c.getD p (.cst false)))
        (gateReads (c.getD 4 (.cst false)))
      have h4' : (gateReads (c.getD p (.cst false)) ∪ gateReads (c.getD 4 (.cst false))).card
          = 4 := by rw [← hSeq, Finset.card_range]
      omega
    rw [hBset] at hB2
    omega
  have hpjk : p = j ∨ p = k := by
    have := hpB
    rw [hBset] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    exact this
  -- t := the other source
  obtain ⟨t, htB, htne, hslot⟩ :
      ∃ t, t ∈ gateReads (c.getD (4:ℕ) (.cst false)) ∧ t ≠ p ∧
        ((j = t ∧ k = p) ∨ (j = p ∧ k = t)) := by
    rcases hpjk with hpj | hpk
    · exact ⟨k, by rw [hBset]; simp, fun he => hjk_ne (hpj.symm.trans he.symm),
        Or.inr ⟨hpj.symm, rfl⟩⟩
    · exact ⟨j, by rw [hBset]; simp, fun he => hjk_ne (he.trans hpk),
        Or.inl ⟨rfl, hpk.symm⟩⟩
  have ht4 : t < 4 := by
    have : t ∈ (Finset.range 4) := by
      rw [hSeq, Finset.mem_union]
      exact Or.inr htB
    rwa [Finset.mem_range] at this
  have htnotA : t ∉ gateReads (c.getD p (.cst false)) := fun hA => hdisj t hA htB
  -- t is one of the var positions
  have htvar : t = w₀ ∨ t = w₁ ∨ t = w₂ := by omega
  -- the representation
  have hfx : ∀ x : Fin 3 → Bool, allEq3Fin x
      = op ((runFrom x [] (c.take 4)).getD j false)
          ((runFrom x [] (c.take 4)).getD k false) := by
    intro x
    have h1 := hcomp x
    rw [output_eq_wire, show c.length - 1 = 4 from by omega,
      wire_eq c x (show (4 : ℕ) < c.length by omega), hg4] at h1
    exact h1.symm
  have hVp : ∀ x : Fin 3 → Bool, (runFrom x [] (c.take 4)).getD p false = wire c x p :=
    fun x => wire_prefix c x (by omega) (by omega)
  have hVt : ∀ x : Fin 3 → Bool, (runFrom x [] (c.take 4)).getD t false = wire c x t :=
    fun x => wire_prefix c x (by omega) (by omega)
  -- uniform equation: allEq3Fin = op' (wire t) (wire p)
  obtain ⟨op', hrep0⟩ : ∃ op' : Bool → Bool → Bool, ∀ x : Fin 3 → Bool,
      allEq3Fin x = op' (wire c x t) (wire c x p) := by
    rcases hslot with ⟨hjt, hkp⟩ | ⟨hjp, hkt⟩
    · exact ⟨op, fun x => by rw [hfx x, hjt, hkp, hVp, hVt]⟩
    · exact ⟨fun a z => op z a, fun x => by rw [hfx x, hjp, hkt, hVp, hVt]⟩
  -- the blindness kit, per variable
  have hblind : ∀ (iT : Fin 3), c.getD t (.cst false) = CGate.var iT →
      (∀ x, wire c x t = x iT) ∧
      (∀ (x : Fin 3 → Bool) (b : Bool), wire c (Function.update x iT b) p = wire c x p) := by
    intro iT hgt
    constructor
    · intro x
      rw [wire_eq c x (show t < c.length by omega), hgt]
      rfl
    · intro x b
      refine wire_inv c iT t (p + 1) (by omega) ?_ ?_ x b p (by omega) (by omega)
      · intro v hv1 hv2 hmem
        have hv4 : v < 4 := by omega
        rcases hclass v hv4 with rfl | rfl | rfl | rfl
        · rw [hg₀] at hmem
          simp [gateReads] at hmem
        · rw [hg₁] at hmem
          simp [gateReads] at hmem
        · rw [hg₂] at hmem
          simp [gateReads] at hmem
        · exact htnotA hmem
      · intro v hv hvt he
        have hv4 : v < 4 := by omega
        rcases hclass v hv4 with rfl | rfl | rfl | rfl
        · rw [hg₀] at he
          have h0 : (0 : Fin 3) = iT := CGate.var.inj he
          rcases htvar with rfl | rfl | rfl
          · exact hvt rfl
          · rw [hg₁] at hgt
            have := CGate.var.inj hgt
            rw [← this] at h0
            exact absurd h0 (by decide)
          · rw [hg₂] at hgt
            have := CGate.var.inj hgt
            rw [← this] at h0
            exact absurd h0 (by decide)
        · rw [hg₁] at he
          have h0 : (1 : Fin 3) = iT := CGate.var.inj he
          rcases htvar with rfl | rfl | rfl
          · rw [hg₀] at hgt
            have := CGate.var.inj hgt
            rw [← this] at h0
            exact absurd h0 (by decide)
          · exact hvt rfl
          · rw [hg₂] at hgt
            have := CGate.var.inj hgt
            rw [← this] at h0
            exact absurd h0 (by decide)
        · rw [hg₂] at he
          have h0 : (2 : Fin 3) = iT := CGate.var.inj he
          rcases htvar with rfl | rfl | rfl
          · rw [hg₀] at hgt
            have := CGate.var.inj hgt
            rw [← this] at h0
            exact absurd h0 (by decide)
          · rw [hg₁] at hgt
            have := CGate.var.inj hgt
            rw [← this] at h0
            exact absurd h0 (by decide)
          · exact hvt rfl
        · exact absurd he (by
            rintro he'
            exact hgp_notvar ⟨iT, he'⟩)
  -- the endgame, per variable at t
  rcases htvar with rfl | rfl | rfl
  · obtain ⟨hwt, hub⟩ := hblind 0 hg₀
    refine absurd ⟨fun a z => op' a z,
      fun β γ => wire c (fun m : Fin 3 => if m.val = 1 then β else if m.val = 2 then γ
        else false) p, ?_⟩ allEq3_no_split_a
    intro a b cc
    have hx := hrep0 (fun m : Fin 3 => if m.val = 0 then a else if m.val = 1 then b else cc)
    rw [hwt] at hx
    have hu : wire c (fun m : Fin 3 => if m.val = 0 then a else if m.val = 1 then b
        else cc) p
        = wire c (fun m : Fin 3 => if m.val = 1 then b else if m.val = 2 then cc
          else false) p := by
      have h1 := hub (fun m : Fin 3 => if m.val = 0 then a else if m.val = 1 then b
        else cc) false
      have h2 : Function.update (fun m : Fin 3 => if m.val = 0 then a
          else if m.val = 1 then b else cc) 0 false
          = (fun m : Fin 3 => if m.val = 1 then b else if m.val = 2 then cc
            else false) := by
        funext m
        fin_cases m <;> simp [Function.update]
      rw [h2] at h1
      exact h1.symm
    rw [hu] at hx
    exact hx
  · obtain ⟨hwt, hub⟩ := hblind 1 hg₁
    refine absurd ⟨fun a z => op' a z,
      fun β γ => wire c (fun m : Fin 3 => if m.val = 0 then β else if m.val = 2 then γ
        else false) p, ?_⟩ allEq3_no_split_b
    intro a b cc
    have hx := hrep0 (fun m : Fin 3 => if m.val = 0 then a else if m.val = 1 then b else cc)
    rw [hwt] at hx
    have hu : wire c (fun m : Fin 3 => if m.val = 0 then a else if m.val = 1 then b
        else cc) p
        = wire c (fun m : Fin 3 => if m.val = 0 then a else if m.val = 2 then cc
          else false) p := by
      have h1 := hub (fun m : Fin 3 => if m.val = 0 then a else if m.val = 1 then b
        else cc) false
      have h2 : Function.update (fun m : Fin 3 => if m.val = 0 then a
          else if m.val = 1 then b else cc) 1 false
          = (fun m : Fin 3 => if m.val = 0 then a else if m.val = 2 then cc
            else false) := by
        funext m
        fin_cases m <;> simp [Function.update]
      rw [h2] at h1
      exact h1.symm
    rw [hu] at hx
    exact hx
  · obtain ⟨hwt, hub⟩ := hblind 2 hg₂
    refine absurd ⟨fun a z => op' a z,
      fun β γ => wire c (fun m : Fin 3 => if m.val = 0 then β else if m.val = 1 then γ
        else false) p, ?_⟩ allEq3_no_split_c
    intro a b cc
    have hx := hrep0 (fun m : Fin 3 => if m.val = 0 then a else if m.val = 1 then b else cc)
    rw [hwt] at hx
    have hu : wire c (fun m : Fin 3 => if m.val = 0 then a else if m.val = 1 then b
        else cc) p
        = wire c (fun m : Fin 3 => if m.val = 0 then a else if m.val = 1 then b
          else false) p := by
      have h1 := hub (fun m : Fin 3 => if m.val = 0 then a else if m.val = 1 then b
        else cc) false
      have h2 : Function.update (fun m : Fin 3 => if m.val = 0 then a
          else if m.val = 1 then b else cc) 2 false
          = (fun m : Fin 3 => if m.val = 0 then a else if m.val = 1 then b
            else false) := by
        funext m
        fin_cases m <;> simp [Function.update]
      rw [h2] at h1
      exact h1.symm
    rw [hu] at hx
    exact hx

/-- **THE FIRST ABOVE-FLOOR LOWER BOUND (proved)**: `6 ≤ cbudget allEq3Fin`, one
above the cone floor `2·3 − 1 = 5`. -/
theorem cbudget_allEq3Fin : 6 ≤ cbudget allEq3Fin := by
  obtain ⟨c, hcomp, hclen⟩ := Nat.sInf_mem (cbudget_set_nonempty allEq3Fin)
  have hclen' : c.length = cbudget allEq3Fin := hclen
  have hcone := cone_bound allEq3Fin
  rw [depSet_allEq3Fin_card] at hcone
  rcases Nat.lt_or_ge (cbudget allEq3Fin) 6 with h | h
  · exact absurd (no_five_gate_allEq3 c hcomp (by omega)) not_false
  · exact h

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.no_five_gate_allEq3
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_allEq3Fin
