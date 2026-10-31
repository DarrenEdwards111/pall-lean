import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATParKillsB3

/-!
# Parallel-case B3 pair kills: the (g0,g2) and (g1,g2) gadget pairs

Multi-wire brick 8d.  Completes the parallel B3 family: at two
reconvergence wires `{u, v}`, any two gadgets each holding exactly one sign
below `u` (avoiding `v`, the first gadget's other signs avoiding `u`) are
impossible.  Same engine as brick 8c (`refine_via` + `wire_u_indep`
complement moves + `b3_kill`), transported to the (g0,g2) and (g1,g2)
positions; the pinned middle/first gadget reduces via `Bool.and_true` /
`Bool.true_and` respectively.

* **`killB3v_17` … `killB3v_39` (proved)** — (g0-slot, g2-slot) ×9.
* **`killB3v_47` … `killB3v_69` (proved)** — (g1-slot, g2-slot) ×9.

With brick 8c this gives all 27 pair kills the parallel pigeonhole
dispatch needs.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor

section ParB3b

variable (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N) (h27 : 27 < N)
  (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N) (h64 : 64 < N)
  (h72 : 72 < N)
  (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
  (hWd : (coneVars c).card ≤ (depSet (SATFamily N)).card)

include hN h15 h21 h27 h34 h41 h48 h56 h64 h72 hcomp hs hWd

/-- **Parallel B3, slots (1,7) (proved)**. -/
theorem killB3v_17 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q56 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hb15 : Reach c u q15) (hnb15v : ¬ Reach c v q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq56c : q56 ∈ cone c) (hq56g : c.getD q56 (.cst false) = CGate.var ⟨56, h56⟩)
    (hb56 : Reach c u q56) (hnb56v : ¬ Reach c v q56) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd56 := sign56_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false true true true d true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a true true true true true d true true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a false false true true true d true true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true true true true d true true) ⟨27, h27⟩ false) u := by
          rw [nineUpd_upd3 h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true true true true d true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true true true true d true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]
              exact hnb27)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true true true d true true) ⟨21, h21⟩ false) u := by
          rw [nineUpd_upd2 h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true true true d true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true true true d true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]
              exact hnb21)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      a true true true true true d true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a true true true true true d true true a' true true true true true d' true true
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15,
        fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hnb15v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hb56,
        fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hnb56v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a true true true true true d true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a' true true true true true d' true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot1_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false true true true d true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a' false false true true true d' true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a false false true true true d true true a' false false true true true d' true true
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15,
        fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hnb15v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hb56,
        fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hnb56v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false true true true d true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a' false false true true true d' true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot1_F, allEq3_slot1_T] at hv
    exact hv

/-- **Parallel B3, slots (1,8) (proved)**. -/
theorem killB3v_18 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q64 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hb15 : Reach c u q15) (hnb15v : ¬ Reach c v q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq64c : q64 ∈ cone c) (hq64g : c.getD q64 (.cst false) = CGate.var ⟨64, h64⟩)
    (hb64 : Reach c u q64) (hnb64v : ¬ Reach c v q64) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd64 := sign64_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false true true true true d true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a true true true true true true d true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a false false true true true true d true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true true true true true d true) ⟨27, h27⟩ false) u := by
          rw [nineUpd_upd3 h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true true true true true d true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true true true true true d true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]
              exact hnb27)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true true true true d true) ⟨21, h21⟩ false) u := by
          rw [nineUpd_upd2 h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true true true true d true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true true true true d true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]
              exact hnb21)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      a true true true true true true d true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a true true true true true true d true a' true true true true true true d' true
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15,
        fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hnb15v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hb64,
        fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hnb64v⟩)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a true true true true true true d true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a' true true true true true true d' true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot1_T, allEq3_slot2_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false true true true true d true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a' false false true true true true d' true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a false false true true true true d true a' false false true true true true d' true
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15,
        fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hnb15v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hb64,
        fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hnb64v⟩)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false true true true true d true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a' false false true true true true d' true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot1_F, allEq3_slot2_T] at hv
    exact hv

/-- **Parallel B3, slots (1,9) (proved)**. -/
theorem killB3v_19 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q72 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hb15 : Reach c u q15) (hnb15v : ¬ Reach c v q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq72c : q72 ∈ cone c) (hq72g : c.getD q72 (.cst false) = CGate.var ⟨72, h72⟩)
    (hb72 : Reach c u q72) (hnb72v : ¬ Reach c v q72) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd72 := sign72_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false true true true true true d) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a true true true true true true true d) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a false false true true true true true d) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true true true true true true d) ⟨27, h27⟩ false) u := by
          rw [nineUpd_upd3 h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true true true true true true d false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true true true true true true d) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]
              exact hnb27)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true true true true true d) ⟨21, h21⟩ false) u := by
          rw [nineUpd_upd2 h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true true true true true d false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true true true true true d) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]
              exact hnb21)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      a true true true true true true true d) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a true true true true true true true d a' true true true true true true true d'
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15,
        fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hnb15v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hb72,
        fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hnb72v⟩)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a true true true true true true true d,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a' true true true true true true true d'] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot1_T, allEq3_slot3_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false true true true true true d) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a' false false true true true true true d') u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a false false true true true true true d a' false false true true true true true d'
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15,
        fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hnb15v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hb72,
        fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hnb72v⟩)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false true true true true true d,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a' false false true true true true true d'] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot1_F, allEq3_slot3_T] at hv
    exact hv

/-- **Parallel B3, slots (2,7) (proved)**. -/
theorem killB3v_27 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q56 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hb21 : Reach c u q21) (hnb21v : ¬ Reach c v q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq56c : q56 ∈ cone c) (hq56g : c.getD q56 (.cst false) = CGate.var ⟨56, h56⟩)
    (hb56 : Reach c u q56) (hnb56v : ¬ Reach c v q56) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd56 := sign56_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false true true true d true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true a true true true true d true true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false a false true true true d true true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true true true true d true true) ⟨27, h27⟩ false) u := by
          rw [nineUpd_upd3 h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true true true true d true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true true true true d true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]
              exact hnb27)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true true true d true true) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true true true d true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true true true d true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]
              exact hnb15)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true a true true true true d true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true a true true true true d true true true a' true true true true d' true true
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21,
        fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hnb21v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hb56,
        fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hnb56v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true a true true true true d true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true a' true true true true d' true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot2_T, allEq3_slot1_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false true true true d true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false a' false true true true d' true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false a false true true true d true true false a' false true true true d' true true
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21,
        fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hnb21v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hb56,
        fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hnb56v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false true true true d true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a' false true true true d' true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot2_F, allEq3_slot1_T] at hv
    exact hv

/-- **Parallel B3, slots (2,8) (proved)**. -/
theorem killB3v_28 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q64 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hb21 : Reach c u q21) (hnb21v : ¬ Reach c v q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq64c : q64 ∈ cone c) (hq64g : c.getD q64 (.cst false) = CGate.var ⟨64, h64⟩)
    (hb64 : Reach c u q64) (hnb64v : ¬ Reach c v q64) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd64 := sign64_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false true true true true d true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true a true true true true true d true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false a false true true true true d true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true true true true true d true) ⟨27, h27⟩ false) u := by
          rw [nineUpd_upd3 h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true true true true true d true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true true true true true d true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]
              exact hnb27)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true true true true d true) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true true true true d true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true true true true d true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]
              exact hnb15)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true a true true true true true d true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true a true true true true true d true true a' true true true true true d' true
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21,
        fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hnb21v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hb64,
        fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hnb64v⟩)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true a true true true true true d true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true a' true true true true true d' true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot2_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false true true true true d true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false a' false true true true true d' true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false a false true true true true d true false a' false true true true true d' true
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21,
        fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hnb21v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hb64,
        fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hnb64v⟩)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false true true true true d true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a' false true true true true d' true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot2_F, allEq3_slot2_T] at hv
    exact hv

/-- **Parallel B3, slots (2,9) (proved)**. -/
theorem killB3v_29 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q72 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hb21 : Reach c u q21) (hnb21v : ¬ Reach c v q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq72c : q72 ∈ cone c) (hq72g : c.getD q72 (.cst false) = CGate.var ⟨72, h72⟩)
    (hb72 : Reach c u q72) (hnb72v : ¬ Reach c v q72) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd72 := sign72_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false true true true true true d) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true a true true true true true true d) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false a false true true true true true d) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true true true true true true d) ⟨27, h27⟩ false) u := by
          rw [nineUpd_upd3 h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true true true true true true d false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true true true true true true d) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]
              exact hnb27)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true true true true true d) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true true true true true d false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true true true true true d) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]
              exact hnb15)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true a true true true true true true d) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true a true true true true true true d true a' true true true true true true d'
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21,
        fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hnb21v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hb72,
        fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hnb72v⟩)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true a true true true true true true d,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true a' true true true true true true d'] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot2_T, allEq3_slot3_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false true true true true true d) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false a' false true true true true true d') u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false a false true true true true true d false a' false true true true true true d'
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21,
        fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hnb21v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hb72,
        fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hnb72v⟩)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false true true true true true d,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a' false true true true true true d'] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot2_F, allEq3_slot3_T] at hv
    exact hv

/-- **Parallel B3, slots (3,7) (proved)**. -/
theorem killB3v_37 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q56 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hb27 : Reach c u q27) (hnb27v : ¬ Reach c v q27)
    (hq56c : q56 ∈ cone c) (hq56g : c.getD q56 (.cst false) = CGate.var ⟨56, h56⟩)
    (hb56 : Reach c u q56) (hnb56v : ¬ Reach c v q56) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd56 := sign56_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a true true true d true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true a true true true d true true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false false a true true true d true true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a true true true d true true) ⟨21, h21⟩ false) u := by
          rw [nineUpd_upd2 h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a true true true d true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a true true true d true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]
              exact hnb21)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true true true d true true) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true true true d true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true true true d true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]
              exact hnb15)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true a true true true d true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true a true true true d true true true true a' true true true d' true true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27,
        fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hnb27v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hb56,
        fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hnb56v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true a true true true d true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true a' true true true d' true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot3_T, allEq3_slot1_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a true true true d true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false false a' true true true d' true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false false a true true true d true true false false a' true true true d' true true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27,
        fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hnb27v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hb56,
        fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hnb56v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a true true true d true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a' true true true d' true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot3_F, allEq3_slot1_T] at hv
    exact hv

/-- **Parallel B3, slots (3,8) (proved)**. -/
theorem killB3v_38 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q64 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hb27 : Reach c u q27) (hnb27v : ¬ Reach c v q27)
    (hq64c : q64 ∈ cone c) (hq64g : c.getD q64 (.cst false) = CGate.var ⟨64, h64⟩)
    (hb64 : Reach c u q64) (hnb64v : ¬ Reach c v q64) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd64 := sign64_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a true true true true d true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true a true true true true d true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false false a true true true true d true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a true true true true d true) ⟨21, h21⟩ false) u := by
          rw [nineUpd_upd2 h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a true true true true d true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a true true true true d true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]
              exact hnb21)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true true true true d true) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true true true true d true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true true true true d true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]
              exact hnb15)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true a true true true true d true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true a true true true true d true true true a' true true true true d' true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27,
        fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hnb27v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hb64,
        fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hnb64v⟩)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true a true true true true d true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true a' true true true true d' true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot3_T, allEq3_slot2_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a true true true true d true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false false a' true true true true d' true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false false a true true true true d true false false a' true true true true d' true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27,
        fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hnb27v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hb64,
        fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hnb64v⟩)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a true true true true d true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a' true true true true d' true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot3_F, allEq3_slot2_T] at hv
    exact hv

/-- **Parallel B3, slots (3,9) (proved)**. -/
theorem killB3v_39 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q72 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hb27 : Reach c u q27) (hnb27v : ¬ Reach c v q27)
    (hq72c : q72 ∈ cone c) (hq72g : c.getD q72 (.cst false) = CGate.var ⟨72, h72⟩)
    (hb72 : Reach c u q72) (hnb72v : ¬ Reach c v q72) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd72 := sign72_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a true true true true true d) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true a true true true true true d) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false false a true true true true true d) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a true true true true true d) ⟨21, h21⟩ false) u := by
          rw [nineUpd_upd2 h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a true true true true true d false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a true true true true true d) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]
              exact hnb21)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true true true true true d) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true true true true true d false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true true true true true d) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]
              exact hnb15)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true a true true true true true d) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true a true true true true true d true true a' true true true true true d'
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27,
        fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hnb27v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hb72,
        fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hnb72v⟩)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true a true true true true true d,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true a' true true true true true d'] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot3_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a true true true true true d) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false false a' true true true true true d') u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false false a true true true true true d false false a' true true true true true d'
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27,
        fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hnb27v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hb72,
        fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hnb72v⟩)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a true true true true true d,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a' true true true true true d'] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot3_F, allEq3_slot3_T] at hv
    exact hv

/-- **Parallel B3, slots (4,7) (proved)**. -/
theorem killB3v_47 {u v : ℕ} (hR : reconvR c = {u, v}) {q34 q41 q48 q56 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hb34 : Reach c u q34) (hnb34v : ¬ Reach c v q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hnb41 : ¬ Reach c u q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hnb48 : ¬ Reach c u q48)
    (hq56c : q56 ∈ cone c) (hq56g : c.getD q56 (.cst false) = CGate.var ⟨56, h56⟩)
    (hb56 : Reach c u q56) (hnb56v : ¬ Reach c v q56) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd56 := sign56_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a false false d true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true a true true d true true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true a false false d true true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a false true d true true) ⟨48, h48⟩ false) u := by
          rw [nineUpd_upd6 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a false true d true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a false true d true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]
              exact hnb48)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a true true d true true) ⟨41, h41⟩ false) u := by
          rw [nineUpd_upd5 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a true true d true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a true true d true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]
              exact hnb41)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true a true true d true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true a true true d true true true true true a' true true d' true true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34,
        fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hnb34v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hb56,
        fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hnb56v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a true true d true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a' true true d' true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot1_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a false false d true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true a' false false d' true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true a false false d true true true true true a' false false d' true true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34,
        fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hnb34v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hb56,
        fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hnb56v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a false false d true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a' false false d' true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot1_F, allEq3_slot1_T] at hv
    exact hv

/-- **Parallel B3, slots (4,8) (proved)**. -/
theorem killB3v_48 {u v : ℕ} (hR : reconvR c = {u, v}) {q34 q41 q48 q64 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hb34 : Reach c u q34) (hnb34v : ¬ Reach c v q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hnb41 : ¬ Reach c u q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hnb48 : ¬ Reach c u q48)
    (hq64c : q64 ∈ cone c) (hq64g : c.getD q64 (.cst false) = CGate.var ⟨64, h64⟩)
    (hb64 : Reach c u q64) (hnb64v : ¬ Reach c v q64) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd64 := sign64_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a false false true d true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true a true true true d true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true a false false true d true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a false true true d true) ⟨48, h48⟩ false) u := by
          rw [nineUpd_upd6 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a false true true d true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a false true true d true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]
              exact hnb48)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a true true true d true) ⟨41, h41⟩ false) u := by
          rw [nineUpd_upd5 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a true true true d true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a true true true d true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]
              exact hnb41)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true a true true true d true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true a true true true d true true true true a' true true true d' true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34,
        fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hnb34v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hb64,
        fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hnb64v⟩)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a true true true d true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a' true true true d' true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot1_T, allEq3_slot2_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a false false true d true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true a' false false true d' true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true a false false true d true true true true a' false false true d' true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34,
        fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hnb34v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hb64,
        fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hnb64v⟩)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a false false true d true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a' false false true d' true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot1_F, allEq3_slot2_T] at hv
    exact hv

/-- **Parallel B3, slots (4,9) (proved)**. -/
theorem killB3v_49 {u v : ℕ} (hR : reconvR c = {u, v}) {q34 q41 q48 q72 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hb34 : Reach c u q34) (hnb34v : ¬ Reach c v q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hnb41 : ¬ Reach c u q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hnb48 : ¬ Reach c u q48)
    (hq72c : q72 ∈ cone c) (hq72g : c.getD q72 (.cst false) = CGate.var ⟨72, h72⟩)
    (hb72 : Reach c u q72) (hnb72v : ¬ Reach c v q72) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd72 := sign72_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a false false true true d) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true a true true true true d) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true a false false true true d) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a false true true true d) ⟨48, h48⟩ false) u := by
          rw [nineUpd_upd6 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a false true true true d false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a false true true true d) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]
              exact hnb48)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a true true true true d) ⟨41, h41⟩ false) u := by
          rw [nineUpd_upd5 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a true true true true d false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true a true true true true d) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]
              exact hnb41)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true a true true true true d) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true a true true true true d true true true a' true true true true d'
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34,
        fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hnb34v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hb72,
        fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hnb72v⟩)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a true true true true d,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a' true true true true d'] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot1_T, allEq3_slot3_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a false false true true d) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true a' false false true true d') u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true a false false true true d true true true a' false false true true d'
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34,
        fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hnb34v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hb72,
        fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hnb72v⟩)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a false false true true d,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a' false false true true d'] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot1_F, allEq3_slot3_T] at hv
    exact hv

/-- **Parallel B3, slots (5,7) (proved)**. -/
theorem killB3v_57 {u v : ℕ} (hR : reconvR c = {u, v}) {q34 q41 q48 q56 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hnb34 : ¬ Reach c u q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hb41 : Reach c u q41) (hnb41v : ¬ Reach c v q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hnb48 : ¬ Reach c u q48)
    (hq56c : q56 ∈ cone c) (hq56g : c.getD q56 (.cst false) = CGate.var ⟨56, h56⟩)
    (hb56 : Reach c u q56) (hnb56v : ¬ Reach c v q56) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd56 := sign56_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false a false d true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true true a true d true true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true false a false d true true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false a true d true true) ⟨48, h48⟩ false) u := by
          rw [nineUpd_upd6 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false a true d true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false a true d true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]
              exact hnb48)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true a true d true true) ⟨34, h34⟩ false) u := by
          rw [nineUpd_upd4 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true a true d true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true a true d true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]
              exact hnb34)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true a true d true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true true a true d true true true true true true a' true d' true true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41,
        fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hnb41v⟩)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hb56,
        fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hnb56v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true a true d true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true a' true d' true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot2_T, allEq3_slot1_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false a false d true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true false a' false d' true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true false a false d true true true true true false a' false d' true true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41,
        fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hnb41v⟩)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hb56,
        fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hnb56v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false a false d true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false a' false d' true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot2_F, allEq3_slot1_T] at hv
    exact hv

/-- **Parallel B3, slots (5,8) (proved)**. -/
theorem killB3v_58 {u v : ℕ} (hR : reconvR c = {u, v}) {q34 q41 q48 q64 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hnb34 : ¬ Reach c u q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hb41 : Reach c u q41) (hnb41v : ¬ Reach c v q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hnb48 : ¬ Reach c u q48)
    (hq64c : q64 ∈ cone c) (hq64g : c.getD q64 (.cst false) = CGate.var ⟨64, h64⟩)
    (hb64 : Reach c u q64) (hnb64v : ¬ Reach c v q64) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd64 := sign64_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false a false true d true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true true a true true d true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true false a false true d true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false a true true d true) ⟨48, h48⟩ false) u := by
          rw [nineUpd_upd6 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false a true true d true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false a true true d true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]
              exact hnb48)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true a true true d true) ⟨34, h34⟩ false) u := by
          rw [nineUpd_upd4 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true a true true d true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true a true true d true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]
              exact hnb34)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true a true true d true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true true a true true d true true true true true a' true true d' true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41,
        fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hnb41v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hb64,
        fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hnb64v⟩)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true a true true d true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true a' true true d' true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot2_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false a false true d true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true false a' false true d' true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true false a false true d true true true true false a' false true d' true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41,
        fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hnb41v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hb64,
        fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hnb64v⟩)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false a false true d true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false a' false true d' true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot2_F, allEq3_slot2_T] at hv
    exact hv

/-- **Parallel B3, slots (5,9) (proved)**. -/
theorem killB3v_59 {u v : ℕ} (hR : reconvR c = {u, v}) {q34 q41 q48 q72 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hnb34 : ¬ Reach c u q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hb41 : Reach c u q41) (hnb41v : ¬ Reach c v q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hnb48 : ¬ Reach c u q48)
    (hq72c : q72 ∈ cone c) (hq72g : c.getD q72 (.cst false) = CGate.var ⟨72, h72⟩)
    (hb72 : Reach c u q72) (hnb72v : ¬ Reach c v q72) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd72 := sign72_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false a false true true d) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true true a true true true d) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true false a false true true d) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false a true true true d) ⟨48, h48⟩ false) u := by
          rw [nineUpd_upd6 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false a true true true d false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false a true true true d) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]
              exact hnb48)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true a true true true d) ⟨34, h34⟩ false) u := by
          rw [nineUpd_upd4 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true a true true true d false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true a true true true d) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]
              exact hnb34)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true a true true true d) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true true a true true true d true true true true a' true true true d'
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41,
        fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hnb41v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hb72,
        fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hnb72v⟩)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true a true true true d,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true a' true true true d'] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot2_T, allEq3_slot3_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false a false true true d) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true false a' false true true d') u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true false a false true true d true true true false a' false true true d'
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41,
        fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hnb41v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hb72,
        fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hnb72v⟩)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false a false true true d,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false a' false true true d'] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot2_F, allEq3_slot3_T] at hv
    exact hv

/-- **Parallel B3, slots (6,7) (proved)**. -/
theorem killB3v_67 {u v : ℕ} (hR : reconvR c = {u, v}) {q34 q41 q48 q56 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hnb34 : ¬ Reach c u q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hnb41 : ¬ Reach c u q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hb48 : Reach c u q48) (hnb48v : ¬ Reach c v q48)
    (hq56c : q56 ∈ cone c) (hq56g : c.getD q56 (.cst false) = CGate.var ⟨56, h56⟩)
    (hb56 : Reach c u q56) (hnb56v : ¬ Reach c v q56) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd56 := sign56_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false false a d true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true true true a d true true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true false false a d true true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false true a d true true) ⟨41, h41⟩ false) u := by
          rw [nineUpd_upd5 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false true a d true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false true a d true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]
              exact hnb41)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true true a d true true) ⟨34, h34⟩ false) u := by
          rw [nineUpd_upd4 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true true a d true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true true a d true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]
              exact hnb34)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true a d true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true true true a d true true true true true true true a' d' true true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48,
        fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hnb48v⟩)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hb56,
        fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hnb56v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true a d true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true a' d' true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot3_T, allEq3_slot1_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false false a d true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true false false a' d' true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true false false a d true true true true true false false a' d' true true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48,
        fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hnb48v⟩)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hb56,
        fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hnb56v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false false a d true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false false a' d' true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot3_F, allEq3_slot1_T] at hv
    exact hv

/-- **Parallel B3, slots (6,8) (proved)**. -/
theorem killB3v_68 {u v : ℕ} (hR : reconvR c = {u, v}) {q34 q41 q48 q64 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hnb34 : ¬ Reach c u q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hnb41 : ¬ Reach c u q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hb48 : Reach c u q48) (hnb48v : ¬ Reach c v q48)
    (hq64c : q64 ∈ cone c) (hq64g : c.getD q64 (.cst false) = CGate.var ⟨64, h64⟩)
    (hb64 : Reach c u q64) (hnb64v : ¬ Reach c v q64) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd64 := sign64_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false false a true d true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true true true a true d true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true false false a true d true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false true a true d true) ⟨41, h41⟩ false) u := by
          rw [nineUpd_upd5 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false true a true d true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false true a true d true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]
              exact hnb41)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true true a true d true) ⟨34, h34⟩ false) u := by
          rw [nineUpd_upd4 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true true a true d true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true true a true d true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]
              exact hnb34)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true a true d true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true true true a true d true true true true true true a' true d' true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48,
        fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hnb48v⟩)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hb64,
        fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hnb64v⟩)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true a true d true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true a' true d' true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot3_T, allEq3_slot2_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false false a true d true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true false false a' true d' true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true false false a true d true true true true false false a' true d' true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48,
        fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hnb48v⟩)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hb64,
        fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hnb64v⟩)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false false a true d true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false false a' true d' true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot3_F, allEq3_slot2_T] at hv
    exact hv

/-- **Parallel B3, slots (6,9) (proved)**. -/
theorem killB3v_69 {u v : ℕ} (hR : reconvR c = {u, v}) {q34 q41 q48 q72 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hnb34 : ¬ Reach c u q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hnb41 : ¬ Reach c u q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hb48 : Reach c u q48) (hnb48v : ¬ Reach c v q48)
    (hq72c : q72 ∈ cone c) (hq72g : c.getD q72 (.cst false) = CGate.var ⟨72, h72⟩)
    (hb72 : Reach c u q72) (hnb72v : ¬ Reach c v q72) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd72 := sign72_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false false a true true d) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true true true a true true d) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true false false a true true d) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false true a true true d) ⟨41, h41⟩ false) u := by
          rw [nineUpd_upd5 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false true a true true d false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true false true a true true d) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]
              exact hnb41)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true true a true true d) ⟨34, h34⟩ false) u := by
          rw [nineUpd_upd4 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true true a true true d false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true true a true true d) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]
              exact hnb34)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true a true true d) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true true true a true true d true true true true true a' true true d'
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48,
        fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hnb48v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hb72,
        fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hnb72v⟩)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true a true true d,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true a' true true d'] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot3_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false false a true true d) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true false false a' true true d') u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true false false a true true d true true true false false a' true true d'
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48,
        fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hnb48v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hb72,
        fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hnb72v⟩)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false false a true true d,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true false false a' true true d'] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and,
      allEq3_slot3_F, allEq3_slot3_T] at hv
    exact hv

end ParB3b

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
