import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATParKillsB1

/-!
# Parallel-case B3 pair kills: gadgets 0 and 1 each exactly one below `u`

Multi-wire brick 8c.  At two reconvergence wires `{u, v}`: gadget 0 with
exactly one sign below `u` (avoiding `v`, other two signs avoiding `u`) and
gadget 1 with a sign below `u` (avoiding `v`) is impossible — the one-wire
B3 collision argument transported through the pair via `refine_via`; the
pinned-complement moves on gadget 0's free slots use `wire_u_indep`
(no reconvergence hypothesis, so free at two wires).

* **`killB3v_14` … `killB3v_36` (proved)** — all nine (g0-slot, g1-slot)
  variants, generic in the wire pair (instantiate `{u₁,u₂}` or the swap via
  `Finset.pair_comm`).  The (g0,g2) and (g1,g2) gadget pairs follow in the
  next brick.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor

section ParB3

variable (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N) (h27 : 27 < N)
  (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N) (h64 : 64 < N)
  (h72 : 72 < N)
  (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
  (hWd : (coneVars c).card ≤ (depSet (SATFamily N)).card)

include hN h15 h21 h27 h34 h41 h48 h56 h64 h72 hcomp hs hWd

/-- **Parallel B3, slots (1,4) (proved)**. -/
theorem killB3v_14 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q34 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hb15 : Reach c u q15) (hnb15v : ¬ Reach c v q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hb34 : Reach c u q34) (hnb34v : ¬ Reach c v q34) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false d true true true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a true true d true true true true true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a false false d true true true true true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true d true true true true true) ⟨27, h27⟩ false) u := by
          rw [nineUpd_upd3 h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true d true true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true d true true true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]
              exact hnb27)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true d true true true true true) ⟨21, h21⟩ false) u := by
          rw [nineUpd_upd2 h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true d true true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true d true true true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]
              exact hnb21)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      a true true d true true true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a true true d true true true true true a' true true d' true true true true true
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15,
        fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hnb15v⟩)
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
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a true true d true true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a' true true d' true true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot1_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false d true true true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a' false false d' true true true true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a false false d true true true true true a' false false d' true true true true true
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15,
        fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hnb15v⟩)
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
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false d true true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a' false false d' true true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot1_F, allEq3_slot1_T] at hv
    exact hv

/-- **Parallel B3, slots (1,5) (proved)**. -/
theorem killB3v_15 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q41 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hb15 : Reach c u q15) (hnb15v : ¬ Reach c v q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hb41 : Reach c u q41) (hnb41v : ¬ Reach c v q41) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false true d true true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a true true true d true true true true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a false false true d true true true true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true true d true true true true) ⟨27, h27⟩ false) u := by
          rw [nineUpd_upd3 h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true true d true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true true d true true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]
              exact hnb27)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true d true true true true) ⟨21, h21⟩ false) u := by
          rw [nineUpd_upd2 h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true d true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true d true true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]
              exact hnb21)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      a true true true d true true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a true true true d true true true true a' true true true d' true true true true
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15,
        fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hnb15v⟩)
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
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a true true true d true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a' true true true d' true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot1_T, allEq3_slot2_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false true d true true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a' false false true d' true true true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a false false true d true true true true a' false false true d' true true true true
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15,
        fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hnb15v⟩)
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
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false true d true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a' false false true d' true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot1_F, allEq3_slot2_T] at hv
    exact hv

/-- **Parallel B3, slots (1,6) (proved)**. -/
theorem killB3v_16 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q48 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hb15 : Reach c u q15) (hnb15v : ¬ Reach c v q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hb48 : Reach c u q48) (hnb48v : ¬ Reach c v q48) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false true true d true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a true true true true d true true true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a false false true true d true true true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true true true d true true true) ⟨27, h27⟩ false) u := by
          rw [nineUpd_upd3 h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true true true d true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a false true true true d true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]
              exact hnb27)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true true d true true true) ⟨21, h21⟩ false) u := by
          rw [nineUpd_upd2 h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true true d true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true true d true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]
              exact hnb21)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      a true true true true d true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a true true true true d true true true a' true true true true d' true true true
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15,
        fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hnb15v⟩)
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
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a true true true true d true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a' true true true true d' true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot1_T, allEq3_slot3_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false true true d true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          a' false false true true d' true true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a false false true true d true true true a' false false true true d' true true true
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15,
        fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hnb15v⟩)
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
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false true true d true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a' false false true true d' true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot1_F, allEq3_slot3_T] at hv
    exact hv

/-- **Parallel B3, slots (2,4) (proved)**. -/
theorem killB3v_24 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q34 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hb21 : Reach c u q21) (hnb21v : ¬ Reach c v q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hb34 : Reach c u q34) (hnb34v : ¬ Reach c v q34) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false d true true true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true a true d true true true true true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false a false d true true true true true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true d true true true true true) ⟨27, h27⟩ false) u := by
          rw [nineUpd_upd3 h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true d true true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true d true true true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]
              exact hnb27)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true d true true true true true) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true d true true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true d true true true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]
              exact hnb15)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true a true d true true true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true a true d true true true true true true a' true d' true true true true true
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21,
        fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hnb21v⟩)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34,
        fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hnb34v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true a true d true true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true a' true d' true true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot2_T, allEq3_slot1_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false d true true true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false a' false d' true true true true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false a false d true true true true true false a' false d' true true true true true
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21,
        fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hnb21v⟩)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34,
        fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hnb34v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false d true true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a' false d' true true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot2_F, allEq3_slot1_T] at hv
    exact hv

/-- **Parallel B3, slots (2,5) (proved)**. -/
theorem killB3v_25 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q41 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hb21 : Reach c u q21) (hnb21v : ¬ Reach c v q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hb41 : Reach c u q41) (hnb41v : ¬ Reach c v q41) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false true d true true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true a true true d true true true true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false a false true d true true true true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true true d true true true true) ⟨27, h27⟩ false) u := by
          rw [nineUpd_upd3 h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true true d true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true true d true true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]
              exact hnb27)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true d true true true true) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true d true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true d true true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]
              exact hnb15)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true a true true d true true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true a true true d true true true true true a' true true d' true true true true
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21,
        fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hnb21v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41,
        fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hnb41v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true a true true d true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true a' true true d' true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot2_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false true d true true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false a' false true d' true true true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false a false true d true true true true false a' false true d' true true true true
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21,
        fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hnb21v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41,
        fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hnb41v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false true d true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a' false true d' true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot2_F, allEq3_slot2_T] at hv
    exact hv

/-- **Parallel B3, slots (2,6) (proved)**. -/
theorem killB3v_26 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q48 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hb21 : Reach c u q21) (hnb21v : ¬ Reach c v q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hb48 : Reach c u q48) (hnb48v : ¬ Reach c v q48) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false true true d true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true a true true true d true true true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false a false true true d true true true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true true true d true true true) ⟨27, h27⟩ false) u := by
          rw [nineUpd_upd3 h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true true true d true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false a true true true d true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]
              exact hnb27)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true true d true true true) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true true d true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true true d true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]
              exact hnb15)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true a true true true d true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true a true true true d true true true true a' true true true d' true true true
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21,
        fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hnb21v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48,
        fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hnb48v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true a true true true d true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true a' true true true d' true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot2_T, allEq3_slot3_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false true true d true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false a' false true true d' true true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false a false true true d true true true false a' false true true d' true true true
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21,
        fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hnb21v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48,
        fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hnb48v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false true true d true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a' false true true d' true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot2_F, allEq3_slot3_T] at hv
    exact hv

/-- **Parallel B3, slots (3,4) (proved)**. -/
theorem killB3v_34 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q34 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hb27 : Reach c u q27) (hnb27v : ¬ Reach c v q27)
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hb34 : Reach c u q34) (hnb34v : ¬ Reach c v q34) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a d true true true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true a d true true true true true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false false a d true true true true true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a d true true true true true) ⟨21, h21⟩ false) u := by
          rw [nineUpd_upd2 h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a d true true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a d true true true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]
              exact hnb21)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a d true true true true true) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a d true true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a d true true true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]
              exact hnb15)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true a d true true true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true a d true true true true true true true a' d' true true true true true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27,
        fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hnb27v⟩)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34,
        fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hnb34v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true a d true true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true a' d' true true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot3_T, allEq3_slot1_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a d true true true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false false a' d' true true true true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false false a d true true true true true false false a' d' true true true true true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27,
        fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hnb27v⟩)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34,
        fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hnb34v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a d true true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a' d' true true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot3_F, allEq3_slot1_T] at hv
    exact hv

/-- **Parallel B3, slots (3,5) (proved)**. -/
theorem killB3v_35 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q41 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hb27 : Reach c u q27) (hnb27v : ¬ Reach c v q27)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hb41 : Reach c u q41) (hnb41v : ¬ Reach c v q41) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a true d true true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true a true d true true true true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false false a true d true true true true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a true d true true true true) ⟨21, h21⟩ false) u := by
          rw [nineUpd_upd2 h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a true d true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a true d true true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]
              exact hnb21)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true d true true true true) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true d true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true d true true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]
              exact hnb15)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true a true d true true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true a true d true true true true true true a' true d' true true true true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27,
        fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hnb27v⟩)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41,
        fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hnb41v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true a true d true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true a' true d' true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot3_T, allEq3_slot2_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a true d true true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false false a' true d' true true true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false false a true d true true true true false false a' true d' true true true true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27,
        fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hnb27v⟩)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41,
        fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hnb41v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a true d true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a' true d' true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot3_F, allEq3_slot2_T] at hv
    exact hv

/-- **Parallel B3, slots (3,6) (proved)**. -/
theorem killB3v_36 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 q48 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hb27 : Reach c u q27) (hnb27v : ¬ Reach c v q27)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hb48 : Reach c u q48) (hnb48v : ¬ Reach c v q48) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have htrans : ∀ a d : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a true true d true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true a true true d true true true) u := by
    intro a d
    calc wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false false a true true d true true true) u
        = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a true true d true true true) ⟨21, h21⟩ false) u := by
          rw [nineUpd_upd2 h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a true true d true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            false true a true true d true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]
              exact hnb21)
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true true d true true true) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true true d true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true true d true true true) u :=
          wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ false
            (fun w hw hg => by
              rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]
              exact hnb15)
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true a true true d true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true a true true d true true true true true a' true true d' true true true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27,
        fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hnb27v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48,
        fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hnb48v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true a true true d true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true a' true true d' true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot3_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a true true d true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          false false a' true true d' true true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false false a true true d true true true false false a' true true d' true true true
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27,
        fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hnb27v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48,
        fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hnb48v⟩)
      (Or.inl rfl)
      (Or.inl rfl)
      (Or.inl rfl)
      hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a true true d true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a' true true d' true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot3_F, allEq3_slot3_T] at hv
    exact hv

end ParB3

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
