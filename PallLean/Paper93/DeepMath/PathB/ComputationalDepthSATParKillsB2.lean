import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATParCore

/-!
# Parallel-case B2 kills: two below one wire, one free

Multi-wire brick 8a.  At two reconvergence wires `{u, v}`: a gadget with two
signs below `u` (avoiding `v`) and the third avoiding `u` is impossible — the
free slot cannot move the `u`-mediator (`wire_u_indep`), yet per fixed free
value the mediator refines `AllEqual₃` through `u` alone (`refine_via`): three
distinct values demanded of one bit (`b2_kill_free*`).

* **`killB2v_g0_free1/2/3`, `killB2v_g1_free4/5/6`, `killB2v_g2_free7/8/9`
  (proved)** — all nine gadget × free-slot variants, generic in the wire pair
  (instantiate `{u₁,u₂}` or the swap).

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

section ParB2

variable (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N) (h27 : 27 < N)
  (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N) (h64 : 64 < N)
  (h72 : 72 < N)
  (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
  (hWd : (coneVars c).card ≤ (depSet (SATFamily N)).card)

include hN h15 h21 h27 h34 h41 h48 h56 h64 h72 hcomp hs hWd

/-- **Parallel B2, gadget 0, free slot 1 (proved)**. -/
theorem killB2v_g0_free1 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15u : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hb21 : Reach c u q21) (hnb21v : ¬ Reach c v q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hb27 : Reach c u q27) (hnb27v : ¬ Reach c v q27) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  refine b2_kill_free1 (fun p q r =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      p q r true true true true true true) u) ?_ ?_
  · intro p q r q' r' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      p q r true true true true true true p q' r' true true true true true true
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21,
        fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hnb21v⟩)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27,
        fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hnb27v⟩)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        p q r true true true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        p q' r' true true true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true] at hv
    exact hv
  · intro p p' q r
    show wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      p q r true true true true true true) u
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        p' q r true true true true true true) u
    conv_lhs => rw [← nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
      p' q r true true true true true true p]
    exact wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ p
      (fun w hw hg => by
        rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hnb15u)

/-- **Parallel B2, gadget 0, free slot 2 (proved)**. -/
theorem killB2v_g0_free2 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hb15 : Reach c u q15) (hnb15v : ¬ Reach c v q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21u : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hb27 : Reach c u q27) (hnb27v : ¬ Reach c v q27) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  refine b2_kill_free2 (fun p q r =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      p q r true true true true true true) u) ?_ ?_
  · intro p q r p' r' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      p q r true true true true true true p' q r' true true true true true true
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15,
        fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hnb15v⟩)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27,
        fun w hw hg => by
          rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hnb27v⟩)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        p q r true true true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        p' q r' true true true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true] at hv
    exact hv
  · intro p q q' r
    show wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      p q r true true true true true true) u
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        p q' r true true true true true true) u
    conv_lhs => rw [← nineUpd_upd2 h15 h21 h27 h34 h41 h48 h56 h64 h72
      p q' r true true true true true true q]
    exact wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ q
      (fun w hw hg => by
        rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hnb21u)

/-- **Parallel B2, gadget 0, free slot 3 (proved)**. -/
theorem killB2v_g0_free3 {u v : ℕ} (hR : reconvR c = {u, v}) {q15 q21 q27 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hb15 : Reach c u q15) (hnb15v : ¬ Reach c v q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hb21 : Reach c u q21) (hnb21v : ¬ Reach c v q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27u : ¬ Reach c u q27) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  refine b2_kill_free3 (fun p q r =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      p q r true true true true true true) u) ?_ ?_
  · intro p q r p' q' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      p q r true true true true true true p' q' r true true true true true true
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15,
        fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hnb15v⟩)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21,
        fun w hw hg => by
          rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hnb21v⟩)
      (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        p q r true true true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        p' q' r true true true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true] at hv
    exact hv
  · intro p q r r'
    show wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      p q r true true true true true true) u
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        p q r' true true true true true true) u
    conv_lhs => rw [← nineUpd_upd3 h15 h21 h27 h34 h41 h48 h56 h64 h72
      p q r' true true true true true true r]
    exact wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ r
      (fun w hw hg => by
        rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hnb27u)

/-- **Parallel B2, gadget 1, free slot 4 (proved)**. -/
theorem killB2v_g1_free4 {u v : ℕ} (hR : reconvR c = {u, v}) {q34 q41 q48 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hnb34u : ¬ Reach c u q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hb41 : Reach c u q41) (hnb41v : ¬ Reach c v q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hb48 : Reach c u q48) (hnb48v : ¬ Reach c v q48) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  refine b2_kill_free1 (fun p q r =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true p q r true true true) u) ?_ ?_
  · intro p q r q' r' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true p q r true true true true true true p q' r' true true true
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41,
        fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hnb41v⟩)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48,
        fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hnb48v⟩)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true p q r true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true p q' r' true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      Bool.true_and] at hv
    exact hv
  · intro p p' q r
    show wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true p q r true true true) u
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true p' q r true true true) u
    conv_lhs => rw [← nineUpd_upd4 h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true p' q r true true true p]
    exact wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ p
      (fun w hw hg => by
        rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hnb34u)

/-- **Parallel B2, gadget 1, free slot 5 (proved)**. -/
theorem killB2v_g1_free5 {u v : ℕ} (hR : reconvR c = {u, v}) {q34 q41 q48 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hb34 : Reach c u q34) (hnb34v : ¬ Reach c v q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hnb41u : ¬ Reach c u q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hb48 : Reach c u q48) (hnb48v : ¬ Reach c v q48) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  refine b2_kill_free2 (fun p q r =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true p q r true true true) u) ?_ ?_
  · intro p q r p' r' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true p q r true true true true true true p' q r' true true true
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34,
        fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hnb34v⟩)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48,
        fun w hw hg => by
          rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hnb48v⟩)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true p q r true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true p' q r' true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      Bool.true_and] at hv
    exact hv
  · intro p q q' r
    show wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true p q r true true true) u
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true p q' r true true true) u
    conv_lhs => rw [← nineUpd_upd5 h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true p q' r true true true q]
    exact wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ q
      (fun w hw hg => by
        rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hnb41u)

/-- **Parallel B2, gadget 1, free slot 6 (proved)**. -/
theorem killB2v_g1_free6 {u v : ℕ} (hR : reconvR c = {u, v}) {q34 q41 q48 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hb34 : Reach c u q34) (hnb34v : ¬ Reach c v q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hb41 : Reach c u q41) (hnb41v : ¬ Reach c v q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hnb48u : ¬ Reach c u q48) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  refine b2_kill_free3 (fun p q r =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true p q r true true true) u) ?_ ?_
  · intro p q r p' q' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true p q r true true true true true true p' q' r true true true
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34,
        fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hnb34v⟩)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41,
        fun w hw hg => by
          rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hnb41v⟩)
      (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true p q r true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true p' q' r true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      Bool.true_and] at hv
    exact hv
  · intro p q r r'
    show wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true p q r true true true) u
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true p q r' true true true) u
    conv_lhs => rw [← nineUpd_upd6 h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true p q r' true true true r]
    exact wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ r
      (fun w hw hg => by
        rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hnb48u)

/-- **Parallel B2, gadget 2, free slot 7 (proved)**. -/
theorem killB2v_g2_free7 {u v : ℕ} (hR : reconvR c = {u, v}) {q56 q64 q72 : ℕ}
    (hq56c : q56 ∈ cone c) (hq56g : c.getD q56 (.cst false) = CGate.var ⟨56, h56⟩)
    (hnb56u : ¬ Reach c u q56)
    (hq64c : q64 ∈ cone c) (hq64g : c.getD q64 (.cst false) = CGate.var ⟨64, h64⟩)
    (hb64 : Reach c u q64) (hnb64v : ¬ Reach c v q64)
    (hq72c : q72 ∈ cone c) (hq72g : c.getD q72 (.cst false) = CGate.var ⟨72, h72⟩)
    (hb72 : Reach c u q72) (hnb72v : ¬ Reach c v q72) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd56 := sign56_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd64 := sign64_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd72 := sign72_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  refine b2_kill_free1 (fun p q r =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true p q r) u) ?_ ?_
  · intro p q r q' r' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true true true true p q r true true true true true true p q' r'
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hb64,
        fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hnb64v⟩)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hb72,
        fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hnb72v⟩)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true true p q r,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true true p q' r'] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and] at hv
    exact hv
  · intro p p' q r
    show wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true p q r) u
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true true p' q r) u
    conv_lhs => rw [← nineUpd_upd7 h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true p' q r p]
    exact wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ p
      (fun w hw hg => by
        rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hnb56u)

/-- **Parallel B2, gadget 2, free slot 8 (proved)**. -/
theorem killB2v_g2_free8 {u v : ℕ} (hR : reconvR c = {u, v}) {q56 q64 q72 : ℕ}
    (hq56c : q56 ∈ cone c) (hq56g : c.getD q56 (.cst false) = CGate.var ⟨56, h56⟩)
    (hb56 : Reach c u q56) (hnb56v : ¬ Reach c v q56)
    (hq64c : q64 ∈ cone c) (hq64g : c.getD q64 (.cst false) = CGate.var ⟨64, h64⟩)
    (hnb64u : ¬ Reach c u q64)
    (hq72c : q72 ∈ cone c) (hq72g : c.getD q72 (.cst false) = CGate.var ⟨72, h72⟩)
    (hb72 : Reach c u q72) (hnb72v : ¬ Reach c v q72) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd56 := sign56_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd64 := sign64_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd72 := sign72_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  refine b2_kill_free2 (fun p q r =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true p q r) u) ?_ ?_
  · intro p q r p' r' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true true true true p q r true true true true true true p' q r'
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hb56,
        fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hnb56v⟩)
      (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hb72,
        fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hnb72v⟩)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true true p q r,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true true p' q r'] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and] at hv
    exact hv
  · intro p q q' r
    show wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true p q r) u
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true true p q' r) u
    conv_lhs => rw [← nineUpd_upd8 h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true p q' r q]
    exact wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ q
      (fun w hw hg => by
        rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hnb64u)

/-- **Parallel B2, gadget 2, free slot 9 (proved)**. -/
theorem killB2v_g2_free9 {u v : ℕ} (hR : reconvR c = {u, v}) {q56 q64 q72 : ℕ}
    (hq56c : q56 ∈ cone c) (hq56g : c.getD q56 (.cst false) = CGate.var ⟨56, h56⟩)
    (hb56 : Reach c u q56) (hnb56v : ¬ Reach c v q56)
    (hq64c : q64 ∈ cone c) (hq64g : c.getD q64 (.cst false) = CGate.var ⟨64, h64⟩)
    (hb64 : Reach c u q64) (hnb64v : ¬ Reach c v q64)
    (hq72c : q72 ∈ cone c) (hq72g : c.getD q72 (.cst false) = CGate.var ⟨72, h72⟩)
    (hnb72u : ¬ Reach c u q72) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd56 := sign56_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd64 := sign64_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd72 := sign72_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  refine b2_kill_free3 (fun p q r =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true p q r) u) ?_ ?_
  · intro p q r p' q' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true true true true p q r true true true true true true p' q' r
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hb56,
        fun w hw hg => by
          rw [huniq ⟨56, h56⟩ hd56 w hw q56 hq56c hg hq56g]; exact hnb56v⟩)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hb64,
        fun w hw hg => by
          rw [huniq ⟨64, h64⟩ hd64 w hw q64 hq64c hg hq64g]; exact hnb64v⟩)
      (Or.inl rfl)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true true p q r,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true true p' q' r] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and] at hv
    exact hv
  · intro p q r r'
    show wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true p q r) u
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true true p q r') u
    conv_lhs => rw [← nineUpd_upd9 h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true p q r' r]
    exact wire_u_indep c u hs ((mem_cone.mp huc).1) ((mem_cone.mp huc).2) _ _ r
      (fun w hw hg => by
        rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hnb72u)

end ParB2

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killB2v_g0_free1
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killB2v_g1_free5
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killB2v_g2_free9
