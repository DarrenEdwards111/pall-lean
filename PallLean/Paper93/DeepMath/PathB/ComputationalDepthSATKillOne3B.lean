import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATKillOne3A

/-!
# Case-(ii) kills at three gadgets, part B: B2, B3, and THE ONE-WIRE KILL

Multi-wire brick 5b.  The B2 (two below + one free) and B3 (one below in each of
two gadgets) kills at the nine-sign substrate, and the assembly:

* **`killB29_g0_free1/2/3`, `killB29_g1_free4/5/6` (proved)**;
* **`killB39_14 … killB39_36` (proved, 9 variants)**;
* **`killOneWire3` (proved)** — CASE (ii) IS CLOSED: no circuit with var-gate
  budget `deps` and a SINGLE reconvergence wire computes a SAT slice `≥ 73`.
  The 64-branch dispatch over gadget-0/1 below-flags covers everything —
  gadget 2's flags are never needed.

Remaining for `+3`: case (iii), two reconvergence wires — the open analytic
core.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor

section KillsB23

variable (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N) (h27 : 27 < N)
  (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N) (h64 : 64 < N)
  (h72 : 72 < N)
  (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
  (hWd : (coneVars c).card ≤ (depSet (SATFamily N)).card)

include hN h15 h21 h27 h34 h41 h48 h56 h64 h72 hcomp hs hWd

/-- **Kill B2 at nine slots, gadget 0, free slot 1 (proved)**. -/
theorem killB29_g0_free1 {u : ℕ} (hR : reconvR c = {u}) {q15 q21 q27 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hb21 : Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hb27 : Reach c u q27) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  refine b2_kill_free1 (fun p q r =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      p q r true true true true true true) u) ?_ ?_
  · intro p q r q' r' hwu
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      p q r true true true true true true p q' r' true true true true true true
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27)
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
    exact wire_indep9 N c hcomp hs hWd hR ⟨15, h15⟩ hd15 hq15c hq15g hnb15 _ p

/-- **Kill B2 at nine slots, gadget 0, free slot 2 (proved)**. -/
theorem killB29_g0_free2 {u : ℕ} (hR : reconvR c = {u}) {q15 q21 q27 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hb15 : Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hb27 : Reach c u q27) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  refine b2_kill_free2 (fun p q r =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      p q r true true true true true true) u) ?_ ?_
  · intro p q r p' r' hwu
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      p q r true true true true true true p' q r' true true true true true true
      (Or.inr fun w hw hg => by
        rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15)
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27)
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
    exact wire_indep9 N c hcomp hs hWd hR ⟨21, h21⟩ hd21 hq21c hq21g hnb21 _ q

/-- **Kill B2 at nine slots, gadget 0, free slot 3 (proved)**. -/
theorem killB29_g0_free3 {u : ℕ} (hR : reconvR c = {u}) {q15 q21 q27 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hb15 : Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hb21 : Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  refine b2_kill_free3 (fun p q r =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      p q r true true true true true true) u) ?_ ?_
  · intro p q r p' q' hwu
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      p q r true true true true true true p' q' r true true true true true true
      (Or.inr fun w hw hg => by
        rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21)
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
    exact wire_indep9 N c hcomp hs hWd hR ⟨27, h27⟩ hd27 hq27c hq27g hnb27 _ r

/-- **Kill B2 at nine slots, gadget 1, free slot 4 (proved)**. -/
theorem killB29_g1_free4 {u : ℕ} (hR : reconvR c = {u}) {q34 q41 q48 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hnb34 : ¬ Reach c u q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hb41 : Reach c u q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hb48 : Reach c u q48) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  refine b2_kill_free1 (fun p q r =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true p q r true true true) u) ?_ ?_
  · intro p q r q' r' hwu
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true p q r true true true true true true p q' r' true true true
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48)
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
    exact wire_indep9 N c hcomp hs hWd hR ⟨34, h34⟩ hd34 hq34c hq34g hnb34 _ p

/-- **Kill B2 at nine slots, gadget 1, free slot 5 (proved)**. -/
theorem killB29_g1_free5 {u : ℕ} (hR : reconvR c = {u}) {q34 q41 q48 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hb34 : Reach c u q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hnb41 : ¬ Reach c u q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hb48 : Reach c u q48) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  refine b2_kill_free2 (fun p q r =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true p q r true true true) u) ?_ ?_
  · intro p q r p' r' hwu
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true p q r true true true true true true p' q r' true true true
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34)
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48)
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
    exact wire_indep9 N c hcomp hs hWd hR ⟨41, h41⟩ hd41 hq41c hq41g hnb41 _ q

/-- **Kill B2 at nine slots, gadget 1, free slot 6 (proved)**. -/
theorem killB29_g1_free6 {u : ℕ} (hR : reconvR c = {u}) {q34 q41 q48 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hb34 : Reach c u q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hb41 : Reach c u q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hnb48 : ¬ Reach c u q48) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  refine b2_kill_free3 (fun p q r =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true p q r true true true) u) ?_ ?_
  · intro p q r p' q' hwu
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true p q r true true true true true true p' q' r true true true
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41)
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
    exact wire_indep9 N c hcomp hs hWd hR ⟨48, h48⟩ hd48 hq48c hq48g hnb48 _ r

/-- **Kill B3 at nine slots, slots (1,4) (proved)**. -/
theorem killB39_14 {u : ℕ} (hR : reconvR c = {u}) {q15 q21 q27 q34 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hb15 : Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hb34 : Reach c u q34) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
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
          wire_indep9 N c hcomp hs hWd hR ⟨27, h27⟩ hd27 hq27c hq27g hnb27 _ false
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true d true true true true true) ⟨21, h21⟩ false) u := by
          rw [nineUpd_upd2 h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true d true true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true d true true true true true) u :=
          wire_indep9 N c hcomp hs hWd hR ⟨21, h21⟩ hd21 hq21c hq21g hnb21 _ false
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      a true true d true true true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a true true d true true true true true a' true true d' true true true true true
      (Or.inr fun w hw hg => by
        rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
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
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a false false d true true true true true
      a' false false d' true true true true true
      (Or.inr fun w hw hg => by
        rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false d true true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a' false false d' true true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot1_F, allEq3_slot1_T] at hv
    exact hv

/-- **Kill B3 at nine slots, slots (1,5) (proved)**. -/
theorem killB39_15 {u : ℕ} (hR : reconvR c = {u}) {q15 q21 q27 q41 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hb15 : Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hb41 : Reach c u q41) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
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
          wire_indep9 N c hcomp hs hWd hR ⟨27, h27⟩ hd27 hq27c hq27g hnb27 _ false
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true d true true true true) ⟨21, h21⟩ false) u := by
          rw [nineUpd_upd2 h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true d true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true d true true true true) u :=
          wire_indep9 N c hcomp hs hWd hR ⟨21, h21⟩ hd21 hq21c hq21g hnb21 _ false
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      a true true true d true true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a true true true d true true true true a' true true true d' true true true true
      (Or.inr fun w hw hg => by
        rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41)
      (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
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
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a false false true d true true true true
      a' false false true d' true true true true
      (Or.inr fun w hw hg => by
        rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41)
      (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false true d true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a' false false true d' true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot1_F, allEq3_slot2_T] at hv
    exact hv

/-- **Kill B3 at nine slots, slots (1,6) (proved)**. -/
theorem killB39_16 {u : ℕ} (hR : reconvR c = {u}) {q15 q21 q27 q48 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hb15 : Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hb48 : Reach c u q48) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
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
          wire_indep9 N c hcomp hs hWd hR ⟨27, h27⟩ hd27 hq27c hq27g hnb27 _ false
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true true d true true true) ⟨21, h21⟩ false) u := by
          rw [nineUpd_upd2 h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true true d true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            a true true true true d true true true) u :=
          wire_indep9 N c hcomp hs hWd hR ⟨21, h21⟩ hd21 hq21c hq21g hnb21 _ false
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      a true true true true d true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a true true true true d true true true a' true true true true d' true true true
      (Or.inr fun w hw hg => by
        rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
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
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      a false false true true d true true true
      a' false false true true d' true true true
      (Or.inr fun w hw hg => by
        rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a false false true true d true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a' false false true true d' true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot1_F, allEq3_slot3_T] at hv
    exact hv

/-- **Kill B3 at nine slots, slots (2,4) (proved)**. -/
theorem killB39_24 {u : ℕ} (hR : reconvR c = {u}) {q15 q21 q27 q34 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hb21 : Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hb34 : Reach c u q34) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
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
          wire_indep9 N c hcomp hs hWd hR ⟨27, h27⟩ hd27 hq27c hq27g hnb27 _ false
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true d true true true true true) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true d true true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true d true true true true true) u :=
          wire_indep9 N c hcomp hs hWd hR ⟨15, h15⟩ hd15 hq15c hq15g hnb15 _ false
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true a true d true true true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true a true d true true true true true true a' true d' true true true true true
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21)
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
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
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false a false d true true true true true
      false a' false d' true true true true true
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21)
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false d true true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a' false d' true true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot2_F, allEq3_slot1_T] at hv
    exact hv

/-- **Kill B3 at nine slots, slots (2,5) (proved)**. -/
theorem killB39_25 {u : ℕ} (hR : reconvR c = {u}) {q15 q21 q27 q41 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hb21 : Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hb41 : Reach c u q41) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
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
          wire_indep9 N c hcomp hs hWd hR ⟨27, h27⟩ hd27 hq27c hq27g hnb27 _ false
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true d true true true true) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true d true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true d true true true true) u :=
          wire_indep9 N c hcomp hs hWd hR ⟨15, h15⟩ hd15 hq15c hq15g hnb15 _ false
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true a true true d true true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true a true true d true true true true true a' true true d' true true true true
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41)
      (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
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
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false a false true d true true true true
      false a' false true d' true true true true
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41)
      (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false true d true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a' false true d' true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot2_F, allEq3_slot2_T] at hv
    exact hv

/-- **Kill B3 at nine slots, slots (2,6) (proved)**. -/
theorem killB39_26 {u : ℕ} (hR : reconvR c = {u}) {q15 q21 q27 q48 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hb21 : Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hb48 : Reach c u q48) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
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
          wire_indep9 N c hcomp hs hWd hR ⟨27, h27⟩ hd27 hq27c hq27g hnb27 _ false
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true true d true true true) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true true d true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true a true true true d true true true) u :=
          wire_indep9 N c hcomp hs hWd hR ⟨15, h15⟩ hd15 hq15c hq15g hnb15 _ false
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true a true true true d true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true a true true true d true true true true a' true true true d' true true true
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
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
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false a false true true d true true true
      false a' false true true d' true true true
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a false true true d true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false a' false true true d' true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot2_F, allEq3_slot3_T] at hv
    exact hv

/-- **Kill B3 at nine slots, slots (3,4) (proved)**. -/
theorem killB39_34 {u : ℕ} (hR : reconvR c = {u}) {q15 q21 q27 q34 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hb27 : Reach c u q27)
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hb34 : Reach c u q34) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
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
          wire_indep9 N c hcomp hs hWd hR ⟨21, h21⟩ hd21 hq21c hq21g hnb21 _ false
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a d true true true true true) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a d true true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a d true true true true true) u :=
          wire_indep9 N c hcomp hs hWd hR ⟨15, h15⟩ hd15 hq15c hq15g hnb15 _ false
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true a d true true true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true a d true true true true true true true a' d' true true true true true
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
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
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false false a d true true true true true
      false false a' d' true true true true true
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a d true true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a' d' true true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot3_F, allEq3_slot1_T] at hv
    exact hv

/-- **Kill B3 at nine slots, slots (3,5) (proved)**. -/
theorem killB39_35 {u : ℕ} (hR : reconvR c = {u}) {q15 q21 q27 q41 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hb27 : Reach c u q27)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hb41 : Reach c u q41) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
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
          wire_indep9 N c hcomp hs hWd hR ⟨21, h21⟩ hd21 hq21c hq21g hnb21 _ false
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true d true true true true) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true d true true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true d true true true true) u :=
          wire_indep9 N c hcomp hs hWd hR ⟨15, h15⟩ hd15 hq15c hq15g hnb15 _ false
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true a true d true true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true a true d true true true true true true a' true d' true true true true
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27)
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41)
      (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
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
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false false a true d true true true true
      false false a' true d' true true true true
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27)
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41)
      (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a true d true true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a' true d' true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot3_F, allEq3_slot2_T] at hv
    exact hv

/-- **Kill B3 at nine slots, slots (3,6) (proved)**. -/
theorem killB39_36 {u : ℕ} (hR : reconvR c = {u}) {q15 q21 q27 q48 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hb27 : Reach c u q27)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hb48 : Reach c u q48) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
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
          wire_indep9 N c hcomp hs hWd hR ⟨21, h21⟩ hd21 hq21c hq21g hnb21 _ false
      _ = wire c (Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true true d true true true) ⟨15, h15⟩ false) u := by
          rw [nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true true d true true true false]
      _ = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true a true true d true true true) u :=
          wire_indep9 N c hcomp hs hWd hR ⟨15, h15⟩ hd15 hq15c hq15g hnb15 _ false
  refine b3_kill (fun a d =>
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true a true true d true true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true a true true d true true true true true a' true true d' true true true
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
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
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      false false a true true d true true true
      false false a' true true d' true true true
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu2
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a true true d true true true,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        false false a' true true d' true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      allEq3_slot3_F, allEq3_slot3_T] at hv
    exact hv

end KillsB23

/-! ### THE ONE-WIRE KILL: case (ii) is closed -/

/-- **THE ONE-WIRE KILL (proved)**: no circuit with var-gate budget `deps` and a
single reconvergence wire computes a SAT slice of length `≥ 73`. -/
theorem killOneWire3 (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N)
    (h27 : 27 < N) (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N)
    (h64 : 64 < N) (h72 : 72 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hWd : (coneVars c).card ≤ (depSet (SATFamily N)).card)
    {u : ℕ} (hR : reconvR c = {u}) : False := by
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  obtain ⟨q15, hq15c, hq15g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd15
  obtain ⟨q21, hq21c, hq21g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd21
  obtain ⟨q27, hq27c, hq27g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd27
  obtain ⟨q34, hq34c, hq34g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd34
  obtain ⟨q41, hq41c, hq41g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd41
  obtain ⟨q48, hq48c, hq48g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd48
  by_cases hb15 : Reach c u q15 <;> by_cases hb21 : Reach c u q21 <;>
    by_cases hb27 : Reach c u q27 <;> by_cases hb34 : Reach c u q34 <;>
    by_cases hb41 : Reach c u q41 <;> by_cases hb48 : Reach c u q48 <;>
    first
      | exact killA9_g0 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 hq21c hq21g hb21 hq27c hq27g hb27
      | exact killA9_g1 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hb34 hq41c hq41g hb41 hq48c hq48g hb48
      | exact killB19_g0 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 hq21c hq21g hb21 hq27c hq27g hb27
      | exact killB19_g1 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hb34 hq41c hq41g hb41 hq48c hq48g hb48
      | exact killB29_g0_free1 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 hq21c hq21g hb21 hq27c hq27g hb27
      | exact killB29_g0_free2 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 hq21c hq21g hb21 hq27c hq27g hb27
      | exact killB29_g0_free3 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 hq21c hq21g hb21 hq27c hq27g hb27
      | exact killB29_g1_free4 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hb34 hq41c hq41g hb41 hq48c hq48g hb48
      | exact killB29_g1_free5 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hb34 hq41c hq41g hb41 hq48c hq48g hb48
      | exact killB29_g1_free6 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hb34 hq41c hq41g hb41 hq48c hq48g hb48
      | exact killB39_14 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 hq21c hq21g hb21 hq27c hq27g hb27 hq34c hq34g hb34
      | exact killB39_15 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 hq21c hq21g hb21 hq27c hq27g hb27 hq41c hq41g hb41
      | exact killB39_16 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 hq21c hq21g hb21 hq27c hq27g hb27 hq48c hq48g hb48
      | exact killB39_24 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 hq21c hq21g hb21 hq27c hq27g hb27 hq34c hq34g hb34
      | exact killB39_25 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 hq21c hq21g hb21 hq27c hq27g hb27 hq41c hq41g hb41
      | exact killB39_26 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 hq21c hq21g hb21 hq27c hq27g hb27 hq48c hq48g hb48
      | exact killB39_34 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 hq21c hq21g hb21 hq27c hq27g hb27 hq34c hq34g hb34
      | exact killB39_35 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 hq21c hq21g hb21 hq27c hq27g hb27 hq41c hq41g hb41
      | exact killB39_36 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 hq21c hq21g hb21 hq27c hq27g hb27 hq48c hq48g hb48

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killB29_g0_free1
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killB39_14
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killB39_36
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killOneWire3
