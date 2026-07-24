import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATParProfile

/-!
# The parallel two-wire case: killParallel3

Multi-wire brick 10b — the parallel-case capstone.

Given two *parallel* reconvergence wires `reconvR c = {u, v}`
(`¬ Reach c u v`, `¬ Reach c v u`), every gadget marks one of the two wires
with a one-below witness (`gadget_marks`).  Three gadgets and two wires: by
pigeonhole two gadgets mark the same wire, and their one-below witnesses feed
the matching `killB3v` pair kill.  The six `killPair_ab{u,v}` lemmas package
"gadgets a, b both mark wire w → False"; `killParallel3` is the 8-way
pigeonhole over the three gadget/wire choices.

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

section ParDispatch

variable (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N) (h27 : 27 < N)
  (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N) (h64 : 64 < N)
  (h72 : 72 < N)
  (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
  (hWd : (coneVars c).card ≤ (depSet (SATFamily N)).card)

include hN h15 h21 h27 h34 h41 h48 h56 h64 h72 hcomp hs hWd

/-- **Pair kill: gadgets 0,1 both mark `u` (proved)**. -/
theorem killPair_01u {u v : ℕ} (hR : reconvR c = {u, v})
    (huv : ¬ Reach c u v) (hvu : ¬ Reach c v u) {q15 q21 q27 q34 q41 q48 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (h0 : (Reach c u q15 ∧ ¬ Reach c u q21 ∧ ¬ Reach c u q27) ∨
     (¬ Reach c u q15 ∧ Reach c u q21 ∧ ¬ Reach c u q27) ∨
     (¬ Reach c u q15 ∧ ¬ Reach c u q21 ∧ Reach c u q27))
    (h1 : (Reach c u q34 ∧ ¬ Reach c u q41 ∧ ¬ Reach c u q48) ∨
     (¬ Reach c u q34 ∧ Reach c u q41 ∧ ¬ Reach c u q48) ∨
     (¬ Reach c u q34 ∧ ¬ Reach c u q41 ∧ Reach c u q48)) : False := by
  have nbb15 := not_below_both c hs hR huv hvu q15 hq15c
  have nbb21 := not_below_both c hs hR huv hvu q21 hq21c
  have nbb27 := not_below_both c hs hR huv hvu q27 hq27c
  have nbb34 := not_below_both c hs hR huv hvu q34 hq34c
  have nbb41 := not_below_both c hs hR huv hvu q41 hq41c
  have nbb48 := not_below_both c hs hR huv hvu q48 hq48c
  rcases h0 with ⟨hb15, hn21, hn27⟩ | ⟨hn15, hb21, hn27⟩ | ⟨hn15, hn21, hb27⟩ <;>
    rcases h1 with ⟨hb34, hn41, hn48⟩ | ⟨hn34, hb41, hn48⟩ | ⟨hn34, hn41, hb48⟩ <;>
    first
      | exact killB3v_14 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 (fun hx => nbb15 ⟨hb15, hx⟩) hq21c hq21g hn21 hq27c hq27g hn27 hq34c hq34g hb34 (fun hx => nbb34 ⟨hb34, hx⟩)
      | exact killB3v_15 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 (fun hx => nbb15 ⟨hb15, hx⟩) hq21c hq21g hn21 hq27c hq27g hn27 hq41c hq41g hb41 (fun hx => nbb41 ⟨hb41, hx⟩)
      | exact killB3v_16 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 (fun hx => nbb15 ⟨hb15, hx⟩) hq21c hq21g hn21 hq27c hq27g hn27 hq48c hq48g hb48 (fun hx => nbb48 ⟨hb48, hx⟩)
      | exact killB3v_24 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hn15 hq21c hq21g hb21 (fun hx => nbb21 ⟨hb21, hx⟩) hq27c hq27g hn27 hq34c hq34g hb34 (fun hx => nbb34 ⟨hb34, hx⟩)
      | exact killB3v_25 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hn15 hq21c hq21g hb21 (fun hx => nbb21 ⟨hb21, hx⟩) hq27c hq27g hn27 hq41c hq41g hb41 (fun hx => nbb41 ⟨hb41, hx⟩)
      | exact killB3v_26 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hn15 hq21c hq21g hb21 (fun hx => nbb21 ⟨hb21, hx⟩) hq27c hq27g hn27 hq48c hq48g hb48 (fun hx => nbb48 ⟨hb48, hx⟩)
      | exact killB3v_34 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hn15 hq21c hq21g hn21 hq27c hq27g hb27 (fun hx => nbb27 ⟨hb27, hx⟩) hq34c hq34g hb34 (fun hx => nbb34 ⟨hb34, hx⟩)
      | exact killB3v_35 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hn15 hq21c hq21g hn21 hq27c hq27g hb27 (fun hx => nbb27 ⟨hb27, hx⟩) hq41c hq41g hb41 (fun hx => nbb41 ⟨hb41, hx⟩)
      | exact killB3v_36 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hn15 hq21c hq21g hn21 hq27c hq27g hb27 (fun hx => nbb27 ⟨hb27, hx⟩) hq48c hq48g hb48 (fun hx => nbb48 ⟨hb48, hx⟩)

/-- **Pair kill: gadgets 0,1 both mark `v` (proved)**. -/
theorem killPair_01v {u v : ℕ} (hR : reconvR c = {u, v})
    (huv : ¬ Reach c u v) (hvu : ¬ Reach c v u) {q15 q21 q27 q34 q41 q48 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (h0 : (Reach c v q15 ∧ ¬ Reach c v q21 ∧ ¬ Reach c v q27) ∨
     (¬ Reach c v q15 ∧ Reach c v q21 ∧ ¬ Reach c v q27) ∨
     (¬ Reach c v q15 ∧ ¬ Reach c v q21 ∧ Reach c v q27))
    (h1 : (Reach c v q34 ∧ ¬ Reach c v q41 ∧ ¬ Reach c v q48) ∨
     (¬ Reach c v q34 ∧ Reach c v q41 ∧ ¬ Reach c v q48) ∨
     (¬ Reach c v q34 ∧ ¬ Reach c v q41 ∧ Reach c v q48)) : False := by
  have hRs : reconvR c = {v, u} := by rw [hR]; exact Finset.pair_comm u v
  have nbb15 := not_below_both c hs hR huv hvu q15 hq15c
  have nbb21 := not_below_both c hs hR huv hvu q21 hq21c
  have nbb27 := not_below_both c hs hR huv hvu q27 hq27c
  have nbb34 := not_below_both c hs hR huv hvu q34 hq34c
  have nbb41 := not_below_both c hs hR huv hvu q41 hq41c
  have nbb48 := not_below_both c hs hR huv hvu q48 hq48c
  rcases h0 with ⟨hb15, hn21, hn27⟩ | ⟨hn15, hb21, hn27⟩ | ⟨hn15, hn21, hb27⟩ <;>
    rcases h1 with ⟨hb34, hn41, hn48⟩ | ⟨hn34, hb41, hn48⟩ | ⟨hn34, hn41, hb48⟩ <;>
    first
      | exact killB3v_14 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hb15 (fun hx => nbb15 ⟨hx, hb15⟩) hq21c hq21g hn21 hq27c hq27g hn27 hq34c hq34g hb34 (fun hx => nbb34 ⟨hx, hb34⟩)
      | exact killB3v_15 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hb15 (fun hx => nbb15 ⟨hx, hb15⟩) hq21c hq21g hn21 hq27c hq27g hn27 hq41c hq41g hb41 (fun hx => nbb41 ⟨hx, hb41⟩)
      | exact killB3v_16 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hb15 (fun hx => nbb15 ⟨hx, hb15⟩) hq21c hq21g hn21 hq27c hq27g hn27 hq48c hq48g hb48 (fun hx => nbb48 ⟨hx, hb48⟩)
      | exact killB3v_24 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hn15 hq21c hq21g hb21 (fun hx => nbb21 ⟨hx, hb21⟩) hq27c hq27g hn27 hq34c hq34g hb34 (fun hx => nbb34 ⟨hx, hb34⟩)
      | exact killB3v_25 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hn15 hq21c hq21g hb21 (fun hx => nbb21 ⟨hx, hb21⟩) hq27c hq27g hn27 hq41c hq41g hb41 (fun hx => nbb41 ⟨hx, hb41⟩)
      | exact killB3v_26 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hn15 hq21c hq21g hb21 (fun hx => nbb21 ⟨hx, hb21⟩) hq27c hq27g hn27 hq48c hq48g hb48 (fun hx => nbb48 ⟨hx, hb48⟩)
      | exact killB3v_34 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hn15 hq21c hq21g hn21 hq27c hq27g hb27 (fun hx => nbb27 ⟨hx, hb27⟩) hq34c hq34g hb34 (fun hx => nbb34 ⟨hx, hb34⟩)
      | exact killB3v_35 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hn15 hq21c hq21g hn21 hq27c hq27g hb27 (fun hx => nbb27 ⟨hx, hb27⟩) hq41c hq41g hb41 (fun hx => nbb41 ⟨hx, hb41⟩)
      | exact killB3v_36 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hn15 hq21c hq21g hn21 hq27c hq27g hb27 (fun hx => nbb27 ⟨hx, hb27⟩) hq48c hq48g hb48 (fun hx => nbb48 ⟨hx, hb48⟩)

/-- **Pair kill: gadgets 0,2 both mark `u` (proved)**. -/
theorem killPair_02u {u v : ℕ} (hR : reconvR c = {u, v})
    (huv : ¬ Reach c u v) (hvu : ¬ Reach c v u) {q15 q21 q27 q56 q64 q72 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hq56c : q56 ∈ cone c) (hq56g : c.getD q56 (.cst false) = CGate.var ⟨56, h56⟩)
    (hq64c : q64 ∈ cone c) (hq64g : c.getD q64 (.cst false) = CGate.var ⟨64, h64⟩)
    (hq72c : q72 ∈ cone c) (hq72g : c.getD q72 (.cst false) = CGate.var ⟨72, h72⟩)
    (h0 : (Reach c u q15 ∧ ¬ Reach c u q21 ∧ ¬ Reach c u q27) ∨
     (¬ Reach c u q15 ∧ Reach c u q21 ∧ ¬ Reach c u q27) ∨
     (¬ Reach c u q15 ∧ ¬ Reach c u q21 ∧ Reach c u q27))
    (h1 : (Reach c u q56 ∧ ¬ Reach c u q64 ∧ ¬ Reach c u q72) ∨
     (¬ Reach c u q56 ∧ Reach c u q64 ∧ ¬ Reach c u q72) ∨
     (¬ Reach c u q56 ∧ ¬ Reach c u q64 ∧ Reach c u q72)) : False := by
  have nbb15 := not_below_both c hs hR huv hvu q15 hq15c
  have nbb21 := not_below_both c hs hR huv hvu q21 hq21c
  have nbb27 := not_below_both c hs hR huv hvu q27 hq27c
  have nbb56 := not_below_both c hs hR huv hvu q56 hq56c
  have nbb64 := not_below_both c hs hR huv hvu q64 hq64c
  have nbb72 := not_below_both c hs hR huv hvu q72 hq72c
  rcases h0 with ⟨hb15, hn21, hn27⟩ | ⟨hn15, hb21, hn27⟩ | ⟨hn15, hn21, hb27⟩ <;>
    rcases h1 with ⟨hb56, hn64, hn72⟩ | ⟨hn56, hb64, hn72⟩ | ⟨hn56, hn64, hb72⟩ <;>
    first
      | exact killB3v_17 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 (fun hx => nbb15 ⟨hb15, hx⟩) hq21c hq21g hn21 hq27c hq27g hn27 hq56c hq56g hb56 (fun hx => nbb56 ⟨hb56, hx⟩)
      | exact killB3v_18 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 (fun hx => nbb15 ⟨hb15, hx⟩) hq21c hq21g hn21 hq27c hq27g hn27 hq64c hq64g hb64 (fun hx => nbb64 ⟨hb64, hx⟩)
      | exact killB3v_19 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hb15 (fun hx => nbb15 ⟨hb15, hx⟩) hq21c hq21g hn21 hq27c hq27g hn27 hq72c hq72g hb72 (fun hx => nbb72 ⟨hb72, hx⟩)
      | exact killB3v_27 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hn15 hq21c hq21g hb21 (fun hx => nbb21 ⟨hb21, hx⟩) hq27c hq27g hn27 hq56c hq56g hb56 (fun hx => nbb56 ⟨hb56, hx⟩)
      | exact killB3v_28 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hn15 hq21c hq21g hb21 (fun hx => nbb21 ⟨hb21, hx⟩) hq27c hq27g hn27 hq64c hq64g hb64 (fun hx => nbb64 ⟨hb64, hx⟩)
      | exact killB3v_29 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hn15 hq21c hq21g hb21 (fun hx => nbb21 ⟨hb21, hx⟩) hq27c hq27g hn27 hq72c hq72g hb72 (fun hx => nbb72 ⟨hb72, hx⟩)
      | exact killB3v_37 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hn15 hq21c hq21g hn21 hq27c hq27g hb27 (fun hx => nbb27 ⟨hb27, hx⟩) hq56c hq56g hb56 (fun hx => nbb56 ⟨hb56, hx⟩)
      | exact killB3v_38 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hn15 hq21c hq21g hn21 hq27c hq27g hb27 (fun hx => nbb27 ⟨hb27, hx⟩) hq64c hq64g hb64 (fun hx => nbb64 ⟨hb64, hx⟩)
      | exact killB3v_39 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hn15 hq21c hq21g hn21 hq27c hq27g hb27 (fun hx => nbb27 ⟨hb27, hx⟩) hq72c hq72g hb72 (fun hx => nbb72 ⟨hb72, hx⟩)

/-- **Pair kill: gadgets 0,2 both mark `v` (proved)**. -/
theorem killPair_02v {u v : ℕ} (hR : reconvR c = {u, v})
    (huv : ¬ Reach c u v) (hvu : ¬ Reach c v u) {q15 q21 q27 q56 q64 q72 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hq56c : q56 ∈ cone c) (hq56g : c.getD q56 (.cst false) = CGate.var ⟨56, h56⟩)
    (hq64c : q64 ∈ cone c) (hq64g : c.getD q64 (.cst false) = CGate.var ⟨64, h64⟩)
    (hq72c : q72 ∈ cone c) (hq72g : c.getD q72 (.cst false) = CGate.var ⟨72, h72⟩)
    (h0 : (Reach c v q15 ∧ ¬ Reach c v q21 ∧ ¬ Reach c v q27) ∨
     (¬ Reach c v q15 ∧ Reach c v q21 ∧ ¬ Reach c v q27) ∨
     (¬ Reach c v q15 ∧ ¬ Reach c v q21 ∧ Reach c v q27))
    (h1 : (Reach c v q56 ∧ ¬ Reach c v q64 ∧ ¬ Reach c v q72) ∨
     (¬ Reach c v q56 ∧ Reach c v q64 ∧ ¬ Reach c v q72) ∨
     (¬ Reach c v q56 ∧ ¬ Reach c v q64 ∧ Reach c v q72)) : False := by
  have hRs : reconvR c = {v, u} := by rw [hR]; exact Finset.pair_comm u v
  have nbb15 := not_below_both c hs hR huv hvu q15 hq15c
  have nbb21 := not_below_both c hs hR huv hvu q21 hq21c
  have nbb27 := not_below_both c hs hR huv hvu q27 hq27c
  have nbb56 := not_below_both c hs hR huv hvu q56 hq56c
  have nbb64 := not_below_both c hs hR huv hvu q64 hq64c
  have nbb72 := not_below_both c hs hR huv hvu q72 hq72c
  rcases h0 with ⟨hb15, hn21, hn27⟩ | ⟨hn15, hb21, hn27⟩ | ⟨hn15, hn21, hb27⟩ <;>
    rcases h1 with ⟨hb56, hn64, hn72⟩ | ⟨hn56, hb64, hn72⟩ | ⟨hn56, hn64, hb72⟩ <;>
    first
      | exact killB3v_17 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hb15 (fun hx => nbb15 ⟨hx, hb15⟩) hq21c hq21g hn21 hq27c hq27g hn27 hq56c hq56g hb56 (fun hx => nbb56 ⟨hx, hb56⟩)
      | exact killB3v_18 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hb15 (fun hx => nbb15 ⟨hx, hb15⟩) hq21c hq21g hn21 hq27c hq27g hn27 hq64c hq64g hb64 (fun hx => nbb64 ⟨hx, hb64⟩)
      | exact killB3v_19 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hb15 (fun hx => nbb15 ⟨hx, hb15⟩) hq21c hq21g hn21 hq27c hq27g hn27 hq72c hq72g hb72 (fun hx => nbb72 ⟨hx, hb72⟩)
      | exact killB3v_27 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hn15 hq21c hq21g hb21 (fun hx => nbb21 ⟨hx, hb21⟩) hq27c hq27g hn27 hq56c hq56g hb56 (fun hx => nbb56 ⟨hx, hb56⟩)
      | exact killB3v_28 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hn15 hq21c hq21g hb21 (fun hx => nbb21 ⟨hx, hb21⟩) hq27c hq27g hn27 hq64c hq64g hb64 (fun hx => nbb64 ⟨hx, hb64⟩)
      | exact killB3v_29 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hn15 hq21c hq21g hb21 (fun hx => nbb21 ⟨hx, hb21⟩) hq27c hq27g hn27 hq72c hq72g hb72 (fun hx => nbb72 ⟨hx, hb72⟩)
      | exact killB3v_37 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hn15 hq21c hq21g hn21 hq27c hq27g hb27 (fun hx => nbb27 ⟨hx, hb27⟩) hq56c hq56g hb56 (fun hx => nbb56 ⟨hx, hb56⟩)
      | exact killB3v_38 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hn15 hq21c hq21g hn21 hq27c hq27g hb27 (fun hx => nbb27 ⟨hx, hb27⟩) hq64c hq64g hb64 (fun hx => nbb64 ⟨hx, hb64⟩)
      | exact killB3v_39 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hn15 hq21c hq21g hn21 hq27c hq27g hb27 (fun hx => nbb27 ⟨hx, hb27⟩) hq72c hq72g hb72 (fun hx => nbb72 ⟨hx, hb72⟩)

/-- **Pair kill: gadgets 1,2 both mark `u` (proved)**. -/
theorem killPair_12u {u v : ℕ} (hR : reconvR c = {u, v})
    (huv : ¬ Reach c u v) (hvu : ¬ Reach c v u) {q34 q41 q48 q56 q64 q72 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hq56c : q56 ∈ cone c) (hq56g : c.getD q56 (.cst false) = CGate.var ⟨56, h56⟩)
    (hq64c : q64 ∈ cone c) (hq64g : c.getD q64 (.cst false) = CGate.var ⟨64, h64⟩)
    (hq72c : q72 ∈ cone c) (hq72g : c.getD q72 (.cst false) = CGate.var ⟨72, h72⟩)
    (h0 : (Reach c u q34 ∧ ¬ Reach c u q41 ∧ ¬ Reach c u q48) ∨
     (¬ Reach c u q34 ∧ Reach c u q41 ∧ ¬ Reach c u q48) ∨
     (¬ Reach c u q34 ∧ ¬ Reach c u q41 ∧ Reach c u q48))
    (h1 : (Reach c u q56 ∧ ¬ Reach c u q64 ∧ ¬ Reach c u q72) ∨
     (¬ Reach c u q56 ∧ Reach c u q64 ∧ ¬ Reach c u q72) ∨
     (¬ Reach c u q56 ∧ ¬ Reach c u q64 ∧ Reach c u q72)) : False := by
  have nbb34 := not_below_both c hs hR huv hvu q34 hq34c
  have nbb41 := not_below_both c hs hR huv hvu q41 hq41c
  have nbb48 := not_below_both c hs hR huv hvu q48 hq48c
  have nbb56 := not_below_both c hs hR huv hvu q56 hq56c
  have nbb64 := not_below_both c hs hR huv hvu q64 hq64c
  have nbb72 := not_below_both c hs hR huv hvu q72 hq72c
  rcases h0 with ⟨hb34, hn41, hn48⟩ | ⟨hn34, hb41, hn48⟩ | ⟨hn34, hn41, hb48⟩ <;>
    rcases h1 with ⟨hb56, hn64, hn72⟩ | ⟨hn56, hb64, hn72⟩ | ⟨hn56, hn64, hb72⟩ <;>
    first
      | exact killB3v_47 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hb34 (fun hx => nbb34 ⟨hb34, hx⟩) hq41c hq41g hn41 hq48c hq48g hn48 hq56c hq56g hb56 (fun hx => nbb56 ⟨hb56, hx⟩)
      | exact killB3v_48 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hb34 (fun hx => nbb34 ⟨hb34, hx⟩) hq41c hq41g hn41 hq48c hq48g hn48 hq64c hq64g hb64 (fun hx => nbb64 ⟨hb64, hx⟩)
      | exact killB3v_49 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hb34 (fun hx => nbb34 ⟨hb34, hx⟩) hq41c hq41g hn41 hq48c hq48g hn48 hq72c hq72g hb72 (fun hx => nbb72 ⟨hb72, hx⟩)
      | exact killB3v_57 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hn34 hq41c hq41g hb41 (fun hx => nbb41 ⟨hb41, hx⟩) hq48c hq48g hn48 hq56c hq56g hb56 (fun hx => nbb56 ⟨hb56, hx⟩)
      | exact killB3v_58 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hn34 hq41c hq41g hb41 (fun hx => nbb41 ⟨hb41, hx⟩) hq48c hq48g hn48 hq64c hq64g hb64 (fun hx => nbb64 ⟨hb64, hx⟩)
      | exact killB3v_59 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hn34 hq41c hq41g hb41 (fun hx => nbb41 ⟨hb41, hx⟩) hq48c hq48g hn48 hq72c hq72g hb72 (fun hx => nbb72 ⟨hb72, hx⟩)
      | exact killB3v_67 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hn34 hq41c hq41g hn41 hq48c hq48g hb48 (fun hx => nbb48 ⟨hb48, hx⟩) hq56c hq56g hb56 (fun hx => nbb56 ⟨hb56, hx⟩)
      | exact killB3v_68 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hn34 hq41c hq41g hn41 hq48c hq48g hb48 (fun hx => nbb48 ⟨hb48, hx⟩) hq64c hq64g hb64 (fun hx => nbb64 ⟨hb64, hx⟩)
      | exact killB3v_69 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hn34 hq41c hq41g hn41 hq48c hq48g hb48 (fun hx => nbb48 ⟨hb48, hx⟩) hq72c hq72g hb72 (fun hx => nbb72 ⟨hb72, hx⟩)

/-- **Pair kill: gadgets 1,2 both mark `v` (proved)**. -/
theorem killPair_12v {u v : ℕ} (hR : reconvR c = {u, v})
    (huv : ¬ Reach c u v) (hvu : ¬ Reach c v u) {q34 q41 q48 q56 q64 q72 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hq56c : q56 ∈ cone c) (hq56g : c.getD q56 (.cst false) = CGate.var ⟨56, h56⟩)
    (hq64c : q64 ∈ cone c) (hq64g : c.getD q64 (.cst false) = CGate.var ⟨64, h64⟩)
    (hq72c : q72 ∈ cone c) (hq72g : c.getD q72 (.cst false) = CGate.var ⟨72, h72⟩)
    (h0 : (Reach c v q34 ∧ ¬ Reach c v q41 ∧ ¬ Reach c v q48) ∨
     (¬ Reach c v q34 ∧ Reach c v q41 ∧ ¬ Reach c v q48) ∨
     (¬ Reach c v q34 ∧ ¬ Reach c v q41 ∧ Reach c v q48))
    (h1 : (Reach c v q56 ∧ ¬ Reach c v q64 ∧ ¬ Reach c v q72) ∨
     (¬ Reach c v q56 ∧ Reach c v q64 ∧ ¬ Reach c v q72) ∨
     (¬ Reach c v q56 ∧ ¬ Reach c v q64 ∧ Reach c v q72)) : False := by
  have hRs : reconvR c = {v, u} := by rw [hR]; exact Finset.pair_comm u v
  have nbb34 := not_below_both c hs hR huv hvu q34 hq34c
  have nbb41 := not_below_both c hs hR huv hvu q41 hq41c
  have nbb48 := not_below_both c hs hR huv hvu q48 hq48c
  have nbb56 := not_below_both c hs hR huv hvu q56 hq56c
  have nbb64 := not_below_both c hs hR huv hvu q64 hq64c
  have nbb72 := not_below_both c hs hR huv hvu q72 hq72c
  rcases h0 with ⟨hb34, hn41, hn48⟩ | ⟨hn34, hb41, hn48⟩ | ⟨hn34, hn41, hb48⟩ <;>
    rcases h1 with ⟨hb56, hn64, hn72⟩ | ⟨hn56, hb64, hn72⟩ | ⟨hn56, hn64, hb72⟩ <;>
    first
      | exact killB3v_47 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq34c hq34g hb34 (fun hx => nbb34 ⟨hx, hb34⟩) hq41c hq41g hn41 hq48c hq48g hn48 hq56c hq56g hb56 (fun hx => nbb56 ⟨hx, hb56⟩)
      | exact killB3v_48 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq34c hq34g hb34 (fun hx => nbb34 ⟨hx, hb34⟩) hq41c hq41g hn41 hq48c hq48g hn48 hq64c hq64g hb64 (fun hx => nbb64 ⟨hx, hb64⟩)
      | exact killB3v_49 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq34c hq34g hb34 (fun hx => nbb34 ⟨hx, hb34⟩) hq41c hq41g hn41 hq48c hq48g hn48 hq72c hq72g hb72 (fun hx => nbb72 ⟨hx, hb72⟩)
      | exact killB3v_57 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq34c hq34g hn34 hq41c hq41g hb41 (fun hx => nbb41 ⟨hx, hb41⟩) hq48c hq48g hn48 hq56c hq56g hb56 (fun hx => nbb56 ⟨hx, hb56⟩)
      | exact killB3v_58 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq34c hq34g hn34 hq41c hq41g hb41 (fun hx => nbb41 ⟨hx, hb41⟩) hq48c hq48g hn48 hq64c hq64g hb64 (fun hx => nbb64 ⟨hx, hb64⟩)
      | exact killB3v_59 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq34c hq34g hn34 hq41c hq41g hb41 (fun hx => nbb41 ⟨hx, hb41⟩) hq48c hq48g hn48 hq72c hq72g hb72 (fun hx => nbb72 ⟨hx, hb72⟩)
      | exact killB3v_67 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq34c hq34g hn34 hq41c hq41g hn41 hq48c hq48g hb48 (fun hx => nbb48 ⟨hx, hb48⟩) hq56c hq56g hb56 (fun hx => nbb56 ⟨hx, hb56⟩)
      | exact killB3v_68 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq34c hq34g hn34 hq41c hq41g hn41 hq48c hq48g hb48 (fun hx => nbb48 ⟨hx, hb48⟩) hq64c hq64g hb64 (fun hx => nbb64 ⟨hx, hb64⟩)
      | exact killB3v_69 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq34c hq34g hn34 hq41c hq41g hn41 hq48c hq48g hb48 (fun hx => nbb48 ⟨hx, hb48⟩) hq72c hq72g hb72 (fun hx => nbb72 ⟨hx, hb72⟩)

/-- **The parallel two-wire case (proved)**: no circuit at `budget ≤ 2d+1`
computes the slice with two *parallel* reconvergence wires. -/
theorem killParallel3 {u v : ℕ} (hR : reconvR c = {u, v})
    (huv : ¬ Reach c u v) (hvu : ¬ Reach c v u) : False := by
  obtain ⟨q15, hq15c, hq15g⟩ := dep_var_gate (SATFamily N) c hcomp hs _
    (sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72)
  obtain ⟨q21, hq21c, hq21g⟩ := dep_var_gate (SATFamily N) c hcomp hs _
    (sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72)
  obtain ⟨q27, hq27c, hq27g⟩ := dep_var_gate (SATFamily N) c hcomp hs _
    (sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72)
  obtain ⟨q34, hq34c, hq34g⟩ := dep_var_gate (SATFamily N) c hcomp hs _
    (sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72)
  obtain ⟨q41, hq41c, hq41g⟩ := dep_var_gate (SATFamily N) c hcomp hs _
    (sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72)
  obtain ⟨q48, hq48c, hq48g⟩ := dep_var_gate (SATFamily N) c hcomp hs _
    (sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72)
  obtain ⟨q56, hq56c, hq56g⟩ := dep_var_gate (SATFamily N) c hcomp hs _
    (sign56_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72)
  obtain ⟨q64, hq64c, hq64g⟩ := dep_var_gate (SATFamily N) c hcomp hs _
    (sign64_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72)
  obtain ⟨q72, hq72c, hq72g⟩ := dep_var_gate (SATFamily N) c hcomp hs _
    (sign72_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72)
  have hm0 := gadget_marks_g0 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR huv hvu hq15c hq15g hq21c hq21g hq27c hq27g
  have hm1 := gadget_marks_g1 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR huv hvu hq34c hq34g hq41c hq41g hq48c hq48g
  have hm2 := gadget_marks_g2 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR huv hvu hq56c hq56g hq64c hq64g hq72c hq72g
  have hg0 : ((Reach c u q15 ∧ ¬ Reach c u q21 ∧ ¬ Reach c u q27) ∨
     (¬ Reach c u q15 ∧ Reach c u q21 ∧ ¬ Reach c u q27) ∨
     (¬ Reach c u q15 ∧ ¬ Reach c u q21 ∧ Reach c u q27)) ∨
     ((Reach c v q15 ∧ ¬ Reach c v q21 ∧ ¬ Reach c v q27) ∨
     (¬ Reach c v q15 ∧ Reach c v q21 ∧ ¬ Reach c v q27) ∨
     (¬ Reach c v q15 ∧ ¬ Reach c v q21 ∧ Reach c v q27)) := by
    rcases hm0 with h | h | h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hg1 : ((Reach c u q34 ∧ ¬ Reach c u q41 ∧ ¬ Reach c u q48) ∨
     (¬ Reach c u q34 ∧ Reach c u q41 ∧ ¬ Reach c u q48) ∨
     (¬ Reach c u q34 ∧ ¬ Reach c u q41 ∧ Reach c u q48)) ∨
     ((Reach c v q34 ∧ ¬ Reach c v q41 ∧ ¬ Reach c v q48) ∨
     (¬ Reach c v q34 ∧ Reach c v q41 ∧ ¬ Reach c v q48) ∨
     (¬ Reach c v q34 ∧ ¬ Reach c v q41 ∧ Reach c v q48)) := by
    rcases hm1 with h | h | h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hg2 : ((Reach c u q56 ∧ ¬ Reach c u q64 ∧ ¬ Reach c u q72) ∨
     (¬ Reach c u q56 ∧ Reach c u q64 ∧ ¬ Reach c u q72) ∨
     (¬ Reach c u q56 ∧ ¬ Reach c u q64 ∧ Reach c u q72)) ∨
     ((Reach c v q56 ∧ ¬ Reach c v q64 ∧ ¬ Reach c v q72) ∨
     (¬ Reach c v q56 ∧ Reach c v q64 ∧ ¬ Reach c v q72) ∨
     (¬ Reach c v q56 ∧ ¬ Reach c v q64 ∧ Reach c v q72)) := by
    rcases hm2 with h | h | h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  rcases hg0 with hU0 | hV0 <;> rcases hg1 with hU1 | hV1 <;>
    rcases hg2 with hU2 | hV2 <;>
    first
      | exact killPair_01u N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR huv hvu hq15c hq15g hq21c hq21g hq27c hq27g hq34c hq34g hq41c hq41g hq48c hq48g hU0 hU1
      | exact killPair_02u N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR huv hvu hq15c hq15g hq21c hq21g hq27c hq27g hq56c hq56g hq64c hq64g hq72c hq72g hU0 hU2
      | exact killPair_12u N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR huv hvu hq34c hq34g hq41c hq41g hq48c hq48g hq56c hq56g hq64c hq64g hq72c hq72g hU1 hU2
      | exact killPair_01v N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR huv hvu hq15c hq15g hq21c hq21g hq27c hq27g hq34c hq34g hq41c hq41g hq48c hq48g hV0 hV1
      | exact killPair_02v N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR huv hvu hq15c hq15g hq21c hq21g hq27c hq27g hq56c hq56g hq64c hq64g hq72c hq72g hV0 hV2
      | exact killPair_12v N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR huv hvu hq34c hq34g hq41c hq41g hq48c hq48g hq56c hq56g hq64c hq64g hq72c hq72g hV1 hV2

end ParDispatch

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
