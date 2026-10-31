import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATParBelowBoth

/-!
# Parallel profile-reduction: each gadget marks a wire with a one-below witness

Multi-wire brick 10a.  At two parallel reconvergence wires
`reconvR c = {u, v}` (`¬ Reach c u v`, `¬ Reach c v u`), a single gadget
either falls to one of the single-gadget kills, or it exhibits **exactly one
sign below a wire with the other two signs avoiding that wire** — the precise
shape the `killB3v` pair kills consume.

Because `not_below_both` forbids a sign below both wires, the six reach flags
of a gadget's three signs collapse: any sign below both is impossible; all
signs avoiding both is `killA2`; two signs below the same wire is
`killB2v`/`killB1v` (directly for `u`, via the swapped pair `{v,u}` for `v`);
the remaining survivors have at most one sign below each wire, hence a
one-below marker.

* **`gadget_marks_g0/g1/g2` (proved)** — for each gadget, a six-way marker
  disjunction (`⟨below-u at slot 1/2/3⟩` or `⟨below-v at slot 1/2/3⟩`),
  generic in the wire pair.

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

section ParProfile

variable (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N) (h27 : 27 < N)
  (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N) (h64 : 64 < N)
  (h72 : 72 < N)
  (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
  (hWd : (coneVars c).card ≤ (depSet (SATFamily N)).card)

include hN h15 h21 h27 h34 h41 h48 h56 h64 h72 hcomp hs hWd

/-- **Gadget-0 profile reduction (proved)**. -/
theorem gadget_marks_g0 {u v : ℕ} (hR : reconvR c = {u, v})
    (huv : ¬ Reach c u v) (hvu : ¬ Reach c v u)
    {q15 q21 q27 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩) :
    (Reach c u q15 ∧ ¬ Reach c u q21 ∧ ¬ Reach c u q27) ∨
    (¬ Reach c u q15 ∧ Reach c u q21 ∧ ¬ Reach c u q27) ∨
    (¬ Reach c u q15 ∧ ¬ Reach c u q21 ∧ Reach c u q27) ∨
    (Reach c v q15 ∧ ¬ Reach c v q21 ∧ ¬ Reach c v q27) ∨
    (¬ Reach c v q15 ∧ Reach c v q21 ∧ ¬ Reach c v q27) ∨
    (¬ Reach c v q15 ∧ ¬ Reach c v q21 ∧ Reach c v q27) := by
  have hRs : reconvR c = {v, u} := by rw [hR]; exact Finset.pair_comm u v
  have nbb15 := not_below_both c hs hR huv hvu q15 hq15c
  have nbb21 := not_below_both c hs hR huv hvu q21 hq21c
  have nbb27 := not_below_both c hs hR huv hvu q27 hq27c
  by_cases hu15 : Reach c u q15 <;> by_cases hv15 : Reach c v q15 <;>
    by_cases hu21 : Reach c u q21 <;> by_cases hv21 : Reach c v q21 <;>
    by_cases hu27 : Reach c u q27 <;> by_cases hv27 : Reach c v q27 <;>
    first
      | exact (nbb15 ⟨hu15, hv15⟩).elim
      | exact (nbb21 ⟨hu21, hv21⟩).elim
      | exact (nbb27 ⟨hu27, hv27⟩).elim
      | exact (killA2_g0 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hu15 hv15 hq21c hq21g hu21 hv21 hq27c hq27g hu27 hv27).elim
      | exact (killB1v_g0 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR huv
          hq15c hq15g hu15 hv15 hq21c hq21g hu21 hv21 hq27c hq27g hu27 hv27).elim
      | exact (killB2v_g0_free1 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hu15 hq21c hq21g hu21 hv21 hq27c hq27g hu27 hv27).elim
      | exact (killB2v_g0_free2 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hu15 hv15 hq21c hq21g hu21 hq27c hq27g hu27 hv27).elim
      | exact (killB2v_g0_free3 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq15c hq15g hu15 hv15 hq21c hq21g hu21 hv21 hq27c hq27g hu27).elim
      | exact (killB1v_g0 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs hvu
          hq15c hq15g hv15 hu15 hq21c hq21g hv21 hu21 hq27c hq27g hv27 hu27).elim
      | exact (killB2v_g0_free1 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hv15 hq21c hq21g hv21 hu21 hq27c hq27g hv27 hu27).elim
      | exact (killB2v_g0_free2 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hv15 hu15 hq21c hq21g hv21 hq27c hq27g hv27 hu27).elim
      | exact (killB2v_g0_free3 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq15c hq15g hv15 hu15 hq21c hq21g hv21 hu21 hq27c hq27g hv27).elim
      | exact Or.inl ⟨hu15, hu21, hu27⟩
      | exact Or.inr (Or.inl ⟨hu15, hu21, hu27⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨hu15, hu21, hu27⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hv15, hv21, hv27⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv15, hv21, hv27⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hv15, hv21, hv27⟩))))


/-- **Gadget-1 profile reduction (proved)**. -/
theorem gadget_marks_g1 {u v : ℕ} (hR : reconvR c = {u, v})
    (huv : ¬ Reach c u v) (hvu : ¬ Reach c v u)
    {q34 q41 q48 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩) :
    (Reach c u q34 ∧ ¬ Reach c u q41 ∧ ¬ Reach c u q48) ∨
    (¬ Reach c u q34 ∧ Reach c u q41 ∧ ¬ Reach c u q48) ∨
    (¬ Reach c u q34 ∧ ¬ Reach c u q41 ∧ Reach c u q48) ∨
    (Reach c v q34 ∧ ¬ Reach c v q41 ∧ ¬ Reach c v q48) ∨
    (¬ Reach c v q34 ∧ Reach c v q41 ∧ ¬ Reach c v q48) ∨
    (¬ Reach c v q34 ∧ ¬ Reach c v q41 ∧ Reach c v q48) := by
  have hRs : reconvR c = {v, u} := by rw [hR]; exact Finset.pair_comm u v
  have nbb34 := not_below_both c hs hR huv hvu q34 hq34c
  have nbb41 := not_below_both c hs hR huv hvu q41 hq41c
  have nbb48 := not_below_both c hs hR huv hvu q48 hq48c
  by_cases hu34 : Reach c u q34 <;> by_cases hv34 : Reach c v q34 <;>
    by_cases hu41 : Reach c u q41 <;> by_cases hv41 : Reach c v q41 <;>
    by_cases hu48 : Reach c u q48 <;> by_cases hv48 : Reach c v q48 <;>
    first
      | exact (nbb34 ⟨hu34, hv34⟩).elim
      | exact (nbb41 ⟨hu41, hv41⟩).elim
      | exact (nbb48 ⟨hu48, hv48⟩).elim
      | exact (killA2_g1 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hu34 hv34 hq41c hq41g hu41 hv41 hq48c hq48g hu48 hv48).elim
      | exact (killB1v_g1 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR huv
          hq34c hq34g hu34 hv34 hq41c hq41g hu41 hv41 hq48c hq48g hu48 hv48).elim
      | exact (killB2v_g1_free4 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hu34 hq41c hq41g hu41 hv41 hq48c hq48g hu48 hv48).elim
      | exact (killB2v_g1_free5 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hu34 hv34 hq41c hq41g hu41 hq48c hq48g hu48 hv48).elim
      | exact (killB2v_g1_free6 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq34c hq34g hu34 hv34 hq41c hq41g hu41 hv41 hq48c hq48g hu48).elim
      | exact (killB1v_g1 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs hvu
          hq34c hq34g hv34 hu34 hq41c hq41g hv41 hu41 hq48c hq48g hv48 hu48).elim
      | exact (killB2v_g1_free4 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq34c hq34g hv34 hq41c hq41g hv41 hu41 hq48c hq48g hv48 hu48).elim
      | exact (killB2v_g1_free5 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq34c hq34g hv34 hu34 hq41c hq41g hv41 hq48c hq48g hv48 hu48).elim
      | exact (killB2v_g1_free6 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq34c hq34g hv34 hu34 hq41c hq41g hv41 hu41 hq48c hq48g hv48).elim
      | exact Or.inl ⟨hu34, hu41, hu48⟩
      | exact Or.inr (Or.inl ⟨hu34, hu41, hu48⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨hu34, hu41, hu48⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hv34, hv41, hv48⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv34, hv41, hv48⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hv34, hv41, hv48⟩))))

/-- **Gadget-2 profile reduction (proved)**. -/
theorem gadget_marks_g2 {u v : ℕ} (hR : reconvR c = {u, v})
    (huv : ¬ Reach c u v) (hvu : ¬ Reach c v u)
    {q56 q64 q72 : ℕ}
    (hq56c : q56 ∈ cone c) (hq56g : c.getD q56 (.cst false) = CGate.var ⟨56, h56⟩)
    (hq64c : q64 ∈ cone c) (hq64g : c.getD q64 (.cst false) = CGate.var ⟨64, h64⟩)
    (hq72c : q72 ∈ cone c) (hq72g : c.getD q72 (.cst false) = CGate.var ⟨72, h72⟩) :
    (Reach c u q56 ∧ ¬ Reach c u q64 ∧ ¬ Reach c u q72) ∨
    (¬ Reach c u q56 ∧ Reach c u q64 ∧ ¬ Reach c u q72) ∨
    (¬ Reach c u q56 ∧ ¬ Reach c u q64 ∧ Reach c u q72) ∨
    (Reach c v q56 ∧ ¬ Reach c v q64 ∧ ¬ Reach c v q72) ∨
    (¬ Reach c v q56 ∧ Reach c v q64 ∧ ¬ Reach c v q72) ∨
    (¬ Reach c v q56 ∧ ¬ Reach c v q64 ∧ Reach c v q72) := by
  have hRs : reconvR c = {v, u} := by rw [hR]; exact Finset.pair_comm u v
  have nbb56 := not_below_both c hs hR huv hvu q56 hq56c
  have nbb64 := not_below_both c hs hR huv hvu q64 hq64c
  have nbb72 := not_below_both c hs hR huv hvu q72 hq72c
  by_cases hu56 : Reach c u q56 <;> by_cases hv56 : Reach c v q56 <;>
    by_cases hu64 : Reach c u q64 <;> by_cases hv64 : Reach c v q64 <;>
    by_cases hu72 : Reach c u q72 <;> by_cases hv72 : Reach c v q72 <;>
    first
      | exact (nbb56 ⟨hu56, hv56⟩).elim
      | exact (nbb64 ⟨hu64, hv64⟩).elim
      | exact (nbb72 ⟨hu72, hv72⟩).elim
      | exact (killA2_g2 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq56c hq56g hu56 hv56 hq64c hq64g hu64 hv64 hq72c hq72g hu72 hv72).elim
      | exact (killB1v_g2 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR huv
          hq56c hq56g hu56 hv56 hq64c hq64g hu64 hv64 hq72c hq72g hu72 hv72).elim
      | exact (killB2v_g2_free7 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq56c hq56g hu56 hq64c hq64g hu64 hv64 hq72c hq72g hu72 hv72).elim
      | exact (killB2v_g2_free8 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq56c hq56g hu56 hv56 hq64c hq64g hu64 hq72c hq72g hu72 hv72).elim
      | exact (killB2v_g2_free9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hR
          hq56c hq56g hu56 hv56 hq64c hq64g hu64 hv64 hq72c hq72g hu72).elim
      | exact (killB1v_g2 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs hvu
          hq56c hq56g hv56 hu56 hq64c hq64g hv64 hu64 hq72c hq72g hv72 hu72).elim
      | exact (killB2v_g2_free7 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq56c hq56g hv56 hq64c hq64g hv64 hu64 hq72c hq72g hv72 hu72).elim
      | exact (killB2v_g2_free8 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq56c hq56g hv56 hu56 hq64c hq64g hv64 hq72c hq72g hv72 hu72).elim
      | exact (killB2v_g2_free9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hWd hRs
          hq56c hq56g hv56 hu56 hq64c hq64g hv64 hu64 hq72c hq72g hv72).elim
      | exact Or.inl ⟨hu56, hu64, hu72⟩
      | exact Or.inr (Or.inl ⟨hu56, hu64, hu72⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨hu56, hu64, hu72⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hv56, hv64, hv72⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv56, hv64, hv72⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hv56, hv64, hv72⟩))))

end ParProfile

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
