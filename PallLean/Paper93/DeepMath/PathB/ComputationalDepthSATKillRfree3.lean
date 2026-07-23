import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATNineSub

/-!
# The case-(i) kill: no reconvergence-free circuit near `2·deps + 1`

Multi-wire brick 4.  At var-gate budget `deps + 1`, at most ONE variable is
duplicated (`dup_at_most_one`) — so among the three codec gadgets at least one
has all three sign gates unique.  Reconvergence-free, that gadget's triple
unwinds to `cnt = 1` (`extractG_cnt_spec`), splits (`gtree_split_cnt`), and the
codec's `AllEqual₃` refuses.

* **`rfree3_kill_g0` / `rfree3_kill_g1` (proved)** — the per-gadget split kills,
  hypothesised on per-coordinate uniqueness;
* **`killRfree3` (proved)** — THE CASE-(i) KILL: any reconvergence-free circuit
  with var-gate budget `deps + 1` computing a SAT slice of length `≥ 73` is
  impossible — the duplicated variable (if any) lives in at most one gadget, and
  a fully-unique gadget dies.

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

/-- **Gadget-0 split kill under per-coordinate uniqueness (proved)**. -/
theorem rfree3_kill_g0 (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N)
    (h27 : 27 < N) (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N)
    (h64 : 64 < N) (h72 : 72 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hrf : reconvR c = ∅)
    (hu15 : ∀ q₁ ∈ cone c, ∀ q₂ ∈ cone c,
      c.getD q₁ (.cst false) = CGate.var (⟨15, h15⟩ : Fin N) →
      c.getD q₂ (.cst false) = CGate.var (⟨15, h15⟩ : Fin N) → q₁ = q₂)
    (hu21 : ∀ q₁ ∈ cone c, ∀ q₂ ∈ cone c,
      c.getD q₁ (.cst false) = CGate.var (⟨21, h21⟩ : Fin N) →
      c.getD q₂ (.cst false) = CGate.var (⟨21, h21⟩ : Fin N) → q₁ = q₂)
    (hu27 : ∀ q₁ ∈ cone c, ∀ q₂ ∈ cone c,
      c.getD q₁ (.cst false) = CGate.var (⟨27, h27⟩ : Fin N) →
      c.getD q₂ (.cst false) = CGate.var (⟨27, h27⟩ : Fin N) → q₁ = q₂) : False := by
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  obtain ⟨q15, hq15c, hq15g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd15
  obtain ⟨q21, hq21c, hq21g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd21
  obtain ⟨q27, hq27c, hq27g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd27
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  have hRvac : ∀ q₀ : ℕ, ∀ u' ∈ reconvR c, ¬ Reach c u' q₀ := by
    intro q₀ u' hu'
    rw [hrf] at hu'
    exact absurd hu' (Finset.notMem_empty u')
  have hcnt15 := (extractG_cnt_spec c hs ⟨15, h15⟩ q15 hq15c hq15g
      (fun q hq hg => hu15 q hq q15 hq15c hg hq15g)
      (hRvac q15) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq15c).2)
  have hcnt21 := (extractG_cnt_spec c hs ⟨21, h21⟩ q21 hq21c hq21g
      (fun q hq hg => hu21 q hq q21 hq21c hg hq21g)
      (hRvac q21) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq21c).2)
  have hcnt27 := (extractG_cnt_spec c hs ⟨27, h27⟩ q27 hq27c hq27g
      (fun q hq hg => hu27 q hq q27 hq27c hg hq27g)
      (hRvac q27) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq27c).2)
  have hsp := gtree_split_cnt (extractG c c.length (c.length - 1))
    ⟨15, h15⟩ ⟨21, h21⟩ ⟨27, h27⟩
    (fne h15 h21 (by omega)) (fne h15 h27 (by omega)) (fne h21 h27 (by omega))
    (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true true)
    hcnt15 hcnt21 hcnt27
  have heval : ∀ y, (extractG c c.length (c.length - 1)).eval y = SATFamily N y := by
    intro y
    rw [extractG_eval c c.length (c.length - 1) (by omega) (by omega) y]
    exact hcomp y
  have heq : (fun a b g => (extractG c c.length (c.length - 1)).eval
      (Function.update (Function.update (Function.update
        (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true true true true true true true)
        ⟨15, h15⟩ a) ⟨21, h21⟩ b) ⟨27, h27⟩ g)) = allEq3 := by
    funext a b g
    rw [nineUpd_upd1, nineUpd_upd2, nineUpd_upd3, heval,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a b g true true true true true true,
      show allEq3 true true true = true from rfl, Bool.and_true, Bool.and_true]
  rw [heq] at hsp
  rcases hsp with h | h | h
  · exact allEq3_no_split_a h
  · exact allEq3_no_split_b h
  · exact allEq3_no_split_c h

/-- **Gadget-1 split kill under per-coordinate uniqueness (proved)**. -/
theorem rfree3_kill_g1 (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N)
    (h27 : 27 < N) (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N)
    (h64 : 64 < N) (h72 : 72 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hrf : reconvR c = ∅)
    (hu34 : ∀ q₁ ∈ cone c, ∀ q₂ ∈ cone c,
      c.getD q₁ (.cst false) = CGate.var (⟨34, h34⟩ : Fin N) →
      c.getD q₂ (.cst false) = CGate.var (⟨34, h34⟩ : Fin N) → q₁ = q₂)
    (hu41 : ∀ q₁ ∈ cone c, ∀ q₂ ∈ cone c,
      c.getD q₁ (.cst false) = CGate.var (⟨41, h41⟩ : Fin N) →
      c.getD q₂ (.cst false) = CGate.var (⟨41, h41⟩ : Fin N) → q₁ = q₂)
    (hu48 : ∀ q₁ ∈ cone c, ∀ q₂ ∈ cone c,
      c.getD q₁ (.cst false) = CGate.var (⟨48, h48⟩ : Fin N) →
      c.getD q₂ (.cst false) = CGate.var (⟨48, h48⟩ : Fin N) → q₁ = q₂) : False := by
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  obtain ⟨q34, hq34c, hq34g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd34
  obtain ⟨q41, hq41c, hq41g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd41
  obtain ⟨q48, hq48c, hq48g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd48
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  have hRvac : ∀ q₀ : ℕ, ∀ u' ∈ reconvR c, ¬ Reach c u' q₀ := by
    intro q₀ u' hu'
    rw [hrf] at hu'
    exact absurd hu' (Finset.notMem_empty u')
  have hcnt34 := (extractG_cnt_spec c hs ⟨34, h34⟩ q34 hq34c hq34g
      (fun q hq hg => hu34 q hq q34 hq34c hg hq34g)
      (hRvac q34) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq34c).2)
  have hcnt41 := (extractG_cnt_spec c hs ⟨41, h41⟩ q41 hq41c hq41g
      (fun q hq hg => hu41 q hq q41 hq41c hg hq41g)
      (hRvac q41) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq41c).2)
  have hcnt48 := (extractG_cnt_spec c hs ⟨48, h48⟩ q48 hq48c hq48g
      (fun q hq hg => hu48 q hq q48 hq48c hg hq48g)
      (hRvac q48) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq48c).2)
  have hsp := gtree_split_cnt (extractG c c.length (c.length - 1))
    ⟨34, h34⟩ ⟨41, h41⟩ ⟨48, h48⟩
    (fne h34 h41 (by omega)) (fne h34 h48 (by omega)) (fne h41 h48 (by omega))
    (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true true)
    hcnt34 hcnt41 hcnt48
  have heval : ∀ y, (extractG c c.length (c.length - 1)).eval y = SATFamily N y := by
    intro y
    rw [extractG_eval c c.length (c.length - 1) (by omega) (by omega) y]
    exact hcomp y
  have heq : (fun a b g => (extractG c c.length (c.length - 1)).eval
      (Function.update (Function.update (Function.update
        (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true true true true true true true)
        ⟨34, h34⟩ a) ⟨41, h41⟩ b) ⟨48, h48⟩ g)) = allEq3 := by
    funext a b g
    rw [nineUpd_upd4, nineUpd_upd5, nineUpd_upd6, heval,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a b g true true true,
      show allEq3 true true true = true from rfl, Bool.and_true, Bool.true_and]
  rw [heq] at hsp
  rcases hsp with h | h | h
  · exact allEq3_no_split_a h
  · exact allEq3_no_split_b h
  · exact allEq3_no_split_c h

/-- **THE CASE-(i) KILL (proved)**: no reconvergence-free circuit with var-gate
budget `deps + 1` computes a SAT slice of length `≥ 73`. -/
theorem killRfree3 (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N)
    (h27 : 27 < N) (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N)
    (h64 : 64 < N) (h72 : 72 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hWd : (coneVars c).card ≤ (depSet (SATFamily N)).card + 1)
    (hrf : reconvR c = ∅) : False := by
  classical
  -- if any gadget-0 coordinate is duplicated, gadget 1 is fully unique
  have hg1_of_dup : ∀ i : Fin N, i ∈ depSet (SATFamily N) →
      i ≠ ⟨34, h34⟩ → i ≠ ⟨41, h41⟩ → i ≠ ⟨48, h48⟩ →
      (∃ q₁, q₁ ∈ cone c ∧ c.getD q₁ (.cst false) = CGate.var i ∧
        ∃ q₂, q₂ ∈ cone c ∧ c.getD q₂ (.cst false) = CGate.var i ∧ q₁ ≠ q₂) →
      False := by
    intro i hdi hne34 hne41 hne48 hdup
    obtain ⟨q₁, hq₁c, hg₁, q₂, hq₂c, hg₂, hne⟩ := hdup
    -- gadget-1 coordinates are then all unique; kill via gadget 1
    have hu34 : ∀ p₁ ∈ cone c, ∀ p₂ ∈ cone c,
        c.getD p₁ (.cst false) = CGate.var (⟨34, h34⟩ : Fin N) →
        c.getD p₂ (.cst false) = CGate.var (⟨34, h34⟩ : Fin N) → p₁ = p₂ := by
      intro p₁ hp₁ p₂ hp₂ hpg₁ hpg₂
      by_contra hpne
      exact dup_at_most_one (SATFamily N) c hcomp hs hWd hdi
        (sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72) hne34
        hq₁c hg₁ hq₂c hg₂ hne hp₁ hpg₁ hp₂ hpg₂ hpne
    have hu41 : ∀ p₁ ∈ cone c, ∀ p₂ ∈ cone c,
        c.getD p₁ (.cst false) = CGate.var (⟨41, h41⟩ : Fin N) →
        c.getD p₂ (.cst false) = CGate.var (⟨41, h41⟩ : Fin N) → p₁ = p₂ := by
      intro p₁ hp₁ p₂ hp₂ hpg₁ hpg₂
      by_contra hpne
      exact dup_at_most_one (SATFamily N) c hcomp hs hWd hdi
        (sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72) hne41
        hq₁c hg₁ hq₂c hg₂ hne hp₁ hpg₁ hp₂ hpg₂ hpne
    have hu48 : ∀ p₁ ∈ cone c, ∀ p₂ ∈ cone c,
        c.getD p₁ (.cst false) = CGate.var (⟨48, h48⟩ : Fin N) →
        c.getD p₂ (.cst false) = CGate.var (⟨48, h48⟩ : Fin N) → p₁ = p₂ := by
      intro p₁ hp₁ p₂ hp₂ hpg₁ hpg₂
      by_contra hpne
      exact dup_at_most_one (SATFamily N) c hcomp hs hWd hdi
        (sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72) hne48
        hq₁c hg₁ hq₂c hg₂ hne hp₁ hpg₁ hp₂ hpg₂ hpne
    exact rfree3_kill_g1 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hrf
      hu34 hu41 hu48
  -- case on gadget-0 uniqueness, coordinate by coordinate
  by_cases hu15 : ∀ q₁ ∈ cone c, ∀ q₂ ∈ cone c,
      c.getD q₁ (.cst false) = CGate.var (⟨15, h15⟩ : Fin N) →
      c.getD q₂ (.cst false) = CGate.var (⟨15, h15⟩ : Fin N) → q₁ = q₂
  · by_cases hu21 : ∀ q₁ ∈ cone c, ∀ q₂ ∈ cone c,
        c.getD q₁ (.cst false) = CGate.var (⟨21, h21⟩ : Fin N) →
        c.getD q₂ (.cst false) = CGate.var (⟨21, h21⟩ : Fin N) → q₁ = q₂
    · by_cases hu27 : ∀ q₁ ∈ cone c, ∀ q₂ ∈ cone c,
          c.getD q₁ (.cst false) = CGate.var (⟨27, h27⟩ : Fin N) →
          c.getD q₂ (.cst false) = CGate.var (⟨27, h27⟩ : Fin N) → q₁ = q₂
      · exact rfree3_kill_g0 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs
          hrf hu15 hu21 hu27
      · push_neg at hu27
        obtain ⟨q₁, hq₁c, q₂, hq₂c, hg₁, hg₂, hne⟩ := hu27
        exact hg1_of_dup ⟨27, h27⟩
          (sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72)
          (fne h27 h34 (by omega)) (fne h27 h41 (by omega)) (fne h27 h48 (by omega))
          ⟨q₁, hq₁c, hg₁, q₂, hq₂c, hg₂, hne⟩
    · push_neg at hu21
      obtain ⟨q₁, hq₁c, q₂, hq₂c, hg₁, hg₂, hne⟩ := hu21
      exact hg1_of_dup ⟨21, h21⟩
        (sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72)
        (fne h21 h34 (by omega)) (fne h21 h41 (by omega)) (fne h21 h48 (by omega))
        ⟨q₁, hq₁c, hg₁, q₂, hq₂c, hg₂, hne⟩
  · push_neg at hu15
    obtain ⟨q₁, hq₁c, q₂, hq₂c, hg₁, hg₂, hne⟩ := hu15
    exact hg1_of_dup ⟨15, h15⟩
      (sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72)
      (fne h15 h34 (by omega)) (fne h15 h41 (by omega)) (fne h15 h48 (by omega))
      ⟨q₁, hq₁c, hg₁, q₂, hq₂c, hg₂, hne⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.rfree3_kill_g0
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.rfree3_kill_g1
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killRfree3
