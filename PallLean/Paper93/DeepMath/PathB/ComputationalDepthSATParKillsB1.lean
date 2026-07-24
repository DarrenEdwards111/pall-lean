import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATParKillsB2

/-!
# Parallel-case B1 kills: a gadget fully below one wire

Multi-wire brick 8b.  At two reconvergence wires `{u, v}` in the **parallel**
position (`¬ Reach c u v`): a gadget with all three signs below `u` (each
avoiding `v`) is impossible.  The engine is the one-wire B1 argument
transported to the pair: the prefix `c.take (u + 1)` is reconvergence-free
**by parallelism** (any reconvergence wire of the prefix lies in its cone,
hence reaches the root `u` inside `c` — for `v` that contradicts
`¬ Reach c u v`, and `u` itself is erased as the prefix root), so the
`extractG`/`gtree_split_cnt` split applies verbatim; the nine-slot refinement
through the pair is `refine_via`, and the split shapes die on
`allEq3_no_split_*`.

* **`killB1v_g0`, `killB1v_g1`, `killB1v_g2` (proved)** — all three gadgets,
  generic in the wire pair (instantiate `{u₁,u₂}` or the swap via
  `Finset.pair_comm`).

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

section ParB1

variable (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N) (h27 : 27 < N)
  (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N) (h64 : 64 < N)
  (h72 : 72 < N)
  (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
  (hWd : (coneVars c).card ≤ (depSet (SATFamily N)).card)

include hN h15 h21 h27 h34 h41 h48 h56 h64 h72 hcomp hs hWd

/-- **Parallel B1, gadget 0 (proved)**: all three gadget-0 signs below `u`
(avoiding `v`), with `v` parallel to `u`, is impossible. -/
theorem killB1v_g0 {u v : ℕ} (hR : reconvR c = {u, v}) (hpar : ¬ Reach c u v)
    {q15 q21 q27 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hb15 : Reach c u q15) (hnb15v : ¬ Reach c v q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hb21 : Reach c u q21) (hnb21v : ¬ Reach c v q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hb27 : Reach c u q27) (hnb27v : ¬ Reach c v q27) : False := by
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have hult : u < c.length := (mem_cone.mp huc).1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hrefine : ∀ p q r p' q' r' : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        p q r true true true true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          p' q' r' true true true true true true) u →
      allEq3 p q r = allEq3 p' q' r' := by
    intro p q r p' q' r' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      p q r true true true true true true p' q' r' true true true true true true
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15,
        fun w hw hg => by
          rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hnb15v⟩)
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
        p' q' r' true true true true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true] at hv
    exact hv
  have hq15le : q15 ≤ u := reach_le hb15
  have hq21le : q21 ≤ u := reach_le hb21
  have hq27le : q27 ≤ u := reach_le hb27
  have htlen : (c.take (u + 1)).length = u + 1 := by
    rw [List.length_take]
    omega
  have hs' : 0 < (c.take (u + 1)).length := by omega
  have hrfree : reconvR (c.take (u + 1)) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro w hw
    obtain ⟨hwne, hwc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hw).1
    have hwfull := reconvR_take_subset c huc hune hw
    rw [hR] at hwfull
    rcases Finset.mem_insert.mp hwfull with hwu | hwv
    · exact hwne (by omega)
    · have hr := inCone_reach_root (mem_cone.mp hwc).2
      rw [show (c.take (u + 1)).length - 1 = u from by omega] at hr
      have hrc : Reach c u w := reach_of_take c hult (le_refl u) hr
      rw [Finset.mem_singleton.mp hwv] at hrc
      exact hpar hrc
  have hucone' : u ∈ cone (c.take (u + 1)) := by
    have hroot' : InCone (c.take (u + 1)) ((c.take (u + 1)).length - 1) := InCone.root
    rw [show (c.take (u + 1)).length - 1 = u from by omega] at hroot'
    exact mem_cone.mpr ⟨by omega, hroot'⟩
  have hRvac : ∀ q₀ : ℕ, ∀ u' ∈ reconvR (c.take (u + 1)),
      ¬ Reach (c.take (u + 1)) u' q₀ := by
    intro q₀ u' hu'
    rw [hrfree] at hu'
    exact absurd hu' (Finset.notMem_empty u')
  have huniq' : ∀ (i : Fin N), i ∈ depSet (SATFamily N) →
      ∀ (qi : ℕ), qi ∈ cone c → c.getD qi (.cst false) = CGate.var i →
      ∀ q ∈ cone (c.take (u + 1)),
        (c.take (u + 1)).getD q (.cst false) = CGate.var i → q = qi := by
    intro i hdi qi hqic hqig q hq hg
    have hqlt : q < (c.take (u + 1)).length := (mem_cone.mp hq).1
    have hqr : Reach (c.take (u + 1)) u q := by
      have hr := inCone_reach_root (mem_cone.mp hq).2
      rw [show (c.take (u + 1)).length - 1 = u from by omega] at hr
      exact hr
    have hqrc : Reach c u q := reach_of_take c hult (le_refl u) hqr
    have hqicn : InCone c q := reach_inCone (mem_cone.mp huc).2 hqrc
    rw [getD_take_eq_g (show q < u + 1 from by omega)] at hg
    exact huniq i hdi q (mem_cone.mpr ⟨inCone_lt hs hqicn, hqicn⟩) qi hqic hg hqig
  have hcnt15 := (extractG_cnt_spec (c.take (u + 1)) hs' ⟨15, h15⟩ q15
      (mem_cone.mpr ⟨by omega, reach_inCone_take c hult hb15⟩)
      (by rw [getD_take_eq_g (show q15 < u + 1 from by omega)]; exact hq15g)
      (huniq' ⟨15, h15⟩ hd15 q15 hq15c hq15g)
      (hRvac q15) (c.take (u + 1)).length u (by omega) hucone').1
      (reach_take_of_reach c hult hb15)
  have hcnt21 := (extractG_cnt_spec (c.take (u + 1)) hs' ⟨21, h21⟩ q21
      (mem_cone.mpr ⟨by omega, reach_inCone_take c hult hb21⟩)
      (by rw [getD_take_eq_g (show q21 < u + 1 from by omega)]; exact hq21g)
      (huniq' ⟨21, h21⟩ hd21 q21 hq21c hq21g)
      (hRvac q21) (c.take (u + 1)).length u (by omega) hucone').1
      (reach_take_of_reach c hult hb21)
  have hcnt27 := (extractG_cnt_spec (c.take (u + 1)) hs' ⟨27, h27⟩ q27
      (mem_cone.mpr ⟨by omega, reach_inCone_take c hult hb27⟩)
      (by rw [getD_take_eq_g (show q27 < u + 1 from by omega)]; exact hq27g)
      (huniq' ⟨27, h27⟩ hd27 q27 hq27c hq27g)
      (hRvac q27) (c.take (u + 1)).length u (by omega) hucone').1
      (reach_take_of_reach c hult hb27)
  have heval' : ∀ y, (extractG (c.take (u + 1)) (c.take (u + 1)).length u).eval y
      = wire c y u := by
    intro y
    rw [extractG_eval (c.take (u + 1)) (c.take (u + 1)).length u (by omega) (by omega) y]
    exact wire_prefix c y (by omega) (by omega)
  have hsp := gtree_split_cnt (extractG (c.take (u + 1)) (c.take (u + 1)).length u)
    ⟨15, h15⟩ ⟨21, h21⟩ ⟨27, h27⟩
    (fne h15 h21 (by omega)) (fne h15 h27 (by omega)) (fne h21 h27 (by omega))
    (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true true)
    hcnt15 hcnt21 hcnt27
  rcases b1_shape (fun p q r =>
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        p q r true true true true true true) u) hrefine
    with hpos | hneg
  · have heq : (fun a b g =>
        (extractG (c.take (u + 1)) (c.take (u + 1)).length u).eval
        (Function.update (Function.update (Function.update
          (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true true true true true true)
          ⟨15, h15⟩ a) ⟨21, h21⟩ b) ⟨27, h27⟩ g)) = allEq3 := by
      funext a b g
      rw [nineUpd_upd1, nineUpd_upd2, nineUpd_upd3, heval']
      exact hpos a b g
    rw [heq] at hsp
    rcases hsp with h | h | h
    · exact allEq3_no_split_a h
    · exact allEq3_no_split_b h
    · exact allEq3_no_split_c h
  · have heq : (fun a b g =>
        (extractG (c.take (u + 1)) (c.take (u + 1)).length u).eval
        (Function.update (Function.update (Function.update
          (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true true true true true true)
          ⟨15, h15⟩ a) ⟨21, h21⟩ b) ⟨27, h27⟩ g))
        = fun a b g => !(allEq3 a b g) := by
      funext a b g
      rw [nineUpd_upd1, nineUpd_upd2, nineUpd_upd3, heval']
      exact hneg a b g
    rw [heq] at hsp
    rcases hsp with h | h | h
    · exact allEq3_no_split_a (split1_comp (fun v => !v) h
        (fun a b g => (Bool.not_not (allEq3 a b g)).symm))
    · exact allEq3_no_split_b (split2_comp (fun v => !v) h
        (fun a b g => (Bool.not_not (allEq3 a b g)).symm))
    · exact allEq3_no_split_c (split3_comp (fun v => !v) h
        (fun a b g => (Bool.not_not (allEq3 a b g)).symm))

/-- **Parallel B1, gadget 1 (proved)**: all three gadget-1 signs below `u`
(avoiding `v`), with `v` parallel to `u`, is impossible. -/
theorem killB1v_g1 {u v : ℕ} (hR : reconvR c = {u, v}) (hpar : ¬ Reach c u v)
    {q34 q41 q48 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hb34 : Reach c u q34) (hnb34v : ¬ Reach c v q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hb41 : Reach c u q41) (hnb41v : ¬ Reach c v q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hb48 : Reach c u q48) (hnb48v : ¬ Reach c v q48) : False := by
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have hult : u < c.length := (mem_cone.mp huc).1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hrefine : ∀ p q r p' q' r' : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true p q r true true true) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true p' q' r' true true true) u →
      allEq3 p q r = allEq3 p' q' r' := by
    intro p q r p' q' r' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true p q r true true true true true true p' q' r' true true true
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34,
        fun w hw hg => by
          rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hnb34v⟩)
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
        true true true p' q' r' true true true] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.and_true,
      Bool.true_and] at hv
    exact hv
  have hq34le : q34 ≤ u := reach_le hb34
  have hq41le : q41 ≤ u := reach_le hb41
  have hq48le : q48 ≤ u := reach_le hb48
  have htlen : (c.take (u + 1)).length = u + 1 := by
    rw [List.length_take]
    omega
  have hs' : 0 < (c.take (u + 1)).length := by omega
  have hrfree : reconvR (c.take (u + 1)) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro w hw
    obtain ⟨hwne, hwc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hw).1
    have hwfull := reconvR_take_subset c huc hune hw
    rw [hR] at hwfull
    rcases Finset.mem_insert.mp hwfull with hwu | hwv
    · exact hwne (by omega)
    · have hr := inCone_reach_root (mem_cone.mp hwc).2
      rw [show (c.take (u + 1)).length - 1 = u from by omega] at hr
      have hrc : Reach c u w := reach_of_take c hult (le_refl u) hr
      rw [Finset.mem_singleton.mp hwv] at hrc
      exact hpar hrc
  have hucone' : u ∈ cone (c.take (u + 1)) := by
    have hroot' : InCone (c.take (u + 1)) ((c.take (u + 1)).length - 1) := InCone.root
    rw [show (c.take (u + 1)).length - 1 = u from by omega] at hroot'
    exact mem_cone.mpr ⟨by omega, hroot'⟩
  have hRvac : ∀ q₀ : ℕ, ∀ u' ∈ reconvR (c.take (u + 1)),
      ¬ Reach (c.take (u + 1)) u' q₀ := by
    intro q₀ u' hu'
    rw [hrfree] at hu'
    exact absurd hu' (Finset.notMem_empty u')
  have huniq' : ∀ (i : Fin N), i ∈ depSet (SATFamily N) →
      ∀ (qi : ℕ), qi ∈ cone c → c.getD qi (.cst false) = CGate.var i →
      ∀ q ∈ cone (c.take (u + 1)),
        (c.take (u + 1)).getD q (.cst false) = CGate.var i → q = qi := by
    intro i hdi qi hqic hqig q hq hg
    have hqlt : q < (c.take (u + 1)).length := (mem_cone.mp hq).1
    have hqr : Reach (c.take (u + 1)) u q := by
      have hr := inCone_reach_root (mem_cone.mp hq).2
      rw [show (c.take (u + 1)).length - 1 = u from by omega] at hr
      exact hr
    have hqrc : Reach c u q := reach_of_take c hult (le_refl u) hqr
    have hqicn : InCone c q := reach_inCone (mem_cone.mp huc).2 hqrc
    rw [getD_take_eq_g (show q < u + 1 from by omega)] at hg
    exact huniq i hdi q (mem_cone.mpr ⟨inCone_lt hs hqicn, hqicn⟩) qi hqic hg hqig
  have hcnt34 := (extractG_cnt_spec (c.take (u + 1)) hs' ⟨34, h34⟩ q34
      (mem_cone.mpr ⟨by omega, reach_inCone_take c hult hb34⟩)
      (by rw [getD_take_eq_g (show q34 < u + 1 from by omega)]; exact hq34g)
      (huniq' ⟨34, h34⟩ hd34 q34 hq34c hq34g)
      (hRvac q34) (c.take (u + 1)).length u (by omega) hucone').1
      (reach_take_of_reach c hult hb34)
  have hcnt41 := (extractG_cnt_spec (c.take (u + 1)) hs' ⟨41, h41⟩ q41
      (mem_cone.mpr ⟨by omega, reach_inCone_take c hult hb41⟩)
      (by rw [getD_take_eq_g (show q41 < u + 1 from by omega)]; exact hq41g)
      (huniq' ⟨41, h41⟩ hd41 q41 hq41c hq41g)
      (hRvac q41) (c.take (u + 1)).length u (by omega) hucone').1
      (reach_take_of_reach c hult hb41)
  have hcnt48 := (extractG_cnt_spec (c.take (u + 1)) hs' ⟨48, h48⟩ q48
      (mem_cone.mpr ⟨by omega, reach_inCone_take c hult hb48⟩)
      (by rw [getD_take_eq_g (show q48 < u + 1 from by omega)]; exact hq48g)
      (huniq' ⟨48, h48⟩ hd48 q48 hq48c hq48g)
      (hRvac q48) (c.take (u + 1)).length u (by omega) hucone').1
      (reach_take_of_reach c hult hb48)
  have heval' : ∀ y, (extractG (c.take (u + 1)) (c.take (u + 1)).length u).eval y
      = wire c y u := by
    intro y
    rw [extractG_eval (c.take (u + 1)) (c.take (u + 1)).length u (by omega) (by omega) y]
    exact wire_prefix c y (by omega) (by omega)
  have hsp := gtree_split_cnt (extractG (c.take (u + 1)) (c.take (u + 1)).length u)
    ⟨34, h34⟩ ⟨41, h41⟩ ⟨48, h48⟩
    (fne h34 h41 (by omega)) (fne h34 h48 (by omega)) (fne h41 h48 (by omega))
    (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true true)
    hcnt34 hcnt41 hcnt48
  rcases b1_shape (fun p q r =>
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true p q r true true true) u) hrefine
    with hpos | hneg
  · have heq : (fun a b g =>
        (extractG (c.take (u + 1)) (c.take (u + 1)).length u).eval
        (Function.update (Function.update (Function.update
          (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true true true true true true)
          ⟨34, h34⟩ a) ⟨41, h41⟩ b) ⟨48, h48⟩ g)) = allEq3 := by
      funext a b g
      rw [nineUpd_upd4, nineUpd_upd5, nineUpd_upd6, heval']
      exact hpos a b g
    rw [heq] at hsp
    rcases hsp with h | h | h
    · exact allEq3_no_split_a h
    · exact allEq3_no_split_b h
    · exact allEq3_no_split_c h
  · have heq : (fun a b g =>
        (extractG (c.take (u + 1)) (c.take (u + 1)).length u).eval
        (Function.update (Function.update (Function.update
          (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true true true true true true)
          ⟨34, h34⟩ a) ⟨41, h41⟩ b) ⟨48, h48⟩ g))
        = fun a b g => !(allEq3 a b g) := by
      funext a b g
      rw [nineUpd_upd4, nineUpd_upd5, nineUpd_upd6, heval']
      exact hneg a b g
    rw [heq] at hsp
    rcases hsp with h | h | h
    · exact allEq3_no_split_a (split1_comp (fun v => !v) h
        (fun a b g => (Bool.not_not (allEq3 a b g)).symm))
    · exact allEq3_no_split_b (split2_comp (fun v => !v) h
        (fun a b g => (Bool.not_not (allEq3 a b g)).symm))
    · exact allEq3_no_split_c (split3_comp (fun v => !v) h
        (fun a b g => (Bool.not_not (allEq3 a b g)).symm))

/-- **Parallel B1, gadget 2 (proved)**: all three gadget-2 signs below `u`
(avoiding `v`), with `v` parallel to `u`, is impossible. -/
theorem killB1v_g2 {u v : ℕ} (hR : reconvR c = {u, v}) (hpar : ¬ Reach c u v)
    {q56 q64 q72 : ℕ}
    (hq56c : q56 ∈ cone c) (hq56g : c.getD q56 (.cst false) = CGate.var ⟨56, h56⟩)
    (hb56 : Reach c u q56) (hnb56v : ¬ Reach c v q56)
    (hq64c : q64 ∈ cone c) (hq64g : c.getD q64 (.cst false) = CGate.var ⟨64, h64⟩)
    (hb64 : Reach c u q64) (hnb64v : ¬ Reach c v q64)
    (hq72c : q72 ∈ cone c) (hq72g : c.getD q72 (.cst false) = CGate.var ⟨72, h72⟩)
    (hb72 : Reach c u q72) (hnb72v : ¬ Reach c v q72) : False := by
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have hult : u < c.length := (mem_cone.mp huc).1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd56 := sign56_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd64 := sign64_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd72 := sign72_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hrefine : ∀ p q r p' q' r' : Bool,
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true true p q r) u
        = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true true true true p' q' r') u →
      allEq3 p q r = allEq3 p' q' r' := by
    intro p q r p' q' r' hwu
    have hv := refine_via N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true true true true p q r true true true true true true p' q' r'
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
      (Or.inr ⟨fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hb72,
        fun w hw hg => by
          rw [huniq ⟨72, h72⟩ hd72 w hw q72 hq72c hg hq72g]; exact hnb72v⟩)
      hwu
    rw [SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true true p q r,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true true p' q' r'] at hv
    simp only [show allEq3 true true true = true from rfl, Bool.true_and] at hv
    exact hv
  have hq56le : q56 ≤ u := reach_le hb56
  have hq64le : q64 ≤ u := reach_le hb64
  have hq72le : q72 ≤ u := reach_le hb72
  have htlen : (c.take (u + 1)).length = u + 1 := by
    rw [List.length_take]
    omega
  have hs' : 0 < (c.take (u + 1)).length := by omega
  have hrfree : reconvR (c.take (u + 1)) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro w hw
    obtain ⟨hwne, hwc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hw).1
    have hwfull := reconvR_take_subset c huc hune hw
    rw [hR] at hwfull
    rcases Finset.mem_insert.mp hwfull with hwu | hwv
    · exact hwne (by omega)
    · have hr := inCone_reach_root (mem_cone.mp hwc).2
      rw [show (c.take (u + 1)).length - 1 = u from by omega] at hr
      have hrc : Reach c u w := reach_of_take c hult (le_refl u) hr
      rw [Finset.mem_singleton.mp hwv] at hrc
      exact hpar hrc
  have hucone' : u ∈ cone (c.take (u + 1)) := by
    have hroot' : InCone (c.take (u + 1)) ((c.take (u + 1)).length - 1) := InCone.root
    rw [show (c.take (u + 1)).length - 1 = u from by omega] at hroot'
    exact mem_cone.mpr ⟨by omega, hroot'⟩
  have hRvac : ∀ q₀ : ℕ, ∀ u' ∈ reconvR (c.take (u + 1)),
      ¬ Reach (c.take (u + 1)) u' q₀ := by
    intro q₀ u' hu'
    rw [hrfree] at hu'
    exact absurd hu' (Finset.notMem_empty u')
  have huniq' : ∀ (i : Fin N), i ∈ depSet (SATFamily N) →
      ∀ (qi : ℕ), qi ∈ cone c → c.getD qi (.cst false) = CGate.var i →
      ∀ q ∈ cone (c.take (u + 1)),
        (c.take (u + 1)).getD q (.cst false) = CGate.var i → q = qi := by
    intro i hdi qi hqic hqig q hq hg
    have hqlt : q < (c.take (u + 1)).length := (mem_cone.mp hq).1
    have hqr : Reach (c.take (u + 1)) u q := by
      have hr := inCone_reach_root (mem_cone.mp hq).2
      rw [show (c.take (u + 1)).length - 1 = u from by omega] at hr
      exact hr
    have hqrc : Reach c u q := reach_of_take c hult (le_refl u) hqr
    have hqicn : InCone c q := reach_inCone (mem_cone.mp huc).2 hqrc
    rw [getD_take_eq_g (show q < u + 1 from by omega)] at hg
    exact huniq i hdi q (mem_cone.mpr ⟨inCone_lt hs hqicn, hqicn⟩) qi hqic hg hqig
  have hcnt56 := (extractG_cnt_spec (c.take (u + 1)) hs' ⟨56, h56⟩ q56
      (mem_cone.mpr ⟨by omega, reach_inCone_take c hult hb56⟩)
      (by rw [getD_take_eq_g (show q56 < u + 1 from by omega)]; exact hq56g)
      (huniq' ⟨56, h56⟩ hd56 q56 hq56c hq56g)
      (hRvac q56) (c.take (u + 1)).length u (by omega) hucone').1
      (reach_take_of_reach c hult hb56)
  have hcnt64 := (extractG_cnt_spec (c.take (u + 1)) hs' ⟨64, h64⟩ q64
      (mem_cone.mpr ⟨by omega, reach_inCone_take c hult hb64⟩)
      (by rw [getD_take_eq_g (show q64 < u + 1 from by omega)]; exact hq64g)
      (huniq' ⟨64, h64⟩ hd64 q64 hq64c hq64g)
      (hRvac q64) (c.take (u + 1)).length u (by omega) hucone').1
      (reach_take_of_reach c hult hb64)
  have hcnt72 := (extractG_cnt_spec (c.take (u + 1)) hs' ⟨72, h72⟩ q72
      (mem_cone.mpr ⟨by omega, reach_inCone_take c hult hb72⟩)
      (by rw [getD_take_eq_g (show q72 < u + 1 from by omega)]; exact hq72g)
      (huniq' ⟨72, h72⟩ hd72 q72 hq72c hq72g)
      (hRvac q72) (c.take (u + 1)).length u (by omega) hucone').1
      (reach_take_of_reach c hult hb72)
  have heval' : ∀ y, (extractG (c.take (u + 1)) (c.take (u + 1)).length u).eval y
      = wire c y u := by
    intro y
    rw [extractG_eval (c.take (u + 1)) (c.take (u + 1)).length u (by omega) (by omega) y]
    exact wire_prefix c y (by omega) (by omega)
  have hsp := gtree_split_cnt (extractG (c.take (u + 1)) (c.take (u + 1)).length u)
    ⟨56, h56⟩ ⟨64, h64⟩ ⟨72, h72⟩
    (fne h56 h64 (by omega)) (fne h56 h72 (by omega)) (fne h64 h72 (by omega))
    (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true true)
    hcnt56 hcnt64 hcnt72
  rcases b1_shape (fun p q r =>
      wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true true p q r) u) hrefine
    with hpos | hneg
  · have heq : (fun a b g =>
        (extractG (c.take (u + 1)) (c.take (u + 1)).length u).eval
        (Function.update (Function.update (Function.update
          (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true true true true true true)
          ⟨56, h56⟩ a) ⟨64, h64⟩ b) ⟨72, h72⟩ g)) = allEq3 := by
      funext a b g
      rw [nineUpd_upd7, nineUpd_upd8, nineUpd_upd9, heval']
      exact hpos a b g
    rw [heq] at hsp
    rcases hsp with h | h | h
    · exact allEq3_no_split_a h
    · exact allEq3_no_split_b h
    · exact allEq3_no_split_c h
  · have heq : (fun a b g =>
        (extractG (c.take (u + 1)) (c.take (u + 1)).length u).eval
        (Function.update (Function.update (Function.update
          (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
            true true true true true true true true true)
          ⟨56, h56⟩ a) ⟨64, h64⟩ b) ⟨72, h72⟩ g))
        = fun a b g => !(allEq3 a b g) := by
      funext a b g
      rw [nineUpd_upd7, nineUpd_upd8, nineUpd_upd9, heval']
      exact hneg a b g
    rw [heq] at hsp
    rcases hsp with h | h | h
    · exact allEq3_no_split_a (split1_comp (fun v => !v) h
        (fun a b g => (Bool.not_not (allEq3 a b g)).symm))
    · exact allEq3_no_split_b (split2_comp (fun v => !v) h
        (fun a b g => (Bool.not_not (allEq3 a b g)).symm))
    · exact allEq3_no_split_c (split3_comp (fun v => !v) h
        (fun a b g => (Bool.not_not (allEq3 a b g)).symm))

end ParB1

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
