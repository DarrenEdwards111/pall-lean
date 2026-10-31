import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATKillRfree3

/-!
# Case-(ii) kills at three gadgets, part A: the avoid and fully-below kills

Multi-wire brick 5a — the `killA`/`killB1` suite re-instantiated at the
nine-sign substrate, with uniqueness supplied by the var-gate budget `deps`
(which case (ii) forces via the spare trade-off).

* **`wire_indep9` (proved)** — mediator-independence at var-gate budget `deps`;
* **`killA9_g0` / `killA9_g1` (proved)** — a gadget whose three sign gates avoid
  `u` kills the circuit;
* **`killB19_g0` / `killB19_g1` (proved)** — a gadget fully below `u` kills the
  circuit (the prefix split).

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

/-- **Mediator-independence at var-gate budget `deps` (proved)**. -/
theorem wire_indep9 (N : ℕ) (c : List (CGate N))
    (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hWd : (coneVars c).card ≤ (depSet (SATFamily N)).card)
    {u : ℕ} (hR : reconvR c = {u}) (i : Fin N) (hdi : i ∈ depSet (SATFamily N))
    {qi : ℕ} (hqic : qi ∈ cone c) (hqig : c.getD qi (.cst false) = CGate.var i)
    (hnbi : ¬ Reach c u qi) (x : Fin N → Bool) (b : Bool) :
    wire c (Function.update x i b) u = wire c x u := by
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_singleton_self u
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have hult : u < c.length := (mem_cone.mp huc).1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  exact wire_u_indep c u hs hult (mem_cone.mp huc).2 x i b
    (fun q hq hg => by rw [huniq i hdi q hq qi hqic hg hqig]; exact hnbi)

/-- **Kill A at nine slots, gadget 0 (proved)**. -/
theorem killA9_g0 (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N)
    (h27 : 27 < N) (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N)
    (h64 : 64 < N) (h72 : 72 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hWd : (coneVars c).card ≤ (depSet (SATFamily N)).card)
    {u : ℕ} (hR : reconvR c = {u})
    {q15 q21 q27 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15 : ¬ Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21 : ¬ Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27 : ¬ Reach c u q27) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  have hRv : ∀ q₀ : ℕ, ¬ Reach c u q₀ → ∀ u' ∈ reconvR c, ¬ Reach c u' q₀ := by
    intro q₀ hnb u' hu'
    rw [hR] at hu'
    rw [Finset.mem_singleton.mp hu']
    exact hnb
  have hcnt15 := (extractG_cnt_spec c hs ⟨15, h15⟩ q15 hq15c hq15g
      (fun q hq hg => huniq ⟨15, h15⟩ hd15 q hq q15 hq15c hg hq15g)
      (hRv q15 hnb15) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq15c).2)
  have hcnt21 := (extractG_cnt_spec c hs ⟨21, h21⟩ q21 hq21c hq21g
      (fun q hq hg => huniq ⟨21, h21⟩ hd21 q hq q21 hq21c hg hq21g)
      (hRv q21 hnb21) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq21c).2)
  have hcnt27 := (extractG_cnt_spec c hs ⟨27, h27⟩ q27 hq27c hq27g
      (fun q hq hg => huniq ⟨27, h27⟩ hd27 q hq q27 hq27c hg hq27g)
      (hRv q27 hnb27) c.length (c.length - 1) (by omega) hroot).1
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
        a b g true true true true true true]
    simp only [show allEq3 true true true = true from rfl, Bool.and_true]
  rw [heq] at hsp
  rcases hsp with h | h | h
  · exact allEq3_no_split_a h
  · exact allEq3_no_split_b h
  · exact allEq3_no_split_c h

/-- **Kill A at nine slots, gadget 1 (proved)**. -/
theorem killA9_g1 (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N)
    (h27 : 27 < N) (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N)
    (h64 : 64 < N) (h72 : 72 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hWd : (coneVars c).card ≤ (depSet (SATFamily N)).card)
    {u : ℕ} (hR : reconvR c = {u})
    {q34 q41 q48 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hnb34 : ¬ Reach c u q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hnb41 : ¬ Reach c u q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hnb48 : ¬ Reach c u q48) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  have hRv : ∀ q₀ : ℕ, ¬ Reach c u q₀ → ∀ u' ∈ reconvR c, ¬ Reach c u' q₀ := by
    intro q₀ hnb u' hu'
    rw [hR] at hu'
    rw [Finset.mem_singleton.mp hu']
    exact hnb
  have hcnt34 := (extractG_cnt_spec c hs ⟨34, h34⟩ q34 hq34c hq34g
      (fun q hq hg => huniq ⟨34, h34⟩ hd34 q hq q34 hq34c hg hq34g)
      (hRv q34 hnb34) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq34c).2)
  have hcnt41 := (extractG_cnt_spec c hs ⟨41, h41⟩ q41 hq41c hq41g
      (fun q hq hg => huniq ⟨41, h41⟩ hd41 q hq q41 hq41c hg hq41g)
      (hRv q41 hnb41) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq41c).2)
  have hcnt48 := (extractG_cnt_spec c hs ⟨48, h48⟩ q48 hq48c hq48g
      (fun q hq hg => huniq ⟨48, h48⟩ hd48 q hq q48 hq48c hg hq48g)
      (hRv q48 hnb48) c.length (c.length - 1) (by omega) hroot).1
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
        true true true a b g true true true]
    simp only [show allEq3 true true true = true from rfl, Bool.and_true, Bool.true_and]
  rw [heq] at hsp
  rcases hsp with h | h | h
  · exact allEq3_no_split_a h
  · exact allEq3_no_split_b h
  · exact allEq3_no_split_c h

/-- **Kill B1 at nine slots, gadget 0 (proved)**: fully below `u` is impossible. -/
theorem killB19_g0 (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N)
    (h27 : 27 < N) (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N)
    (h64 : 64 < N) (h72 : 72 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hWd : (coneVars c).card ≤ (depSet (SATFamily N)).card)
    {u : ℕ} (hR : reconvR c = {u})
    {q15 q21 q27 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hb15 : Reach c u q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hb21 : Reach c u q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hb27 : Reach c u q27) : False := by
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_singleton_self u
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
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      p q r true true true true true true p' q' r' true true true true true true
      (Or.inr fun w hw hg => by
        rw [huniq ⟨15, h15⟩ hd15 w hw q15 hq15c hg hq15g]; exact hb15)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨21, h21⟩ hd21 w hw q21 hq21c hg hq21g]; exact hb21)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨27, h27⟩ hd27 w hw q27 hq27c hg hq27g]; exact hb27)
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
    intro v hv
    have hvne := (Finset.mem_erase.mp (Finset.mem_filter.mp hv).1).1
    have hvfull := reconvR_take_subset c huc hune hv
    rw [hR] at hvfull
    have hveq : v = u := Finset.mem_singleton.mp hvfull
    exact hvne (by omega)
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

/-- **Kill B1 at nine slots, gadget 1 (proved)**: fully below `u` is impossible. -/
theorem killB19_g1 (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N)
    (h27 : 27 < N) (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N)
    (h64 : 64 < N) (h72 : 72 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hWd : (coneVars c).card ≤ (depSet (SATFamily N)).card)
    {u : ℕ} (hR : reconvR c = {u})
    {q34 q41 q48 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hb34 : Reach c u q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hb41 : Reach c u q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hb48 : Reach c u q48) : False := by
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_singleton_self u
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
    have hv := refine_nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
      true true true p q r true true true true true true p' q' r' true true true
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨34, h34⟩ hd34 w hw q34 hq34c hg hq34g]; exact hb34)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨41, h41⟩ hd41 w hw q41 hq41c hg hq41g]; exact hb41)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨48, h48⟩ hd48 w hw q48 hq48c hg hq48g]; exact hb48)
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
    intro v hv
    have hvne := (Finset.mem_erase.mp (Finset.mem_filter.mp hv).1).1
    have hvfull := reconvR_take_subset c huc hune hv
    rw [hR] at hvfull
    have hveq : v = u := Finset.mem_singleton.mp hvfull
    exact hvne (by omega)
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

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.wire_indep9
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killA9_g0
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killB19_g0
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killB19_g1
