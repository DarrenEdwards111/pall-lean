import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATSixSub

/-!
# The B1 kills: a gadget fully below the reconvergence wire

Brick 3b-ii of the `+2` campaign.  If ALL THREE sign gates of a gadget lie below
the single reconvergence wire `u`, the gadget's whole influence flows through
`u`'s one bit.  The master refinement then forces that bit to BE `±AllEqual₃` on
the triple (`b1_shape`) — and the prefix `c.take (u+1)`, which computes the bit
and is reconvergence-FREE, unwinds to a tree with `cnt = 1` at the triple, which
must split (`gtree_split_cnt`).  `±AllEqual₃` refuses every split.

* **`killB1_g0` (proved)** — gadget 0 fully below `u` is impossible;
* **`killB1_g1` (proved)** — gadget 1 fully below `u` is impossible.

With brick 3b-i's case-A kills, the remaining collision cases are B2 (two below,
one free) and B3 (one below in each gadget) — brick 3b-iii.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor

/-- **Kill B1, gadget 0 (proved)**: all three `x₀`-sign gates below `u` is
impossible for a near-floor circuit. -/
theorem killB1_g0 (N : ℕ) (hN : 46 ≤ N) (h12 : 12 < N) (h18 : 18 < N) (h24 : 24 < N)
    (h31 : 31 < N) (h38 : 38 < N) (h45 : 45 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hlen : c.length ≤ 2 * (depSet (SATFamily N)).card)
    {u : ℕ} (hR : reconvR c = {u})
    {q12 q18 q24 : ℕ}
    (hq12c : q12 ∈ cone c) (hq12g : c.getD q12 (.cst false) = CGate.var ⟨12, h12⟩)
    (hb12 : Reach c u q12)
    (hq18c : q18 ∈ cone c) (hq18g : c.getD q18 (.cst false) = CGate.var ⟨18, h18⟩)
    (hb18 : Reach c u q18)
    (hq24c : q24 ∈ cone c) (hq24g : c.getD q24 (.cst false) = CGate.var ⟨24, h24⟩)
    (hb24 : Reach c u q24) : False := by
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_singleton_self u
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have hult : u < c.length := (mem_cone.mp huc).1
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd12 := sign12_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd18 := sign18_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd24 := sign24_dep6 N hN h12 h18 h24 h31 h38 h45
  -- the refinement: the u-bit refines AllEqual₃ on the gadget-0 triple
  have hrefine : ∀ p q r p' q' r' : Bool,
      wire c (sixUpd N h12 h18 h24 h31 h38 h45 p q r true true true) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 p' q' r' true true true) u →
      allEq3 p q r = allEq3 p' q' r' := by
    intro p q r p' q' r' hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      p q r true true true p' q' r' true true true
      (Or.inr fun w hw hg => by
        rw [huniq ⟨12, h12⟩ hd12 w hw q12 hq12c hg hq12g]; exact hb12)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨18, h18⟩ hd18 w hw q18 hq18c hg hq18g]; exact hb18)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨24, h24⟩ hd24 w hw q24 hq24c hg hq24g]; exact hb24)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 p q r true true true,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 p' q' r' true true true,
      show allEq3 true true true = true from rfl, Bool.and_true, Bool.and_true] at hv
    exact hv
  -- prefix facts
  have hq12le : q12 ≤ u := reach_le hb12
  have hq18le : q18 ≤ u := reach_le hb18
  have hq24le : q24 ≤ u := reach_le hb24
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
  have hcnt12 := (extractG_cnt_spec (c.take (u + 1)) hs' ⟨12, h12⟩ q12
      (mem_cone.mpr ⟨by omega, reach_inCone_take c hult hb12⟩)
      (by rw [getD_take_eq_g (show q12 < u + 1 from by omega)]; exact hq12g)
      (huniq' ⟨12, h12⟩ hd12 q12 hq12c hq12g)
      (hRvac q12) (c.take (u + 1)).length u (by omega) hucone').1
      (reach_take_of_reach c hult hb12)
  have hcnt18 := (extractG_cnt_spec (c.take (u + 1)) hs' ⟨18, h18⟩ q18
      (mem_cone.mpr ⟨by omega, reach_inCone_take c hult hb18⟩)
      (by rw [getD_take_eq_g (show q18 < u + 1 from by omega)]; exact hq18g)
      (huniq' ⟨18, h18⟩ hd18 q18 hq18c hq18g)
      (hRvac q18) (c.take (u + 1)).length u (by omega) hucone').1
      (reach_take_of_reach c hult hb18)
  have hcnt24 := (extractG_cnt_spec (c.take (u + 1)) hs' ⟨24, h24⟩ q24
      (mem_cone.mpr ⟨by omega, reach_inCone_take c hult hb24⟩)
      (by rw [getD_take_eq_g (show q24 < u + 1 from by omega)]; exact hq24g)
      (huniq' ⟨24, h24⟩ hd24 q24 hq24c hq24g)
      (hRvac q24) (c.take (u + 1)).length u (by omega) hucone').1
      (reach_take_of_reach c hult hb24)
  have heval' : ∀ y, (extractG (c.take (u + 1)) (c.take (u + 1)).length u).eval y
      = wire c y u := by
    intro y
    rw [extractG_eval (c.take (u + 1)) (c.take (u + 1)).length u (by omega) (by omega) y]
    exact wire_prefix c y (by omega) (by omega)
  have hsp := gtree_split_cnt (extractG (c.take (u + 1)) (c.take (u + 1)).length u)
    ⟨12, h12⟩ ⟨18, h18⟩ ⟨24, h24⟩
    (fne h12 h18 (by omega)) (fne h12 h24 (by omega)) (fne h18 h24 (by omega))
    (sixUpd N h12 h18 h24 h31 h38 h45 true true true true true true)
    hcnt12 hcnt18 hcnt24
  rcases b1_shape (fun p q r =>
      wire c (sixUpd N h12 h18 h24 h31 h38 h45 p q r true true true) u) hrefine
    with hpos | hneg
  · have heq : (fun a b g =>
        (extractG (c.take (u + 1)) (c.take (u + 1)).length u).eval
        (Function.update (Function.update (Function.update
          (sixUpd N h12 h18 h24 h31 h38 h45 true true true true true true)
          ⟨12, h12⟩ a) ⟨18, h18⟩ b) ⟨24, h24⟩ g)) = allEq3 := by
      funext a b g
      rw [sixUpd_upd1, sixUpd_upd2, sixUpd_upd3, heval']
      exact hpos a b g
    rw [heq] at hsp
    rcases hsp with h | h | h
    · exact allEq3_no_split_a h
    · exact allEq3_no_split_b h
    · exact allEq3_no_split_c h
  · have heq : (fun a b g =>
        (extractG (c.take (u + 1)) (c.take (u + 1)).length u).eval
        (Function.update (Function.update (Function.update
          (sixUpd N h12 h18 h24 h31 h38 h45 true true true true true true)
          ⟨12, h12⟩ a) ⟨18, h18⟩ b) ⟨24, h24⟩ g))
        = fun a b g => !(allEq3 a b g) := by
      funext a b g
      rw [sixUpd_upd1, sixUpd_upd2, sixUpd_upd3, heval']
      exact hneg a b g
    rw [heq] at hsp
    rcases hsp with h | h | h
    · exact allEq3_no_split_a (split1_comp (fun v => !v) h
        (fun a b g => (Bool.not_not (allEq3 a b g)).symm))
    · exact allEq3_no_split_b (split2_comp (fun v => !v) h
        (fun a b g => (Bool.not_not (allEq3 a b g)).symm))
    · exact allEq3_no_split_c (split3_comp (fun v => !v) h
        (fun a b g => (Bool.not_not (allEq3 a b g)).symm))

/-- **Kill B1, gadget 1 (proved)**: all three `x₁`-sign gates below `u` is
impossible for a near-floor circuit. -/
theorem killB1_g1 (N : ℕ) (hN : 46 ≤ N) (h12 : 12 < N) (h18 : 18 < N) (h24 : 24 < N)
    (h31 : 31 < N) (h38 : 38 < N) (h45 : 45 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hlen : c.length ≤ 2 * (depSet (SATFamily N)).card)
    {u : ℕ} (hR : reconvR c = {u})
    {q31 q38 q45 : ℕ}
    (hq31c : q31 ∈ cone c) (hq31g : c.getD q31 (.cst false) = CGate.var ⟨31, h31⟩)
    (hb31 : Reach c u q31)
    (hq38c : q38 ∈ cone c) (hq38g : c.getD q38 (.cst false) = CGate.var ⟨38, h38⟩)
    (hb38 : Reach c u q38)
    (hq45c : q45 ∈ cone c) (hq45g : c.getD q45 (.cst false) = CGate.var ⟨45, h45⟩)
    (hb45 : Reach c u q45) : False := by
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_singleton_self u
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have hult : u < c.length := (mem_cone.mp huc).1
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd31 := sign31_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd38 := sign38_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd45 := sign45_dep6 N hN h12 h18 h24 h31 h38 h45
  have hrefine : ∀ p q r p' q' r' : Bool,
      wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true true p q r) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true true p' q' r') u →
      allEq3 p q r = allEq3 p' q' r' := by
    intro p q r p' q' r' hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      true true true p q r true true true p' q' r'
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨31, h31⟩ hd31 w hw q31 hq31c hg hq31g]; exact hb31)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨38, h38⟩ hd38 w hw q38 hq38c hg hq38g]; exact hb38)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨45, h45⟩ hd45 w hw q45 hq45c hg hq45g]; exact hb45)
      hwu
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true p q r,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true p' q' r',
      show allEq3 true true true = true from rfl, Bool.true_and, Bool.true_and] at hv
    exact hv
  have hq31le : q31 ≤ u := reach_le hb31
  have hq38le : q38 ≤ u := reach_le hb38
  have hq45le : q45 ≤ u := reach_le hb45
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
  have hcnt31 := (extractG_cnt_spec (c.take (u + 1)) hs' ⟨31, h31⟩ q31
      (mem_cone.mpr ⟨by omega, reach_inCone_take c hult hb31⟩)
      (by rw [getD_take_eq_g (show q31 < u + 1 from by omega)]; exact hq31g)
      (huniq' ⟨31, h31⟩ hd31 q31 hq31c hq31g)
      (hRvac q31) (c.take (u + 1)).length u (by omega) hucone').1
      (reach_take_of_reach c hult hb31)
  have hcnt38 := (extractG_cnt_spec (c.take (u + 1)) hs' ⟨38, h38⟩ q38
      (mem_cone.mpr ⟨by omega, reach_inCone_take c hult hb38⟩)
      (by rw [getD_take_eq_g (show q38 < u + 1 from by omega)]; exact hq38g)
      (huniq' ⟨38, h38⟩ hd38 q38 hq38c hq38g)
      (hRvac q38) (c.take (u + 1)).length u (by omega) hucone').1
      (reach_take_of_reach c hult hb38)
  have hcnt45 := (extractG_cnt_spec (c.take (u + 1)) hs' ⟨45, h45⟩ q45
      (mem_cone.mpr ⟨by omega, reach_inCone_take c hult hb45⟩)
      (by rw [getD_take_eq_g (show q45 < u + 1 from by omega)]; exact hq45g)
      (huniq' ⟨45, h45⟩ hd45 q45 hq45c hq45g)
      (hRvac q45) (c.take (u + 1)).length u (by omega) hucone').1
      (reach_take_of_reach c hult hb45)
  have heval' : ∀ y, (extractG (c.take (u + 1)) (c.take (u + 1)).length u).eval y
      = wire c y u := by
    intro y
    rw [extractG_eval (c.take (u + 1)) (c.take (u + 1)).length u (by omega) (by omega) y]
    exact wire_prefix c y (by omega) (by omega)
  have hsp := gtree_split_cnt (extractG (c.take (u + 1)) (c.take (u + 1)).length u)
    ⟨31, h31⟩ ⟨38, h38⟩ ⟨45, h45⟩
    (fne h31 h38 (by omega)) (fne h31 h45 (by omega)) (fne h38 h45 (by omega))
    (sixUpd N h12 h18 h24 h31 h38 h45 true true true true true true)
    hcnt31 hcnt38 hcnt45
  rcases b1_shape (fun p q r =>
      wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true true p q r) u) hrefine
    with hpos | hneg
  · have heq : (fun a b g =>
        (extractG (c.take (u + 1)) (c.take (u + 1)).length u).eval
        (Function.update (Function.update (Function.update
          (sixUpd N h12 h18 h24 h31 h38 h45 true true true true true true)
          ⟨31, h31⟩ a) ⟨38, h38⟩ b) ⟨45, h45⟩ g)) = allEq3 := by
      funext a b g
      rw [sixUpd_upd4, sixUpd_upd5, sixUpd_upd6, heval']
      exact hpos a b g
    rw [heq] at hsp
    rcases hsp with h | h | h
    · exact allEq3_no_split_a h
    · exact allEq3_no_split_b h
    · exact allEq3_no_split_c h
  · have heq : (fun a b g =>
        (extractG (c.take (u + 1)) (c.take (u + 1)).length u).eval
        (Function.update (Function.update (Function.update
          (sixUpd N h12 h18 h24 h31 h38 h45 true true true true true true)
          ⟨31, h31⟩ a) ⟨38, h38⟩ b) ⟨45, h45⟩ g))
        = fun a b g => !(allEq3 a b g) := by
      funext a b g
      rw [sixUpd_upd4, sixUpd_upd5, sixUpd_upd6, heval']
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

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killB1_g0
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killB1_g1
