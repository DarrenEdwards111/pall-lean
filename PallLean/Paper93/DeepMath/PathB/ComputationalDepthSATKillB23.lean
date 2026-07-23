import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATKillB1

/-!
# The B2 and B3 kills: partial collisions at the single reconvergence wire

Brick 3b-iii(a) of the `+2` campaign — the remaining collision cases.

* **`wire_indep_of_not_below` (proved)** — the packaged mediator-independence: a
  coordinate whose unique gate avoids `u` cannot move `u`'s bit;
* **`killB2_g0_free1/2/3`, `killB2_g1_free4/5/6` (proved)** — TWO signs of one
  gadget below `u`, the third free: the free slot cannot move the mediator, yet
  per fixed free value the mediator refines `AllEqual₃` — three distinct Boolean
  values demanded of one bit (`b2_kill_free*`);
* **`killB3_14 … killB3_36` (proved, 9 variants)** — ONE sign below `u` in EACH
  gadget: the mediator refines `a ∧ d` under all-true pins and `¬a ∧ d` under the
  polarity-flipped pins (transported by mediator-independence of the pin slots) —
  impossible (`b3_kill`).

With 3b-i (case A) and 3b-ii (case B1), every collision configuration is killed;
the case-tree capstone follows in `SATPlusTwo`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor

/-- **Packaged mediator-independence (proved)**: a coordinate whose unique var gate
avoids `u` cannot move `u`'s bit. -/
theorem wire_indep_of_not_below (N : ℕ) (c : List (CGate N))
    (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hlen : c.length ≤ 2 * (depSet (SATFamily N)).card)
    {u : ℕ} (hR : reconvR c = {u}) (i : Fin N) (hdi : i ∈ depSet (SATFamily N))
    {qi : ℕ} (hqic : qi ∈ cone c) (hqig : c.getD qi (.cst false) = CGate.var i)
    (hnbi : ¬ Reach c u qi) (x : Fin N → Bool) (b : Bool) :
    wire c (Function.update x i b) u = wire c x u := by
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_singleton_self u
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have hult : u < c.length := (mem_cone.mp huc).1
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  exact wire_u_indep c u hs hult (mem_cone.mp huc).2 x i b
    (fun q hq hg => by rw [huniq i hdi q hq qi hqic hg hqig]; exact hnbi)

/-! ### The B2 kills, gadget 0 -/

/-- **Kill B2, gadget 0, free slot 1 (proved)**. -/
theorem killB2_g0_free1 (N : ℕ) (hN : 46 ≤ N) (h12 : 12 < N) (h18 : 18 < N)
    (h24 : 24 < N) (h31 : 31 < N) (h38 : 38 < N) (h45 : 45 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hlen : c.length ≤ 2 * (depSet (SATFamily N)).card)
    {u : ℕ} (hR : reconvR c = {u})
    {q12 q18 q24 : ℕ}
    (hq12c : q12 ∈ cone c) (hq12g : c.getD q12 (.cst false) = CGate.var ⟨12, h12⟩)
    (hnb12 : ¬ Reach c u q12)
    (hq18c : q18 ∈ cone c) (hq18g : c.getD q18 (.cst false) = CGate.var ⟨18, h18⟩)
    (hb18 : Reach c u q18)
    (hq24c : q24 ∈ cone c) (hq24g : c.getD q24 (.cst false) = CGate.var ⟨24, h24⟩)
    (hb24 : Reach c u q24) : False := by
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd12 := sign12_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd18 := sign18_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd24 := sign24_dep6 N hN h12 h18 h24 h31 h38 h45
  refine b2_kill_free1 (fun p q r =>
    wire c (sixUpd N h12 h18 h24 h31 h38 h45 p q r true true true) u) ?_ ?_
  · intro p q r q' r' hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      p q r true true true p q' r' true true true
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨18, h18⟩ hd18 w hw q18 hq18c hg hq18g]; exact hb18)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨24, h24⟩ hd24 w hw q24 hq24c hg hq24g]; exact hb24)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 p q r true true true,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 p q' r' true true true,
      show allEq3 true true true = true from rfl, Bool.and_true, Bool.and_true] at hv
    exact hv
  · intro p p' q r
    show wire c (sixUpd N h12 h18 h24 h31 h38 h45 p q r true true true) u
      = wire c (sixUpd N h12 h18 h24 h31 h38 h45 p' q r true true true) u
    conv_lhs => rw [← sixUpd_upd1 h12 h18 h24 h31 h38 h45 p' q r true true true p]
    exact wire_indep_of_not_below N c hcomp hs hlen hR ⟨12, h12⟩ hd12
      hq12c hq12g hnb12 _ p

/-- **Kill B2, gadget 0, free slot 2 (proved)**. -/
theorem killB2_g0_free2 (N : ℕ) (hN : 46 ≤ N) (h12 : 12 < N) (h18 : 18 < N)
    (h24 : 24 < N) (h31 : 31 < N) (h38 : 38 < N) (h45 : 45 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hlen : c.length ≤ 2 * (depSet (SATFamily N)).card)
    {u : ℕ} (hR : reconvR c = {u})
    {q12 q18 q24 : ℕ}
    (hq12c : q12 ∈ cone c) (hq12g : c.getD q12 (.cst false) = CGate.var ⟨12, h12⟩)
    (hb12 : Reach c u q12)
    (hq18c : q18 ∈ cone c) (hq18g : c.getD q18 (.cst false) = CGate.var ⟨18, h18⟩)
    (hnb18 : ¬ Reach c u q18)
    (hq24c : q24 ∈ cone c) (hq24g : c.getD q24 (.cst false) = CGate.var ⟨24, h24⟩)
    (hb24 : Reach c u q24) : False := by
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd12 := sign12_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd18 := sign18_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd24 := sign24_dep6 N hN h12 h18 h24 h31 h38 h45
  refine b2_kill_free2 (fun p q r =>
    wire c (sixUpd N h12 h18 h24 h31 h38 h45 p q r true true true) u) ?_ ?_
  · intro p q r p' r' hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      p q r true true true p' q r' true true true
      (Or.inr fun w hw hg => by
        rw [huniq ⟨12, h12⟩ hd12 w hw q12 hq12c hg hq12g]; exact hb12)
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨24, h24⟩ hd24 w hw q24 hq24c hg hq24g]; exact hb24)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 p q r true true true,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 p' q r' true true true,
      show allEq3 true true true = true from rfl, Bool.and_true, Bool.and_true] at hv
    exact hv
  · intro p q q' r
    show wire c (sixUpd N h12 h18 h24 h31 h38 h45 p q r true true true) u
      = wire c (sixUpd N h12 h18 h24 h31 h38 h45 p q' r true true true) u
    conv_lhs => rw [← sixUpd_upd2 h12 h18 h24 h31 h38 h45 p q' r true true true q]
    exact wire_indep_of_not_below N c hcomp hs hlen hR ⟨18, h18⟩ hd18
      hq18c hq18g hnb18 _ q

/-- **Kill B2, gadget 0, free slot 3 (proved)**. -/
theorem killB2_g0_free3 (N : ℕ) (hN : 46 ≤ N) (h12 : 12 < N) (h18 : 18 < N)
    (h24 : 24 < N) (h31 : 31 < N) (h38 : 38 < N) (h45 : 45 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hlen : c.length ≤ 2 * (depSet (SATFamily N)).card)
    {u : ℕ} (hR : reconvR c = {u})
    {q12 q18 q24 : ℕ}
    (hq12c : q12 ∈ cone c) (hq12g : c.getD q12 (.cst false) = CGate.var ⟨12, h12⟩)
    (hb12 : Reach c u q12)
    (hq18c : q18 ∈ cone c) (hq18g : c.getD q18 (.cst false) = CGate.var ⟨18, h18⟩)
    (hb18 : Reach c u q18)
    (hq24c : q24 ∈ cone c) (hq24g : c.getD q24 (.cst false) = CGate.var ⟨24, h24⟩)
    (hnb24 : ¬ Reach c u q24) : False := by
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd12 := sign12_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd18 := sign18_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd24 := sign24_dep6 N hN h12 h18 h24 h31 h38 h45
  refine b2_kill_free3 (fun p q r =>
    wire c (sixUpd N h12 h18 h24 h31 h38 h45 p q r true true true) u) ?_ ?_
  · intro p q r p' q' hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      p q r true true true p' q' r true true true
      (Or.inr fun w hw hg => by
        rw [huniq ⟨12, h12⟩ hd12 w hw q12 hq12c hg hq12g]; exact hb12)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨18, h18⟩ hd18 w hw q18 hq18c hg hq18g]; exact hb18)
      (Or.inl rfl)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hwu
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 p q r true true true,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 p' q' r true true true,
      show allEq3 true true true = true from rfl, Bool.and_true, Bool.and_true] at hv
    exact hv
  · intro p q r r'
    show wire c (sixUpd N h12 h18 h24 h31 h38 h45 p q r true true true) u
      = wire c (sixUpd N h12 h18 h24 h31 h38 h45 p q r' true true true) u
    conv_lhs => rw [← sixUpd_upd3 h12 h18 h24 h31 h38 h45 p q r' true true true r]
    exact wire_indep_of_not_below N c hcomp hs hlen hR ⟨24, h24⟩ hd24
      hq24c hq24g hnb24 _ r

/-! ### The B2 kills, gadget 1 -/

/-- **Kill B2, gadget 1, free slot 4 (proved)**. -/
theorem killB2_g1_free4 (N : ℕ) (hN : 46 ≤ N) (h12 : 12 < N) (h18 : 18 < N)
    (h24 : 24 < N) (h31 : 31 < N) (h38 : 38 < N) (h45 : 45 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hlen : c.length ≤ 2 * (depSet (SATFamily N)).card)
    {u : ℕ} (hR : reconvR c = {u})
    {q31 q38 q45 : ℕ}
    (hq31c : q31 ∈ cone c) (hq31g : c.getD q31 (.cst false) = CGate.var ⟨31, h31⟩)
    (hnb31 : ¬ Reach c u q31)
    (hq38c : q38 ∈ cone c) (hq38g : c.getD q38 (.cst false) = CGate.var ⟨38, h38⟩)
    (hb38 : Reach c u q38)
    (hq45c : q45 ∈ cone c) (hq45g : c.getD q45 (.cst false) = CGate.var ⟨45, h45⟩)
    (hb45 : Reach c u q45) : False := by
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd31 := sign31_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd38 := sign38_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd45 := sign45_dep6 N hN h12 h18 h24 h31 h38 h45
  refine b2_kill_free1 (fun p q r =>
    wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true true p q r) u) ?_ ?_
  · intro p q r q' r' hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      true true true p q r true true true p q' r'
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨38, h38⟩ hd38 w hw q38 hq38c hg hq38g]; exact hb38)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨45, h45⟩ hd45 w hw q45 hq45c hg hq45g]; exact hb45)
      hwu
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true p q r,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true p q' r',
      show allEq3 true true true = true from rfl, Bool.true_and, Bool.true_and] at hv
    exact hv
  · intro p p' q r
    show wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true true p q r) u
      = wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true true p' q r) u
    conv_lhs => rw [← sixUpd_upd4 h12 h18 h24 h31 h38 h45 true true true p' q r p]
    exact wire_indep_of_not_below N c hcomp hs hlen hR ⟨31, h31⟩ hd31
      hq31c hq31g hnb31 _ p

/-- **Kill B2, gadget 1, free slot 5 (proved)**. -/
theorem killB2_g1_free5 (N : ℕ) (hN : 46 ≤ N) (h12 : 12 < N) (h18 : 18 < N)
    (h24 : 24 < N) (h31 : 31 < N) (h38 : 38 < N) (h45 : 45 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hlen : c.length ≤ 2 * (depSet (SATFamily N)).card)
    {u : ℕ} (hR : reconvR c = {u})
    {q31 q38 q45 : ℕ}
    (hq31c : q31 ∈ cone c) (hq31g : c.getD q31 (.cst false) = CGate.var ⟨31, h31⟩)
    (hb31 : Reach c u q31)
    (hq38c : q38 ∈ cone c) (hq38g : c.getD q38 (.cst false) = CGate.var ⟨38, h38⟩)
    (hnb38 : ¬ Reach c u q38)
    (hq45c : q45 ∈ cone c) (hq45g : c.getD q45 (.cst false) = CGate.var ⟨45, h45⟩)
    (hb45 : Reach c u q45) : False := by
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd31 := sign31_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd38 := sign38_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd45 := sign45_dep6 N hN h12 h18 h24 h31 h38 h45
  refine b2_kill_free2 (fun p q r =>
    wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true true p q r) u) ?_ ?_
  · intro p q r p' r' hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      true true true p q r true true true p' q r'
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨31, h31⟩ hd31 w hw q31 hq31c hg hq31g]; exact hb31)
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨45, h45⟩ hd45 w hw q45 hq45c hg hq45g]; exact hb45)
      hwu
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true p q r,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true p' q r',
      show allEq3 true true true = true from rfl, Bool.true_and, Bool.true_and] at hv
    exact hv
  · intro p q q' r
    show wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true true p q r) u
      = wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true true p q' r) u
    conv_lhs => rw [← sixUpd_upd5 h12 h18 h24 h31 h38 h45 true true true p q' r q]
    exact wire_indep_of_not_below N c hcomp hs hlen hR ⟨38, h38⟩ hd38
      hq38c hq38g hnb38 _ q

/-- **Kill B2, gadget 1, free slot 6 (proved)**. -/
theorem killB2_g1_free6 (N : ℕ) (hN : 46 ≤ N) (h12 : 12 < N) (h18 : 18 < N)
    (h24 : 24 < N) (h31 : 31 < N) (h38 : 38 < N) (h45 : 45 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hlen : c.length ≤ 2 * (depSet (SATFamily N)).card)
    {u : ℕ} (hR : reconvR c = {u})
    {q31 q38 q45 : ℕ}
    (hq31c : q31 ∈ cone c) (hq31g : c.getD q31 (.cst false) = CGate.var ⟨31, h31⟩)
    (hb31 : Reach c u q31)
    (hq38c : q38 ∈ cone c) (hq38g : c.getD q38 (.cst false) = CGate.var ⟨38, h38⟩)
    (hb38 : Reach c u q38)
    (hq45c : q45 ∈ cone c) (hq45g : c.getD q45 (.cst false) = CGate.var ⟨45, h45⟩)
    (hnb45 : ¬ Reach c u q45) : False := by
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd31 := sign31_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd38 := sign38_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd45 := sign45_dep6 N hN h12 h18 h24 h31 h38 h45
  refine b2_kill_free3 (fun p q r =>
    wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true true p q r) u) ?_ ?_
  · intro p q r p' q' hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      true true true p q r true true true p' q' r
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨31, h31⟩ hd31 w hw q31 hq31c hg hq31g]; exact hb31)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨38, h38⟩ hd38 w hw q38 hq38c hg hq38g]; exact hb38)
      (Or.inl rfl)
      hwu
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true p q r,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true p' q' r,
      show allEq3 true true true = true from rfl, Bool.true_and, Bool.true_and] at hv
    exact hv
  · intro p q r r'
    show wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true true p q r) u
      = wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true true p q r') u
    conv_lhs => rw [← sixUpd_upd6 h12 h18 h24 h31 h38 h45 true true true p q r' r]
    exact wire_indep_of_not_below N c hcomp hs hlen hR ⟨45, h45⟩ hd45
      hq45c hq45g hnb45 _ r

/-! ### The B3 kills: one sign below `u` in each gadget (9 position variants) -/

section B3

variable (N : ℕ) (hN : 46 ≤ N) (h12 : 12 < N) (h18 : 18 < N) (h24 : 24 < N)
  (h31 : 31 < N) (h38 : 38 < N) (h45 : 45 < N)
  (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
  (hlen : c.length ≤ 2 * (depSet (SATFamily N)).card)

include hN h12 h18 h24 h31 h38 h45 hcomp hs hlen

/-- **Kill B3, slots (1,4) (proved)**. -/
theorem killB3_14 {u : ℕ} (hR : reconvR c = {u}) {q12 q18 q24 q31 : ℕ}
    (hq12c : q12 ∈ cone c) (hq12g : c.getD q12 (.cst false) = CGate.var ⟨12, h12⟩)
    (hb12 : Reach c u q12)
    (hq18c : q18 ∈ cone c) (hq18g : c.getD q18 (.cst false) = CGate.var ⟨18, h18⟩)
    (hnb18 : ¬ Reach c u q18)
    (hq24c : q24 ∈ cone c) (hq24g : c.getD q24 (.cst false) = CGate.var ⟨24, h24⟩)
    (hnb24 : ¬ Reach c u q24)
    (hq31c : q31 ∈ cone c) (hq31g : c.getD q31 (.cst false) = CGate.var ⟨31, h31⟩)
    (hb31 : Reach c u q31) : False := by
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd12 := sign12_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd18 := sign18_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd24 := sign24_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd31 := sign31_dep6 N hN h12 h18 h24 h31 h38 h45
  have htrans : ∀ a d : Bool,
      wire c (sixUpd N h12 h18 h24 h31 h38 h45 a false false d true true) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 a true true d true true) u := by
    intro a d
    calc wire c (sixUpd N h12 h18 h24 h31 h38 h45 a false false d true true) u
        = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            a false true d true true) ⟨24, h24⟩ false) u := by
          rw [sixUpd_upd3 h12 h18 h24 h31 h38 h45 a false true d true true false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 a false true d true true) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨24, h24⟩ hd24
            hq24c hq24g hnb24 _ false
      _ = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            a true true d true true) ⟨18, h18⟩ false) u := by
          rw [sixUpd_upd2 h12 h18 h24 h31 h38 h45 a true true d true true false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 a true true d true true) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨18, h18⟩ hd18
            hq18c hq18g hnb18 _ false
  refine b3_kill (fun a d =>
    wire c (sixUpd N h12 h18 h24 h31 h38 h45 a true true d true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      a true true d true true a' true true d' true true
      (Or.inr fun w hw hg => by
        rw [huniq ⟨12, h12⟩ hd12 w hw q12 hq12c hg hq12g]; exact hb12)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨31, h31⟩ hd31 w hw q31 hq31c hg hq31g]; exact hb31)
      (Or.inl rfl) (Or.inl rfl) hwu
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 a true true d true true,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 a' true true d' true true,
      allEq3_slot1_T, allEq3_slot1_T, allEq3_slot1_T, allEq3_slot1_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (sixUpd N h12 h18 h24 h31 h38 h45 a false false d true true) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 a' false false d' true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      a false false d true true a' false false d' true true
      (Or.inr fun w hw hg => by
        rw [huniq ⟨12, h12⟩ hd12 w hw q12 hq12c hg hq12g]; exact hb12)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨31, h31⟩ hd31 w hw q31 hq31c hg hq31g]; exact hb31)
      (Or.inl rfl) (Or.inl rfl) hwu2
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 a false false d true true,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 a' false false d' true true,
      allEq3_slot1_F, allEq3_slot1_F, allEq3_slot1_T, allEq3_slot1_T] at hv
    exact hv

/-- **Kill B3, slots (1,5) (proved)**. -/
theorem killB3_15 {u : ℕ} (hR : reconvR c = {u}) {q12 q18 q24 q38 : ℕ}
    (hq12c : q12 ∈ cone c) (hq12g : c.getD q12 (.cst false) = CGate.var ⟨12, h12⟩)
    (hb12 : Reach c u q12)
    (hq18c : q18 ∈ cone c) (hq18g : c.getD q18 (.cst false) = CGate.var ⟨18, h18⟩)
    (hnb18 : ¬ Reach c u q18)
    (hq24c : q24 ∈ cone c) (hq24g : c.getD q24 (.cst false) = CGate.var ⟨24, h24⟩)
    (hnb24 : ¬ Reach c u q24)
    (hq38c : q38 ∈ cone c) (hq38g : c.getD q38 (.cst false) = CGate.var ⟨38, h38⟩)
    (hb38 : Reach c u q38) : False := by
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd12 := sign12_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd18 := sign18_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd24 := sign24_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd38 := sign38_dep6 N hN h12 h18 h24 h31 h38 h45
  have htrans : ∀ a d : Bool,
      wire c (sixUpd N h12 h18 h24 h31 h38 h45 a false false true d true) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 a true true true d true) u := by
    intro a d
    calc wire c (sixUpd N h12 h18 h24 h31 h38 h45 a false false true d true) u
        = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            a false true true d true) ⟨24, h24⟩ false) u := by
          rw [sixUpd_upd3 h12 h18 h24 h31 h38 h45 a false true true d true false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 a false true true d true) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨24, h24⟩ hd24
            hq24c hq24g hnb24 _ false
      _ = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            a true true true d true) ⟨18, h18⟩ false) u := by
          rw [sixUpd_upd2 h12 h18 h24 h31 h38 h45 a true true true d true false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 a true true true d true) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨18, h18⟩ hd18
            hq18c hq18g hnb18 _ false
  refine b3_kill (fun a d =>
    wire c (sixUpd N h12 h18 h24 h31 h38 h45 a true true true d true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      a true true true d true a' true true true d' true
      (Or.inr fun w hw hg => by
        rw [huniq ⟨12, h12⟩ hd12 w hw q12 hq12c hg hq12g]; exact hb12)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨38, h38⟩ hd38 w hw q38 hq38c hg hq38g]; exact hb38)
      (Or.inl rfl) hwu
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 a true true true d true,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 a' true true true d' true,
      allEq3_slot1_T, allEq3_slot1_T, allEq3_slot2_T, allEq3_slot2_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (sixUpd N h12 h18 h24 h31 h38 h45 a false false true d true) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 a' false false true d' true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      a false false true d true a' false false true d' true
      (Or.inr fun w hw hg => by
        rw [huniq ⟨12, h12⟩ hd12 w hw q12 hq12c hg hq12g]; exact hb12)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨38, h38⟩ hd38 w hw q38 hq38c hg hq38g]; exact hb38)
      (Or.inl rfl) hwu2
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 a false false true d true,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 a' false false true d' true,
      allEq3_slot1_F, allEq3_slot1_F, allEq3_slot2_T, allEq3_slot2_T] at hv
    exact hv

/-- **Kill B3, slots (1,6) (proved)**. -/
theorem killB3_16 {u : ℕ} (hR : reconvR c = {u}) {q12 q18 q24 q45 : ℕ}
    (hq12c : q12 ∈ cone c) (hq12g : c.getD q12 (.cst false) = CGate.var ⟨12, h12⟩)
    (hb12 : Reach c u q12)
    (hq18c : q18 ∈ cone c) (hq18g : c.getD q18 (.cst false) = CGate.var ⟨18, h18⟩)
    (hnb18 : ¬ Reach c u q18)
    (hq24c : q24 ∈ cone c) (hq24g : c.getD q24 (.cst false) = CGate.var ⟨24, h24⟩)
    (hnb24 : ¬ Reach c u q24)
    (hq45c : q45 ∈ cone c) (hq45g : c.getD q45 (.cst false) = CGate.var ⟨45, h45⟩)
    (hb45 : Reach c u q45) : False := by
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd12 := sign12_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd18 := sign18_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd24 := sign24_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd45 := sign45_dep6 N hN h12 h18 h24 h31 h38 h45
  have htrans : ∀ a d : Bool,
      wire c (sixUpd N h12 h18 h24 h31 h38 h45 a false false true true d) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 a true true true true d) u := by
    intro a d
    calc wire c (sixUpd N h12 h18 h24 h31 h38 h45 a false false true true d) u
        = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            a false true true true d) ⟨24, h24⟩ false) u := by
          rw [sixUpd_upd3 h12 h18 h24 h31 h38 h45 a false true true true d false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 a false true true true d) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨24, h24⟩ hd24
            hq24c hq24g hnb24 _ false
      _ = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            a true true true true d) ⟨18, h18⟩ false) u := by
          rw [sixUpd_upd2 h12 h18 h24 h31 h38 h45 a true true true true d false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 a true true true true d) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨18, h18⟩ hd18
            hq18c hq18g hnb18 _ false
  refine b3_kill (fun a d =>
    wire c (sixUpd N h12 h18 h24 h31 h38 h45 a true true true true d) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      a true true true true d a' true true true true d'
      (Or.inr fun w hw hg => by
        rw [huniq ⟨12, h12⟩ hd12 w hw q12 hq12c hg hq12g]; exact hb12)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨45, h45⟩ hd45 w hw q45 hq45c hg hq45g]; exact hb45)
      hwu
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 a true true true true d,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 a' true true true true d',
      allEq3_slot1_T, allEq3_slot1_T, allEq3_slot3_T, allEq3_slot3_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (sixUpd N h12 h18 h24 h31 h38 h45 a false false true true d) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 a' false false true true d') u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      a false false true true d a' false false true true d'
      (Or.inr fun w hw hg => by
        rw [huniq ⟨12, h12⟩ hd12 w hw q12 hq12c hg hq12g]; exact hb12)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨45, h45⟩ hd45 w hw q45 hq45c hg hq45g]; exact hb45)
      hwu2
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 a false false true true d,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 a' false false true true d',
      allEq3_slot1_F, allEq3_slot1_F, allEq3_slot3_T, allEq3_slot3_T] at hv
    exact hv

/-- **Kill B3, slots (2,4) (proved)**. -/
theorem killB3_24 {u : ℕ} (hR : reconvR c = {u}) {q12 q18 q24 q31 : ℕ}
    (hq12c : q12 ∈ cone c) (hq12g : c.getD q12 (.cst false) = CGate.var ⟨12, h12⟩)
    (hnb12 : ¬ Reach c u q12)
    (hq18c : q18 ∈ cone c) (hq18g : c.getD q18 (.cst false) = CGate.var ⟨18, h18⟩)
    (hb18 : Reach c u q18)
    (hq24c : q24 ∈ cone c) (hq24g : c.getD q24 (.cst false) = CGate.var ⟨24, h24⟩)
    (hnb24 : ¬ Reach c u q24)
    (hq31c : q31 ∈ cone c) (hq31g : c.getD q31 (.cst false) = CGate.var ⟨31, h31⟩)
    (hb31 : Reach c u q31) : False := by
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd12 := sign12_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd18 := sign18_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd24 := sign24_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd31 := sign31_dep6 N hN h12 h18 h24 h31 h38 h45
  have htrans : ∀ a d : Bool,
      wire c (sixUpd N h12 h18 h24 h31 h38 h45 false a false d true true) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 true a true d true true) u := by
    intro a d
    calc wire c (sixUpd N h12 h18 h24 h31 h38 h45 false a false d true true) u
        = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            false a true d true true) ⟨24, h24⟩ false) u := by
          rw [sixUpd_upd3 h12 h18 h24 h31 h38 h45 false a true d true true false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 false a true d true true) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨24, h24⟩ hd24
            hq24c hq24g hnb24 _ false
      _ = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            true a true d true true) ⟨12, h12⟩ false) u := by
          rw [sixUpd_upd1 h12 h18 h24 h31 h38 h45 true a true d true true false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 true a true d true true) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨12, h12⟩ hd12
            hq12c hq12g hnb12 _ false
  refine b3_kill (fun a d =>
    wire c (sixUpd N h12 h18 h24 h31 h38 h45 true a true d true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      true a true d true true true a' true d' true true
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨18, h18⟩ hd18 w hw q18 hq18c hg hq18g]; exact hb18)
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨31, h31⟩ hd31 w hw q31 hq31c hg hq31g]; exact hb31)
      (Or.inl rfl) (Or.inl rfl) hwu
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true a true d true true,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true a' true d' true true,
      allEq3_slot2_T, allEq3_slot2_T, allEq3_slot1_T, allEq3_slot1_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (sixUpd N h12 h18 h24 h31 h38 h45 false a false d true true) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 false a' false d' true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      false a false d true true false a' false d' true true
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨18, h18⟩ hd18 w hw q18 hq18c hg hq18g]; exact hb18)
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨31, h31⟩ hd31 w hw q31 hq31c hg hq31g]; exact hb31)
      (Or.inl rfl) (Or.inl rfl) hwu2
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 false a false d true true,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 false a' false d' true true,
      allEq3_slot2_F, allEq3_slot2_F, allEq3_slot1_T, allEq3_slot1_T] at hv
    exact hv

/-- **Kill B3, slots (2,5) (proved)**. -/
theorem killB3_25 {u : ℕ} (hR : reconvR c = {u}) {q12 q18 q24 q38 : ℕ}
    (hq12c : q12 ∈ cone c) (hq12g : c.getD q12 (.cst false) = CGate.var ⟨12, h12⟩)
    (hnb12 : ¬ Reach c u q12)
    (hq18c : q18 ∈ cone c) (hq18g : c.getD q18 (.cst false) = CGate.var ⟨18, h18⟩)
    (hb18 : Reach c u q18)
    (hq24c : q24 ∈ cone c) (hq24g : c.getD q24 (.cst false) = CGate.var ⟨24, h24⟩)
    (hnb24 : ¬ Reach c u q24)
    (hq38c : q38 ∈ cone c) (hq38g : c.getD q38 (.cst false) = CGate.var ⟨38, h38⟩)
    (hb38 : Reach c u q38) : False := by
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd12 := sign12_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd18 := sign18_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd24 := sign24_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd38 := sign38_dep6 N hN h12 h18 h24 h31 h38 h45
  have htrans : ∀ a d : Bool,
      wire c (sixUpd N h12 h18 h24 h31 h38 h45 false a false true d true) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 true a true true d true) u := by
    intro a d
    calc wire c (sixUpd N h12 h18 h24 h31 h38 h45 false a false true d true) u
        = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            false a true true d true) ⟨24, h24⟩ false) u := by
          rw [sixUpd_upd3 h12 h18 h24 h31 h38 h45 false a true true d true false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 false a true true d true) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨24, h24⟩ hd24
            hq24c hq24g hnb24 _ false
      _ = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            true a true true d true) ⟨12, h12⟩ false) u := by
          rw [sixUpd_upd1 h12 h18 h24 h31 h38 h45 true a true true d true false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 true a true true d true) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨12, h12⟩ hd12
            hq12c hq12g hnb12 _ false
  refine b3_kill (fun a d =>
    wire c (sixUpd N h12 h18 h24 h31 h38 h45 true a true true d true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      true a true true d true true a' true true d' true
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨18, h18⟩ hd18 w hw q18 hq18c hg hq18g]; exact hb18)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨38, h38⟩ hd38 w hw q38 hq38c hg hq38g]; exact hb38)
      (Or.inl rfl) hwu
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true a true true d true,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true a' true true d' true,
      allEq3_slot2_T, allEq3_slot2_T, allEq3_slot2_T, allEq3_slot2_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (sixUpd N h12 h18 h24 h31 h38 h45 false a false true d true) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 false a' false true d' true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      false a false true d true false a' false true d' true
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨18, h18⟩ hd18 w hw q18 hq18c hg hq18g]; exact hb18)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨38, h38⟩ hd38 w hw q38 hq38c hg hq38g]; exact hb38)
      (Or.inl rfl) hwu2
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 false a false true d true,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 false a' false true d' true,
      allEq3_slot2_F, allEq3_slot2_F, allEq3_slot2_T, allEq3_slot2_T] at hv
    exact hv

/-- **Kill B3, slots (2,6) (proved)**. -/
theorem killB3_26 {u : ℕ} (hR : reconvR c = {u}) {q12 q18 q24 q45 : ℕ}
    (hq12c : q12 ∈ cone c) (hq12g : c.getD q12 (.cst false) = CGate.var ⟨12, h12⟩)
    (hnb12 : ¬ Reach c u q12)
    (hq18c : q18 ∈ cone c) (hq18g : c.getD q18 (.cst false) = CGate.var ⟨18, h18⟩)
    (hb18 : Reach c u q18)
    (hq24c : q24 ∈ cone c) (hq24g : c.getD q24 (.cst false) = CGate.var ⟨24, h24⟩)
    (hnb24 : ¬ Reach c u q24)
    (hq45c : q45 ∈ cone c) (hq45g : c.getD q45 (.cst false) = CGate.var ⟨45, h45⟩)
    (hb45 : Reach c u q45) : False := by
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd12 := sign12_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd18 := sign18_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd24 := sign24_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd45 := sign45_dep6 N hN h12 h18 h24 h31 h38 h45
  have htrans : ∀ a d : Bool,
      wire c (sixUpd N h12 h18 h24 h31 h38 h45 false a false true true d) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 true a true true true d) u := by
    intro a d
    calc wire c (sixUpd N h12 h18 h24 h31 h38 h45 false a false true true d) u
        = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            false a true true true d) ⟨24, h24⟩ false) u := by
          rw [sixUpd_upd3 h12 h18 h24 h31 h38 h45 false a true true true d false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 false a true true true d) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨24, h24⟩ hd24
            hq24c hq24g hnb24 _ false
      _ = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            true a true true true d) ⟨12, h12⟩ false) u := by
          rw [sixUpd_upd1 h12 h18 h24 h31 h38 h45 true a true true true d false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 true a true true true d) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨12, h12⟩ hd12
            hq12c hq12g hnb12 _ false
  refine b3_kill (fun a d =>
    wire c (sixUpd N h12 h18 h24 h31 h38 h45 true a true true true d) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      true a true true true d true a' true true true d'
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨18, h18⟩ hd18 w hw q18 hq18c hg hq18g]; exact hb18)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨45, h45⟩ hd45 w hw q45 hq45c hg hq45g]; exact hb45)
      hwu
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true a true true true d,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true a' true true true d',
      allEq3_slot2_T, allEq3_slot2_T, allEq3_slot3_T, allEq3_slot3_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (sixUpd N h12 h18 h24 h31 h38 h45 false a false true true d) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 false a' false true true d') u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      false a false true true d false a' false true true d'
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨18, h18⟩ hd18 w hw q18 hq18c hg hq18g]; exact hb18)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨45, h45⟩ hd45 w hw q45 hq45c hg hq45g]; exact hb45)
      hwu2
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 false a false true true d,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 false a' false true true d',
      allEq3_slot2_F, allEq3_slot2_F, allEq3_slot3_T, allEq3_slot3_T] at hv
    exact hv

/-- **Kill B3, slots (3,4) (proved)**. -/
theorem killB3_34 {u : ℕ} (hR : reconvR c = {u}) {q12 q18 q24 q31 : ℕ}
    (hq12c : q12 ∈ cone c) (hq12g : c.getD q12 (.cst false) = CGate.var ⟨12, h12⟩)
    (hnb12 : ¬ Reach c u q12)
    (hq18c : q18 ∈ cone c) (hq18g : c.getD q18 (.cst false) = CGate.var ⟨18, h18⟩)
    (hnb18 : ¬ Reach c u q18)
    (hq24c : q24 ∈ cone c) (hq24g : c.getD q24 (.cst false) = CGate.var ⟨24, h24⟩)
    (hb24 : Reach c u q24)
    (hq31c : q31 ∈ cone c) (hq31g : c.getD q31 (.cst false) = CGate.var ⟨31, h31⟩)
    (hb31 : Reach c u q31) : False := by
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd12 := sign12_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd18 := sign18_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd24 := sign24_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd31 := sign31_dep6 N hN h12 h18 h24 h31 h38 h45
  have htrans : ∀ a d : Bool,
      wire c (sixUpd N h12 h18 h24 h31 h38 h45 false false a d true true) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true a d true true) u := by
    intro a d
    calc wire c (sixUpd N h12 h18 h24 h31 h38 h45 false false a d true true) u
        = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            false true a d true true) ⟨18, h18⟩ false) u := by
          rw [sixUpd_upd2 h12 h18 h24 h31 h38 h45 false true a d true true false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 false true a d true true) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨18, h18⟩ hd18
            hq18c hq18g hnb18 _ false
      _ = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            true true a d true true) ⟨12, h12⟩ false) u := by
          rw [sixUpd_upd1 h12 h18 h24 h31 h38 h45 true true a d true true false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true a d true true) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨12, h12⟩ hd12
            hq12c hq12g hnb12 _ false
  refine b3_kill (fun a d =>
    wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true a d true true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      true true a d true true true true a' d' true true
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨24, h24⟩ hd24 w hw q24 hq24c hg hq24g]; exact hb24)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨31, h31⟩ hd31 w hw q31 hq31c hg hq31g]; exact hb31)
      (Or.inl rfl) (Or.inl rfl) hwu
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true a d true true,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true a' d' true true,
      allEq3_slot3_T, allEq3_slot3_T, allEq3_slot1_T, allEq3_slot1_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (sixUpd N h12 h18 h24 h31 h38 h45 false false a d true true) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 false false a' d' true true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      false false a d true true false false a' d' true true
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨24, h24⟩ hd24 w hw q24 hq24c hg hq24g]; exact hb24)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨31, h31⟩ hd31 w hw q31 hq31c hg hq31g]; exact hb31)
      (Or.inl rfl) (Or.inl rfl) hwu2
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 false false a d true true,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 false false a' d' true true,
      allEq3_slot3_F, allEq3_slot3_F, allEq3_slot1_T, allEq3_slot1_T] at hv
    exact hv

/-- **Kill B3, slots (3,5) (proved)**. -/
theorem killB3_35 {u : ℕ} (hR : reconvR c = {u}) {q12 q18 q24 q38 : ℕ}
    (hq12c : q12 ∈ cone c) (hq12g : c.getD q12 (.cst false) = CGate.var ⟨12, h12⟩)
    (hnb12 : ¬ Reach c u q12)
    (hq18c : q18 ∈ cone c) (hq18g : c.getD q18 (.cst false) = CGate.var ⟨18, h18⟩)
    (hnb18 : ¬ Reach c u q18)
    (hq24c : q24 ∈ cone c) (hq24g : c.getD q24 (.cst false) = CGate.var ⟨24, h24⟩)
    (hb24 : Reach c u q24)
    (hq38c : q38 ∈ cone c) (hq38g : c.getD q38 (.cst false) = CGate.var ⟨38, h38⟩)
    (hb38 : Reach c u q38) : False := by
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd12 := sign12_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd18 := sign18_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd24 := sign24_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd38 := sign38_dep6 N hN h12 h18 h24 h31 h38 h45
  have htrans : ∀ a d : Bool,
      wire c (sixUpd N h12 h18 h24 h31 h38 h45 false false a true d true) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true a true d true) u := by
    intro a d
    calc wire c (sixUpd N h12 h18 h24 h31 h38 h45 false false a true d true) u
        = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            false true a true d true) ⟨18, h18⟩ false) u := by
          rw [sixUpd_upd2 h12 h18 h24 h31 h38 h45 false true a true d true false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 false true a true d true) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨18, h18⟩ hd18
            hq18c hq18g hnb18 _ false
      _ = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            true true a true d true) ⟨12, h12⟩ false) u := by
          rw [sixUpd_upd1 h12 h18 h24 h31 h38 h45 true true a true d true false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true a true d true) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨12, h12⟩ hd12
            hq12c hq12g hnb12 _ false
  refine b3_kill (fun a d =>
    wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true a true d true) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      true true a true d true true true a' true d' true
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨24, h24⟩ hd24 w hw q24 hq24c hg hq24g]; exact hb24)
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨38, h38⟩ hd38 w hw q38 hq38c hg hq38g]; exact hb38)
      (Or.inl rfl) hwu
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true a true d true,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true a' true d' true,
      allEq3_slot3_T, allEq3_slot3_T, allEq3_slot2_T, allEq3_slot2_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (sixUpd N h12 h18 h24 h31 h38 h45 false false a true d true) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 false false a' true d' true) u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      false false a true d true false false a' true d' true
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨24, h24⟩ hd24 w hw q24 hq24c hg hq24g]; exact hb24)
      (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨38, h38⟩ hd38 w hw q38 hq38c hg hq38g]; exact hb38)
      (Or.inl rfl) hwu2
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 false false a true d true,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 false false a' true d' true,
      allEq3_slot3_F, allEq3_slot3_F, allEq3_slot2_T, allEq3_slot2_T] at hv
    exact hv

/-- **Kill B3, slots (3,6) (proved)**. -/
theorem killB3_36 {u : ℕ} (hR : reconvR c = {u}) {q12 q18 q24 q45 : ℕ}
    (hq12c : q12 ∈ cone c) (hq12g : c.getD q12 (.cst false) = CGate.var ⟨12, h12⟩)
    (hnb12 : ¬ Reach c u q12)
    (hq18c : q18 ∈ cone c) (hq18g : c.getD q18 (.cst false) = CGate.var ⟨18, h18⟩)
    (hnb18 : ¬ Reach c u q18)
    (hq24c : q24 ∈ cone c) (hq24g : c.getD q24 (.cst false) = CGate.var ⟨24, h24⟩)
    (hb24 : Reach c u q24)
    (hq45c : q45 ∈ cone c) (hq45g : c.getD q45 (.cst false) = CGate.var ⟨45, h45⟩)
    (hb45 : Reach c u q45) : False := by
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd12 := sign12_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd18 := sign18_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd24 := sign24_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd45 := sign45_dep6 N hN h12 h18 h24 h31 h38 h45
  have htrans : ∀ a d : Bool,
      wire c (sixUpd N h12 h18 h24 h31 h38 h45 false false a true true d) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true a true true d) u := by
    intro a d
    calc wire c (sixUpd N h12 h18 h24 h31 h38 h45 false false a true true d) u
        = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            false true a true true d) ⟨18, h18⟩ false) u := by
          rw [sixUpd_upd2 h12 h18 h24 h31 h38 h45 false true a true true d false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 false true a true true d) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨18, h18⟩ hd18
            hq18c hq18g hnb18 _ false
      _ = wire c (Function.update (sixUpd N h12 h18 h24 h31 h38 h45
            true true a true true d) ⟨12, h12⟩ false) u := by
          rw [sixUpd_upd1 h12 h18 h24 h31 h38 h45 true true a true true d false]
      _ = wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true a true true d) u :=
          wire_indep_of_not_below N c hcomp hs hlen hR ⟨12, h12⟩ hd12
            hq12c hq12g hnb12 _ false
  refine b3_kill (fun a d =>
    wire c (sixUpd N h12 h18 h24 h31 h38 h45 true true a true true d) u) ?_ ?_
  · intro a d a' d' hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      true true a true true d true true a' true true d'
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨24, h24⟩ hd24 w hw q24 hq24c hg hq24g]; exact hb24)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨45, h45⟩ hd45 w hw q45 hq45c hg hq45g]; exact hb45)
      hwu
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true a true true d,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true a' true true d',
      allEq3_slot3_T, allEq3_slot3_T, allEq3_slot3_T, allEq3_slot3_T] at hv
    exact hv
  · intro a d a' d' hwu
    have hwu2 : wire c (sixUpd N h12 h18 h24 h31 h38 h45 false false a true true d) u
        = wire c (sixUpd N h12 h18 h24 h31 h38 h45 false false a' true true d') u := by
      rw [htrans a d, htrans a' d']
      exact hwu
    have hv := refine_sixUpd N h12 h18 h24 h31 h38 h45 c hcomp hs hR
      false false a true true d false false a' true true d'
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨24, h24⟩ hd24 w hw q24 hq24c hg hq24g]; exact hb24)
      (Or.inl rfl) (Or.inl rfl)
      (Or.inr fun w hw hg => by
        rw [huniq ⟨45, h45⟩ hd45 w hw q45 hq45c hg hq45g]; exact hb45)
      hwu2
    rw [SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 false false a true true d,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 false false a' true true d',
      allEq3_slot3_F, allEq3_slot3_F, allEq3_slot3_T, allEq3_slot3_T] at hv
    exact hv

end B3

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.wire_indep_of_not_below
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killB2_g0_free1
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killB2_g1_free6
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killB3_14
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killB3_36
