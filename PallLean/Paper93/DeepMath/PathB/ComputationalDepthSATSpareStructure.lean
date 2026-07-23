import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATAboveFloor
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSlotCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMediatedDichotomy
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGTreeSplit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShapeTreeExtract

/-!
# The spare structure of near-floor SAT circuits: exactly one reconvergence wire

Brick 2 of the `+2` campaign.  At one unit above the cone floor
(`c.length ≤ 2·deps`), the slot identity pins the circuit's shape:

* **`spare_bound` (proved, general)** — excess `≤ 1`, `|coneVars| = deps` exactly,
  and `≤ 1` reconvergence wire;
* **`dep_var_gate` / `unique_var_gate` (proved, general)** — every dependent
  variable has a var gate in the cone, and at `|coneVars| ≤ deps` that gate is
  UNIQUE (the choice-image fills `coneVars`, so a second gate has nowhere to live);
* **`sign9_dep`/`sign15_dep`/`sign21_dep` (proved)** — the sign positions are
  genuine dependencies of every SAT slice `≥ 22`;
* **`rfree_dies` (proved)** — a reconvergence-FREE near-floor circuit is
  impossible: unique gates + no reconvergence force `cnt = 1` at the three sign
  coordinates in the unwound tree (`extractG_cnt_spec`), so it splits
  (`gtree_split_cnt`) — but the codec's `AllEqual₃` refuses every split;
* **`SATFamily_spare_structure` (proved)** — hence every near-floor circuit for a
  SAT slice has **exactly one** reconvergence wire;
* **`SATFamily_optimal_one_reconv` (proved)** — in particular every optimal
  circuit, whenever `cbudget (SATFamily N) ≤ 2·deps`.

## Honest scope

This pins the one-spare-unit shape; the remaining `+2` content is the collision
analysis at that single wire (both gadget triples routed through it — the
mediation kill), which is the open brick 3.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor

/-! ### The triple restriction and the sign dependencies -/

/-- The codec triple restriction, packaged for the function itself. -/
theorem SATFamily_triple_restrict (N : ℕ) (hN : 22 ≤ N) (h9 : 9 < N) (h15 : 15 < N)
    (h21 : 21 < N) :
    (fun a b c => SATFamily N (Function.update (Function.update
      (Function.update (zBase N) ⟨9, h9⟩ a) ⟨15, h15⟩ b) ⟨21, h21⟩ c)) = allEq3 := by
  funext a b c
  show SATFamily N _ = allEq3 a b c
  rw [SATFamily_apply, word_triple N hN h9 h15 h21 a b c, SATLang_se_append]

/-- **Sign position 9 is a genuine dependency (proved)**. -/
theorem sign9_dep (N : ℕ) (hN : 22 ≤ N) (h9 : 9 < N) (h15 : 15 < N) (h21 : 21 < N) :
    (⟨9, h9⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  have hF := SATFamily_triple_restrict N hN h9 h15 h21
  have hFv : ∀ a b c, SATFamily N (Function.update (Function.update
      (Function.update (zBase N) ⟨9, h9⟩ a) ⟨15, h15⟩ b) ⟨21, h21⟩ c) = allEq3 a b c :=
    fun a b c => congrFun (congrFun (congrFun hF a) b) c
  have hne21_9 : (⟨21, h21⟩ : Fin N) ≠ ⟨9, h9⟩ := by
    intro he; rw [Fin.mk.injEq] at he; omega
  have hne15_9 : (⟨15, h15⟩ : Fin N) ≠ ⟨9, h9⟩ := by
    intro he; rw [Fin.mk.injEq] at he; omega
  refine ⟨Function.update (Function.update (Function.update (zBase N)
    ⟨9, h9⟩ true) ⟨15, h15⟩ true) ⟨21, h21⟩ true, false, ?_⟩
  have hx : Function.update (Function.update (Function.update (Function.update (zBase N)
      ⟨9, h9⟩ true) ⟨15, h15⟩ true) ⟨21, h21⟩ true) ⟨9, h9⟩ false
      = Function.update (Function.update (Function.update (zBase N)
        ⟨9, h9⟩ false) ⟨15, h15⟩ true) ⟨21, h21⟩ true := by
    rw [Function.update_comm hne21_9, Function.update_comm hne15_9,
      Function.update_idem]
  rw [hx, hFv false true true, hFv true true true]
  decide

/-- **Sign position 15 is a genuine dependency (proved)**. -/
theorem sign15_dep (N : ℕ) (hN : 22 ≤ N) (h9 : 9 < N) (h15 : 15 < N) (h21 : 21 < N) :
    (⟨15, h15⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  have hF := SATFamily_triple_restrict N hN h9 h15 h21
  have hFv : ∀ a b c, SATFamily N (Function.update (Function.update
      (Function.update (zBase N) ⟨9, h9⟩ a) ⟨15, h15⟩ b) ⟨21, h21⟩ c) = allEq3 a b c :=
    fun a b c => congrFun (congrFun (congrFun hF a) b) c
  have hne21_15 : (⟨21, h21⟩ : Fin N) ≠ ⟨15, h15⟩ := by
    intro he; rw [Fin.mk.injEq] at he; omega
  refine ⟨Function.update (Function.update (Function.update (zBase N)
    ⟨9, h9⟩ true) ⟨15, h15⟩ true) ⟨21, h21⟩ true, false, ?_⟩
  have hx : Function.update (Function.update (Function.update (Function.update (zBase N)
      ⟨9, h9⟩ true) ⟨15, h15⟩ true) ⟨21, h21⟩ true) ⟨15, h15⟩ false
      = Function.update (Function.update (Function.update (zBase N)
        ⟨9, h9⟩ true) ⟨15, h15⟩ false) ⟨21, h21⟩ true := by
    rw [Function.update_comm hne21_15, Function.update_idem]
  rw [hx, hFv true false true, hFv true true true]
  decide

/-- **Sign position 21 is a genuine dependency (proved)**. -/
theorem sign21_dep (N : ℕ) (hN : 22 ≤ N) (h9 : 9 < N) (h15 : 15 < N) (h21 : 21 < N) :
    (⟨21, h21⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  have hF := SATFamily_triple_restrict N hN h9 h15 h21
  have hFv : ∀ a b c, SATFamily N (Function.update (Function.update
      (Function.update (zBase N) ⟨9, h9⟩ a) ⟨15, h15⟩ b) ⟨21, h21⟩ c) = allEq3 a b c :=
    fun a b c => congrFun (congrFun (congrFun hF a) b) c
  refine ⟨Function.update (Function.update (Function.update (zBase N)
    ⟨9, h9⟩ true) ⟨15, h15⟩ true) ⟨21, h21⟩ true, false, ?_⟩
  rw [Function.update_idem, hFv true true false, hFv true true true]
  decide

/-! ### The spare bound: excess ≤ 1, coneVars = deps, ≤ 1 reconvergence -/

theorem cone_card_le_length {n : ℕ} (c : List (CGate n)) :
    (cone c).card ≤ c.length := by
  calc (cone c).card
      ≤ (Finset.range c.length).card := Finset.card_le_card (by
        intro w hw
        exact Finset.mem_range.mpr (mem_cone.mp hw).1)
    _ = c.length := Finset.card_range _

/-- **The spare bound (proved, general)**: one unit above the floor leaves excess
`≤ 1`, fills `coneVars` exactly, and admits at most one reconvergence wire. -/
theorem spare_bound {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hs : 0 < c.length)
    (hlen : c.length ≤ 2 * (depSet f).card) :
    excessX c ≤ 1 ∧ (coneVars c).card = (depSet f).card ∧ (reconvR c).card ≤ 1 := by
  have hdW := depSet_card_le_coneVars f c hcomp hs
  have hslot := cone_ge_slot c hs
  have hcone := cone_card_le_length c
  have hrX := reconvR_card_le c
  refine ⟨by omega, by omega, by omega⟩

/-! ### Unique var gates in the tight regime -/

/-- **Every dependency has a cone var gate (proved, general)**. -/
theorem dep_var_gate {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hs : 0 < c.length) :
    ∀ i ∈ depSet f, ∃ w, w ∈ cone c ∧ c.getD w (.cst false) = CGate.var i := by
  intro i hi
  obtain ⟨x, b, hxb⟩ := mem_depSet.mp hi
  by_contra hno
  push_neg at hno
  have hnv : ∀ w, InCone c w → c.getD w (.cst false) ≠ CGate.var i := fun w hw he =>
    hno w (mem_cone.mpr ⟨inCone_lt hs hw, hw⟩) he
  refine hxb ?_
  rw [← hcomp (Function.update x i b), ← hcomp x, output_eq_wire, output_eq_wire]
  exact cone_wire_agree c i x b hs hnv _ InCone.root

/-- **The unique gate theorem (proved, general)**: when `|coneVars| ≤ deps`, each
dependency's var gate is unique — the choice-image already fills `coneVars`. -/
theorem unique_var_gate {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hs : 0 < c.length)
    (hWd : (coneVars c).card ≤ (depSet f).card) :
    ∀ i ∈ depSet f, ∀ q₁ ∈ cone c, ∀ q₂ ∈ cone c,
      c.getD q₁ (.cst false) = CGate.var i → c.getD q₂ (.cst false) = CGate.var i →
      q₁ = q₂ := by
  classical
  have hex := dep_var_gate f c hcomp hs
  intro i hi q₁ hq₁ q₂ hq₂ hg₁ hg₂
  let φ : Fin n → ℕ := fun j =>
    if h : ∃ w, w ∈ cone c ∧ c.getD w (.cst false) = CGate.var j
    then Classical.choose h else 0
  have hφspec : ∀ j ∈ depSet f,
      φ j ∈ cone c ∧ c.getD (φ j) (.cst false) = CGate.var j := by
    intro j hj
    obtain ⟨w, hw⟩ := hex j hj
    have hex' : ∃ w, w ∈ cone c ∧ c.getD w (.cst false) = CGate.var j := ⟨w, hw⟩
    have hdef : φ j = Classical.choose hex' := dif_pos hex'
    rw [hdef]
    exact Classical.choose_spec hex'
  have himg : (depSet f).image φ ⊆ coneVars c := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hc1, hc2⟩ := hφspec j hj
    rw [coneVars, Finset.mem_filter]
    exact ⟨hc1, ⟨j, hc2⟩⟩
  have hinj : Set.InjOn φ (depSet f) := by
    intro a ha b hb hab
    have hsa := (hφspec a (Finset.mem_coe.mp ha)).2
    have hsb := (hφspec b (Finset.mem_coe.mp hb)).2
    rw [hab] at hsa
    exact CGate.var.inj (hsa.symm.trans hsb)
  have hcard : ((depSet f).image φ).card = (depSet f).card :=
    Finset.card_image_of_injOn hinj
  have heq : (depSet f).image φ = coneVars c :=
    Finset.eq_of_subset_of_card_le himg (by omega)
  have hq₁v : q₁ ∈ (depSet f).image φ := by
    rw [heq, coneVars, Finset.mem_filter]
    exact ⟨hq₁, ⟨i, hg₁⟩⟩
  have hq₂v : q₂ ∈ (depSet f).image φ := by
    rw [heq, coneVars, Finset.mem_filter]
    exact ⟨hq₂, ⟨i, hg₂⟩⟩
  obtain ⟨a, ha, hφa⟩ := Finset.mem_image.mp hq₁v
  obtain ⟨b, hb, hφb⟩ := Finset.mem_image.mp hq₂v
  have hga := (hφspec a ha).2
  rw [hφa] at hga
  have hai : a = i := CGate.var.inj (hga.symm.trans hg₁)
  have hgb := (hφspec b hb).2
  rw [hφb] at hgb
  have hbi : b = i := CGate.var.inj (hgb.symm.trans hg₂)
  rw [← hφa, ← hφb, hai, hbi]

/-! ### The reconvergence-free case dies -/

/-- **No reconvergence-free near-floor circuit computes a SAT slice (proved)**:
unique gates + no reconvergence force `cnt = 1` at the sign triple in the unwound
tree, which then splits — refuted by the codec's `AllEqual₃`. -/
theorem rfree_dies (N : ℕ) (hN : 22 ≤ N) (c : List (CGate N))
    (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hlen : c.length ≤ 2 * (depSet (SATFamily N)).card)
    (hrf : reconvR c = ∅) : False := by
  have h9 : (9 : ℕ) < N := by omega
  have h15 : (15 : ℕ) < N := by omega
  have h21 : (21 : ℕ) < N := by omega
  have hd9 := sign9_dep N hN h9 h15 h21
  have hd15 := sign15_dep N hN h9 h15 h21
  have hd21 := sign21_dep N hN h9 h15 h21
  obtain ⟨hX, hWd, hR⟩ := spare_bound (SATFamily N) c hcomp hs hlen
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  obtain ⟨q9, hq9c, hq9g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd9
  obtain ⟨q15, hq15c, hq15g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd15
  obtain ⟨q21, hq21c, hq21g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd21
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  have hRvac : ∀ q₀ : ℕ, ∀ u ∈ reconvR c, ¬ Reach c u q₀ := by
    intro q₀ u hu
    rw [hrf] at hu
    exact absurd hu (Finset.notMem_empty u)
  have hcnt9 := (extractG_cnt_spec c hs ⟨9, h9⟩ q9 hq9c hq9g
      (fun q hq hg => huniq ⟨9, h9⟩ hd9 q hq q9 hq9c hg hq9g)
      (hRvac q9) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq9c).2)
  have hcnt15 := (extractG_cnt_spec c hs ⟨15, h15⟩ q15 hq15c hq15g
      (fun q hq hg => huniq ⟨15, h15⟩ hd15 q hq q15 hq15c hg hq15g)
      (hRvac q15) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq15c).2)
  have hcnt21 := (extractG_cnt_spec c hs ⟨21, h21⟩ q21 hq21c hq21g
      (fun q hq hg => huniq ⟨21, h21⟩ hd21 q hq q21 hq21c hg hq21g)
      (hRvac q21) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq21c).2)
  have hsp := gtree_split_cnt (extractG c c.length (c.length - 1))
    ⟨9, h9⟩ ⟨15, h15⟩ ⟨21, h21⟩
    (by intro he; rw [Fin.mk.injEq] at he; omega)
    (by intro he; rw [Fin.mk.injEq] at he; omega)
    (by intro he; rw [Fin.mk.injEq] at he; omega)
    (zBase N) hcnt9 hcnt15 hcnt21
  have heval : ∀ x, (extractG c c.length (c.length - 1)).eval x = SATFamily N x := by
    intro x
    rw [extractG_eval c c.length (c.length - 1) (by omega) (by omega) x]
    exact hcomp x
  have heq : (fun a b g => (extractG c c.length (c.length - 1)).eval
      (Function.update (Function.update (Function.update (zBase N)
        ⟨9, h9⟩ a) ⟨15, h15⟩ b) ⟨21, h21⟩ g)) = allEq3 := by
    funext a b g
    rw [heval]
    have hF := SATFamily_triple_restrict N hN h9 h15 h21
    exact congrFun (congrFun (congrFun hF a) b) g
  rw [heq] at hsp
  rcases hsp with h | h | h
  · exact allEq3_no_split_a h
  · exact allEq3_no_split_b h
  · exact allEq3_no_split_c h

/-! ### The spare structure theorem -/

/-- **THE SPARE STRUCTURE (proved)**: every near-floor circuit for a SAT slice has
exactly ONE reconvergence wire. -/
theorem SATFamily_spare_structure (N : ℕ) (hN : 22 ≤ N) (c : List (CGate N))
    (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hlen : c.length ≤ 2 * (depSet (SATFamily N)).card) :
    (reconvR c).card = 1 := by
  obtain ⟨hX, hWd, hR⟩ := spare_bound (SATFamily N) c hcomp hs hlen
  rcases Nat.eq_zero_or_pos (reconvR c).card with h0 | hpos
  · exact (rfree_dies N hN c hcomp hs hlen (Finset.card_eq_zero.mp h0)).elim
  · omega

/-- **Optimal circuits at the `+1` level (proved)**: whenever
`cbudget (SATFamily N) ≤ 2·deps`, every optimal circuit has exactly one
reconvergence wire. -/
theorem SATFamily_optimal_one_reconv (N : ℕ) (hN : 22 ≤ N)
    (hcb : cbudget (SATFamily N) ≤ 2 * (depSet (SATFamily N)).card) :
    ∀ c : List (CGate N), computes c (SATFamily N) →
      c.length = cbudget (SATFamily N) → (reconvR c).card = 1 := by
  intro c hcomp hclen
  have h9 : (9 : ℕ) < N := by omega
  have hd1 : 1 ≤ (depSet (SATFamily N)).card :=
    Finset.card_pos.mpr ⟨_, sign9_dep N hN h9 (by omega) (by omega)⟩
  have hfl := cone_bound (SATFamily N)
  have hs : 0 < c.length := by omega
  exact SATFamily_spare_structure N hN c hcomp hs (by omega)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.spare_bound
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.unique_var_gate
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.rfree_dies
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.SATFamily_spare_structure
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.SATFamily_optimal_one_reconv
