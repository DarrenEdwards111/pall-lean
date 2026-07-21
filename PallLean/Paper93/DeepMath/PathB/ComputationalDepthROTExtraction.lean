import PallLean.Paper93.DeepMath.PathB.ComputationalDepthROTSplit

/-!
# The circuit half: floor circuits realize read-once trees

Discharge of the `FloorRealizesROT` fence.  At the cone floor
(`length + 1 = 2·deps`) the parent-edge counting is *exact*, and everything
follows from that exactness:

* **`floor_wiring` (proved)** — every read of every cone gate is in-range, lands in
  the cone, misses the root, and no binary gate reads the same wire twice: the edge
  set coincides with the parent-injection image, so a stray edge (out-of-range,
  or a repeated slot) breaks `|E| = |cone| − 1`;
* **`floor_var_injective` (proved)** — distinct cone `var` positions carry distinct
  variables: the `d` dependent variables inject into the `d` var positions, so the
  correspondence is a bijection;
* **`reach_not_both` (proved)** — the two sources of a binary cone gate reach
  disjoint position sets: readers are unique (`floor_fanout_le_one`), so the
  reader chain from a common descendant is deterministic and cannot pass through
  both sources;
* **`extractT` / `extractT_spec` (proved)** — fuel-indexed extraction of a
  read-once tree from any cone position, computing the wire and with leaves
  tracked by reachability;
* **`floor_realizes_ROT` (proved)** — `FloorRealizesROT` holds: THE FENCE IS
  DISCHARGED;
* **`cbudget_above_floor_of_unsplittable` (proved)** — the reusable cash-out: a
  function with one unsplittable triple restriction satisfies
  `2·deps ≤ cbudget`;
* **`AEm_above_floor` (proved, unconditional)** — `6m ≤ cbudget (AEm m)` for every
  `m ≥ 1`.

## Honest scope

`6m` is `floor + 1` **globally**, not `+1` per gadget: `6m < 7m − 1` for `m ≥ 2`,
so `SlackComposes` remains open and this is exactly the "slack survives
composition only as `+O(1)`" scenario to be probed further.  Everything here is
linear.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-! ### Downward reachability from an arbitrary position -/

/-- Positions reachable downward from `w` through in-range reads. -/
inductive Reach (c : List (CGate n)) : ℕ → ℕ → Prop
  | refl (w : ℕ) : Reach c w w
  | step {w p q : ℕ} : Reach c w p → q ∈ gateReads (c.getD p (.cst false)) → q < p →
      Reach c w q

theorem reach_le {c : List (CGate n)} {a b : ℕ} (h : Reach c a b) : b ≤ a := by
  induction h with
  | refl => exact le_refl _
  | step hp hq hlt ih => omega

theorem reach_inCone {c : List (CGate n)} {a b : ℕ} (ha : InCone c a)
    (h : Reach c a b) : InCone c b := by
  induction h with
  | refl => exact ha
  | step hp hq hlt ih => exact InCone.step ih hq hlt

theorem reach_trans {c : List (CGate n)} {a b d : ℕ} (h1 : Reach c a b)
    (h2 : Reach c b d) : Reach c a d := by
  induction h2 with
  | refl => exact h1
  | step hp hq hlt ih => exact Reach.step ih hq hlt

/-- A reached position other than the start has a reached in-range reader. -/
theorem reach_last {c : List (CGate n)} {a b : ℕ} (h : Reach c a b) (hne : b ≠ a) :
    ∃ p, Reach c a p ∧ b ∈ gateReads (c.getD p (.cst false)) ∧ b < p := by
  cases h with
  | refl => exact absurd rfl hne
  | step hp hq hlt => exact ⟨_, hp, hq, hlt⟩

/-! ### Exact wiring at the floor -/

/-- **Floor wiring (proved).**  At the floor the edge count is exact, so every read
of every cone gate is in-range, in the cone, and not the root — and no binary cone
gate reads the same wire in both slots. -/
theorem floor_wiring {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hlen : c.length + 1 = 2 * (depSet f).card) :
    (∀ w ∈ cone c, ∀ t ∈ gateReads (c.getD w (.cst false)),
      t < w ∧ t ∈ cone c ∧ t ≠ c.length - 1)
    ∧ ∀ w ∈ cone c, ∀ (op : Bool → Bool → Bool) (j : ℕ),
        c.getD w (.cst false) ≠ CGate.bin op j j := by
  classical
  have hs : 0 < c.length := by omega
  obtain ⟨hconeCard, hvarCard, hbin⟩ := floor_census f c hcomp hlen
  -- the slot sum is exactly |cone| − 1
  have hsplit : ∑ w ∈ coneVars c, inSlots (c.getD w (.cst false))
      + ∑ w ∈ (cone c).filter
          (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
          inSlots (c.getD w (.cst false))
      = ∑ w ∈ cone c, inSlots (c.getD w (.cst false)) := by
    rw [coneVars]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hvar0 : ∑ w ∈ coneVars c, inSlots (c.getD w (.cst false)) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    rw [coneVars, Finset.mem_filter] at hw
    obtain ⟨-, i', hi'⟩ := hw
    rw [hi']
    rfl
  have hterms : ∀ w ∈ (cone c).filter
      (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
      inSlots (c.getD w (.cst false)) = 2 := by
    intro w hw
    rw [Finset.mem_filter] at hw
    exact hbin w hw.1 hw.2
  have hrest2 : ∑ w ∈ (cone c).filter
      (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
      inSlots (c.getD w (.cst false))
      = 2 * ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card := by
    rw [Finset.sum_congr rfl hterms, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hpart : (coneVars c).card
      + ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card
      = (cone c).card := by
    rw [coneVars]
    exact Finset.card_filter_add_card_filter_not (s := cone c)
      (p := fun w => ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')
  have hsum : ∑ w ∈ cone c, inSlots (c.getD w (.cst false)) = (cone c).card - 1 := by
    omega
  -- the parent-edge injection scaffold
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  have hex : ∀ x ∈ (cone c).erase (c.length - 1),
      ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w := by
    intro x hx
    obtain ⟨hxne, hxc⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxlt, hxcone⟩ := mem_cone.mp hxc
    cases hxcone with
    | root => exact absurd rfl hxne
    | step hw hjm hjw => exact ⟨_, hw, hjm, hjw⟩
  have himg_sub : ((cone c).erase (c.length - 1)).image
      (fun x => (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0, x))
      ⊆ (cone c).biUnion
        (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t))) := by
    intro pr hpr
    obtain ⟨x, hx, hφ⟩ := Finset.mem_image.mp hpr
    obtain ⟨w, hw⟩ := hex x hx
    rw [← hφ, dif_pos ⟨w, hw⟩]
    have hspec := Classical.choose_spec
      (⟨w, hw⟩ : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w)
    rw [Finset.mem_biUnion]
    exact ⟨_, mem_cone.mpr ⟨inCone_lt hs hspec.1, hspec.1⟩,
      Finset.mem_image.mpr ⟨x, hspec.2.1, rfl⟩⟩
  have hinj : Set.InjOn
      (fun x => (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0, x))
      ((cone c).erase (c.length - 1)) := by
    intro a _ b _ hab
    exact congrArg Prod.snd hab
  have himg_card : (((cone c).erase (c.length - 1)).image
      (fun x => (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0, x))).card
      = (cone c).card - 1 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hroot]
  have hEle : ((cone c).biUnion
      (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t)))).card
      ≤ ∑ w ∈ cone c, (gateReads (c.getD w (.cst false))).card := by
    refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum ?_)
    intro w _
    exact Finset.card_image_le
  have hcards : ∀ w' ∈ cone c,
      (gateReads (c.getD w' (.cst false))).card ≤ inSlots (c.getD w' (.cst false)) :=
    fun w' _ => gateReads_card_le _
  have hEsl : ∑ w ∈ cone c, (gateReads (c.getD w (.cst false))).card
      ≤ ∑ w ∈ cone c, inSlots (c.getD w (.cst false)) := Finset.sum_le_sum hcards
  have hElo : (cone c).card - 1 ≤ ((cone c).biUnion
      (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t)))).card := by
    rw [← himg_card]
    exact Finset.card_le_card himg_sub
  have hcpos : 1 ≤ (cone c).card := Finset.card_pos.mpr ⟨_, hroot⟩
  constructor
  · -- every edge is a parent-injection edge
    intro w hwc t ht
    have hEmem : (w, t) ∈ (cone c).biUnion
        (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t))) :=
      Finset.mem_biUnion.mpr ⟨w, hwc, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩
    have hEeq : ((cone c).erase (c.length - 1)).image
        (fun x => (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
          then Classical.choose h else 0, x))
        = (cone c).biUnion
          (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t))) :=
      Finset.eq_of_subset_of_card_le himg_sub (by omega)
    rw [← hEeq] at hEmem
    obtain ⟨x, hx, hφ⟩ := Finset.mem_image.mp hEmem
    have hxt : x = t := congrArg Prod.snd hφ
    subst hxt
    obtain ⟨htne, htc⟩ := Finset.mem_erase.mp hx
    have hφ1 : (if h : ∃ w', InCone c w' ∧ x ∈ gateReads (c.getD w' (.cst false)) ∧ x < w'
        then Classical.choose h else 0) = w := congrArg Prod.fst hφ
    have hxe := hex x hx
    rw [dif_pos hxe] at hφ1
    have hspec := Classical.choose_spec hxe
    rw [hφ1] at hspec
    exact ⟨hspec.2.2, htc, htne⟩
  · -- no repeated slot
    intro w hwc op j hg
    have hstrict : ∑ w' ∈ cone c, (gateReads (c.getD w' (.cst false))).card
        < ∑ w' ∈ cone c, inSlots (c.getD w' (.cst false)) := by
      refine Finset.sum_lt_sum hcards ⟨w, hwc, ?_⟩
      rw [hg]
      show ({j, j} : Finset ℕ).card < 2
      rw [Finset.insert_eq_self.mpr (Finset.mem_singleton_self j)]
      rw [Finset.card_singleton]
      omega
    omega

/-! ### Variables are carried by unique cone positions -/

/-- **Var injectivity at the floor (proved).**  The `d` dependent variables inject
into the `d` cone var positions, so the correspondence is a bijection: two cone
positions carrying the same variable coincide. -/
theorem floor_var_injective {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hlen : c.length + 1 = 2 * (depSet f).card)
    {w₁ w₂ : ℕ} {i : Fin n} (h₁ : w₁ ∈ cone c) (h₂ : w₂ ∈ cone c)
    (hg₁ : c.getD w₁ (.cst false) = CGate.var i)
    (hg₂ : c.getD w₂ (.cst false) = CGate.var i) : w₁ = w₂ := by
  classical
  have hs : 0 < c.length := by omega
  have hex : ∀ i' ∈ depSet f, ∃ p, p ∈ cone c ∧ c.getD p (.cst false) = CGate.var i' :=
    fun i' hi' => var_position_exists f c hcomp hs i' hi'
  set S : Finset ℕ := (depSet f).attach.image
    (fun x => Classical.choose (hex x.1 x.2)) with hSdef
  have hSsub : S ⊆ coneVars c := by
    intro p hp
    rw [hSdef, Finset.mem_image] at hp
    obtain ⟨x, -, hpx⟩ := hp
    obtain ⟨hpc, hpg⟩ := Classical.choose_spec (hex x.1 x.2)
    rw [← hpx, coneVars, Finset.mem_filter]
    exact ⟨hpc, ⟨x.1, hpg⟩⟩
  have hinjOn : Set.InjOn
      (fun x : {i' // i' ∈ depSet f} => Classical.choose (hex x.1 x.2))
      ((depSet f).attach : Finset {i' // i' ∈ depSet f}) := by
    intro x _ y _ hxy
    have hxy' : Classical.choose (hex x.1 x.2) = Classical.choose (hex y.1 y.2) := hxy
    obtain ⟨-, hgx⟩ := Classical.choose_spec (hex x.1 x.2)
    obtain ⟨-, hgy⟩ := Classical.choose_spec (hex y.1 y.2)
    rw [hxy'] at hgx
    have hv : CGate.var (n := n) x.1 = CGate.var y.1 := hgx.symm.trans hgy
    exact Subtype.ext (CGate.var.inj hv)
  have hScard : S.card = (depSet f).card := by
    rw [hSdef, Finset.card_image_of_injOn hinjOn, Finset.card_attach]
  have hSeq : S = coneVars c := by
    refine Finset.eq_of_subset_of_card_le hSsub ?_
    rw [hScard]
    exact le_of_eq (floor_census f c hcomp hlen).2.1
  have hw₁ : w₁ ∈ S := by
    rw [hSeq, coneVars, Finset.mem_filter]
    exact ⟨h₁, ⟨i, hg₁⟩⟩
  have hw₂ : w₂ ∈ S := by
    rw [hSeq, coneVars, Finset.mem_filter]
    exact ⟨h₂, ⟨i, hg₂⟩⟩
  rw [hSdef, Finset.mem_image] at hw₁ hw₂
  obtain ⟨x, -, hx⟩ := hw₁
  obtain ⟨y, -, hy⟩ := hw₂
  obtain ⟨-, hgx⟩ := Classical.choose_spec (hex x.1 x.2)
  obtain ⟨-, hgy⟩ := Classical.choose_spec (hex y.1 y.2)
  rw [hx, hg₁] at hgx
  rw [hy, hg₂] at hgy
  have hxy : x = y := Subtype.ext ((CGate.var.inj hgx).symm.trans (CGate.var.inj hgy))
  rw [← hx, ← hy, hxy]

/-! ### The two sources of a binary gate reach disjoint sets -/

/-- **Reader-chain disjointness (proved).**  At the floor, readers are unique, so
the reader chain from any position is deterministic — it cannot pass through both
sources of a binary cone gate. -/
theorem reach_not_both {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hlen : c.length + 1 = 2 * (depSet f).card)
    {w j k : ℕ} (hwc : w ∈ cone c)
    (hj : j ∈ gateReads (c.getD w (.cst false))) (hjw : j < w)
    (hk : k ∈ gateReads (c.getD w (.cst false))) (hkw : k < w)
    (hjk : j ≠ k) :
    ∀ (m q : ℕ), c.length - q ≤ m → Reach c j q → Reach c k q → False := by
  have hs : 0 < c.length := by omega
  have hwlt : w < c.length := (mem_cone.mp hwc).1
  have hwic : InCone c w := (mem_cone.mp hwc).2
  have hjc : j ∈ cone c := mem_cone.mpr ⟨by omega, InCone.step hwic hj hjw⟩
  have hkc : k ∈ cone c := mem_cone.mpr ⟨by omega, InCone.step hwic hk hkw⟩
  intro m
  induction m with
  | zero =>
    intro q hq hrj _
    have hql := reach_le hrj
    have hjlt : j < c.length := (mem_cone.mp hjc).1
    omega
  | succ m ih =>
    intro q hq hrj hrk
    by_cases hqj : q = j
    · subst hqj
      obtain ⟨p, hpk, hqp, hqlt⟩ := reach_last hrk hjk
      have hpic : InCone c p := reach_inCone (mem_cone.mp hkc).2 hpk
      have hpc : p ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hpic, hpic⟩
      have hqroot : q ≠ c.length - 1 := by omega
      have hpw : p = w :=
        floor_fanout_le_one f c hcomp hlen q hjc hqroot p w hpc hwc hqp hj
      subst hpw
      have := reach_le hpk
      omega
    · by_cases hqk : q = k
      · subst hqk
        obtain ⟨p, hpj, hqp, hqlt⟩ := reach_last hrj (Ne.symm hjk)
        have hpic : InCone c p := reach_inCone (mem_cone.mp hjc).2 hpj
        have hpc : p ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hpic, hpic⟩
        have hqroot : q ≠ c.length - 1 := by omega
        have hpw : p = w :=
          floor_fanout_le_one f c hcomp hlen q hkc hqroot p w hpc hwc hqp hk
        subst hpw
        have := reach_le hpj
        omega
      · obtain ⟨p₁, hp₁, hqr₁, hql₁⟩ := reach_last hrj hqj
        obtain ⟨p₂, hp₂, hqr₂, hql₂⟩ := reach_last hrk hqk
        have hp₁ic : InCone c p₁ := reach_inCone (mem_cone.mp hjc).2 hp₁
        have hp₂ic : InCone c p₂ := reach_inCone (mem_cone.mp hkc).2 hp₂
        have hp₁c : p₁ ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hp₁ic, hp₁ic⟩
        have hp₂c : p₂ ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hp₂ic, hp₂ic⟩
        have hp₁le := reach_le hp₁
        have hqc : q ∈ cone c :=
          mem_cone.mpr ⟨by omega, InCone.step hp₁ic hqr₁ hql₁⟩
        have hqroot : q ≠ c.length - 1 := by omega
        have h12 : p₁ = p₂ :=
          floor_fanout_le_one f c hcomp hlen q hqc hqroot p₁ p₂ hp₁c hp₂c hqr₁ hqr₂
        subst h12
        exact ih p₁ (by omega) hp₁ hp₂

/-! ### The extraction -/

/-- Fuel-indexed extraction of a read-once tree from a circuit position. -/
def extractT (c : List (CGate n)) (i₀ : Fin n) : ℕ → ℕ → ROT n
  | 0, _ => .leaf i₀
  | fuel + 1, w =>
    match c.getD w (.cst false) with
    | .var i => .leaf i
    | .bin op j k => .node op (extractT c i₀ fuel j) (extractT c i₀ fuel k)
    | .un _ _ => .leaf i₀
    | .cst _ => .leaf i₀

theorem extractT_var {n : ℕ} {c : List (CGate n)} {i₀ i : Fin n} {fuel w : ℕ}
    (hg : c.getD w (.cst false) = CGate.var i) :
    extractT c i₀ (fuel + 1) w = ROT.leaf i := by
  simp only [extractT]
  rw [hg]

theorem extractT_bin {n : ℕ} {c : List (CGate n)} {i₀ : Fin n} {fuel w : ℕ}
    {op : Bool → Bool → Bool} {j k : ℕ}
    (hg : c.getD w (.cst false) = CGate.bin op j k) :
    extractT c i₀ (fuel + 1) w
      = ROT.node op (extractT c i₀ fuel j) (extractT c i₀ fuel k) := by
  simp only [extractT]
  rw [hg]

/-- **The extraction is correct (proved).**  From every cone position, the extracted
tree is read-once, computes the wire, and its leaves are the variables of reachable
var positions. -/
theorem extractT_spec {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hlen : c.length + 1 = 2 * (depSet f).card) (i₀ : Fin n) :
    ∀ (fuel w : ℕ), w < fuel → w ∈ cone c →
      ROT.ReadOnce (extractT c i₀ fuel w)
      ∧ (∀ x, (extractT c i₀ fuel w).eval x = wire c x w)
      ∧ (∀ i, i ∈ (extractT c i₀ fuel w).leaves →
          ∃ p, Reach c w p ∧ c.getD p (.cst false) = CGate.var i) := by
  obtain ⟨hedge, hnoself⟩ := floor_wiring f c hcomp hlen
  intro fuel
  induction fuel with
  | zero => intro w hw _; exact absurd hw (Nat.not_lt_zero w)
  | succ fuel ih =>
    intro w hw hwc
    have hwlt : w < c.length := (mem_cone.mp hwc).1
    cases hg : c.getD w (.cst false) with
    | cst b =>
      exfalso
      have hslots := (floor_census f c hcomp hlen).2.2 w hwc
        (by rintro ⟨i', hi'⟩; rw [hg] at hi'; simp at hi')
      rw [hg] at hslots
      simp [inSlots] at hslots
    | un op j =>
      exfalso
      have hslots := (floor_census f c hcomp hlen).2.2 w hwc
        (by rintro ⟨i', hi'⟩; rw [hg] at hi'; simp at hi')
      rw [hg] at hslots
      simp [inSlots] at hslots
    | var i =>
      rw [extractT_var hg]
      refine ⟨trivial, ?_, ?_⟩
      · intro x
        rw [wire_eq c x hwlt, hg]
        rfl
      · intro i' hi'
        have hii : i' = i := Finset.mem_singleton.mp hi'
        subst hii
        exact ⟨w, Reach.refl w, hg⟩
    | bin op j k =>
      have hjm : j ∈ gateReads (c.getD w (.cst false)) := by
        rw [hg]
        exact Finset.mem_insert_self j {k}
      have hkm : k ∈ gateReads (c.getD w (.cst false)) := by
        rw [hg]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self k)
      obtain ⟨hjw, hjc, -⟩ := hedge w hwc j hjm
      obtain ⟨hkw, hkc, -⟩ := hedge w hwc k hkm
      have hjk : j ≠ k := by
        intro he
        rw [he] at hg
        exact hnoself w hwc op k hg
      rw [extractT_bin hg]
      obtain ⟨hROj, hevj, hlvj⟩ := ih j (by omega) hjc
      obtain ⟨hROk, hevk, hlvk⟩ := ih k (by omega) hkc
      refine ⟨⟨?_, hROj, hROk⟩, ?_, ?_⟩
      · -- sibling subtrees have disjoint leaf sets
        rw [Finset.disjoint_left]
        intro i hij hik
        obtain ⟨p₁, hrp₁, hgp₁⟩ := hlvj i hij
        obtain ⟨p₂, hrp₂, hgp₂⟩ := hlvk i hik
        have hp₁ic : InCone c p₁ := reach_inCone (mem_cone.mp hjc).2 hrp₁
        have hp₂ic : InCone c p₂ := reach_inCone (mem_cone.mp hkc).2 hrp₂
        have hp₁c : p₁ ∈ cone c :=
          mem_cone.mpr ⟨inCone_lt (by omega) hp₁ic, hp₁ic⟩
        have hp₂c : p₂ ∈ cone c :=
          mem_cone.mpr ⟨inCone_lt (by omega) hp₂ic, hp₂ic⟩
        have hpp : p₁ = p₂ :=
          floor_var_injective f c hcomp hlen hp₁c hp₂c hgp₁ hgp₂
        subst hpp
        exact reach_not_both f c hcomp hlen hwc hjm hjw hkm hkw hjk
          c.length p₁ (by omega) hrp₁ hrp₂
      · -- the tree computes the wire
        intro x
        show op ((extractT c i₀ fuel j).eval x) ((extractT c i₀ fuel k).eval x)
          = wire c x w
        rw [wire_eq c x hwlt, hg]
        show op ((extractT c i₀ fuel j).eval x) ((extractT c i₀ fuel k).eval x)
          = op ((runFrom x [] (c.take w)).getD j false)
            ((runFrom x [] (c.take w)).getD k false)
        rw [wire_prefix c x hjw (le_of_lt hwlt),
          wire_prefix c x hkw (le_of_lt hwlt), hevj x, hevk x]
      · -- leaves come from reachable var positions
        intro i hi
        rcases Finset.mem_union.mp hi with hij | hik
        · obtain ⟨p, hrp, hgp⟩ := hlvj i hij
          exact ⟨p, reach_trans (Reach.step (Reach.refl w) hjm hjw) hrp, hgp⟩
        · obtain ⟨p, hrp, hgp⟩ := hlvk i hik
          exact ⟨p, reach_trans (Reach.step (Reach.refl w) hkm hkw) hrp, hgp⟩

/-! ### The fence is discharged -/

/-- **THE FENCE IS DISCHARGED (proved)**: floor circuits realize read-once trees. -/
theorem floor_realizes_ROT : FloorRealizesROT := by
  intro n f c hcomp hlen
  have hd : 1 ≤ (depSet f).card := by omega
  have hs : 0 < c.length := by omega
  obtain ⟨i₀, -⟩ := Finset.card_pos.mp hd
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  obtain ⟨hro, hev, -⟩ :=
    extractT_spec f c hcomp hlen i₀ c.length (c.length - 1) (by omega) hroot
  refine ⟨extractT c i₀ c.length (c.length - 1), hro, ?_⟩
  funext x
  rw [hev x, ← output_eq_wire]
  exact hcomp x

/-- **The reusable cash-out (proved)**: one unsplittable triple restriction pushes
`cbudget` above the cone floor: `2·deps ≤ cbudget`. -/
theorem cbudget_above_floor_of_unsplittable {n : ℕ} (f : (Fin n → Bool) → Bool)
    (i₁ i₂ i₃ : Fin n) (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    (z : Fin n → Bool)
    (h1 : ¬ Split1 (fun a b c => f
      (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)))
    (h2 : ¬ Split2 (fun a b c => f
      (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)))
    (h3 : ¬ Split3 (fun a b c => f
      (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))) :
    2 * (depSet f).card ≤ cbudget f := by
  rcases Nat.lt_or_ge (cbudget f) (2 * (depSet f).card) with h | h
  · exfalso
    have hcb := cone_bound f
    obtain ⟨c, hcomp, hclen⟩ := Nat.sInf_mem (cbudget_set_nonempty f)
    have hclen' : c.length = cbudget f := hclen
    have hlen : c.length + 1 = 2 * (depSet f).card := by omega
    obtain ⟨t, hro, hev⟩ := floor_realizes_ROT n f c hcomp hlen
    have hsp := rot_split t hro i₁ i₂ i₃ h12 h13 h23 z
    rw [hev] at hsp
    rcases hsp with hs | hs | hs
    · exact h1 hs
    · exact h2 hs
    · exact h3 hs
  · exact h

/-- **THE `6m` DATAPOINT, UNCONDITIONAL (proved)**: one above the floor at every
`m`.  Note `6m < 7m − 1` for `m ≥ 2`: the slack survives composition only as a
global `+1` along this route — `SlackComposes` (`+1` per gadget) remains open. -/
theorem AEm_above_floor (m : ℕ) (hm : 1 ≤ m) : 6 * m ≤ cbudget (AEm m) :=
  AEm_above_floor_of_extraction floor_realizes_ROT m hm

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.floor_realizes_ROT
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_above_floor_of_unsplittable
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.AEm_above_floor
