import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATSpareStructure
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPrefixTransfer

/-!
# The cut lemma at the single reconvergence wire, and the three collision shapes

Brick 3a of the `+2` campaign: the structural foundation of the collision
analysis.  With exactly one reconvergence wire `u` (brick 2), the circuit above
`u` sees the below-`u` region only through `u`'s single bit:

* **`slotCnt_pos_of_mem` / `two_readers_mem_reconv` (proved)** — two distinct
  cone readers of a wire put it in `reconvR`;
* **`read_structure` (proved)** — a cone wire NOT below `u` reads only `u` itself
  or other not-below wires (a below-`u` read would force a second reconvergence);
* **`cut_agree` (proved)** — THE CUT LEMMA: two inputs with equal `u`-value that
  agree at every coordinate owning a not-below var gate produce equal values on
  every not-below wire — in particular at the root;
* **`wire_u_indep` (proved)** — dually, coordinates with no below-`u` gate cannot
  affect `u`'s value;
* **`b1_shape` / `b2_kill_free1/2/3` / `b3_kill` (proved, `decide`)** — the three
  pure-Boolean collision shapes: a triple fully through one bit forces the bit to
  BE `±AllEqual₃`; two-through-one-free is outright impossible (three distinct
  Boolean values demanded of one bit); and one-through from EACH gadget is killed
  by the polarity-flip pins (`a∧d` and `¬a∧d` cannot share a mediator);
* **`allEq3_slot*` (proved)** — the slot-evaluation facts feeding the assemblies.

Brick 3b (next) instantiates these on the two-gadget codec word and assembles
`cbudget (SATFamily N) ≥ 2·deps + 1`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-! ### Two readers force a reconvergence -/

theorem slotCnt_pos_of_mem {n : ℕ} {g : CGate n} {j : ℕ} (h : j ∈ gateReads g) :
    1 ≤ slotCnt g j := by
  cases g with
  | var i => exact absurd h (Finset.notMem_empty j)
  | cst b => exact absurd h (Finset.notMem_empty j)
  | un op j' =>
    have hj : j = j' := Finset.mem_singleton.mp h
    show 1 ≤ if j' = j then 1 else 0
    rw [if_pos hj.symm]
  | bin op j' k' =>
    show 1 ≤ (if j' = j then 1 else 0) + (if k' = j then 1 else 0)
    rcases Finset.mem_insert.mp h with hj | hj
    · rw [if_pos hj.symm]; omega
    · rw [if_pos (Finset.mem_singleton.mp hj).symm]; omega

/-- **Two distinct cone readers put a non-root wire in `reconvR` (proved)**. -/
theorem two_readers_mem_reconv {n : ℕ} (c : List (CGate n)) {w p j : ℕ}
    (hw : w ∈ cone c) (hp : p ∈ cone c) (hwp : w ≠ p)
    (hjw : j ∈ gateReads (c.getD w (.cst false)))
    (hjp : j ∈ gateReads (c.getD p (.cst false)))
    (hjc : j ∈ cone c) (hjroot : j ≠ c.length - 1) :
    j ∈ reconvR c := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hjroot, hjc⟩, ?_⟩
  have hsub : ({w, p} : Finset ℕ) ⊆ cone c := by
    intro q hq
    rcases Finset.mem_insert.mp hq with h | h
    · rw [h]; exact hw
    · rw [Finset.mem_singleton.mp h]; exact hp
  calc (2 : ℕ) = 1 + 1 := rfl
    _ ≤ slotCnt (c.getD w (.cst false)) j + slotCnt (c.getD p (.cst false)) j :=
        Nat.add_le_add (slotCnt_pos_of_mem hjw) (slotCnt_pos_of_mem hjp)
    _ = ∑ q ∈ ({w, p} : Finset ℕ), slotCnt (c.getD q (.cst false)) j :=
        (Finset.sum_pair (f := fun q => slotCnt (c.getD q (.cst false)) j) hwp).symm
    _ ≤ ∑ q ∈ cone c, slotCnt (c.getD q (.cst false)) j :=
        Finset.sum_le_sum_of_subset hsub
    _ = slotReads c j := rfl

/-! ### The read structure away from the reconvergence -/

/-- **The read structure (proved)**: with `reconvR c = {u}`, a cone wire not below
`u` reads only `u` itself or other not-below wires. -/
theorem read_structure {n : ℕ} (c : List (CGate n)) (u : ℕ) (hs : 0 < c.length)
    (hR : reconvR c = {u}) (hu_cone : InCone c u)
    {w j : ℕ} (hw : w ∈ cone c) (hnb : ¬ Reach c u w)
    (hj : j ∈ gateReads (c.getD w (.cst false))) (hjw : j < w) :
    j = u ∨ ¬ Reach c u j := by
  by_cases hju : j = u
  · exact Or.inl hju
  refine Or.inr (fun hreach => ?_)
  obtain ⟨p, hp, hjp, hjlt⟩ :
      ∃ p, Reach c u p ∧ j ∈ gateReads (c.getD p (.cst false)) ∧ j < p := by
    cases hreach with
    | refl => exact absurd rfl hju
    | step hp hq hlt => exact ⟨_, hp, hq, hlt⟩
  by_cases hpw : p = w
  · rw [hpw] at hp
    exact hnb hp
  · have hpic : InCone c p := reach_inCone hu_cone hp
    have hpc : p ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hpic, hpic⟩
    have hwlt : w < c.length := (mem_cone.mp hw).1
    have hjc : j ∈ cone c :=
      mem_cone.mpr ⟨by omega, InCone.step (mem_cone.mp hw).2 hj hjw⟩
    have hjroot : j ≠ c.length - 1 := by omega
    have hmem := two_readers_mem_reconv c hw hpc (fun he => hpw he.symm)
      hj hjp hjc hjroot
    rw [hR] at hmem
    exact hju (Finset.mem_singleton.mp hmem)

/-! ### THE CUT LEMMA -/

/-- **The cut lemma (proved)**: two inputs with equal `u`-value, agreeing at every
coordinate that owns a not-below var gate, give equal values on every not-below
cone wire. -/
theorem cut_agree {n : ℕ} (c : List (CGate n)) (u : ℕ) (hs : 0 < c.length)
    (hR : reconvR c = {u}) (hu_cone : InCone c u)
    (x x' : Fin n → Bool) (hu : wire c x u = wire c x' u)
    (hagree : ∀ i : Fin n,
      (∃ q, q ∈ cone c ∧ c.getD q (.cst false) = CGate.var i ∧ ¬ Reach c u q) →
      x i = x' i) :
    ∀ w, w ∈ cone c → ¬ Reach c u w → wire c x w = wire c x' w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwc hnb
    have hwlt : w < c.length := (mem_cone.mp hwc).1
    rw [wire_eq c x hwlt, wire_eq c x' hwlt]
    have hread : ∀ m : ℕ, m ∈ gateReads (c.getD w (.cst false)) → m < w →
        wire c x m = wire c x' m := by
      intro m hmr hmw
      have hmc : m ∈ cone c :=
        mem_cone.mpr ⟨by omega, InCone.step (mem_cone.mp hwc).2 hmr hmw⟩
      rcases read_structure c u hs hR hu_cone hwc hnb hmr hmw with hmu | hnbm
      · rw [hmu]; exact hu
      · exact ih m hmw hmc hnbm
    have hgetD : ∀ m : ℕ, m ∈ gateReads (c.getD w (.cst false)) →
        (runFrom x [] (c.take w)).getD m false
          = (runFrom x' [] (c.take w)).getD m false := by
      intro m hmr
      by_cases hmw : m < w
      · rw [wire_prefix c x hmw (le_of_lt hwlt), wire_prefix c x' hmw (le_of_lt hwlt)]
        exact hread m hmr hmw
      · have hlen : (runFrom x [] (c.take w)).length = w := by
          rw [runFrom_length, List.length_take]
          simp
          omega
        have hlen' : (runFrom x' [] (c.take w)).length = w := by
          rw [runFrom_length, List.length_take]
          simp
          omega
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    cases hg : c.getD w (.cst false) with
    | var i =>
      show x i = x' i
      exact hagree i ⟨w, hwc, hg, hnb⟩
    | cst b => rfl
    | un op j =>
      show op ((runFrom x [] (c.take w)).getD j false)
        = op ((runFrom x' [] (c.take w)).getD j false)
      rw [hgetD j (by rw [hg]; exact Finset.mem_singleton_self j)]
    | bin op j k =>
      show op ((runFrom x [] (c.take w)).getD j false)
          ((runFrom x [] (c.take w)).getD k false)
        = op ((runFrom x' [] (c.take w)).getD j false)
          ((runFrom x' [] (c.take w)).getD k false)
      rw [hgetD j (by rw [hg]; exact Finset.mem_insert_self j {k}),
        hgetD k (by rw [hg]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self k))]

/-! ### Not-below coordinates cannot move the mediator -/

/-- **The mediator ignores not-below coordinates (proved)**: a coordinate with no
below-`u` var gate in the cone cannot affect `u`'s value. -/
theorem wire_u_indep {n : ℕ} (c : List (CGate n)) (u : ℕ) (hs : 0 < c.length)
    (hu_lt : u < c.length) (hu_cone : InCone c u)
    (x : Fin n → Bool) (i : Fin n) (b : Bool)
    (hno : ∀ q, q ∈ cone c → c.getD q (.cst false) = CGate.var i → ¬ Reach c u q) :
    wire c (Function.update x i b) u = wire c x u := by
  have hpre : ∀ y : Fin n → Bool, wire c y u = wire (c.take (u + 1)) y u := by
    intro y
    exact (wire_prefix c y (show u < u + 1 by omega)
      (show u + 1 ≤ c.length by omega)).symm
  rw [hpre, hpre]
  have hlen' : (c.take (u + 1)).length = u + 1 := by
    rw [List.length_take]
    omega
  have hs' : 0 < (c.take (u + 1)).length := by omega
  have hnv : ∀ q, InCone (c.take (u + 1)) q →
      (c.take (u + 1)).getD q (.cst false) ≠ CGate.var i := by
    intro q hq he
    have hqlt : q < (c.take (u + 1)).length := inCone_lt hs' hq
    have hru : Reach (c.take (u + 1)) u q := by
      have hr := inCone_reach_root hq
      rw [show (c.take (u + 1)).length - 1 = u from by omega] at hr
      exact hr
    have hrc : Reach c u q := reach_of_take c hu_lt (le_refl u) hru
    have hqic : InCone c q := reach_inCone hu_cone hrc
    have hqc : q ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hqic, hqic⟩
    rw [getD_take_eq_g (show q < u + 1 from by omega)] at he
    exact hno q hqc he hrc
  have hui : InCone (c.take (u + 1)) u := by
    have hroot : InCone (c.take (u + 1)) ((c.take (u + 1)).length - 1) := InCone.root
    rw [show (c.take (u + 1)).length - 1 = u from by omega] at hroot
    exact hroot
  exact cone_wire_agree (c.take (u + 1)) i x b hs' hnv u hui

/-! ### The three pure-Boolean collision shapes -/

set_option maxRecDepth 8000

/-- **B1 shape (proved)**: a mediator refining `AllEqual₃` on a full triple IS
`±AllEqual₃`. -/
theorem b1_shape : ∀ μ : Bool → Bool → Bool → Bool,
    (∀ p q r p' q' r', μ p q r = μ p' q' r' → allEq3 p q r = allEq3 p' q' r') →
    (∀ p q r, μ p q r = allEq3 p q r) ∨ (∀ p q r, μ p q r = !(allEq3 p q r)) := by
  decide

/-- **B2 kill, free slot 1 (proved)**: slots 2,3 through one bit, slot 1 free —
impossible (three distinct Boolean values demanded of the bit). -/
theorem b2_kill_free1 : ∀ μ : Bool → Bool → Bool → Bool,
    (∀ p q r q' r', μ p q r = μ p q' r' → allEq3 p q r = allEq3 p q' r') →
    (∀ p p' q r, μ p q r = μ p' q r) → False := by
  decide

/-- **B2 kill, free slot 2 (proved)**. -/
theorem b2_kill_free2 : ∀ μ : Bool → Bool → Bool → Bool,
    (∀ p q r p' r', μ p q r = μ p' q r' → allEq3 p q r = allEq3 p' q r') →
    (∀ p q q' r, μ p q r = μ p q' r) → False := by
  decide

/-- **B2 kill, free slot 3 (proved)**. -/
theorem b2_kill_free3 : ∀ μ : Bool → Bool → Bool → Bool,
    (∀ p q r p' q', μ p q r = μ p' q' r → allEq3 p q r = allEq3 p' q' r) →
    (∀ p q r r', μ p q r = μ p q r') → False := by
  decide

/-- **B3 kill (proved)**: one bit cannot mediate both `a ∧ d` and `¬a ∧ d` — the
polarity-flip pins demand three distinct Boolean values. -/
theorem b3_kill : ∀ μ : Bool → Bool → Bool,
    (∀ a d a' d', μ a d = μ a' d' → (a && d) = (a' && d')) →
    (∀ a d a' d', μ a d = μ a' d' → ((!a) && d) = ((!a') && d')) → False := by
  decide

/-! ### Slot-evaluation facts -/

theorem allEq3_slot1_T (a : Bool) : allEq3 a true true = a := by cases a <;> rfl
theorem allEq3_slot2_T (a : Bool) : allEq3 true a true = a := by cases a <;> rfl
theorem allEq3_slot3_T (a : Bool) : allEq3 true true a = a := by cases a <;> rfl
theorem allEq3_slot1_F (a : Bool) : allEq3 a false false = !a := by cases a <;> rfl
theorem allEq3_slot2_F (a : Bool) : allEq3 false a false = !a := by cases a <;> rfl
theorem allEq3_slot3_F (a : Bool) : allEq3 false false a = !a := by cases a <;> rfl

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.two_readers_mem_reconv
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.read_structure
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cut_agree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.wire_u_indep
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.b1_shape
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.b3_kill
