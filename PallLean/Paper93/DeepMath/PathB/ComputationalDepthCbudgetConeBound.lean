import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATFamilyCircuitFloor

/-!
# The gate-elimination rung: the cone bound `2·deps − 1 ≤ cbudget`

Second rung of the attack on `∀ k, ∃ n, n^k + k < cbudget (SATFamily n)`.  The
dependency floor charged one gate per read coordinate; this file adds the
**combining cost**: the gates that funnel the read coordinates into the single output
wire.  This is the graph-theoretic core of gate elimination, adapted to the `CGate`
model (where input access itself costs a `.var` gate):

* `InCone` — backward reachability from the output wire through in-range wire reads;
* **cone soundness (proved)**: the output is blind to any coordinate with no `.var`
  gate in the cone (`cone_wire_agree`, strong induction on wire index);
* **the parent-edge injection (proved)**: every non-root cone gate is read by some
  cone gate, and a (consumer, source) pair determines its source — so
  `|cone| ≤ 1 + Σ in-slots`, with `.var`/`.cst` contributing `0` slots, `.un` one,
  `.bin` two (`cone_card_le`);
* **the counting assembly (proved)**: `2·|cone var-gates| ≤ |cone| + 1 ≤ size + 1`,
  hence `cone_bound : 2·(depSet f).card ≤ cbudget f + 1`;
* **the improved floor (proved)**: `2m ≤ cbudget (SATFamily (7m+1)) + 1` — the
  slope of the unconditional SAT floor doubles.

## Honest scope

This technique's structural ceiling is `2n − 1` on a length-`n` slice (all
coordinates dependent, one output wire).  Going beyond `2n` requires genuine
restriction-induction gate elimination (Schnorr-style — the next rung); anything
`ω(n)` for general circuits is beyond current mathematics.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CbudgetConeBound

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec

variable {n : ℕ}

/-! ### Wire reads and in-slots -/

/-- The earlier wires a gate reads. -/
def gateReads : CGate n → Finset ℕ
  | .var _ => ∅
  | .cst _ => ∅
  | .un _ j => {j}
  | .bin _ j k => {j, k}

/-- The in-degree budget of a gate. -/
def inSlots : CGate n → ℕ
  | .var _ => 0
  | .cst _ => 0
  | .un _ _ => 1
  | .bin _ _ _ => 2

theorem gateReads_card_le (g : CGate n) : (gateReads g).card ≤ inSlots g := by
  cases g with
  | var i => simp [gateReads, inSlots]
  | cst b => simp [gateReads, inSlots]
  | un op j => simp [gateReads, inSlots]
  | bin op j k =>
    simp only [gateReads, inSlots]
    exact le_trans (Finset.card_insert_le _ _) (by simp)

theorem inSlots_le_two (g : CGate n) : inSlots g ≤ 2 := by
  cases g <;> simp [inSlots]

/-! ### The output cone -/

/-- Backward reachability from the output wire: the root is the last wire; a cone
gate's in-range reads are in the cone. -/
inductive InCone (c : List (CGate n)) : ℕ → Prop
  | root : InCone c (c.length - 1)
  | step {w j : ℕ} : InCone c w → j ∈ gateReads (c.getD w (.cst false)) → j < w → InCone c j

theorem inCone_lt {c : List (CGate n)} (hs : 0 < c.length) :
    ∀ {w}, InCone c w → w < c.length := by
  intro w h
  induction h with
  | root => omega
  | step hw hj hjw ih => omega

/-! ### Wire semantics -/

/-- The value of wire `w`. -/
def wire (c : List (CGate n)) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (runFrom x [] c).getD w false

theorem output_eq_wire (c : List (CGate n)) (x : Fin n → Bool) :
    output c x = wire c x (c.length - 1) := rfl

theorem runFrom_length (x : Fin n → Bool) :
    ∀ (gs : List (CGate n)) (vals : List Bool),
      (runFrom x vals gs).length = vals.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro vals; simp [runFrom]
  | cons g gs ih =>
    intro vals
    show (runFrom x (vals ++ [evalGate x vals g]) gs).length = _
    rw [ih, List.length_append]
    simp
    omega

theorem runFrom_eq_append (x : Fin n → Bool) :
    ∀ (gs : List (CGate n)) (vals : List Bool), ∃ w', runFrom x vals gs = vals ++ w' := by
  intro gs
  induction gs with
  | nil => intro vals; exact ⟨[], (List.append_nil vals).symm⟩
  | cons g gs ih =>
    intro vals
    obtain ⟨w', hw'⟩ := ih (vals ++ [evalGate x vals g])
    refine ⟨[evalGate x vals g] ++ w', ?_⟩
    show runFrom x (vals ++ [evalGate x vals g]) gs = _
    rw [hw', List.append_assoc]

/-- The wire recurrence: wire `w` is its gate evaluated against the first `w` wires. -/
theorem wire_eq (c : List (CGate n)) (x : Fin n → Bool) {w : ℕ} (hw : w < c.length) :
    wire c x w = evalGate x (runFrom x [] (c.take w)) (c.getD w (.cst false)) := by
  have hsplit : c = c.take w ++ c.getD w (.cst false) :: c.drop (w + 1) := by
    conv_lhs => rw [← List.take_append_drop w c]
    rw [List.drop_eq_getElem_cons hw, List.getD_eq_getElem c (CGate.cst false) hw]
  have hlenV : (runFrom x [] (c.take w)).length = w := by
    rw [runFrom_length, List.length_take]
    simp
    omega
  show (runFrom x [] c).getD w false = _
  conv_lhs => rw [hsplit]
  rw [runFrom_append]
  set V := runFrom x [] (c.take w) with hV
  obtain ⟨rest, hrest⟩ :=
    runFrom_eq_append x (c.drop (w + 1)) (V ++ [evalGate x V (c.getD w (.cst false))])
  show (runFrom x (V ++ [evalGate x V (c.getD w (.cst false))]) (c.drop (w + 1))).getD w false
    = evalGate x V (c.getD w (.cst false))
  rw [hrest, List.append_assoc,
    List.getD_append_right V _ false w (by omega),
    show w - V.length = 0 from by omega]
  rfl

/-- Wires below `w` are already fixed by the length-`w` prefix. -/
theorem wire_prefix (c : List (CGate n)) (x : Fin n → Bool) {j w : ℕ} (hj : j < w)
    (hw : w ≤ c.length) : (runFrom x [] (c.take w)).getD j false = wire c x j := by
  have hlenV : (runFrom x [] (c.take w)).length = w := by
    rw [runFrom_length, List.length_take]
    simp
    omega
  obtain ⟨rest, hrest⟩ := runFrom_eq_append x (c.drop w) (runFrom x [] (c.take w))
  show _ = (runFrom x [] c).getD j false
  conv_rhs => rw [← List.take_append_drop w c]
  rw [runFrom_append, hrest, List.getD_append _ _ false j (by omega)]

/-! ### Cone soundness: no cone `.var i` gate ⟹ blind to `i` -/

theorem cone_wire_agree (c : List (CGate n)) (i : Fin n) (x : Fin n → Bool) (b : Bool)
    (hs : 0 < c.length)
    (hnv : ∀ w, InCone c w → c.getD w (.cst false) ≠ CGate.var i) :
    ∀ w, InCone c w → wire c (Function.update x i b) w = wire c x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    have hwlt := inCone_lt hs hw
    have hread : ∀ j ∈ gateReads (c.getD w (.cst false)),
        (runFrom (Function.update x i b) [] (c.take w)).getD j false
          = (runFrom x [] (c.take w)).getD j false := by
      intro j hj
      by_cases hjw : j < w
      · rw [wire_prefix c _ hjw (le_of_lt hwlt), wire_prefix c x hjw (le_of_lt hwlt)]
        exact ih j hjw (InCone.step hw hj hjw)
      · rw [List.getD_eq_default _ _ (by
            rw [runFrom_length, List.length_take]; simp; omega),
          List.getD_eq_default _ _ (by
            rw [runFrom_length, List.length_take]; simp; omega)]
    rw [wire_eq c _ hwlt, wire_eq c x hwlt]
    cases hg : c.getD w (.cst false) with
    | var i' =>
      simp only [evalGate]
      have hne : i' ≠ i := fun he => hnv w hw (by rw [hg, he])
      exact Function.update_of_ne hne b x
    | cst b' => rfl
    | un op j =>
      simp only [evalGate]
      rw [hread j (by rw [hg]; simp [gateReads])]
    | bin op j k =>
      simp only [evalGate]
      rw [hread j (by rw [hg]; simp [gateReads]),
        hread k (by rw [hg]; simp [gateReads])]

/-! ### The cone as a `Finset`, and the parent-edge injection -/

open Classical in
/-- The cone as a finite set of wire indices. -/
noncomputable def cone (c : List (CGate n)) : Finset ℕ :=
  (Finset.range c.length).filter (InCone c)

theorem mem_cone {c : List (CGate n)} {w : ℕ} :
    w ∈ cone c ↔ w < c.length ∧ InCone c w := by
  simp [cone]

open Classical in
/-- The `.var` gates of the cone. -/
noncomputable def coneVars (c : List (CGate n)) : Finset ℕ :=
  (cone c).filter (fun w => ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')

/-- **The parent-edge injection**: every non-root cone gate is read by a cone gate,
and (consumer, source) determines the source, so `|cone| ≤ 1 + Σ in-slots`. -/
theorem cone_card_le (c : List (CGate n)) (hs : 0 < c.length) :
    (cone c).card ≤ 1 + ∑ w ∈ cone c, inSlots (c.getD w (.cst false)) := by
  classical
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  have hex : ∀ x ∈ (cone c).erase (c.length - 1),
      ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w := by
    intro x hx
    obtain ⟨hxne, hxc⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxlt, hxcone⟩ := mem_cone.mp hxc
    cases hxcone with
    | root => exact absurd rfl hxne
    | step hw hj hjw => exact ⟨_, hw, hj, hjw⟩
  have hcard : ((cone c).erase (c.length - 1)).card
      ≤ ((cone c).biUnion
          (fun w => (gateReads (c.getD w (.cst false))).image (fun j => (w, j)))).card := by
    apply Finset.card_le_card_of_injOn
      (fun x => (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0, x))
    · intro x hx
      rw [Finset.mem_coe] at hx
      obtain ⟨w, hw⟩ := hex x hx
      show (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0, x) ∈ _
      rw [dif_pos ⟨w, hw⟩, Finset.mem_coe, Finset.mem_biUnion]
      have hspec := Classical.choose_spec
        (⟨w, hw⟩ : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w)
      exact ⟨_, mem_cone.mpr ⟨inCone_lt hs hspec.1, hspec.1⟩,
        Finset.mem_image.mpr ⟨x, hspec.2.1, rfl⟩⟩
    · intro a _ b _ hab
      exact congrArg Prod.snd hab
  have hEcard : ((cone c).biUnion
      (fun w => (gateReads (c.getD w (.cst false))).image (fun j => (w, j)))).card
      ≤ ∑ w ∈ cone c, inSlots (c.getD w (.cst false)) := by
    refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum ?_)
    intro w _
    exact le_trans Finset.card_image_le (gateReads_card_le _)
  have := Finset.card_erase_add_one hroot
  omega

/-! ### Variable coverage: every dependence is a cone `.var` gate -/

theorem depSet_card_le_coneVars (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hs : 0 < c.length) :
    (depSet f).card ≤ (coneVars c).card := by
  classical
  have hex : ∀ i ∈ depSet f, ∃ w, w ∈ cone c ∧ c.getD w (.cst false) = CGate.var i := by
    intro i hi
    obtain ⟨x, b, hxb⟩ := mem_depSet.mp hi
    by_contra hno
    push_neg at hno
    have hnv : ∀ w, InCone c w → c.getD w (.cst false) ≠ CGate.var i := fun w hw he =>
      hno w (mem_cone.mpr ⟨inCone_lt hs hw, hw⟩) he
    refine hxb ?_
    rw [← hcomp (Function.update x i b), ← hcomp x, output_eq_wire, output_eq_wire]
    exact cone_wire_agree c i x b hs hnv _ InCone.root
  apply Finset.card_le_card_of_injOn
    (fun i => if h : ∃ w, w ∈ cone c ∧ c.getD w (.cst false) = CGate.var i
      then Classical.choose h else 0)
  · intro i hi
    rw [Finset.mem_coe] at hi
    obtain ⟨w, hw⟩ := hex i hi
    show (if h : ∃ w, w ∈ cone c ∧ c.getD w (.cst false) = CGate.var i
      then Classical.choose h else 0) ∈ _
    rw [dif_pos ⟨w, hw⟩, Finset.mem_coe]
    have hspec := Classical.choose_spec
      (⟨w, hw⟩ : ∃ w, w ∈ cone c ∧ c.getD w (.cst false) = CGate.var i)
    rw [coneVars, Finset.mem_filter]
    exact ⟨hspec.1, ⟨i, hspec.2⟩⟩
  · intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    obtain ⟨wa, hwa⟩ := hex a ha
    obtain ⟨wb, hwb⟩ := hex b hb
    have hab' : (if h : ∃ w, w ∈ cone c ∧ c.getD w (.cst false) = CGate.var a
        then Classical.choose h else 0)
      = (if h : ∃ w, w ∈ cone c ∧ c.getD w (.cst false) = CGate.var b
        then Classical.choose h else 0) := hab
    rw [dif_pos ⟨wa, hwa⟩, dif_pos ⟨wb, hwb⟩] at hab'
    have hsa := Classical.choose_spec
      (⟨wa, hwa⟩ : ∃ w, w ∈ cone c ∧ c.getD w (.cst false) = CGate.var a)
    have hsb := Classical.choose_spec
      (⟨wb, hwb⟩ : ∃ w, w ∈ cone c ∧ c.getD w (.cst false) = CGate.var b)
    have hv : CGate.var (n := n) a = CGate.var b := by
      rw [← hsa.2, hab', hsb.2]
    exact CGate.var.inj hv

/-! ### The counting assembly -/

theorem cone_counting (c : List (CGate n)) (hs : 0 < c.length) :
    2 * (coneVars c).card ≤ c.length + 1 := by
  classical
  have hA := cone_card_le c hs
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
    obtain ⟨_, i', hi'⟩ := hw
    rw [hi']
    rfl
  have hrest : ∑ w ∈ (cone c).filter
      (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
      inSlots (c.getD w (.cst false))
      ≤ 2 * ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ 2 (fun w _ => inSlots_le_two _)) ?_
    rw [smul_eq_mul]
    omega
  have hpart : (coneVars c).card
      + ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card
      = (cone c).card := by
    rw [coneVars]
    exact Finset.card_filter_add_card_filter_not (s := cone c)
      (p := fun w => ∃ i' : Fin n, c.getD w (CGate.cst false) = CGate.var i')
  have hcone_le : (cone c).card ≤ c.length :=
    le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range _))
  omega

/-! ### THE CONE BOUND -/

/-- **The gate-elimination cone bound (proved).**  Every circuit pays one gate per
dependent coordinate *and* one combining gate per coordinate beyond the first:
`2·deps − 1 ≤ cbudget`. -/
theorem cone_bound (f : (Fin n → Bool) → Bool) :
    2 * (depSet f).card ≤ cbudget f + 1 := by
  rcases Nat.eq_zero_or_pos (depSet f).card with hd | hd
  · omega
  · have hne : {s | ∃ c : List (CGate n), computes c f ∧ c.length = s}.Nonempty := by
      refine ⟨(compile 0 (dnfFor f)).length, compile 0 (dnfFor f), ?_, rfl⟩
      have h := compile_computes (dnfFor f)
      rwa [show (fun x => eval (dnfFor f) x) = f from funext fun x =>
        congrFun (eval_dnfFor f) x] at h
    obtain ⟨c, hcomp, hclen⟩ := Nat.sInf_mem hne
    have hs : 0 < c.length := by
      rcases Nat.eq_zero_or_pos c.length with h0 | h0
      · exfalso
        have hc : c = [] := by
          cases c with
          | nil => rfl
          | cons g gs => simp at h0
        have hconst : ∀ x, f x = false := by
          intro x
          rw [← hcomp x, hc]
          rfl
        have hd0 : (depSet f).card = 0 := by
          rw [Finset.card_eq_zero]
          rw [Finset.eq_empty_iff_forall_notMem]
          intro i hi
          obtain ⟨x, b, hxb⟩ := mem_depSet.mp hi
          exact hxb (by rw [hconst, hconst])
        omega
      · exact h0
    calc 2 * (depSet f).card ≤ 2 * (coneVars c).card := by
          have := depSet_card_le_coneVars f c hcomp hs
          omega
      _ ≤ c.length + 1 := cone_counting c hs
      _ = cbudget f + 1 := by rw [hclen]; rfl

/-! ### The improved SAT floor: the slope doubles -/

/-- **The gate-elimination rung on the exact target**: `2m ≤ cbudget (SATFamily (7m+1)) + 1`. -/
theorem cbudget_SATFamily_ge_two (m : ℕ) (hm : 2 ≤ m) :
    2 * m ≤ cbudget (SATFamily (7 * m + 1)) + 1 := by
  have h1 := depSet_card_ge m hm
  have h2 := cone_bound (SATFamily (encodeFormula' (phiSat m)).length)
  rw [← encode_phiSat_length m]
  omega

/-- Subtraction form: `2m − 1 ≤ cbudget (SATFamily (7m+1))`. -/
theorem cbudget_SATFamily_ge_two' (m : ℕ) (hm : 2 ≤ m) :
    2 * m - 1 ≤ cbudget (SATFamily (7 * m + 1)) := by
  have := cbudget_SATFamily_ge_two m hm
  omega

end PallLean.Paper93.DeepMath.PathB.CbudgetConeBound

#print axioms PallLean.Paper93.DeepMath.PathB.CbudgetConeBound.cone_bound
#print axioms PallLean.Paper93.DeepMath.PathB.CbudgetConeBound.cbudget_SATFamily_ge_two
#print axioms PallLean.Paper93.DeepMath.PathB.CbudgetConeBound.cbudget_SATFamily_ge_two'
