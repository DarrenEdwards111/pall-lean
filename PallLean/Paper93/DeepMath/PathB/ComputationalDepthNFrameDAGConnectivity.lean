import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDAGNoDeadBits

/-!
# N-Frame: the connectivity bound — internal gates must merge the inputs, and the `≈ 2N` circuit bound

The first second-order DAG bound: past counting the forced `var` gates, the circuit must *combine* them.  The
output's dependency cone is a rooted sub-DAG; with fan-in two, a cone containing `K` variable gates must contain
at least `K − 1` binary gates — sharing does not help, because the count charges the cone's *edges* against its
*nodes*, not any tree unfolding.

  `coneOf` / `cone_child` / `cone_parent` — the dependency cone of a wire: the reflexive-transitive closure of
        in-range references, with its two structural facts (children stay in the cone; every cone member other
        than the root is somebody's child).
  `cone_val_agree` — **PROVED, the semantic content**: the cone determines the output — two inputs agreeing on
        every variable read *inside the cone* produce the same output.  Hence every essential variable owns a
        `var` gate in the cone, not merely in the circuit.
  `cbudget_connectivity` — **PROVED, the general bound**: `K` essential variables force
        `2·K − 1 ≤ cbudget f`: `K` variable gates in the cone, and — by the rooted-DAG count
        `|cone| ≤ 1 + #un + 2·#bin` — at least `K − 1` binary gates on top of them.
  `sat3_cbudget_connectivity` — **PROVED, the record**:

        `2·m·D − 1 = 6·m·v + 6·m − 1 ≤ cbudget (sat3Family N)`,   i.e.   `≈ 2N`

        (`sat3_cbudget_near_2N`: `2·N ≤ cbudget + 2·D`) — doubling the no-dead-bits record: SAT needs a full
        layer of merging gates on top of its full layer of input gates.

## Honest scope

This is the classical `2n − O(1)` connectivity floor, formalized sharing-aware on the straight-line model: the
count is over the DAG's positions, so reuse is fully accounted.  It is the *last* bound obtainable without
analyzing what the gates compute — beyond it live Schnorr/Stockmeyer-style multi-kill case analyses
(`2.5n`, `3n − o(n)`, the field's frontier) and the open fan-out/cone-reuse accounting.  The mountain —
`sat3Target`, super-polynomial `cbudget` — is not touched by linear bounds and is not claimed.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Gate anatomy -/

def isVarGate {n : ℕ} : CGate n → Bool
  | .var _ => true
  | _ => false

def isUnGate {n : ℕ} : CGate n → Bool
  | .un _ _ => true
  | _ => false

def isBinGate {n : ℕ} : CGate n → Bool
  | .bin _ _ _ => true
  | _ => false

/-- The in-range references of the gate at position `p`. -/
def childrenOf {n : ℕ} (c : List (CGate n)) (p : ℕ) : Finset ℕ :=
  match c.getD p (CGate.cst false) with
  | .var _ => ∅
  | .cst _ => ∅
  | .un _ j => if j < p then {j} else ∅
  | .bin _ j k => (if j < p then {j} else ∅) ∪ (if k < p then {k} else ∅)

theorem childrenOf_eq_var {n : ℕ} (c : List (CGate n)) (p : ℕ) (i : Fin n)
    (h : c.getD p (CGate.cst false) = CGate.var i) : childrenOf c p = ∅ := by
  unfold childrenOf
  rw [h]

theorem childrenOf_eq_cst {n : ℕ} (c : List (CGate n)) (p : ℕ) (b : Bool)
    (h : c.getD p (CGate.cst false) = CGate.cst b) : childrenOf c p = ∅ := by
  unfold childrenOf
  rw [h]

theorem childrenOf_eq_un {n : ℕ} (c : List (CGate n)) (p : ℕ) (op : Bool → Bool) (j : ℕ)
    (h : c.getD p (CGate.cst false) = CGate.un op j) :
    childrenOf c p = if j < p then {j} else ∅ := by
  unfold childrenOf
  rw [h]

theorem childrenOf_eq_bin {n : ℕ} (c : List (CGate n)) (p : ℕ)
    (op : Bool → Bool → Bool) (j k : ℕ)
    (h : c.getD p (CGate.cst false) = CGate.bin op j k) :
    childrenOf c p = (if j < p then {j} else ∅) ∪ (if k < p then {k} else ∅) := by
  unfold childrenOf
  rw [h]

/-- The fan-in weight of the gate at position `p`. -/
def gateWeight {n : ℕ} (c : List (CGate n)) (p : ℕ) : ℕ :=
  match c.getD p (CGate.cst false) with
  | .var _ => 0
  | .cst _ => 0
  | .un _ _ => 1
  | .bin _ _ _ => 2

theorem childrenOf_card_le {n : ℕ} (c : List (CGate n)) (p : ℕ) :
    (childrenOf c p).card ≤ gateWeight c p := by
  unfold childrenOf gateWeight
  cases c.getD p (CGate.cst false) with
  | var i =>
    show (∅ : Finset ℕ).card ≤ 0
    simp
  | cst b =>
    show (∅ : Finset ℕ).card ≤ 0
    simp
  | un op j =>
    show (if j < p then ({j} : Finset ℕ) else ∅).card ≤ 1
    split <;> simp
  | bin op j k =>
    show ((if j < p then ({j} : Finset ℕ) else ∅) ∪ (if k < p then ({k} : Finset ℕ) else ∅)).card ≤ 2
    apply le_trans (Finset.card_union_le _ _)
    have h1 : (if j < p then ({j} : Finset ℕ) else ∅).card ≤ 1 := by split <;> simp
    have h2 : (if k < p then ({k} : Finset ℕ) else ∅).card ≤ 1 := by split <;> simp
    omega

/-! ### The dependency cone -/

/-- The dependency cone of wire `q`: `q` together with everything transitively referenced below it. -/
def coneOf {n : ℕ} (c : List (CGate n)) (q : ℕ) : Finset ℕ :=
  insert q
    (match c.getD q (CGate.cst false) with
     | .var _ => ∅
     | .cst _ => ∅
     | .un _ j => if _h : j < q then coneOf c j else ∅
     | .bin _ j k =>
         (if _h : j < q then coneOf c j else ∅) ∪ (if _h : k < q then coneOf c k else ∅))
termination_by q
decreasing_by
  · assumption
  · assumption
  · assumption

theorem coneOf_eq_var {n : ℕ} (c : List (CGate n)) (q : ℕ) (i : Fin n)
    (h : c.getD q (CGate.cst false) = CGate.var i) :
    coneOf c q = insert q (∅ : Finset ℕ) := by
  unfold coneOf
  rw [h]

theorem coneOf_eq_cst {n : ℕ} (c : List (CGate n)) (q : ℕ) (b : Bool)
    (h : c.getD q (CGate.cst false) = CGate.cst b) :
    coneOf c q = insert q (∅ : Finset ℕ) := by
  unfold coneOf
  rw [h]

theorem coneOf_eq_un {n : ℕ} (c : List (CGate n)) (q : ℕ) (op : Bool → Bool) (j : ℕ)
    (h : c.getD q (CGate.cst false) = CGate.un op j) :
    coneOf c q = insert q (if _h : j < q then coneOf c j else ∅) := by
  conv_lhs => unfold coneOf
  rw [h]

theorem coneOf_eq_bin {n : ℕ} (c : List (CGate n)) (q : ℕ) (op : Bool → Bool → Bool)
    (j k : ℕ) (h : c.getD q (CGate.cst false) = CGate.bin op j k) :
    coneOf c q = insert q
      ((if _h : j < q then coneOf c j else ∅) ∪ (if _h : k < q then coneOf c k else ∅)) := by
  conv_lhs => unfold coneOf
  rw [h]

theorem cone_self {n : ℕ} (c : List (CGate n)) (q : ℕ) : q ∈ coneOf c q := by
  cases hg : c.getD q (CGate.cst false) with
  | var i => rw [coneOf_eq_var c q i hg]; exact Finset.mem_insert_self q _
  | cst b => rw [coneOf_eq_cst c q b hg]; exact Finset.mem_insert_self q _
  | un op j => rw [coneOf_eq_un c q op j hg]; exact Finset.mem_insert_self q _
  | bin op j k => rw [coneOf_eq_bin c q op j k hg]; exact Finset.mem_insert_self q _

theorem cone_le {n : ℕ} (c : List (CGate n)) :
    ∀ q p, p ∈ coneOf c q → p ≤ q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro p hp
    cases hg : c.getD q (CGate.cst false) with
    | var i =>
      rw [coneOf_eq_var c q i hg] at hp
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact le_refl p
      · exact absurd hp' (Finset.notMem_empty p)
    | cst b =>
      rw [coneOf_eq_cst c q b hg] at hp
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact le_refl p
      · exact absurd hp' (Finset.notMem_empty p)
    | un op j =>
      rw [coneOf_eq_un c q op j hg] at hp
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact le_refl p
      · by_cases hj : j < q
        · rw [dif_pos hj] at hp'
          exact le_trans (ih j hj p hp') (le_of_lt hj)
        · rw [dif_neg hj] at hp'
          exact absurd hp' (Finset.notMem_empty p)
    | bin op j k =>
      rw [coneOf_eq_bin c q op j k hg] at hp
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact le_refl p
      · rcases Finset.mem_union.mp hp' with hp'' | hp''
        · by_cases hj : j < q
          · rw [dif_pos hj] at hp''
            exact le_trans (ih j hj p hp'') (le_of_lt hj)
          · rw [dif_neg hj] at hp''
            exact absurd hp'' (Finset.notMem_empty p)
        · by_cases hk : k < q
          · rw [dif_pos hk] at hp''
            exact le_trans (ih k hk p hp'') (le_of_lt hk)
          · rw [dif_neg hk] at hp''
            exact absurd hp'' (Finset.notMem_empty p)

/-- **Cone closure (proved)**: children of cone members are cone members. -/
theorem cone_child {n : ℕ} (c : List (CGate n)) :
    ∀ root q, q ∈ coneOf c root → ∀ p, p ∈ childrenOf c q → p ∈ coneOf c root := by
  intro root
  induction root using Nat.strong_induction_on with
  | _ root ih =>
    intro q hq p hp
    cases hg : c.getD root (CGate.cst false) with
    | var i =>
      rw [coneOf_eq_var c root i hg] at hq
      rcases Finset.mem_insert.mp hq with rfl | hq'
      · rw [childrenOf_eq_var c q i hg] at hp
        exact absurd hp (Finset.notMem_empty p)
      · exact absurd hq' (Finset.notMem_empty q)
    | cst b =>
      rw [coneOf_eq_cst c root b hg] at hq
      rcases Finset.mem_insert.mp hq with rfl | hq'
      · rw [childrenOf_eq_cst c q b hg] at hp
        exact absurd hp (Finset.notMem_empty p)
      · exact absurd hq' (Finset.notMem_empty q)
    | un op j =>
      rw [coneOf_eq_un c root op j hg] at hq
      rcases Finset.mem_insert.mp hq with rfl | hq'
      · rw [childrenOf_eq_un c q op j hg] at hp
        by_cases hj : j < q
        · rw [if_pos hj] at hp
          rw [Finset.mem_singleton] at hp
          subst hp
          rw [coneOf_eq_un c q op p hg]
          apply Finset.mem_insert_of_mem
          rw [dif_pos hj]
          exact cone_self c p
        · rw [if_neg hj] at hp
          exact absurd hp (Finset.notMem_empty p)
      · by_cases hj : j < root
        · rw [dif_pos hj] at hq'
          have hmem := ih j hj q hq' p hp
          rw [coneOf_eq_un c root op j hg]
          apply Finset.mem_insert_of_mem
          rw [dif_pos hj]
          exact hmem
        · rw [dif_neg hj] at hq'
          exact absurd hq' (Finset.notMem_empty q)
    | bin op j k =>
      rw [coneOf_eq_bin c root op j k hg] at hq
      rcases Finset.mem_insert.mp hq with rfl | hq'
      · rw [childrenOf_eq_bin c q op j k hg] at hp
        rcases Finset.mem_union.mp hp with hp' | hp'
        · by_cases hj : j < q
          · rw [if_pos hj] at hp'
            rw [Finset.mem_singleton] at hp'
            subst hp'
            rw [coneOf_eq_bin c q op p k hg]
            apply Finset.mem_insert_of_mem
            apply Finset.mem_union_left
            rw [dif_pos hj]
            exact cone_self c p
          · rw [if_neg hj] at hp'
            exact absurd hp' (Finset.notMem_empty p)
        · by_cases hk : k < q
          · rw [if_pos hk] at hp'
            rw [Finset.mem_singleton] at hp'
            subst hp'
            rw [coneOf_eq_bin c q op j p hg]
            apply Finset.mem_insert_of_mem
            apply Finset.mem_union_right
            rw [dif_pos hk]
            exact cone_self c p
          · rw [if_neg hk] at hp'
            exact absurd hp' (Finset.notMem_empty p)
      · rcases Finset.mem_union.mp hq' with hq'' | hq''
        · by_cases hj : j < root
          · rw [dif_pos hj] at hq''
            have hmem := ih j hj q hq'' p hp
            rw [coneOf_eq_bin c root op j k hg]
            apply Finset.mem_insert_of_mem
            apply Finset.mem_union_left
            rw [dif_pos hj]
            exact hmem
          · rw [dif_neg hj] at hq''
            exact absurd hq'' (Finset.notMem_empty q)
        · by_cases hk : k < root
          · rw [dif_pos hk] at hq''
            have hmem := ih k hk q hq'' p hp
            rw [coneOf_eq_bin c root op j k hg]
            apply Finset.mem_insert_of_mem
            apply Finset.mem_union_right
            rw [dif_pos hk]
            exact hmem
          · rw [dif_neg hk] at hq''
            exact absurd hq'' (Finset.notMem_empty q)

/-- **Cone anatomy (proved)**: every cone member other than the root is some cone member's child. -/
theorem cone_parent {n : ℕ} (c : List (CGate n)) :
    ∀ root p, p ∈ coneOf c root → p = root ∨ ∃ r ∈ coneOf c root, p ∈ childrenOf c r := by
  intro root
  induction root using Nat.strong_induction_on with
  | _ root ih =>
    intro p hp
    cases hg : c.getD root (CGate.cst false) with
    | var i =>
      rw [coneOf_eq_var c root i hg] at hp
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact Or.inl rfl
      · exact absurd hp' (Finset.notMem_empty p)
    | cst b =>
      rw [coneOf_eq_cst c root b hg] at hp
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact Or.inl rfl
      · exact absurd hp' (Finset.notMem_empty p)
    | un op j =>
      rw [coneOf_eq_un c root op j hg] at hp
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact Or.inl rfl
      · by_cases hj : j < root
        · rw [dif_pos hj] at hp'
          rcases ih j hj p hp' with rfl | ⟨r, hr, hchild⟩
          · right
            refine ⟨root, cone_self c root, ?_⟩
            rw [childrenOf_eq_un c root op p hg, if_pos hj]
            exact Finset.mem_singleton_self p
          · right
            refine ⟨r, ?_, hchild⟩
            rw [coneOf_eq_un c root op j hg]
            apply Finset.mem_insert_of_mem
            rw [dif_pos hj]
            exact hr
        · rw [dif_neg hj] at hp'
          exact absurd hp' (Finset.notMem_empty p)
    | bin op j k =>
      rw [coneOf_eq_bin c root op j k hg] at hp
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact Or.inl rfl
      · rcases Finset.mem_union.mp hp' with hp'' | hp''
        · by_cases hj : j < root
          · rw [dif_pos hj] at hp''
            rcases ih j hj p hp'' with rfl | ⟨r, hr, hchild⟩
            · right
              refine ⟨root, cone_self c root, ?_⟩
              rw [childrenOf_eq_bin c root op p k hg]
              apply Finset.mem_union_left
              rw [if_pos hj]
              exact Finset.mem_singleton_self p
            · right
              refine ⟨r, ?_, hchild⟩
              rw [coneOf_eq_bin c root op j k hg]
              apply Finset.mem_insert_of_mem
              apply Finset.mem_union_left
              rw [dif_pos hj]
              exact hr
          · rw [dif_neg hj] at hp''
            exact absurd hp'' (Finset.notMem_empty p)
        · by_cases hk : k < root
          · rw [dif_pos hk] at hp''
            rcases ih k hk p hp'' with rfl | ⟨r, hr, hchild⟩
            · right
              refine ⟨root, cone_self c root, ?_⟩
              rw [childrenOf_eq_bin c root op j p hg]
              apply Finset.mem_union_right
              rw [if_pos hk]
              exact Finset.mem_singleton_self p
            · right
              refine ⟨r, ?_, hchild⟩
              rw [coneOf_eq_bin c root op j k hg]
              apply Finset.mem_insert_of_mem
              apply Finset.mem_union_right
              rw [dif_pos hk]
              exact hr
          · rw [dif_neg hk] at hp''
            exact absurd hp'' (Finset.notMem_empty p)

/-! ### Wire values by position -/

theorem runFrom_getD_stable {n : ℕ} (x : Fin n → Bool) :
    ∀ (gs : List (CGate n)) (vals : List Bool) (q : ℕ), q < vals.length →
      (runFrom x vals gs).getD q false = vals.getD q false := by
  intro gs
  induction gs with
  | nil => intro vals q _; rfl
  | cons g rest ih =>
    intro vals q hq
    show (runFrom x (vals ++ [evalGate x vals g]) rest).getD q false = vals.getD q false
    rw [ih (vals ++ [evalGate x vals g]) q (by
      rw [List.length_append]
      show q < vals.length + 1
      omega)]
    exact List.getD_append vals [evalGate x vals g] false q hq

/-- **The wire value at a position (proved)**: the run's `q`-th value is the `q`-th gate evaluated against the
prefix run. -/
theorem runFrom_getD_at {n : ℕ} (x : Fin n → Bool) :
    ∀ (gs : List (CGate n)) (vals : List Bool) (q : ℕ), q < gs.length →
      (runFrom x vals gs).getD (vals.length + q) false
        = evalGate x (runFrom x vals (gs.take q)) (gs.getD q (CGate.cst false)) := by
  intro gs
  induction gs with
  | nil =>
    intro vals q hq
    exact absurd hq (by simp)
  | cons g rest ih =>
    intro vals q hq
    cases q with
    | zero =>
      show (runFrom x (vals ++ [evalGate x vals g]) rest).getD (vals.length + 0) false
          = evalGate x (runFrom x vals ((g :: rest).take 0)) ((g :: rest).getD 0 (CGate.cst false))
      rw [show vals.length + 0 = vals.length by omega]
      rw [runFrom_getD_stable x rest (vals ++ [evalGate x vals g]) vals.length (by
        rw [List.length_append]
        show vals.length < vals.length + 1
        omega)]
      rw [getD_concat]
      rfl
    | succ q' =>
      show (runFrom x (vals ++ [evalGate x vals g]) rest).getD (vals.length + (q' + 1)) false
          = evalGate x (runFrom x vals ((g :: rest).take (q' + 1)))
              ((g :: rest).getD (q' + 1) (CGate.cst false))
      rw [show vals.length + (q' + 1) = (vals ++ [evalGate x vals g]).length + q' by
        rw [List.length_append]
        show vals.length + (q' + 1) = vals.length + 1 + q'
        omega]
      rw [ih (vals ++ [evalGate x vals g]) q' (by
        have h := hq
        rw [List.length_cons] at h
        omega)]
      rfl

theorem output_getD_at {n : ℕ} (x : Fin n → Bool) (c : List (CGate n)) (q : ℕ)
    (hq : q < c.length) :
    (runFrom x [] c).getD q false
      = evalGate x (runFrom x [] (c.take q)) (c.getD q (CGate.cst false)) := by
  have h := runFrom_getD_at x c [] q hq
  rw [show ([] : List Bool).length + q = q by simp] at h
  exact h

theorem takeRun_getD {n : ℕ} (x : Fin n → Bool) (c : List (CGate n)) (q j : ℕ)
    (hj : j < q) (hq : q ≤ c.length) :
    (runFrom x [] (c.take q)).getD j false = (runFrom x [] c).getD j false := by
  conv_rhs => rw [← List.take_append_drop q c]
  rw [runFrom_append]
  rw [runFrom_getD_stable x (c.drop q) (runFrom x [] (c.take q)) j (by
    rw [runFrom_length x (c.take q) [], List.length_take]
    show j < ([] : List Bool).length + min q c.length
    simp only [List.length_nil]
    omega)]

/-! ### The cone determines the output -/

/-- **The semantic content (proved)**: inputs agreeing on every variable read inside the cone give the same
value at every cone wire. -/
theorem cone_val_agree {n : ℕ} (c : List (CGate n)) (root : ℕ) (x x' : Fin n → Bool)
    (hvars : ∀ p ∈ coneOf c root, ∀ i, c.getD p (CGate.cst false) = CGate.var i → x i = x' i) :
    ∀ q, q ∈ coneOf c root →
      (runFrom x [] c).getD q false = (runFrom x' [] c).getD q false := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq
    by_cases hlen : q < c.length
    · rw [output_getD_at x c q hlen, output_getD_at x' c q hlen]
      cases hg : c.getD q (CGate.cst false) with
      | var i =>
        show x i = x' i
        exact hvars q hq i hg
      | cst b => rfl
      | un op j =>
        show op ((runFrom x [] (c.take q)).getD j false)
            = op ((runFrom x' [] (c.take q)).getD j false)
        by_cases hj : j < q
        · rw [takeRun_getD x c q j hj (le_of_lt hlen),
            takeRun_getD x' c q j hj (le_of_lt hlen)]
          rw [ih j hj (cone_child c root q hq j (by
            rw [childrenOf_eq_un c q op j hg, if_pos hj]
            exact Finset.mem_singleton_self j))]
        · have hxlen : (runFrom x [] (c.take q)).length ≤ j := by
            rw [runFrom_length x (c.take q) [], List.length_take]
            show ([] : List Bool).length + min q c.length ≤ j
            simp only [List.length_nil]
            omega
          have hxlen' : (runFrom x' [] (c.take q)).length ≤ j := by
            rw [runFrom_length x' (c.take q) [], List.length_take]
            show ([] : List Bool).length + min q c.length ≤ j
            simp only [List.length_nil]
            omega
          rw [List.getD_eq_default _ false hxlen, List.getD_eq_default _ false hxlen']
      | bin op j k =>
        show op ((runFrom x [] (c.take q)).getD j false)
              ((runFrom x [] (c.take q)).getD k false)
            = op ((runFrom x' [] (c.take q)).getD j false)
              ((runFrom x' [] (c.take q)).getD k false)
        have hjv : (runFrom x [] (c.take q)).getD j false
            = (runFrom x' [] (c.take q)).getD j false := by
          by_cases hj : j < q
          · rw [takeRun_getD x c q j hj (le_of_lt hlen),
              takeRun_getD x' c q j hj (le_of_lt hlen)]
            exact ih j hj (cone_child c root q hq j (by
              rw [childrenOf_eq_bin c q op j k hg]
              apply Finset.mem_union_left
              rw [if_pos hj]
              exact Finset.mem_singleton_self j))
          · have hxlen : (runFrom x [] (c.take q)).length ≤ j := by
              rw [runFrom_length x (c.take q) [], List.length_take]
              show ([] : List Bool).length + min q c.length ≤ j
              simp only [List.length_nil]
              omega
            have hxlen' : (runFrom x' [] (c.take q)).length ≤ j := by
              rw [runFrom_length x' (c.take q) [], List.length_take]
              show ([] : List Bool).length + min q c.length ≤ j
              simp only [List.length_nil]
              omega
            rw [List.getD_eq_default _ false hxlen, List.getD_eq_default _ false hxlen']
        have hkv : (runFrom x [] (c.take q)).getD k false
            = (runFrom x' [] (c.take q)).getD k false := by
          by_cases hk : k < q
          · rw [takeRun_getD x c q k hk (le_of_lt hlen),
              takeRun_getD x' c q k hk (le_of_lt hlen)]
            exact ih k hk (cone_child c root q hq k (by
              rw [childrenOf_eq_bin c q op j k hg]
              apply Finset.mem_union_right
              rw [if_pos hk]
              exact Finset.mem_singleton_self k))
          · have hxlen : (runFrom x [] (c.take q)).length ≤ k := by
              rw [runFrom_length x (c.take q) [], List.length_take]
              show ([] : List Bool).length + min q c.length ≤ k
              simp only [List.length_nil]
              omega
            have hxlen' : (runFrom x' [] (c.take q)).length ≤ k := by
              rw [runFrom_length x' (c.take q) [], List.length_take]
              show ([] : List Bool).length + min q c.length ≤ k
              simp only [List.length_nil]
              omega
            rw [List.getD_eq_default _ false hxlen, List.getD_eq_default _ false hxlen']
        rw [hjv, hkv]
    · have hL : (runFrom x [] c).length ≤ q := by
        rw [runFrom_length x c []]
        show ([] : List Bool).length + c.length ≤ q
        simp only [List.length_nil]
        omega
      have hL' : (runFrom x' [] c).length ≤ q := by
        rw [runFrom_length x' c []]
        show ([] : List Bool).length + c.length ≤ q
        simp only [List.length_nil]
        omega
      rw [List.getD_eq_default _ false hL, List.getD_eq_default _ false hL']

/-! ### The connectivity bound -/

/-- **THE CONNECTIVITY BOUND (proved)**: `K` essential variables force `2·K − 1` gates — `K` variable gates in
the output's cone, and at least `K − 1` binary gates to merge them, sharing fully accounted. -/
theorem cbudget_connectivity {n : ℕ} (f : (Fin n → Bool) → Bool) (V : Finset (Fin n))
    (hess : ∀ i ∈ V, ∃ x₁ x₀ : Fin n → Bool,
      (∀ b : Fin n, x₁ b ≠ x₀ b → b = i) ∧ f x₁ ≠ f x₀) :
    2 * V.card - 1 ≤ cbudget f := by
  classical
  by_cases hV : V = ∅
  · rw [hV]
    show 2 * (∅ : Finset (Fin n)).card - 1 ≤ cbudget f
    rw [Finset.card_empty]
    omega
  obtain ⟨c, hcomp, hlen⟩ := Nat.sInf_mem (cbudget_set_nonempty f)
  have hlen' : c.length = cbudget f := hlen
  have hcne : c ≠ [] := by
    intro hcon
    obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hV
    obtain ⟨x₁, x₀, -, hnev⟩ := hess i₀ hi₀
    apply hnev
    rw [← hcomp x₁, ← hcomp x₀, hcon]
    rfl
  have hcpos : 0 < c.length :=
    Nat.pos_of_ne_zero (fun h => hcne (List.eq_nil_of_length_eq_zero h))
  set root : ℕ := c.length - 1 with hroot
  set R : Finset ℕ := coneOf c root with hRdef
  -- every essential variable owns a var gate in the cone
  have hvarin : ∀ i ∈ V, ∃ p ∈ R, c.getD p (CGate.cst false) = CGate.var i := by
    intro i hi
    obtain ⟨x₁, x₀, hd, hnev⟩ := hess i hi
    by_contra hno
    push_neg at hno
    apply hnev
    rw [← hcomp x₁, ← hcomp x₀]
    show (runFrom x₁ [] c).getD (c.length - 1) false
        = (runFrom x₀ [] c).getD (c.length - 1) false
    apply cone_val_agree c root x₁ x₀ ?_ (c.length - 1) ?_
    · intro p hp i' hgate
      by_cases hii : i' = i
      · exact absurd (hii ▸ hgate) (hno p hp)
      · by_contra hne
        exact hii (hd i' hne)
    · exact cone_self c root
  -- the chosen var-gate positions inject into the cone's var gates
  set pos : Fin n → ℕ := fun i =>
    if h : ∃ p ∈ R, c.getD p (CGate.cst false) = CGate.var i then h.choose else 0
    with hposdef
  have hposmem : ∀ i ∈ V, pos i ∈ R ∧ c.getD (pos i) (CGate.cst false) = CGate.var i := by
    intro i hi
    have h := hvarin i hi
    have hp : pos i = h.choose := by
      rw [hposdef]
      exact dif_pos h
    rw [hp]
    exact ⟨h.choose_spec.1, h.choose_spec.2⟩
  set A : Finset ℕ := R.filter (fun p => isVarGate (c.getD p (CGate.cst false)) = true)
    with hA
  set B : Finset ℕ := R.filter (fun p => isUnGate (c.getD p (CGate.cst false)) = true)
    with hB
  set C : Finset ℕ := R.filter (fun p => isBinGate (c.getD p (CGate.cst false)) = true)
    with hC
  have hVcard : V.card ≤ A.card := by
    apply Finset.card_le_card_of_injOn pos
    · intro i hi
      obtain ⟨hmem, hgate⟩ := hposmem i (Finset.mem_coe.mp hi)
      rw [hA]
      show pos i ∈ Finset.filter _ R
      rw [Finset.mem_filter]
      refine ⟨hmem, ?_⟩
      rw [hgate]
      rfl
    · intro i hi i' hi' heq
      obtain ⟨-, hg⟩ := hposmem i (Finset.mem_coe.mp hi)
      obtain ⟨-, hg'⟩ := hposmem i' (Finset.mem_coe.mp hi')
      rw [heq] at hg
      exact CGate.var.inj (hg.symm.trans hg')
  -- partition: var + un + bin gates fit inside the cone
  have hABdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    rw [hA, Finset.mem_filter] at hpA
    rw [hB, Finset.mem_filter] at hpB
    cases hg : c.getD p (CGate.cst false) with
    | var i => rw [hg] at hpB; exact Bool.noConfusion hpB.2
    | cst b => rw [hg] at hpA; exact Bool.noConfusion hpA.2
    | un op j => rw [hg] at hpA; exact Bool.noConfusion hpA.2
    | bin op j k => rw [hg] at hpA; exact Bool.noConfusion hpA.2
  have hABCdis : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro p hpAB hpC
    rw [hC, Finset.mem_filter] at hpC
    rcases Finset.mem_union.mp hpAB with hpA | hpB
    · rw [hA, Finset.mem_filter] at hpA
      cases hg : c.getD p (CGate.cst false) with
      | var i => rw [hg] at hpC; exact Bool.noConfusion hpC.2
      | cst b => rw [hg] at hpA; exact Bool.noConfusion hpA.2
      | un op j => rw [hg] at hpA; exact Bool.noConfusion hpA.2
      | bin op j k => rw [hg] at hpA; exact Bool.noConfusion hpA.2
    · rw [hB, Finset.mem_filter] at hpB
      cases hg : c.getD p (CGate.cst false) with
      | var i => rw [hg] at hpB; exact Bool.noConfusion hpB.2
      | cst b => rw [hg] at hpB; exact Bool.noConfusion hpB.2
      | un op j => rw [hg] at hpC; exact Bool.noConfusion hpC.2
      | bin op j k => rw [hg] at hpB; exact Bool.noConfusion hpB.2
  have hABC : A.card + B.card + C.card ≤ R.card := by
    have h1 : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hABdis
    have h2 : ((A ∪ B) ∪ C).card = (A ∪ B).card + C.card :=
      Finset.card_union_of_disjoint hABCdis
    have h3 : (A ∪ B) ∪ C ⊆ R := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp' | hp'
      · rcases Finset.mem_union.mp hp' with hp'' | hp''
        · exact (Finset.mem_filter.mp (hA ▸ hp'')).1
        · exact (Finset.mem_filter.mp (hB ▸ hp'')).1
      · exact (Finset.mem_filter.mp (hC ▸ hp')).1
    have h4 := Finset.card_le_card h3
    omega
  -- the rooted count: |R| ≤ 1 + #un + 2·#bin
  have hparent : R ⊆ insert root (R.biUnion (childrenOf c)) := by
    intro p hp
    rcases cone_parent c root p hp with rfl | ⟨r, hr, hchild⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨r, hr, hchild⟩)
  have hsum1 : R.card ≤ 1 + ∑ p ∈ R, (childrenOf c p).card := by
    have h1 := Finset.card_le_card hparent
    have h2 := Finset.card_insert_le root (R.biUnion (childrenOf c))
    have h3 : (R.biUnion (childrenOf c)).card ≤ ∑ p ∈ R, (childrenOf c p).card :=
      Finset.card_biUnion_le
    omega
  have hsum2 : ∑ p ∈ R, (childrenOf c p).card ≤ ∑ p ∈ R, gateWeight c p :=
    Finset.sum_le_sum (fun p _ => childrenOf_card_le c p)
  have hpt : ∀ p, gateWeight c p
      = (if isUnGate (c.getD p (CGate.cst false)) = true then 1 else 0)
        + (if isBinGate (c.getD p (CGate.cst false)) = true then 2 else 0) := by
    intro p
    unfold gateWeight
    cases c.getD p (CGate.cst false) <;> rfl
  have hsum3 : ∑ p ∈ R, gateWeight c p = B.card + 2 * C.card := by
    rw [Finset.sum_congr rfl (fun p _ => hpt p), Finset.sum_add_distrib]
    congr 1
    · rw [hB, Finset.card_filter]
    · have h2 : ∀ p ∈ R, (if isBinGate (c.getD p (CGate.cst false)) = true then 2 else 0)
          = 2 * (if isBinGate (c.getD p (CGate.cst false)) = true then 1 else 0) := by
        intro p _
        split <;> rfl
      rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, hC, Finset.card_filter]
  -- the cone fits in the circuit
  have hrange : R ⊆ Finset.range c.length := by
    intro p hp
    rw [Finset.mem_range]
    have h := cone_le c root p hp
    omega
  have hRlen : R.card ≤ c.length := by
    have h := Finset.card_le_card hrange
    rw [Finset.card_range] at h
    exact h
  omega

/-! ### The `≈ 2N` bound for SAT -/

/-- **THE `≈ 2N` CIRCUIT BOUND FOR SAT (proved)**: `2·m·D − 1 ≤ cbudget (sat3Family N)` — a full layer of
merging gates on top of the full layer of input gates. -/
theorem sat3_cbudget_connectivity (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N) :
    2 * (sat3M N * sat3D N) - 1 ≤ cbudget (sat3Family N) := by
  have hinj : Function.Injective
      (fun p : Fin (sat3M N) × Fin 3 × Fin (sat3V N + 1) =>
        sat3Bit N p.1 p.2.1 p.2.2.val p.2.2.isLt) := by
    intro p q h
    obtain ⟨hc, ht, hf⟩ := sat3Bit_inj N p.2.2.isLt q.2.2.isLt h
    exact Prod.ext hc (Prod.ext ht (Fin.ext hf))
  have h := cbudget_connectivity (sat3Family N)
    (Finset.univ.image (fun p : Fin (sat3M N) × Fin 3 × Fin (sat3V N + 1) =>
      sat3Bit N p.1 p.2.1 p.2.2.val p.2.2.isLt))
    (by
      intro i hi
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨x₁, x₀, h1, h0, hforce⟩ :=
        sat3_layout_pair N hv hm2 p.1 p.2.1 p.2.2.val p.2.2.isLt
      exact ⟨x₁, x₀, hforce, by
        rw [h1, h0]
        decide⟩)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin] at h
  have hD : sat3M N * sat3D N = sat3M N * (3 * (sat3V N + 1)) := rfl
  omega

/-- **Within two blocks of `2N` (proved)**: `2·N ≤ cbudget (sat3Family N) + 2·D`. -/
theorem sat3_cbudget_near_2N (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N) :
    2 * N ≤ cbudget (sat3Family N) + 2 * sat3D N := by
  have h := sat3_cbudget_connectivity N hv hm2
  have hdm := Nat.div_add_mod N (sat3D N)
  have hmod : N % sat3D N < sat3D N := Nat.mod_lt N (sat3D_pos N)
  have hM : sat3M N * sat3D N = sat3D N * (N / sat3D N) := by
    show N / sat3D N * sat3D N = sat3D N * (N / sat3D N)
    exact Nat.mul_comm _ _
  have hpos : 1 ≤ sat3M N * sat3D N := by
    have h1 : 1 ≤ sat3M N := by omega
    have h2 : 1 ≤ sat3D N := sat3D_pos N
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cone_child
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cone_parent
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cone_val_agree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_connectivity
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_connectivity
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_near_2N
