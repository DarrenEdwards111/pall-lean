import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConeFloorROT

/-!
# Brick 2a of the `SlackComposes` m = 2 attack: the gate dichotomy at 12 gates

A hypothetical 12-gate circuit for `AEm 2` pins `cbudget (AEm 2) = 12`, so every
surgery that saves a gate is a contradiction.  This brick grinds through the
eliminations:

* **`computes_swap_mid` (proved)** — replacing a gate by one that evaluates
  equally at its own wire frontier preserves the computed function;
* **`no_cst_mid` / `no_un_mid` (proved)** — a 12-gate circuit for `AEm 2` has no
  constant and no unary gate anywhere: mid-circuit they are eliminated by the
  existing surgeries (`cbudget_le_of_cst_mid` / `cbudget_le_of_un_mid` ⟹ an
  11-gate circuit, impossible); at the root, `unary_shape` splits into the
  constant case (`AEm 2` is not constant), the `id` case (the prefix computes
  `AEm 2` with ≤ 11 gates), and the `not` case (the prefix computes `¬AEm 2`,
  and `12 ≤ cbudget (¬AEm 2)` too, by negation transfer);
* **`twelve_gate_dichotomy` (proved)** — every gate of a 12-gate circuit for
  `AEm 2` is a variable gate or a *genuine* binary gate (both sources in-range
  and distinct): degenerate binaries are eval-equal to unary gates and die by
  the above;
* **`twelve_cone_all` / `twelve_var_inj` (proved)** — the cone is the whole
  circuit and the six variables sit in six distinct var gates (bijectivity).

Brick 2b (the fanout dichotomy: exactly one doubly-read wire) assembles these
into the shape theorem.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-! ### Generic tools -/

/-- Split a list at a position, exposing the gate there. -/
theorem split_at_getD {n : ℕ} (c : List (CGate n)) {p : ℕ} (hp : p < c.length) :
    c = c.take p ++ c.getD p (.cst false) :: c.drop (p + 1) := by
  conv_lhs => rw [← List.take_append_drop p c]
  rw [List.drop_eq_getElem_cons hp, List.getD_eq_getElem c (CGate.cst false) hp]

/-- Replacing a gate by one that evaluates equally at its own wire frontier
preserves the computed function. -/
theorem computes_swap_mid {n : ℕ} (c₁ c₂ : List (CGate n)) (g g' : CGate n)
    (f : (Fin n → Bool) → Bool) (hcomp : computes (c₁ ++ g :: c₂) f)
    (hval : ∀ (x : Fin n → Bool) (vals : List Bool), vals.length = c₁.length →
      evalGate x vals g' = evalGate x vals g) :
    computes (c₁ ++ g' :: c₂) f := by
  intro x
  have hx := hcomp x
  have hVlen : (runFrom x [] c₁).length = c₁.length := by
    rw [runFrom_length]
    simp
  show (runFrom x [] (c₁ ++ g' :: c₂)).getD ((c₁ ++ g' :: c₂).length - 1) false = f x
  rw [runFrom_append]
  show (runFrom x (runFrom x [] c₁ ++ [evalGate x (runFrom x [] c₁) g']) c₂).getD
    ((c₁ ++ g' :: c₂).length - 1) false = f x
  rw [hval x (runFrom x [] c₁) hVlen]
  have hlen2 : (c₁ ++ g' :: c₂).length = (c₁ ++ g :: c₂).length := by simp
  rw [hlen2]
  show (runFrom x (runFrom x [] c₁) (g :: c₂)).getD ((c₁ ++ g :: c₂).length - 1) false
    = f x
  rw [← runFrom_append]
  exact hx

/-! ### Negation transfer -/

theorem depSet_not {n : ℕ} (f : (Fin n → Bool) → Bool) :
    depSet (fun x => !(f x)) = depSet f := by
  ext i
  rw [mem_depSet, mem_depSet]
  constructor
  · rintro ⟨x, b, hne⟩
    exact ⟨x, b, fun he => hne (by rw [he])⟩
  · rintro ⟨x, b, hne⟩
    exact ⟨x, b, fun he => hne (by
      have := congrArg (fun v => !v) he
      simpa using this)⟩

theorem split1_of_not {F : Bool → Bool → Bool → Bool}
    (h : Split1 (fun a b c => !(F a b c))) : Split1 F := by
  obtain ⟨op, g, hop⟩ := h
  refine ⟨fun a u => !(op a u), g, fun a b c => ?_⟩
  show F a b c = !(op a (g b c))
  rw [← hop a b c]
  show F a b c = !(!(F a b c))
  rw [Bool.not_not]

theorem split2_of_not {F : Bool → Bool → Bool → Bool}
    (h : Split2 (fun a b c => !(F a b c))) : Split2 F := by
  obtain ⟨op, g, hop⟩ := h
  refine ⟨fun a u => !(op a u), g, fun a b c => ?_⟩
  show F a b c = !(op b (g a c))
  rw [← hop a b c]
  show F a b c = !(!(F a b c))
  rw [Bool.not_not]

theorem split3_of_not {F : Bool → Bool → Bool → Bool}
    (h : Split3 (fun a b c => !(F a b c))) : Split3 F := by
  obtain ⟨op, g, hop⟩ := h
  refine ⟨fun a u => !(op a u), g, fun a b c => ?_⟩
  show F a b c = !(op c (g a b))
  rw [← hop a b c]
  show F a b c = !(!(F a b c))
  rw [Bool.not_not]

/-- Negation preserves the above-floor bound: `12 ≤ cbudget (¬ AEm 2)`. -/
theorem cbudget_not_AEm_two : 12 ≤ cbudget (fun x => !(AEm 2 x)) := by
  have h0 : (0:ℕ) < 3 * 2 := by omega
  have h1 : (1:ℕ) < 3 * 2 := by omega
  have h2 : (2:ℕ) < 3 * 2 := by omega
  have hd : (depSet (fun x => !(AEm 2 x))).card = 6 := by
    rw [depSet_not, depSet_AEm, Finset.card_univ, Fintype.card_fin]
  have hlb := cbudget_above_floor_of_unsplittable (fun x => !(AEm 2 x))
    ⟨0, h0⟩ ⟨1, h1⟩ ⟨2, h2⟩
    (by intro he; simp at he) (by intro he; simp at he) (by intro he; simp at he)
    (fun _ => true)
    (by
      intro hs
      apply allEq3_no_split_a
      have hs' := split1_of_not hs
      rw [AEm_gadget_allEq3 2 h0 h1 h2] at hs'
      exact hs')
    (by
      intro hs
      apply allEq3_no_split_b
      have hs' := split2_of_not hs
      rw [AEm_gadget_allEq3 2 h0 h1 h2] at hs'
      exact hs')
    (by
      intro hs
      apply allEq3_no_split_c
      have hs' := split3_of_not hs
      rw [AEm_gadget_allEq3 2 h0 h1 h2] at hs'
      exact hs')
  omega

/-- `AEm 2` is not constant. -/
theorem AEm_two_not_const (b : Bool) (hall : ∀ x, AEm 2 x = b) : False := by
  have h0 : (⟨0, by omega⟩ : Fin (3 * 2)) ∈ depSet (AEm 2) := by
    rw [depSet_AEm]
    exact Finset.mem_univ _
  obtain ⟨y, bb, hne⟩ := mem_depSet.mp h0
  exact hne (by rw [hall, hall])

/-! ### The eliminations -/

/-- No 12-gate circuit for `AEm 2` contains a constant gate. -/
theorem no_cst_mid (c₁ c₂ : List (CGate (3 * 2))) (b : Bool)
    (hcomp : computes (c₁ ++ CGate.cst b :: c₂) (AEm 2))
    (hlen : c₁.length + c₂.length + 1 = 12) : False := by
  have hcb : 12 ≤ cbudget (AEm 2) := by
    have := AEm_above_floor 2 (by omega)
    omega
  cases c₂ with
  | cons g₂ rest =>
    have hle := cbudget_le_of_cst_mid c₁ (g₂ :: rest) b (AEm 2) hcomp (by simp)
    simp only [List.length_cons] at hle hlen
    omega
  | nil =>
    -- the root is the constant: `AEm 2` would be constant
    refine AEm_two_not_const b (fun x => ?_)
    have hx := hcomp x
    have hVlen : (runFrom x [] c₁).length = c₁.length := by
      rw [runFrom_length]
      simp
    rw [← hx]
    show (runFrom x [] (c₁ ++ [CGate.cst b])).getD
      ((c₁ ++ [CGate.cst b]).length - 1) false = b
    rw [runFrom_append]
    show ((runFrom x [] c₁) ++ [evalGate x (runFrom x [] c₁) (CGate.cst b)]).getD
      ((c₁ ++ [CGate.cst b]).length - 1) false = b
    have hidx : (c₁ ++ [CGate.cst b]).length - 1 = (runFrom x [] c₁).length := by
      rw [hVlen]
      simp
    rw [hidx, getD_concat]
    rfl

/-- No 12-gate circuit for `AEm 2` contains a unary gate. -/
theorem no_un_mid (c₁ c₂ : List (CGate (3 * 2))) (op : Bool → Bool) (q : ℕ)
    (hcomp : computes (c₁ ++ CGate.un op q :: c₂) (AEm 2))
    (hlen : c₁.length + c₂.length + 1 = 12) : False := by
  have hcb : 12 ≤ cbudget (AEm 2) := by
    have := AEm_above_floor 2 (by omega)
    omega
  cases c₂ with
  | cons g₂ rest =>
    have hle := cbudget_le_of_un_mid c₁ (g₂ :: rest) op q (AEm 2) hcomp (by simp)
    simp only [List.length_cons] at hle hlen
    omega
  | nil =>
    -- the root is unary over the 11-gate prefix
    have hc₁len : c₁.length = 11 := by simpa using hlen
    -- the output value is `op` of wire `q` of the prefix
    have hval : ∀ x, AEm 2 x = op ((runFrom x [] c₁).getD q false) := by
      intro x
      have hx := hcomp x
      rw [← hx]
      show (runFrom x [] (c₁ ++ [CGate.un op q])).getD
        ((c₁ ++ [CGate.un op q]).length - 1) false
        = op ((runFrom x [] c₁).getD q false)
      rw [runFrom_append]
      show ((runFrom x [] c₁) ++ [evalGate x (runFrom x [] c₁) (CGate.un op q)]).getD
        ((c₁ ++ [CGate.un op q]).length - 1) false
        = op ((runFrom x [] c₁).getD q false)
      have hVlen : (runFrom x [] c₁).length = c₁.length := by
        rw [runFrom_length]
        simp
      have hidx : (c₁ ++ [CGate.un op q]).length - 1 = (runFrom x [] c₁).length := by
        rw [hVlen]
        simp
      rw [hidx, getD_concat]
      rfl
    by_cases hq : q < c₁.length
    · -- in-range source: the prefix computes `±(wire q)`
      have htake : ∀ x, output (c₁.take (q + 1)) x = (runFrom x [] c₁).getD q false := by
        intro x
        show (runFrom x [] (c₁.take (q + 1))).getD ((c₁.take (q + 1)).length - 1) false
          = (runFrom x [] c₁).getD q false
        have hlt : (c₁.take (q + 1)).length = q + 1 := by
          rw [List.length_take]
          omega
        rw [hlt]
        exact wire_prefix c₁ x (by omega) (by omega)
      have htlen : (c₁.take (q + 1)).length = q + 1 := by
        rw [List.length_take]
        omega
      rcases unary_shape op with hop | hop | hop
      · -- constant: `AEm 2` constant
        refine AEm_two_not_const (op false) (fun x => ?_)
        rw [hval x, hop]
      · -- identity: the ≤ 11-gate prefix computes `AEm 2`
        have hcomp' : computes (c₁.take (q + 1)) (AEm 2) := by
          intro x
          rw [htake x, ← hop ((runFrom x [] c₁).getD q false), ← hval x]
        have hle : cbudget (AEm 2) ≤ q + 1 :=
          le_trans (Nat.sInf_le ⟨c₁.take (q + 1), hcomp', rfl⟩) (le_of_eq htlen)
        omega
      · -- negation: the ≤ 11-gate prefix computes `¬ AEm 2`
        have hcomp' : computes (c₁.take (q + 1)) (fun x => !(AEm 2 x)) := by
          intro x
          rw [htake x]
          show (runFrom x [] c₁).getD q false = !(AEm 2 x)
          rw [hval x, hop]
          rw [Bool.not_not]
        have hle : cbudget (fun x => !(AEm 2 x)) ≤ q + 1 :=
          le_trans (Nat.sInf_le ⟨c₁.take (q + 1), hcomp', rfl⟩) (le_of_eq htlen)
        have := cbudget_not_AEm_two
        omega
    · -- out-of-range source: constant output
      refine AEm_two_not_const (op false) (fun x => ?_)
      rw [hval x]
      have hVlen : (runFrom x [] c₁).length = c₁.length := by
        rw [runFrom_length]
        simp
      rw [List.getD_eq_default _ _ (by omega)]

/-! ### The gate dichotomy -/

/-- getD form: no constant gates. -/
theorem twelve_no_cst (c : List (CGate (3 * 2))) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) (p : ℕ) (hp : p < 12) (b : Bool)
    (hg : c.getD p (.cst false) = CGate.cst b) : False := by
  have hsplit := split_at_getD c (show p < c.length by omega)
  rw [hg] at hsplit
  rw [hsplit] at hcomp
  refine no_cst_mid (c.take p) (c.drop (p + 1)) b hcomp ?_
  have h1 : (c.take p).length = p := by
    rw [List.length_take]
    omega
  have h2 : (c.drop (p + 1)).length = c.length - (p + 1) := List.length_drop
  omega

/-- getD form: no unary gates. -/
theorem twelve_no_un (c : List (CGate (3 * 2))) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) (p : ℕ) (hp : p < 12) (op : Bool → Bool) (q : ℕ)
    (hg : c.getD p (.cst false) = CGate.un op q) : False := by
  have hsplit := split_at_getD c (show p < c.length by omega)
  rw [hg] at hsplit
  rw [hsplit] at hcomp
  refine no_un_mid (c.take p) (c.drop (p + 1)) op q hcomp ?_
  have h1 : (c.take p).length = p := by
    rw [List.length_take]
    omega
  have h2 : (c.drop (p + 1)).length = c.length - (p + 1) := List.length_drop
  omega

/-- Binary gates are genuine: sources in-range and distinct. -/
theorem twelve_bins_genuine (c : List (CGate (3 * 2))) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) (p : ℕ) (hp : p < 12) (op : Bool → Bool → Bool) (j k : ℕ)
    (hg : c.getD p (.cst false) = CGate.bin op j k) :
    j < p ∧ k < p ∧ j ≠ k := by
  have hsplit := split_at_getD c (show p < c.length by omega)
  rw [hg] at hsplit
  have hcomp' := hcomp
  rw [hsplit] at hcomp'
  have h1 : (c.take p).length = p := by
    rw [List.length_take]
    omega
  have h2 : (c.drop (p + 1)).length = c.length - (p + 1) := List.length_drop
  have hlen' : (c.take p).length + (c.drop (p + 1)).length + 1 = 12 := by omega
  by_cases hkp : k < p
  · by_cases hjp : j < p
    · refine ⟨hjp, hkp, ?_⟩
      intro he
      subst he
      -- repeated slot: eval-equal to a unary gate
      have hswap := computes_swap_mid (c.take p) (c.drop (p + 1))
        (CGate.bin op j j) (CGate.un (fun v => op v v) j) (AEm 2) hcomp'
        (fun x vals _ => rfl)
      exact no_un_mid _ _ _ _ hswap hlen'
    · -- j out of range: eval-equal to a unary gate on k
      exfalso
      have hswap := computes_swap_mid (c.take p) (c.drop (p + 1))
        (CGate.bin op j k) (CGate.un (fun v => op false v) k) (AEm 2) hcomp'
        (fun x vals hv => by
          have hj0 : vals.getD j false = false := List.getD_eq_default _ _ (by omega)
          show (fun v => op false v) (vals.getD k false)
            = op (vals.getD j false) (vals.getD k false)
          rw [hj0])
      exact no_un_mid _ _ _ _ hswap hlen'
  · -- k out of range: eval-equal to a unary gate on j
    exfalso
    have hswap := computes_swap_mid (c.take p) (c.drop (p + 1))
      (CGate.bin op j k) (CGate.un (fun v => op v false) j) (AEm 2) hcomp'
      (fun x vals hv => by
        have hk0 : vals.getD k false = false := List.getD_eq_default _ _ (by omega)
        show (fun v => op v false) (vals.getD j false)
          = op (vals.getD j false) (vals.getD k false)
        rw [hk0])
    exact no_un_mid _ _ _ _ hswap hlen'

/-- **The gate dichotomy (proved)**: every gate of a 12-gate circuit for `AEm 2`
is a variable gate or a genuine binary gate. -/
theorem twelve_gate_dichotomy (c : List (CGate (3 * 2))) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) (p : ℕ) (hp : p < 12) :
    (∃ i : Fin (3 * 2), c.getD p (.cst false) = CGate.var i)
    ∨ ∃ op j k, c.getD p (.cst false) = CGate.bin op j k ∧ j < p ∧ k < p ∧ j ≠ k := by
  cases hg : c.getD p (.cst false) with
  | var i => exact Or.inl ⟨i, rfl⟩
  | cst b => exact absurd (twelve_no_cst c hcomp hlen p hp b hg) (fun h => h)
  | un op q => exact absurd (twelve_no_un c hcomp hlen p hp op q hg) (fun h => h)
  | bin op j k =>
    obtain ⟨hj, hk, hjk⟩ := twelve_bins_genuine c hcomp hlen p hp op j k hg
    exact Or.inr ⟨op, j, k, rfl, hj, hk, hjk⟩

/-! ### All-cone and var bijectivity -/

/-- The cone is the whole circuit. -/
theorem twelve_cone_all (c : List (CGate (3 * 2))) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) : cone c = Finset.range 12 := by
  have hge := AEm_cone_ge 2 (by omega) c hcomp (by omega)
  have hsub : cone c ⊆ Finset.range 12 := by
    intro w hw
    rw [Finset.mem_range]
    have := (mem_cone.mp hw).1
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range]; omega)

/-- Exactly six cone var gates. -/
theorem twelve_varsEq (c : List (CGate (3 * 2))) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) : (coneVars c).card = (depSet (AEm 2)).card := by
  classical
  have hs : 0 < c.length := by omega
  have hconeCard : (cone c).card = 12 := by
    rw [twelve_cone_all c hcomp hlen, Finset.card_range]
  have hA := cone_card_le c hs
  have h2 := depSet_card_le_coneVars (AEm 2) c hcomp hs
  have hsplit : ∑ w ∈ coneVars c, inSlots (c.getD w (.cst false))
      + ∑ w ∈ (cone c).filter
          (fun w => ¬ ∃ i' : Fin (3 * 2), c.getD w (.cst false) = CGate.var i'),
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
  have hrest : ∑ w ∈ (cone c).filter
      (fun w => ¬ ∃ i' : Fin (3 * 2), c.getD w (.cst false) = CGate.var i'),
      inSlots (c.getD w (.cst false))
      ≤ 2 * ((cone c).filter
        (fun w => ¬ ∃ i' : Fin (3 * 2), c.getD w (.cst false) = CGate.var i')).card := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ 2 (fun w _ => inSlots_le_two _)) ?_
    rw [smul_eq_mul]
    omega
  have hpart : (coneVars c).card
      + ((cone c).filter
        (fun w => ¬ ∃ i' : Fin (3 * 2), c.getD w (.cst false) = CGate.var i')).card
      = (cone c).card := by
    rw [coneVars]
    exact Finset.card_filter_add_card_filter_not (s := cone c)
      (p := fun w => ∃ i' : Fin (3 * 2), c.getD w (.cst false) = CGate.var i')
  have hd : (depSet (AEm 2)).card = 6 := by
    rw [depSet_AEm, Finset.card_univ, Fintype.card_fin]
  omega

/-- Var injectivity from the vars-count equality (the floor is not needed). -/
theorem var_injective_of_varsEq {n : ℕ} (f : (Fin n → Bool) → Bool)
    (c : List (CGate n)) (hcomp : computes c f) (hs : 0 < c.length)
    (hveq : (coneVars c).card = (depSet f).card)
    {w₁ w₂ : ℕ} {i : Fin n} (h₁ : w₁ ∈ cone c) (h₂ : w₂ ∈ cone c)
    (hg₁ : c.getD w₁ (.cst false) = CGate.var i)
    (hg₂ : c.getD w₂ (.cst false) = CGate.var i) : w₁ = w₂ := by
  classical
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
    exact le_of_eq hveq
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

/-- **Var bijectivity (proved)**: in a 12-gate circuit for `AEm 2`, the six
variables sit in six distinct var-gate positions. -/
theorem twelve_var_inj (c : List (CGate (3 * 2))) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) {w₁ w₂ : ℕ} {i : Fin (3 * 2)}
    (h₁ : w₁ < 12) (h₂ : w₂ < 12)
    (hg₁ : c.getD w₁ (.cst false) = CGate.var i)
    (hg₂ : c.getD w₂ (.cst false) = CGate.var i) : w₁ = w₂ := by
  have hall := twelve_cone_all c hcomp hlen
  refine var_injective_of_varsEq (AEm 2) c hcomp (by omega)
    (twelve_varsEq c hcomp hlen) ?_ ?_ hg₁ hg₂
  · rw [hall, Finset.mem_range]
    omega
  · rw [hall, Finset.mem_range]
    omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.twelve_gate_dichotomy
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.twelve_var_inj
