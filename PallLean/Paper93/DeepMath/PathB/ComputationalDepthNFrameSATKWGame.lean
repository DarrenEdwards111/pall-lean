import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameKWSubstrate

/-!
# N-Frame: the SAT boundary KW game — protocols, the cost interface, and the first protocol lower bound

The boundary game, formalized: Alice holds a satisfiable encoding `x` (`sat3Family x = true` — she has a globally
coherent witness), Bob holds an unsatisfiable one (`sat3Family y = false` — some clause set is contradictory); they
communicate to find a **bit where their encodings disagree**.  Deterministic protocols are trees whose nodes query
one player's input and whose leaves announce a coordinate.

  `KWProt` / `run` / `cost` / `Solves` — the game and its protocols.
  `kwProtOf` + `kwProtOf_cost` + `kwProtOf_solves` — **PROVED, transducer ⇒ protocol**: a transducer of depth `d`
        compiles to a protocol of cost `≤ 2d` (each `bin` node: Alice and Bob each announce their child value).
  `kwCost_le_two_budget` — **PROVED, the new cost interface**: `kwCost f ≤ 2·budget f`.
  `kwCost_and_le` / `kwCost_parity_le` — **PROVED, calibration**: AND and parity have KW cost `≤ 2(2n+1)` — the game
        does not falsely explode on easy functions (majority is likewise covered by the generic interface).
  `sat3_forcing_pair` — **PROVED**: for every clause block, a 1/0-input pair differing *only* at that block's slot-0
        sign bit — the game's answer is forced.
  `sat3_kw_protocol_lb` — **PROVED, the first protocol lower bound in the arc**: any protocol solving the SAT
        boundary game has `sat3M N ≤ 2^cost`, i.e. cost `≥ log₂ m` — forced answers require `m` distinct output
        leaves, and a cost-`c` protocol has at most `2^c`.
  `sat3_kwCost_lb` — **PROVED**: the same at the `kwCost` minimum.

## Honest scope

The lower bound is **logarithmic** — the trivial scale, recorded as calibration of the new interface (consistent with
`volume ≥ m`).  The three open pieces, named and not claimed: the **hard direction** (protocol ⇒ shallow transducer),
**Spira rebalancing** (`depthBudget ≲ log budget` — the converter from superlog depth to superpoly volume), and a
**superlogarithmic** KW lower bound for `sat3Family` — the genuine frontier, where "maintaining one globally coherent
witness across many clauses" must cost communication.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The game -/

/-- A deterministic KW protocol: internal nodes query one player's input, leaves announce a coordinate. -/
inductive KWProt (n : ℕ) where
  | out : Fin n → KWProt n
  | askA : ((Fin n → Bool) → Bool) → KWProt n → KWProt n → KWProt n
  | askB : ((Fin n → Bool) → Bool) → KWProt n → KWProt n → KWProt n

namespace KWProt

/-- Run the protocol on Alice's input `x` and Bob's input `y`. -/
def run {n : ℕ} : KWProt n → (Fin n → Bool) → (Fin n → Bool) → Fin n
  | .out i, _, _ => i
  | .askA q l r, x, y => if q x then l.run x y else r.run x y
  | .askB q l r, x, y => if q y then l.run x y else r.run x y

/-- Communication cost = tree depth (one bit per query). -/
def cost {n : ℕ} : KWProt n → ℕ
  | .out _ => 0
  | .askA _ l r => max l.cost r.cost + 1
  | .askB _ l r => max l.cost r.cost + 1

/-- The set of coordinates the protocol can announce. -/
def outs {n : ℕ} : KWProt n → Finset (Fin n)
  | .out i => {i}
  | .askA _ l r => l.outs ∪ r.outs
  | .askB _ l r => l.outs ∪ r.outs

theorem run_out {n : ℕ} (i : Fin n) (x y : Fin n → Bool) : (out i).run x y = i := rfl

theorem run_askA {n : ℕ} (q : (Fin n → Bool) → Bool) (l r : KWProt n) (x y : Fin n → Bool) :
    (askA q l r).run x y = if q x then l.run x y else r.run x y := rfl

theorem run_askB {n : ℕ} (q : (Fin n → Bool) → Bool) (l r : KWProt n) (x y : Fin n → Bool) :
    (askB q l r).run x y = if q y then l.run x y else r.run x y := rfl

end KWProt

/-- The protocol solves the boundary game for `f`: on any 1/0-input pair it announces a differing coordinate. -/
def Solves {n : ℕ} (p : KWProt n) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, f x = true → f y = false → x (p.run x y) ≠ y (p.run x y)

/-- The run always lands on an announced coordinate. -/
theorem run_mem_outs {n : ℕ} (p : KWProt n) (x y : Fin n → Bool) :
    p.run x y ∈ p.outs := by
  induction p with
  | out i => exact Finset.mem_singleton_self i
  | askA q l r ihl ihr =>
    show (if q x then l.run x y else r.run x y) ∈ l.outs ∪ r.outs
    by_cases h : q x = true
    · rw [if_pos h]
      exact Finset.mem_union_left _ ihl
    · rw [if_neg h]
      exact Finset.mem_union_right _ ihr
  | askB q l r ihl ihr =>
    show (if q y then l.run x y else r.run x y) ∈ l.outs ∪ r.outs
    by_cases h : q y = true
    · rw [if_pos h]
      exact Finset.mem_union_left _ ihl
    · rw [if_neg h]
      exact Finset.mem_union_right _ ihr

/-- A cost-`c` protocol announces at most `2^c` distinct coordinates. -/
theorem outs_card_le {n : ℕ} (p : KWProt n) : p.outs.card ≤ 2 ^ p.cost := by
  induction p with
  | out i =>
    show ({i} : Finset (Fin n)).card ≤ 2 ^ 0
    rw [Finset.card_singleton, pow_zero]
  | askA q l r ihl ihr =>
    show (l.outs ∪ r.outs).card ≤ 2 ^ (max l.cost r.cost + 1)
    have h := Finset.card_union_le l.outs r.outs
    have h1 : (2 : ℕ) ^ l.cost ≤ 2 ^ max l.cost r.cost :=
      Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
    have h2 : (2 : ℕ) ^ r.cost ≤ 2 ^ max l.cost r.cost :=
      Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
    have h3 : (2 : ℕ) ^ (max l.cost r.cost + 1) = 2 * 2 ^ max l.cost r.cost := by
      rw [pow_succ]
      ring
    omega
  | askB q l r ihl ihr =>
    show (l.outs ∪ r.outs).card ≤ 2 ^ (max l.cost r.cost + 1)
    have h := Finset.card_union_le l.outs r.outs
    have h1 : (2 : ℕ) ^ l.cost ≤ 2 ^ max l.cost r.cost :=
      Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
    have h2 : (2 : ℕ) ^ r.cost ≤ 2 ^ max l.cost r.cost :=
      Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
    have h3 : (2 : ℕ) ^ (max l.cost r.cost + 1) = 2 * 2 ^ max l.cost r.cost := by
      rw [pow_succ]
      ring
    omega

/-! ### Transducer ⇒ protocol: the compiler -/

/-- Compile a transducer into a protocol: at each `bin` node Alice and Bob each announce their value of the left
child; equal values send the game into the right child, differing values into the left. -/
def kwProtOf {n : ℕ} (hn : 0 < n) : Trans n → KWProt n
  | .var i => .out i
  | .cst _ => .out ⟨0, hn⟩
  | .un _ s => kwProtOf hn s
  | .bin _ s₁ s₂ =>
      .askA (eval s₁)
        (.askB (eval s₁) (kwProtOf hn s₂) (kwProtOf hn s₁))
        (.askB (eval s₁) (kwProtOf hn s₁) (kwProtOf hn s₂))

theorem kwProtOf_cost {n : ℕ} (hn : 0 < n) (t : Trans n) :
    (kwProtOf hn t).cost ≤ 2 * depth t := by
  induction t with
  | var i => exact Nat.le_refl 0
  | cst b => exact Nat.zero_le _
  | un op s ih =>
    show (kwProtOf hn s).cost ≤ 2 * (depth s + 1)
    omega
  | bin op s₁ s₂ ih₁ ih₂ =>
    show max (max (kwProtOf hn s₂).cost (kwProtOf hn s₁).cost + 1)
        (max (kwProtOf hn s₁).cost (kwProtOf hn s₂).cost + 1) + 1
        ≤ 2 * (max (depth s₁) (depth s₂) + 1)
    have hd1 : depth s₁ ≤ max (depth s₁) (depth s₂) := Nat.le_max_left _ _
    have hd2 : depth s₂ ≤ max (depth s₁) (depth s₂) := Nat.le_max_right _ _
    have hM1 : max (kwProtOf hn s₂).cost (kwProtOf hn s₁).cost
        ≤ 2 * max (depth s₁) (depth s₂) :=
      max_le (by omega) (by omega)
    have hM2 : max (kwProtOf hn s₁).cost (kwProtOf hn s₂).cost
        ≤ 2 * max (depth s₁) (depth s₂) :=
      max_le (by omega) (by omega)
    have hM3 : max (max (kwProtOf hn s₂).cost (kwProtOf hn s₁).cost + 1)
        (max (kwProtOf hn s₁).cost (kwProtOf hn s₂).cost + 1)
        ≤ 2 * max (depth s₁) (depth s₂) + 1 :=
      max_le (by omega) (by omega)
    omega

theorem kwProtOf_run_diff {n : ℕ} (hn : 0 < n) (t : Trans n) (x y : Fin n → Bool)
    (h : eval t x ≠ eval t y) :
    x ((kwProtOf hn t).run x y) ≠ y ((kwProtOf hn t).run x y) := by
  induction t with
  | var i => exact h
  | cst b => exact absurd rfl h
  | un op s ih =>
    have hs : eval s x ≠ eval s y := fun hc => h (by
      show op (eval s x) = op (eval s y)
      rw [hc])
    exact ih hs
  | bin op s₁ s₂ ih₁ ih₂ =>
    have hred : (kwProtOf hn (Trans.bin op s₁ s₂)).run x y
        = if eval s₁ x then
            (if eval s₁ y then (kwProtOf hn s₂).run x y else (kwProtOf hn s₁).run x y)
          else
            (if eval s₁ y then (kwProtOf hn s₁).run x y else (kwProtOf hn s₂).run x y) := by
      show (if eval s₁ x then _ else _) = _
      by_cases ha : eval s₁ x = true
      · rw [if_pos ha, if_pos ha]
        rfl
      · rw [if_neg ha, if_neg ha]
        rfl
    by_cases ha : eval s₁ x = true <;> by_cases hb : eval s₁ y = true
    · -- both true: left child agrees, right child must differ
      have heq : eval s₁ x = eval s₁ y := ha.trans hb.symm
      have h2 : eval s₂ x ≠ eval s₂ y := fun hc => h (by
        show op (eval s₁ x) (eval s₂ x) = op (eval s₁ y) (eval s₂ y)
        rw [heq, hc])
      rw [hred, if_pos ha, if_pos hb]
      exact ih₂ h2
    · -- true/false: left child differs
      have h1 : eval s₁ x ≠ eval s₁ y := by
        intro hc
        exact hb (hc ▸ ha)
      rw [hred, if_pos ha, if_neg hb]
      exact ih₁ h1
    · -- false/true: left child differs
      have h1 : eval s₁ x ≠ eval s₁ y := by
        intro hc
        exact ha (hc.symm ▸ hb)
      rw [hred, if_neg ha, if_pos hb]
      exact ih₁ h1
    · -- both false: right child must differ
      have hxf : eval s₁ x = false := by
        cases hxx : eval s₁ x
        · rfl
        · exact absurd hxx ha
      have hyf : eval s₁ y = false := by
        cases hyy : eval s₁ y
        · rfl
        · exact absurd hyy hb
      have h2 : eval s₂ x ≠ eval s₂ y := fun hc => h (by
        show op (eval s₁ x) (eval s₂ x) = op (eval s₁ y) (eval s₂ y)
        rw [hxf, hyf, hc])
      rw [hred, if_neg ha, if_neg hb]
      exact ih₂ h2

/-- **Transducer ⇒ protocol (proved)**: the compiled protocol solves the boundary game for `eval t`. -/
theorem kwProtOf_solves {n : ℕ} (hn : 0 < n) (t : Trans n) :
    Solves (kwProtOf hn t) (eval t) := by
  intro x y hx hy
  apply kwProtOf_run_diff hn t x y
  rw [hx, hy]
  decide

/-! ### The KW cost and the new cost interface -/

/-- The minimum communication over protocols solving the boundary game for `f`. -/
noncomputable def kwCost {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {c | ∃ p : KWProt n, Solves p f ∧ p.cost = c}

/-- **The new cost interface (proved)**: `kwCost f ≤ 2 · budget f`. -/
theorem kwCost_le_two_budget {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    kwCost f ≤ 2 * budget f := by
  have hne : {v | ∃ t : Trans n, eval t = f ∧ volume t = v}.Nonempty :=
    ⟨volume (dnfFor f), dnfFor f, eval_dnfFor f, rfl⟩
  obtain ⟨t, ht, hvol⟩ := Nat.sInf_mem hne
  have hs : Solves (kwProtOf hn t) f := by
    rw [← ht]
    exact kwProtOf_solves hn t
  have h1 : kwCost f ≤ (kwProtOf hn t).cost := Nat.sInf_le ⟨kwProtOf hn t, hs, rfl⟩
  have h2 := kwProtOf_cost hn t
  have h3 := depth_lt_volume t
  have h4 : volume t = budget f := hvol
  omega

/-! ### Calibration: easy functions have cheap games -/

theorem volume_xorVars {n : ℕ} (is : List (Fin n)) :
    volume (xorVars is) ≤ 2 * is.length + 1 := by
  induction is with
  | nil =>
    show (1 : ℕ) ≤ 2 * 0 + 1
    omega
  | cons hd tl ih =>
    show 1 + volume (xorVars tl) + 1 ≤ 2 * (tl.length + 1) + 1
    omega

theorem budget_parity_le (n : ℕ) : budget (parityFn n) ≤ 2 * n + 1 := by
  have h1 : budget (parityFn n) ≤ volume (xorVars (List.finRange n)) :=
    Nat.sInf_le ⟨xorVars (List.finRange n), by
      funext x
      rw [eval_xorVars]
      rfl, rfl⟩
  have h2 := volume_xorVars (List.finRange n)
  rw [List.length_finRange] at h2
  omega

/-- **Calibration: parity (proved)** — KW cost at most `2(2n+1)`: no false explosion. -/
theorem kwCost_parity_le (n : ℕ) (hn : 0 < n) : kwCost (parityFn n) ≤ 2 * (2 * n + 1) := by
  have h1 := kwCost_le_two_budget hn (parityFn n)
  have h2 := budget_parity_le n
  omega

/-- **Calibration: AND (proved)** — KW cost at most `2(2n+1)`: no false explosion. -/
theorem kwCost_and_le (n : ℕ) (hn : 0 < n) : kwCost (fullAndFn n) ≤ 2 * (2 * n + 1) := by
  have h1 := kwCost_le_two_budget hn (fullAndFn n)
  have h2 := budget_fullAnd_le (n := n)
  omega

/-! ### The forced game instance and the SAT protocol lower bound -/

/-- **The forcing pair (proved)**: for every clause block, a 1/0-input pair differing *only* at that block's slot-0
sign bit — any correct protocol's answer on it is forced. -/
theorem sat3_forcing_pair (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (c : Fin (sat3M N)) :
    ∃ x₁ x₀ : Fin N → Bool, sat3Family N x₁ = true ∧ sat3Family N x₀ = false ∧
      ∀ i : Fin N, x₁ i ≠ x₀ i → i = sat3SignBit N c := by
  have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set j₀ : Fin (sat3M N - 2) := ⟨0, by omega⟩ with hj₀
  set vj : Fin (sat3V N) := ⟨0, hv⟩ with hvjdef
  set ctx : Fin N → Bool := sat3Context N c hk (fun _ => false) with hctx
  refine ⟨sat3Patch N c ctx (sat3Probe N vj true),
    sat3Patch N c ctx (sat3Probe N vj false), ?_, ?_, ?_⟩
  · rw [hctx]
    exact sat3Context_probe_eval N hv hk hkv c (fun _ => false) j₀ vj rfl true
  · rw [hctx]
    exact sat3Context_probe_eval N hv hk hkv c (fun _ => false) j₀ vj rfl false
  · intro i hdiff
    by_contra hcon
    apply hdiff
    show (if i.val / sat3D N = c.val then sat3Probe N vj true i else ctx i)
        = (if i.val / sat3D N = c.val then sat3Probe N vj false i else ctx i)
    by_cases hd : i.val / sat3D N = c.val
    · rw [if_pos hd, if_pos hd]
      show decide _ = decide _
      rw [decide_eq_decide]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact Or.inl h
        · exfalso
          apply hcon
          apply Fin.ext
          have hdm := Nat.div_add_mod i.val (sat3D N)
          rw [hd, h] at hdm
          show i.val = (sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega)).val
          rw [sat3Bit_val]
          show i.val = c.val * sat3D N + (0 : ℕ) * (sat3V N + 1) + sat3V N
          have hcomm : sat3D N * c.val = c.val * sat3D N := Nat.mul_comm _ _
          omega
      · rintro (h | ⟨-, h⟩)
        · exact Or.inl h
        · exact Bool.noConfusion h
    · rw [if_neg hd, if_neg hd]

/-- **The first protocol lower bound in the arc (proved)**: any protocol solving the SAT boundary game has
`sat3M N ≤ 2^cost` — the `m` forced answers require `m` distinct output leaves. -/
theorem sat3_kw_protocol_lb (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (p : KWProt N) (hsolve : Solves p (sat3Family N)) :
    sat3M N ≤ 2 ^ p.cost := by
  have hmem : ∀ c : Fin (sat3M N), sat3SignBit N c ∈ p.outs := by
    intro c
    obtain ⟨x₁, x₀, h1, h0, hforce⟩ := sat3_forcing_pair N hv hm3 c
    have hrun := hsolve x₁ x₀ h1 h0
    have hloc : p.run x₁ x₀ = sat3SignBit N c := hforce _ hrun
    rw [← hloc]
    exact run_mem_outs p x₁ x₀
  have hinj : Function.Injective (sat3SignBit N) := by
    intro c c' h
    apply Fin.ext
    rw [← sat3Bit_clause N c ⟨0, by omega⟩ (sat3V N) (by omega),
      ← sat3Bit_clause N c' ⟨0, by omega⟩ (sat3V N) (by omega)]
    show (sat3SignBit N c).val / sat3D N = (sat3SignBit N c').val / sat3D N
    rw [h]
  have hcard : sat3M N ≤ p.outs.card := by
    have himg : (Finset.univ.image (sat3SignBit N)) ⊆ p.outs := by
      intro i hi
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hi
      exact hmem c
    have hcardimg : (Finset.univ.image (sat3SignBit N)).card = sat3M N := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    rw [← hcardimg]
    exact Finset.card_le_card himg
  exact le_trans hcard (outs_card_le p)

/-- **The lower bound at the minimum (proved)**: `sat3M N ≤ 2^(kwCost (sat3Family N))` — communication `≥ log₂ m`.
Logarithmic scale: the honest calibration of the interface; the superlogarithmic version is the open frontier. -/
theorem sat3_kwCost_lb (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N) :
    sat3M N ≤ 2 ^ kwCost (sat3Family N) := by
  have hN : 0 < N := by
    by_contra h
    push_neg at h
    interval_cases N
    revert hm3
    decide
  have hne : {c | ∃ p : KWProt N, Solves p (sat3Family N) ∧ p.cost = c}.Nonempty := by
    refine ⟨(kwProtOf hN (dnfFor (sat3Family N))).cost,
      kwProtOf hN (dnfFor (sat3Family N)), ?_, rfl⟩
    have := kwProtOf_solves hN (dnfFor (sat3Family N))
    rw [eval_dnfFor] at this
    exact this
  obtain ⟨p, hp, hcost⟩ := Nat.sInf_mem hne
  have := sat3_kw_protocol_lb N hv hm3 p hp
  show sat3M N ≤ 2 ^ sInf {c | ∃ p : KWProt N, Solves p (sat3Family N) ∧ p.cost = c}
  rw [← hcost]
  exact this

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.kwProtOf_solves
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.kwCost_le_two_budget
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.kwCost_parity_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.kwCost_and_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_kw_protocol_lb
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_kwCost_lb
