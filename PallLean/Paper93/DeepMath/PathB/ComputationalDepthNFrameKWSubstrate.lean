import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameNeciporukCostInterface

/-!
# N-Frame: the Karchmer–Wigderson substrate — depth, the difference-descent, and sign-bit forcing

The witness-coupling collapse showed that converting coupling into volume needs a mechanism sensitive to **joint
structure**, not per-block counts.  Classically that mechanism is the Karchmer–Wigderson connection: formula depth
= communication needed to find a differing coordinate between a 1-input and a 0-input.  This file builds the
Trans-native substrate.

  `depth` + `volume_lt_two_pow` / `depth_lt_volume` / `depthBudget_lt_budget` — **PROVED**: the depth measure and
        its two-sided volume relations (`V < 2^(d+1)`; min-depth < min-volume).
  `kwFind` / `kwFind_correct` — **PROVED, the KW easy direction**: a computable difference-descent — given a
        1-input and a 0-input it walks the tree, at each `bin` node following a child whose values differ, and
        returns a coordinate `i` with `x i ≠ y i` that is moreover a **read leaf** of the tree (`readsVar`).
  `kwSteps_le_depth` — **PROVED, the communication reading**: the descent makes at most `depth t` binary decisions —
        exchanging the child-values (2 bits/level) solves the KW search in `≤ 2·depth` communicated bits.
  `sat3_reads_every_signbit` — **PROVED, the mechanism demonstrated**: the workhorse supplies 1/0-input pairs
        differing **only at the slot-0 sign bit** of any chosen clause block, so the descent's answer is forced —
        every transducer computing `sat3Family` reads every block's sign bit.
  `sat3_kw_volume_ge` — **PROVED**: hence `volume ≥ m` — *weaker* than the Nečiporuk `m(m−2)/4`, included as a
        demonstration that KW-style coordinate-localization converts to leaf presence, not as a new bound.

## Honest scope

This is the *easy* KW direction.  The load-bearing open pieces, named and not claimed: the **hard direction**
(communication protocols ⇒ shallow transducers), **Spira rebalancing** (`depthBudget ≲ log budget`, which is what
converts superlogarithmic depth bounds into superpolynomial volume bounds), and a **superlogarithmic KW lower bound
for `sat3Family`** — the last being the genuine research frontier (beyond-Nečiporuk formula bounds).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Depth and its volume relations -/

/-- Tree depth: the transducer's parallel time / KW communication budget. -/
def depth {n : ℕ} : Trans n → ℕ
  | .var _ => 0
  | .cst _ => 0
  | .un _ s => depth s + 1
  | .bin _ s₁ s₂ => max (depth s₁) (depth s₂) + 1

theorem volume_lt_two_pow {n : ℕ} (t : Trans n) : volume t < 2 ^ (depth t + 1) := by
  induction t with
  | var i =>
    show (1 : ℕ) < 2 ^ (0 + 1)
    norm_num
  | cst b =>
    show (1 : ℕ) < 2 ^ (0 + 1)
    norm_num
  | un op s ih =>
    show volume s + 1 < 2 ^ (depth s + 1 + 1)
    have h2 : (2 : ℕ) ^ (depth s + 1 + 1) = 2 * 2 ^ (depth s + 1) := by
      rw [pow_succ]
      ring
    omega
  | bin op s₁ s₂ ih₁ ih₂ =>
    show volume s₁ + volume s₂ + 1 < 2 ^ (max (depth s₁) (depth s₂) + 1 + 1)
    have hm1 : (2 : ℕ) ^ (depth s₁ + 1) ≤ 2 ^ (max (depth s₁) (depth s₂) + 1) :=
      Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right (Nat.le_max_left _ _) 1)
    have hm2 : (2 : ℕ) ^ (depth s₂ + 1) ≤ 2 ^ (max (depth s₁) (depth s₂) + 1) :=
      Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right (Nat.le_max_right _ _) 1)
    have h2 : (2 : ℕ) ^ (max (depth s₁) (depth s₂) + 1 + 1)
        = 2 * 2 ^ (max (depth s₁) (depth s₂) + 1) := by
      rw [pow_succ]
      ring
    omega

theorem depth_lt_volume {n : ℕ} (t : Trans n) : depth t < volume t := by
  induction t with
  | var i =>
    show (0 : ℕ) < 1
    omega
  | cst b =>
    show (0 : ℕ) < 1
    omega
  | un op s ih =>
    show depth s + 1 < volume s + 1
    omega
  | bin op s₁ s₂ ih₁ ih₂ =>
    show max (depth s₁) (depth s₂) + 1 < volume s₁ + volume s₂ + 1
    have hle : max (depth s₁) (depth s₂) ≤ depth s₁ + depth s₂ :=
      max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    omega

/-- The minimum depth over transducers computing `f`. -/
noncomputable def depthBudget {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {d | ∃ t : Trans n, eval t = f ∧ depth t = d}

theorem depthBudget_lt_budget {n : ℕ} (f : (Fin n → Bool) → Bool) :
    depthBudget f < budget f := by
  have hne : {v | ∃ t : Trans n, eval t = f ∧ volume t = v}.Nonempty :=
    ⟨volume (dnfFor f), dnfFor f, eval_dnfFor f, rfl⟩
  obtain ⟨t, ht, hvol⟩ := Nat.sInf_mem hne
  have h1 : depthBudget f ≤ depth t := Nat.sInf_le ⟨t, ht, rfl⟩
  have h2 := depth_lt_volume t
  show depthBudget f < sInf {v | ∃ t : Trans n, eval t = f ∧ volume t = v}
  omega

/-! ### The difference-descent: the KW easy direction -/

/-- `i` is read by a `var` leaf of the tree. -/
def readsVar {n : ℕ} : Trans n → Fin n → Prop
  | .var j, i => j = i
  | .cst _, _ => False
  | .un _ s, i => readsVar s i
  | .bin _ s₁ s₂, i => readsVar s₁ i ∨ readsVar s₂ i

/-- The KW difference-descent: at each `bin` node follow a child whose values on `x`/`y` differ. -/
def kwFind {n : ℕ} : Trans n → (Fin n → Bool) → (Fin n → Bool) → Option (Fin n)
  | .var i, x, y => if x i = y i then none else some i
  | .cst _, _, _ => none
  | .un _ s, x, y => kwFind s x y
  | .bin _ s₁ s₂, x, y =>
      if eval s₁ x = eval s₁ y then kwFind s₂ x y else kwFind s₁ x y

/-- The number of binary decisions made by the descent. -/
def kwSteps {n : ℕ} : Trans n → (Fin n → Bool) → (Fin n → Bool) → ℕ
  | .var _, _, _ => 0
  | .cst _, _, _ => 0
  | .un _ s, x, y => kwSteps s x y
  | .bin _ s₁ s₂, x, y =>
      (if eval s₁ x = eval s₁ y then kwSteps s₂ x y else kwSteps s₁ x y) + 1

/-- **The communication reading (proved)**: the descent makes at most `depth t` decisions. -/
theorem kwSteps_le_depth {n : ℕ} (t : Trans n) (x y : Fin n → Bool) :
    kwSteps t x y ≤ depth t := by
  induction t with
  | var i => exact Nat.le_refl 0
  | cst b => exact Nat.le_refl 0
  | un op s ih =>
    show kwSteps s x y ≤ depth s + 1
    omega
  | bin op s₁ s₂ ih₁ ih₂ =>
    show (if eval s₁ x = eval s₁ y then kwSteps s₂ x y else kwSteps s₁ x y) + 1
        ≤ max (depth s₁) (depth s₂) + 1
    have hm1 : depth s₁ ≤ max (depth s₁) (depth s₂) := Nat.le_max_left _ _
    have hm2 : depth s₂ ≤ max (depth s₁) (depth s₂) := Nat.le_max_right _ _
    by_cases h : eval s₁ x = eval s₁ y
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      omega

/-- **The KW easy direction (proved)**: on any 1/0-input pair the descent returns a differing coordinate that is
moreover a read leaf of the tree. -/
theorem kwFind_correct {n : ℕ} (t : Trans n) (x y : Fin n → Bool)
    (h : eval t x ≠ eval t y) :
    ∃ i, kwFind t x y = some i ∧ x i ≠ y i ∧ readsVar t i := by
  induction t with
  | var i =>
    have hxy : x i ≠ y i := h
    refine ⟨i, ?_, hxy, rfl⟩
    show (if x i = y i then none else some i) = some i
    rw [if_neg hxy]
  | cst b => exact absurd rfl h
  | un op s ih =>
    have hs : eval s x ≠ eval s y := fun hc => h (by
      show op (eval s x) = op (eval s y)
      rw [hc])
    obtain ⟨i, h1, h2, h3⟩ := ih hs
    exact ⟨i, h1, h2, h3⟩
  | bin op s₁ s₂ ih₁ ih₂ =>
    by_cases h1 : eval s₁ x = eval s₁ y
    · have h2 : eval s₂ x ≠ eval s₂ y := fun hc => h (by
        show op (eval s₁ x) (eval s₂ x) = op (eval s₁ y) (eval s₂ y)
        rw [h1, hc])
      obtain ⟨i, ha, hb, hread⟩ := ih₂ h2
      refine ⟨i, ?_, hb, Or.inr hread⟩
      show (if eval s₁ x = eval s₁ y then kwFind s₂ x y else kwFind s₁ x y) = some i
      rw [if_pos h1]
      exact ha
    · obtain ⟨i, ha, hb, hread⟩ := ih₁ h1
      refine ⟨i, ?_, hb, Or.inl hread⟩
      show (if eval s₁ x = eval s₁ y then kwFind s₂ x y else kwFind s₁ x y) = some i
      rw [if_neg h1]
      exact ha

/-- A read variable inside a block contributes a leaf to that block's count. -/
theorem leavesOn_pos_of_readsVar {n : ℕ} (t : Trans n) (P : Fin n → Bool) (i : Fin n)
    (hr : readsVar t i) (hP : P i = true) : 1 ≤ leavesOn P t := by
  induction t with
  | var j =>
    have hj : j = i := hr
    subst hj
    show 1 ≤ (if P j then 1 else 0)
    rw [if_pos hP]
  | cst b => exact hr.elim
  | un op s ih => exact ih hr
  | bin op s₁ s₂ ih₁ ih₂ =>
    show 1 ≤ leavesOn P s₁ + leavesOn P s₂
    rcases hr with h | h
    · have := ih₁ h
      omega
    · have := ih₂ h
      omega

/-! ### The mechanism demonstrated on SAT: sign-bit forcing -/

/-- The slot-0 sign bit of clause block `c`. -/
def sat3SignBit (N : ℕ) (c : Fin (sat3M N)) : Fin N :=
  sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega)

/-- **Sign-bit forcing (proved)**: the workhorse supplies a 1/0-input pair differing only at block `c`'s slot-0 sign
bit, so the KW descent's answer is forced — every transducer computing `sat3Family` reads every block's sign bit. -/
theorem sat3_reads_every_signbit (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (t : Trans N) (heval : eval t = sat3Family N) (c : Fin (sat3M N)) :
    readsVar t (sat3SignBit N c) := by
  have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set j₀ : Fin (sat3M N - 2) := ⟨0, by omega⟩ with hj₀
  set vj : Fin (sat3V N) := ⟨0, hv⟩ with hvjdef
  set ctx : Fin N → Bool := sat3Context N c hk (fun _ => false) with hctx
  set x₁ : Fin N → Bool := sat3Patch N c ctx (sat3Probe N vj true) with hx₁
  set x₀ : Fin N → Bool := sat3Patch N c ctx (sat3Probe N vj false) with hx₀
  have hv₁ : sat3Family N x₁ = true := by
    rw [hx₁, hctx]
    exact sat3Context_probe_eval N hv hk hkv c (fun _ => false) j₀ vj rfl true
  have hv₀ : sat3Family N x₀ = false := by
    rw [hx₀, hctx]
    exact sat3Context_probe_eval N hv hk hkv c (fun _ => false) j₀ vj rfl false
  have hne : eval t x₁ ≠ eval t x₀ := by
    rw [heval, hv₁, hv₀]
    decide
  obtain ⟨i, -, hdiff, hreads⟩ := kwFind_correct t x₁ x₀ hne
  have hloc : i = sat3SignBit N c := by
    by_contra hcon
    apply hdiff
    rw [hx₁, hx₀]
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
  rw [← hloc]
  exact hreads

/-- **The KW-style volume corollary (proved)**: `volume ≥ m`.  Weaker than the Nečiporuk `m(m−2)/4` — included as a
demonstration that coordinate-localization converts to leaf presence, not as a new bound. -/
theorem sat3_kw_volume_ge (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (t : Trans N) (heval : eval t = sat3Family N) :
    sat3M N ≤ volume t := by
  have hper : ∀ c : Fin (sat3M N), 1 ≤ leavesOn (sat3BlockP N c) t := by
    intro c
    apply leavesOn_pos_of_readsVar t _ (sat3SignBit N c)
      (sat3_reads_every_signbit N hv hm3 t heval c)
    show decide _ = true
    rw [decide_eq_true_eq]
    exact sat3Bit_clause N c ⟨0, by omega⟩ (sat3V N) (by omega)
  have hsum := sum_leavesOn_le_volume (sat3BlockP N) (sat3BlockP_disjoint N) t
  have hsum2 : (∑ _c : Fin (sat3M N), 1) ≤ ∑ c, leavesOn (sat3BlockP N c) t :=
    Finset.sum_le_sum (fun c _ => hper c)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.mul_one] at hsum2
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.depthBudget_lt_budget
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.kwFind_correct
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.kwSteps_le_depth
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_reads_every_signbit
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_kw_volume_ge
