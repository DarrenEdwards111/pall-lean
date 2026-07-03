import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameBlockMachine

/-!
# N-Frame: the concrete TM δ-table instantiation

The block-machine file supplied the radius-1 locality engine and named the δ-table instantiation as a residue.  This file
does it: a genuine single-tape Turing machine — states `Fin Q`, binary alphabet, transition table `δ`, head with boundary
clamping — encoded into the blockwise model, with the **step correspondence proved**.

  `TMachine` / `TMCfg` / `tmStep` / `tmRun` — the machine: `δ : state × symbol → state × write × direction`
        (direction as `Bool`: `false` = left, `true` = right; moves off the tape clamp).
  `CellView` / `view` / `nextView` — the semantic layer: a cell's view is (symbol, head-flag, present-flag, one-hot
        state); `nextView` is the radius-1 rule at view level (head arrives from left/right neighbours or stays when
        clamped at a boundary, detected by the neighbour's *present* flag).
  `arrives_correct` / `nextView_correct` — **PROVED, the step correspondence**: the view-level rule applied to a cell and
        its neighbours equals the view of the TM-stepped configuration — the Cook–Levin cell-consistency lemma.
  `encodeBlock` / `decodeBlock` / `decode_encode` — **PROVED**: the `Q+3`-bit block encoding of views and its faithful
        decoding (one-hot state decoded by a fold).
  `tmRule` / `tm_encode_step` / `tm_iter_encode` — **PROVED**: the induced blockwise rule satisfies
        `blockStep ∘ encode = encode ∘ tmStep`, iterated to `T` steps.
  `retypeInpCB` / `localMachine_cbudget_cb` — **PROVED**: the constant-or-variable input embedding (the TM's initial
        head/state/present bits are constants — brick 5's `Option` embedding could not produce `true` constants).
  `tm_cbudget` — **PROVED, the headline**: a `Q`-state TM on an `N`-cell tape deciding `f` in `T` steps gives
        `cbudget f ≤ N·(Q+3) + T·(N·(Q+3)·(7·2^{3(Q+3)})) + 1` — polynomial in `N, T` for fixed `Q`: the full
        Cook–Levin `P ⊆ P/poly` bound for a concrete machine model, machine-checked.

## Honest scope

The TM has a binary tape alphabet and an `N`-cell tape (bounded-space runs; time-`T` computations use `N ≥ T`-cell tapes
in the standard way).  The initial-configuration layout is passed as the embedding hypothesis `hinit` (input bits at
symbol positions, constants elsewhere) — instantiating a specific layout is routine.  The RAM residue is unchanged:
`O(log B)` windows via the general local-machine interface.  The open target `NFrameCircuitLowerBoundTarget SAT` is
untouched.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The machine -/

/-- A single-tape Turing machine: `δ state symbol = (state', write, direction)`, direction `false` = left,
`true` = right. -/
structure TMachine (Q : ℕ) where
  δ : Fin Q → Bool → Fin Q × Bool × Bool

/-- A configuration: state, head position, tape. -/
structure TMCfg (Q N : ℕ) where
  state : Fin Q
  head : Fin N
  tape : Fin N → Bool

variable {Q N : ℕ}

/-- Head movement with boundary clamping (`Nat` subtraction clamps at `0`; `min` clamps at `N−1`). -/
def moveVal (d : Bool) (h : ℕ) (N : ℕ) : ℕ := if d then min (h + 1) (N - 1) else h - 1

theorem moveVal_lt (d : Bool) (h : Fin N) : moveVal d h.val N < N := by
  have := h.isLt
  unfold moveVal
  split <;> omega

/-- One TM step. -/
def tmStep (M : TMachine Q) (cfg : TMCfg Q N) : TMCfg Q N :=
  { state := (M.δ cfg.state (cfg.tape cfg.head)).1
    head := ⟨moveVal (M.δ cfg.state (cfg.tape cfg.head)).2.2 cfg.head.val N,
      moveVal_lt _ cfg.head⟩
    tape := Function.update cfg.tape cfg.head (M.δ cfg.state (cfg.tape cfg.head)).2.1 }

/-- `T` TM steps. -/
def tmRun (M : TMachine Q) : ℕ → TMCfg Q N → TMCfg Q N
  | 0, cfg => cfg
  | T + 1, cfg => tmRun M T (tmStep M cfg)

/-! ### The semantic layer: cell views -/

/-- A cell's view: symbol, head-flag, present-flag, one-hot state (at the head cell only). -/
structure CellView (Q : ℕ) where
  sym : Bool
  head : Bool
  present : Bool
  st : Option (Fin Q)

/-- The view of cell `q`. -/
def view (cfg : TMCfg Q N) (q : Fin N) : CellView Q :=
  { sym := cfg.tape q
    head := decide (cfg.head = q)
    present := true
    st := if cfg.head = q then some cfg.state else none }

/-- The view of a missing (out-of-range) cell. -/
def deadView : CellView Q := { sym := false, head := false, present := false, st := none }

/-- The view of a possibly-missing cell. -/
def optView (cfg : TMCfg Q N) : Option (Fin N) → CellView Q
  | none => deadView
  | some q => view cfg q

/-- The direction the head at this view will move (if the head is here). -/
def outDir (M : TMachine Q) (v : CellView Q) : Option Bool :=
  v.st.map fun s => (M.δ s v.sym).2.2

/-- The state the head at this view will carry (if the head is here). -/
def outSt (M : TMachine Q) (v : CellView Q) : Option (Fin Q) :=
  v.st.map fun s => (M.δ s v.sym).1

/-- The symbol this view's cell will hold next (write if the head is here). -/
def outW (M : TMachine Q) (v : CellView Q) : Bool :=
  (v.st.map fun s => (M.δ s v.sym).2.1).getD v.sym

/-- Does the head arrive at this cell — from the left neighbour moving right, the right neighbour moving left, or by
staying when clamped at a boundary (detected by the neighbour's `present` flag)?  Returns the arriving state. -/
def arrives (M : TMachine Q) (Lv Sv Rv : CellView Q) : Option (Fin Q) :=
  if Lv.head = true ∧ outDir M Lv = some true then outSt M Lv
  else if Rv.head = true ∧ outDir M Rv = some false then outSt M Rv
  else if Sv.head = true ∧ ((outDir M Sv = some false ∧ Lv.present = false)
      ∨ (outDir M Sv = some true ∧ Rv.present = false)) then outSt M Sv
  else none

/-- The radius-1 rule at view level. -/
def nextView (M : TMachine Q) (Lv Sv Rv : CellView Q) : CellView Q :=
  { sym := if Sv.head = true then outW M Sv else Sv.sym
    head := (arrives M Lv Sv Rv).isSome
    present := Sv.present
    st := arrives M Lv Sv Rv }

/-! ### The step correspondence, at view level -/

theorem view_st_eq (cfg : TMCfg Q N) (q : Fin N) :
    (view cfg q).st = if cfg.head = q then some cfg.state else none := rfl

/-- **The arrival lemma (proved)**: the head arrives at `q` (with its new state) iff the TM-stepped head is at `q`. -/
theorem arrives_correct (M : TMachine Q) (cfg : TMCfg Q N) (q : Fin N) :
    arrives M (optView cfg (leftOf q)) (view cfg q) (optView cfg (rightOf q))
      = (if (tmStep M cfg).head = q then some (tmStep M cfg).state else none) := by
  have hqlt := q.isLt
  have hhlt := cfg.head.isLt
  -- view evaluation helpers
  have hview_head : ∀ p : Fin N, (view cfg p).head = true ↔ cfg.head = p := by
    intro p
    simp [view]
  have hview_dir : ∀ p : Fin N, cfg.head = p →
      outDir M (view cfg p) = some ((M.δ cfg.state (cfg.tape cfg.head)).2.2) := by
    intro p hp
    subst hp
    simp [outDir, view]
  have hview_dir_none : ∀ p : Fin N, ¬ cfg.head = p → outDir M (view cfg p) = none := by
    intro p hp
    simp [outDir, view, hp]
  have hview_st : ∀ p : Fin N, cfg.head = p →
      outSt M (view cfg p) = some ((M.δ cfg.state (cfg.tape cfg.head)).1) := by
    intro p hp
    subst hp
    simp [outSt, view]
  -- neighbour resolution helpers
  have hLdead : q.val = 0 → optView cfg (leftOf q) = deadView := by
    intro h0
    simp [leftOf, optView, h0]
  have hLview : ¬ q.val = 0 → optView cfg (leftOf q)
      = view cfg ⟨q.val - 1, by omega⟩ := by
    intro h0
    simp [leftOf, optView, h0]
  have hRdead : ¬ q.val + 1 < N → optView cfg (rightOf q) = deadView := by
    intro hN
    simp [rightOf, optView, hN]
  have hRview : ∀ hN : q.val + 1 < N, optView cfg (rightOf q) = view cfg ⟨q.val + 1, hN⟩ := by
    intro hN
    simp [rightOf, optView, hN]
  -- the stepped head, at value level
  have hstep_head : (tmStep M cfg).head.val
      = moveVal (M.δ cfg.state (cfg.tape cfg.head)).2.2 cfg.head.val N := rfl
  have hstep_st : (tmStep M cfg).state = (M.δ cfg.state (cfg.tape cfg.head)).1 := rfl
  by_cases hd : (M.δ cfg.state (cfg.tape cfg.head)).2.2 = true
  · -- direction RIGHT
    by_cases hA : cfg.head.val + 1 = q.val
    · -- arrival from the left neighbour
      have hq0 : ¬ q.val = 0 := by omega
      have hLhead : cfg.head = (⟨q.val - 1, by omega⟩ : Fin N) := Fin.ext (by simp; omega)
      have hG1 : (optView cfg (leftOf q)).head = true
          ∧ outDir M (optView cfg (leftOf q)) = some true := by
        rw [hLview hq0]
        exact ⟨(hview_head _).mpr hLhead, by rw [hview_dir _ hLhead, hd]⟩
      unfold arrives
      rw [if_pos hG1, hLview hq0, hview_st _ hLhead,
        if_pos (Fin.ext (by
          rw [hstep_head]
          unfold moveVal
          rw [if_pos hd]
          omega)), hstep_st]
    · by_cases hD : cfg.head.val = q.val ∧ q.val + 1 = N
      · -- clamped at the right edge: the head stays
        obtain ⟨hhq, hqN⟩ := hD
        have hhq' : cfg.head = q := Fin.ext hhq
        have hqN' : ¬ q.val + 1 < N := by omega
        have hG1 : ¬ ((optView cfg (leftOf q)).head = true
            ∧ outDir M (optView cfg (leftOf q)) = some true) := by
          rintro ⟨hh1, -⟩
          by_cases hq0 : q.val = 0
          · rw [hLdead hq0] at hh1
            exact Bool.noConfusion hh1
          · rw [hLview hq0] at hh1
            have := congrArg Fin.val ((hview_head _).mp hh1)
            try simp at this
            omega
        have hG2 : ¬ ((optView cfg (rightOf q)).head = true
            ∧ outDir M (optView cfg (rightOf q)) = some false) := by
          rintro ⟨hh2, -⟩
          rw [hRdead hqN'] at hh2
          exact Bool.noConfusion hh2
        have hG3 : (view cfg q).head = true
            ∧ ((outDir M (view cfg q) = some false ∧ (optView cfg (leftOf q)).present = false)
              ∨ (outDir M (view cfg q) = some true ∧ (optView cfg (rightOf q)).present = false)) := by
          refine ⟨(hview_head q).mpr hhq', Or.inr ⟨by rw [hview_dir q hhq', hd], ?_⟩⟩
          rw [hRdead hqN']
          rfl
        unfold arrives
        rw [if_neg hG1, if_neg hG2, if_pos hG3, hview_st q hhq',
          if_pos (Fin.ext (by
            rw [hstep_head]
            unfold moveVal
            rw [if_pos hd]
            omega)), hstep_st]
      · -- no arrival at q
        have hG1 : ¬ ((optView cfg (leftOf q)).head = true
            ∧ outDir M (optView cfg (leftOf q)) = some true) := by
          rintro ⟨hh1, -⟩
          by_cases hq0 : q.val = 0
          · rw [hLdead hq0] at hh1
            exact Bool.noConfusion hh1
          · rw [hLview hq0] at hh1
            have := congrArg Fin.val ((hview_head _).mp hh1)
            try simp at this
            omega
        have hG2 : ¬ ((optView cfg (rightOf q)).head = true
            ∧ outDir M (optView cfg (rightOf q)) = some false) := by
          rintro ⟨hh2, hd2⟩
          by_cases hqN : q.val + 1 < N
          · rw [hRview hqN] at hh2 hd2
            have hp := (hview_head _).mp hh2
            rw [hview_dir _ hp, hd] at hd2
            simp at hd2
          · rw [hRdead hqN] at hh2
            exact Bool.noConfusion hh2
        have hG3 : ¬ ((view cfg q).head = true
            ∧ ((outDir M (view cfg q) = some false ∧ (optView cfg (leftOf q)).present = false)
              ∨ (outDir M (view cfg q) = some true ∧ (optView cfg (rightOf q)).present = false))) := by
          rintro ⟨hh3, hcase⟩
          have hp := (hview_head q).mp hh3
          have hpv := congrArg Fin.val hp
          rcases hcase with ⟨hdirF, -⟩ | ⟨-, hpres⟩
          · rw [hview_dir q hp, hd] at hdirF
            simp at hdirF
          · by_cases hqN : q.val + 1 < N
            · rw [hRview hqN] at hpres
              exact Bool.noConfusion hpres
            · exact hD ⟨hpv, by omega⟩
        unfold arrives
        rw [if_neg hG1, if_neg hG2, if_neg hG3,
          if_neg (fun hEq : (tmStep M cfg).head = q => by
            have := congrArg Fin.val hEq
            rw [hstep_head] at this
            unfold moveVal at this
            rw [if_pos hd] at this
            by_cases hcl : cfg.head.val + 1 ≤ N - 1
            · have : cfg.head.val + 1 = q.val := by omega
              exact hA this
            · exact hD ⟨by omega, by omega⟩)]
  · -- direction LEFT
    have hdf : (M.δ cfg.state (cfg.tape cfg.head)).2.2 = false := by
      cases hval : (M.δ cfg.state (cfg.tape cfg.head)).2.2
      · rfl
      · exact absurd hval hd
    by_cases hB : cfg.head.val = q.val + 1
    · -- arrival from the right neighbour
      have hqN : q.val + 1 < N := by omega
      have hRhead : cfg.head = (⟨q.val + 1, hqN⟩ : Fin N) := Fin.ext (by simp; omega)
      have hG1 : ¬ ((optView cfg (leftOf q)).head = true
          ∧ outDir M (optView cfg (leftOf q)) = some true) := by
        rintro ⟨hh1, -⟩
        by_cases hq0 : q.val = 0
        · rw [hLdead hq0] at hh1
          exact Bool.noConfusion hh1
        · rw [hLview hq0] at hh1
          have := congrArg Fin.val ((hview_head _).mp hh1)
          try simp at this
          omega
      have hG2 : (optView cfg (rightOf q)).head = true
          ∧ outDir M (optView cfg (rightOf q)) = some false := by
        rw [hRview hqN]
        exact ⟨(hview_head _).mpr hRhead, by rw [hview_dir _ hRhead, hdf]⟩
      unfold arrives
      rw [if_neg hG1, if_pos hG2, hRview hqN, hview_st _ hRhead,
        if_pos (Fin.ext (by
          rw [hstep_head]
          unfold moveVal
          rw [if_neg (by rw [hdf]; exact Bool.false_ne_true)]
          omega)), hstep_st]
    · by_cases hC : cfg.head.val = q.val ∧ q.val = 0
      · -- clamped at the left edge: the head stays
        obtain ⟨hhq, hq0⟩ := hC
        have hhq' : cfg.head = q := Fin.ext hhq
        have hG1 : ¬ ((optView cfg (leftOf q)).head = true
            ∧ outDir M (optView cfg (leftOf q)) = some true) := by
          rintro ⟨hh1, -⟩
          rw [hLdead hq0] at hh1
          exact Bool.noConfusion hh1
        have hG2 : ¬ ((optView cfg (rightOf q)).head = true
            ∧ outDir M (optView cfg (rightOf q)) = some false) := by
          rintro ⟨hh2, -⟩
          by_cases hqN : q.val + 1 < N
          · rw [hRview hqN] at hh2
            have := congrArg Fin.val ((hview_head _).mp hh2)
            try simp at this
            omega
          · rw [hRdead hqN] at hh2
            exact Bool.noConfusion hh2
        have hG3 : (view cfg q).head = true
            ∧ ((outDir M (view cfg q) = some false ∧ (optView cfg (leftOf q)).present = false)
              ∨ (outDir M (view cfg q) = some true ∧ (optView cfg (rightOf q)).present = false)) := by
          refine ⟨(hview_head q).mpr hhq', Or.inl ⟨by rw [hview_dir q hhq', hdf], ?_⟩⟩
          rw [hLdead hq0]
          rfl
        unfold arrives
        rw [if_neg hG1, if_neg hG2, if_pos hG3, hview_st q hhq',
          if_pos (Fin.ext (by
            rw [hstep_head]
            unfold moveVal
            rw [if_neg (by rw [hdf]; exact Bool.false_ne_true)]
            omega)), hstep_st]
      · -- no arrival at q
        have hG1 : ¬ ((optView cfg (leftOf q)).head = true
            ∧ outDir M (optView cfg (leftOf q)) = some true) := by
          rintro ⟨hh1, hd1⟩
          by_cases hq0 : q.val = 0
          · rw [hLdead hq0] at hh1
            exact Bool.noConfusion hh1
          · rw [hLview hq0] at hh1 hd1
            have hp := (hview_head _).mp hh1
            rw [hview_dir _ hp, hdf] at hd1
            simp at hd1
        have hG2 : ¬ ((optView cfg (rightOf q)).head = true
            ∧ outDir M (optView cfg (rightOf q)) = some false) := by
          rintro ⟨hh2, -⟩
          by_cases hqN : q.val + 1 < N
          · rw [hRview hqN] at hh2
            have := congrArg Fin.val ((hview_head _).mp hh2)
            try simp at this
            omega
          · rw [hRdead hqN] at hh2
            exact Bool.noConfusion hh2
        have hG3 : ¬ ((view cfg q).head = true
            ∧ ((outDir M (view cfg q) = some false ∧ (optView cfg (leftOf q)).present = false)
              ∨ (outDir M (view cfg q) = some true ∧ (optView cfg (rightOf q)).present = false))) := by
          rintro ⟨hh3, hcase⟩
          have hp := (hview_head q).mp hh3
          have hpv := congrArg Fin.val hp
          rcases hcase with ⟨-, hpres⟩ | ⟨hdirT, -⟩
          · by_cases hq0 : q.val = 0
            · exact hC ⟨hpv, hq0⟩
            · rw [hLview hq0] at hpres
              exact Bool.noConfusion hpres
          · rw [hview_dir q hp, hdf] at hdirT
            simp at hdirT
        unfold arrives
        rw [if_neg hG1, if_neg hG2, if_neg hG3,
          if_neg (fun hEq : (tmStep M cfg).head = q => by
            have := congrArg Fin.val hEq
            rw [hstep_head] at this
            unfold moveVal at this
            rw [if_neg (by rw [hdf]; exact Bool.false_ne_true)] at this
            rcases Nat.eq_zero_or_pos cfg.head.val with hz | hz
            · exact hC ⟨by omega, by omega⟩
            · exact hB (by omega))]

/-- **The view-level step correspondence (proved)**: the radius-1 rule at a cell and its neighbours computes the view of
the TM-stepped configuration — the Cook–Levin cell-consistency lemma. -/
theorem nextView_correct (M : TMachine Q) (cfg : TMCfg Q N) (q : Fin N) :
    nextView M (optView cfg (leftOf q)) (view cfg q) (optView cfg (rightOf q))
      = view (tmStep M cfg) q := by
  have hext : ∀ a b : CellView Q, a.sym = b.sym → a.head = b.head → a.present = b.present →
      a.st = b.st → a = b := by
    rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h1 h2 h3 h4
    simp_all
  have harr := arrives_correct M cfg q
  apply hext
  · -- the symbol
    show (if (view cfg q).head = true then outW M (view cfg q) else (view cfg q).sym)
        = (view (tmStep M cfg) q).sym
    by_cases hh : cfg.head = q
    · rw [if_pos (by simp [view, hh])]
      show outW M (view cfg q) = (tmStep M cfg).tape q
      rw [outW, view_st_eq, if_pos hh]
      show ((some cfg.state).map fun s => (M.δ s (view cfg q).sym).2.1).getD (view cfg q).sym
        = Function.update cfg.tape cfg.head (M.δ cfg.state (cfg.tape cfg.head)).2.1 q
      simp only [Option.map_some, Option.getD_some]
      rw [show (view cfg q).sym = cfg.tape q from rfl, ← hh, Function.update_self]
    · rw [if_neg (by simp [view, hh])]
      show cfg.tape q
        = Function.update cfg.tape cfg.head (M.δ cfg.state (cfg.tape cfg.head)).2.1 q
      rw [Function.update_of_ne (fun h => hh h.symm)]
  · -- the head flag
    show (arrives M (optView cfg (leftOf q)) (view cfg q) (optView cfg (rightOf q))).isSome
        = (view (tmStep M cfg) q).head
    rw [harr]
    show _ = decide ((tmStep M cfg).head = q)
    by_cases hs : (tmStep M cfg).head = q
    · simp [hs]
    · simp [hs]
  · rfl
  · -- the state
    show arrives M (optView cfg (leftOf q)) (view cfg q) (optView cfg (rightOf q))
        = (view (tmStep M cfg) q).st
    rw [harr]
    rfl

/-! ### The bit-level encoding -/

/-- Encode a view as a `Q+3`-bit block: bit 0 = symbol, bit 1 = head, bit 2 = present, bits `3+s` = one-hot state. -/
def encodeBlock (v : CellView Q) (b : Fin (Q + 3)) : Bool :=
  if b.val = 0 then v.sym
  else if b.val = 1 then v.head
  else if b.val = 2 then v.present
  else if hb : 3 ≤ b.val then decide (v.st = some ⟨b.val - 3, by have := b.isLt; omega⟩)
  else false

/-- Decode a `Q+3`-bit block into a view (one-hot state decoded by a right fold). -/
def decodeBlock (blk : Fin (Q + 3) → Bool) : CellView Q :=
  { sym := blk ⟨0, by omega⟩
    head := blk ⟨1, by omega⟩
    present := blk ⟨2, by omega⟩
    st := (List.finRange Q).foldr
      (fun s acc => if blk ⟨s.val + 3, by have := s.isLt; omega⟩ = true then some s else acc)
      none }

theorem foldr_onehot_none {Q' : ℕ} (p : Fin Q' → Bool) (h : ∀ s, p s = false)
    (l : List (Fin Q')) :
    l.foldr (fun s acc => if p s = true then some s else acc) none = none := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [h a, ih]

theorem foldr_onehot_some {Q' : ℕ} (p : Fin Q' → Bool) (s0 : Fin Q')
    (h : ∀ s, p s = true ↔ s = s0) (l : List (Fin Q')) (hmem : s0 ∈ l) :
    l.foldr (fun s acc => if p s = true then some s else acc) none = some s0 := by
  induction l with
  | nil => exact absurd hmem List.not_mem_nil
  | cons a l ih =>
    by_cases ha : a = s0
    · subst ha
      simp [(h a).mpr rfl]
    · have hpa : p a = false := by
        cases hp : p a
        · rfl
        · exact absurd ((h a).mp hp) ha
      have hmem' : s0 ∈ l := by
        rcases List.mem_cons.mp hmem with h' | h'
        · exact absurd h'.symm ha
        · exact h'
      simp [hpa, ih hmem']

/-- **Decoding is faithful (proved)**: `decodeBlock ∘ encodeBlock = id`. -/
theorem encodeBlock_state (v : CellView Q) (s : Fin Q) :
    encodeBlock v ⟨s.val + 3, by have := s.isLt; omega⟩ = decide (v.st = some s) := by
  unfold encodeBlock
  rw [if_neg (show ¬(s.val + 3 = 0) by omega), if_neg (show ¬(s.val + 3 = 1) by omega),
    if_neg (show ¬(s.val + 3 = 2) by omega), dif_pos (show 3 ≤ s.val + 3 by omega)]
  rw [show (⟨(⟨s.val + 3, by have := s.isLt; omega⟩ : Fin (Q + 3)).val - 3,
      by have := s.isLt; omega⟩ : Fin Q) = s from Fin.ext (show s.val + 3 - 3 = s.val by omega)]

theorem decode_encode (v : CellView Q) : decodeBlock (encodeBlock v) = v := by
  have hst_fold : (List.finRange Q).foldr
      (fun s acc => if encodeBlock v ⟨s.val + 3, by have := s.isLt; omega⟩ = true
        then some s else acc) none = v.st := by
    cases hst : v.st with
    | none =>
      apply foldr_onehot_none
      intro s
      rw [encodeBlock_state, hst]
      simp
    | some s0 =>
      apply foldr_onehot_some _ s0 _ _ (List.mem_finRange s0)
      intro s
      rw [encodeBlock_state, hst]
      simp only [decide_eq_true_eq, Option.some_inj]
      exact eq_comm
  obtain ⟨vs, vh, vp, vst⟩ := v
  unfold decodeBlock
  simp only [CellView.mk.injEq]
  exact ⟨rfl, rfl, rfl, hst_fold⟩

/-! ### The induced blockwise rule and the encoded step -/

/-- The TM's blockwise rule: decode the three blocks, apply the view rule, re-encode. -/
def tmRule (M : TMachine Q) (L S R : Fin (Q + 3) → Bool) : Fin (Q + 3) → Bool :=
  encodeBlock (nextView M (decodeBlock L) (decodeBlock S) (decodeBlock R))

/-- The configuration encoding: cell blocks laid out flat. -/
def tmEncode (cfg : TMCfg Q N) : Fin (N * (Q + 3)) → Bool :=
  fun j => encodeBlock (view cfg (cellOf j)) (bitOf j)

theorem cellOf_cellIdx (q : Fin N) (b : Fin (Q + 3)) :
    cellOf (cellIdx (c := Q + 3) q b) = q := by
  apply Fin.ext
  show (q.val * (Q + 3) + b.val) / (Q + 3) = q.val
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < Q + 3),
    Nat.div_eq_of_lt b.isLt]
  omega

theorem bitOf_cellIdx (q : Fin N) (b : Fin (Q + 3)) :
    bitOf (cellIdx (c := Q + 3) q b) = b := by
  apply Fin.ext
  show (q.val * (Q + 3) + b.val) % (Q + 3) = b.val
  rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt b.isLt

theorem blockOf_tmEncode (cfg : TMCfg Q N) (q : Fin N) :
    blockOf (tmEncode cfg) q = encodeBlock (view cfg q) := by
  funext b
  show tmEncode cfg (cellIdx q b) = _
  unfold tmEncode
  rw [cellOf_cellIdx, bitOf_cellIdx]

theorem encodeBlock_dead : encodeBlock (deadView (Q := Q)) = fun _ => false := by
  funext b
  unfold encodeBlock deadView
  split_ifs <;> simp

theorem blockOpt_tmEncode (cfg : TMCfg Q N) (o : Option (Fin N)) :
    blockOpt (tmEncode cfg) o = encodeBlock (optView cfg o) := by
  cases o with
  | none =>
    show (fun _ => false) = encodeBlock deadView
    rw [encodeBlock_dead]
  | some q => exact blockOf_tmEncode cfg q

/-- **The encoded step correspondence (proved)**: the blockwise machine with the TM's rule steps exactly as the TM. -/
theorem tm_encode_step (M : TMachine Q) (cfg : TMCfg Q N) :
    (fun j => blockStep (tmRule M) j (tmEncode cfg)) = tmEncode (tmStep M cfg) := by
  funext j
  show tmRule M (blockOpt (tmEncode cfg) (leftOf (cellOf j)))
      (blockOf (tmEncode cfg) (cellOf j))
      (blockOpt (tmEncode cfg) (rightOf (cellOf j))) (bitOf j)
    = encodeBlock (view (tmStep M cfg) (cellOf j)) (bitOf j)
  rw [blockOpt_tmEncode, blockOf_tmEncode, blockOpt_tmEncode]
  unfold tmRule
  rw [decode_encode, decode_encode, decode_encode, nextView_correct]

/-- **Iterated (proved)**: `T` blockwise steps encode `T` TM steps. -/
theorem tm_iter_encode (M : TMachine Q) :
    ∀ (T : ℕ) (cfg : TMCfg Q N),
      iterStep (fun j => blockStep (tmRule M) j) T (tmEncode cfg)
        = tmEncode (tmRun M T cfg) := by
  intro T
  induction T with
  | zero => intro cfg; rfl
  | succ T ih =>
    intro cfg
    show iterStep (fun j => blockStep (tmRule M) j) T
        (fun j => blockStep (tmRule M) j (tmEncode cfg)) = _
    rw [tm_encode_step]
    exact ih (tmStep M cfg)

/-! ### Constant-or-variable input embedding -/

/-- Retype through a constant-or-variable embedding: each workspace bit is an input variable or a fixed constant. -/
def retypeInpCB {B n : ℕ} (inp : Fin B → Sum (Fin n) Bool) : CGate B → CGate n
  | .var j => Sum.elim CGate.var CGate.cst (inp j)
  | .cst b => .cst b
  | .un op j => .un op j
  | .bin op j k => .bin op j k

theorem runFrom_retypeInpCB {B n : ℕ} (inp : Fin B → Sum (Fin n) Bool) (x : Fin n → Bool) :
    ∀ (c : List (CGate B)) (vals : List Bool),
      runFrom x vals (c.map (retypeInpCB inp))
        = runFrom (fun j => Sum.elim x id (inp j)) vals c := by
  intro c
  induction c with
  | nil => intro vals; rfl
  | cons g gs ih =>
    intro vals
    have hgate : evalGate x vals (retypeInpCB inp g)
        = evalGate (fun j => Sum.elim x id (inp j)) vals g := by
      cases g with
      | var j => cases hj : inp j <;> simp [retypeInpCB, evalGate, hj]
      | cst b => rfl
      | un op j => rfl
      | bin op j k => rfl
    show runFrom x (vals ++ [evalGate x vals (retypeInpCB inp g)]) (gs.map (retypeInpCB inp)) = _
    rw [hgate]
    exact ih _

/-- The local-machine circuit bound with a constant-or-variable embedding. -/
theorem localMachine_cbudget_cb {B n : ℕ} (S : Fin B → (Fin B → Bool) → Bool)
    (W : Fin B → List (Fin B)) (k : ℕ) (hW : ∀ i, (W i).length ≤ k)
    (hloc : ∀ i x y, (∀ j ∈ W i, x j = y j) → S i x = S i y)
    (T : ℕ) (out : Fin B) (inp : Fin B → Sum (Fin n) Bool) (f : (Fin n → Bool) → Bool)
    (hdec : ∀ x : Fin n → Bool, iterStep S T (fun j => Sum.elim x id (inp j)) out = f x) :
    cbudget f ≤ B + T * (B * (7 * 2 ^ k)) + 1 := by
  obtain ⟨cs, hcomp, hc0, hsz⟩ := local_machine_circuits S W k hW hloc
  have hs0 : 0 < 7 * 2 ^ k := by positivity
  have hmc := machineCircuit_computes cs S (7 * 2 ^ k) T out hsz hc0 hcomp hs0
  have hcomputes : computes ((machineCircuit cs (7 * 2 ^ k) T out).map (retypeInpCB inp)) f := by
    intro x
    show (runFrom x [] ((machineCircuit cs (7 * 2 ^ k) T out).map (retypeInpCB inp))).getD
        (((machineCircuit cs (7 * 2 ^ k) T out).map (retypeInpCB inp)).length - 1) false = f x
    rw [List.length_map, runFrom_retypeInpCB inp x]
    have hmc2 := hmc (fun j => Sum.elim x id (inp j))
    unfold output at hmc2
    rw [hmc2]
    exact hdec x
  have hmem : cbudget f ≤ ((machineCircuit cs (7 * 2 ^ k) T out).map (retypeInpCB inp)).length :=
    Nat.sInf_le ⟨_, hcomputes, rfl⟩
  have hlen : ((machineCircuit cs (7 * 2 ^ k) T out).map (retypeInpCB inp)).length
      = B + T * (B * (7 * 2 ^ k)) + 1 := by
    rw [List.length_map, machineCircuit_length cs (7 * 2 ^ k) T out hsz]
  omega

/-! ### The headline: the concrete-TM Cook–Levin bound -/

/-- **The concrete-TM circuit bound (proved).**  A `Q`-state TM on an `N`-cell tape, with initial configuration laid out
by the embedding `inp` (`hinit`), deciding `f` in `T` steps at tape cell `outCell` (`hout`), gives

  `cbudget f ≤ N·(Q+3) + T·(N·(Q+3)·(7·2^{3(Q+3)})) + 1`

— polynomial in `N` and `T` for fixed `Q`: the Cook–Levin `P ⊆ P/poly` bound for a concrete machine, machine-checked. -/
theorem tm_cbudget {n : ℕ} (M : TMachine Q) (T : ℕ)
    (cfg0 : (Fin n → Bool) → TMCfg Q N)
    (inp : Fin (N * (Q + 3)) → Sum (Fin n) Bool)
    (hinit : ∀ x, tmEncode (cfg0 x) = fun j => Sum.elim x id (inp j))
    (outCell : Fin N) (f : (Fin n → Bool) → Bool)
    (hout : ∀ x, (tmRun M T (cfg0 x)).tape outCell = f x) :
    cbudget f ≤ N * (Q + 3) + T * (N * (Q + 3) * (7 * 2 ^ (3 * (Q + 3)))) + 1 := by
  refine localMachine_cbudget_cb (fun j => blockStep (tmRule M) j) blockWindow (3 * (Q + 3))
    blockWindow_length (fun j x y h => blockStep_local (tmRule M) j x y h) T
    (cellIdx outCell ⟨0, by omega⟩) inp f ?_
  intro x
  rw [← hinit x, tm_iter_encode]
  show tmEncode (tmRun M T (cfg0 x)) (cellIdx outCell ⟨0, by omega⟩) = f x
  unfold tmEncode
  rw [cellOf_cellIdx, bitOf_cellIdx]
  show encodeBlock (view (tmRun M T (cfg0 x)) outCell) ⟨0, by omega⟩ = f x
  unfold encodeBlock
  rw [if_pos rfl]
  exact hout x

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.arrives_correct
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.tm_encode_step
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.tm_cbudget
