import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitWriteFamily

/-!
# Cook–Levin M2 emitter — THE DYNAMICS FAMILY (option (i): padded left loop)

The dynamics family loops `t < B`, `q < card`, `p ≤ P`, `b ∈ {false, true}` — TWO implication
windows per tuple (state conclusion + head conclusion).  The move for `(q, b)` is a MACHINE
CONSTANT, so the head body is meta-selected per `(q, b)`: stay/right/reset heads fuse with the
state window in the standard per-`p` round; the LEFT mover's head window is emitted by the
SHIFTED body (guards at `k + 1`, conclusion at `k`), which at the stale bound `P + 1` covers
the family's `p = 1..P` plus ONE spurious window at `p = P + 1` (harmless: `fullAssign` keeps
the head `≤ P` — the equisatisfiability packaging is E6 glue).  The missing `p = 0` left head
window has ALL-CONSTANT position coordinates, so a second grand loop at `P := 0` (the one-shot
chain — the brick-47 generic `q`-chain, bound armed at `1`) emits exactly one such window per
`(t, left-mover)`.  Both loops are `rep_qcFamily_run` instantiations.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitDynFamily

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinWrite
open PallLean.Paper93.DeepMath.PathB.CookLevinConverse
open PallLean.Paper93.DeepMath.PathB.CookLevinAssembly
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTemplates
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRepP
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPairT
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterRow
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterGrand
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTriangleHead
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSnoc6
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitHeadFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCellFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitWriteFamily

/-! ## The offset live splice and the five dynamics row bodies -/

/-- The live-source splice at offset `1`: emits `encodeNat (k + 1)`. -/
def sJ1 : List L3Instr := bitsI3 [true] ++ sJ

/-- The state-conclusion dynamics window (`qc` = the `δ`-next state index, a constant). -/
def dynStateRow3 (qi qc : ℕ) (b : Bool) : List L3Instr :=
  winPre3 qi b ++ (sA1 ++ (bitsI3 (encodeNat qc) ++ bitsI3 [true, true, false, true]))

theorem dynStateRow3_prog3Out (qi qc : ℕ) (b : Bool) (t c k : ℕ) :
    prog3Out (dynStateRow3 qi qc b) t c k
      = encodeClause' (implClause (stateVar t qi, true) (headVar t k, true)
          (cellVar t k, b) (stateVar (t + 1) qc, true)) := by
  rw [encodeClause'_implWindow, encodeLit'_stateVar, dynStateRow3, sA1]
  simp only [prog3Out_append, winPre3_prog3Out, prog3Out_bits, prog3Out_sA]
  simp [encodeNat, List.replicate_succ, List.append_assoc]

/-- The stay-mover head window: conclusion `headVar (t+1) k`. -/
def dynHeadStayRow3 (qi : ℕ) (b : Bool) : List L3Instr :=
  winPre3 qi b ++ (sA1 ++ (sJ ++ bitsI3 [true, false, true]))

theorem dynHeadStayRow3_prog3Out (qi : ℕ) (b : Bool) (t c k : ℕ) :
    prog3Out (dynHeadStayRow3 qi b) t c k
      = encodeClause' (implClause (stateVar t qi, true) (headVar t k, true)
          (cellVar t k, b) (headVar (t + 1) k, true)) := by
  rw [encodeClause'_implWindow, encodeLit'_headVar, dynHeadStayRow3, sA1]
  simp only [prog3Out_append, winPre3_prog3Out, prog3Out_bits, prog3Out_sA, prog3Out_sJ]
  simp [encodeNat, List.replicate_succ, List.append_assoc]

/-- The right-mover head window: conclusion `headVar (t+1) (k+1)`. -/
def dynHeadRightRow3 (qi : ℕ) (b : Bool) : List L3Instr :=
  winPre3 qi b ++ (sA1 ++ (sJ1 ++ bitsI3 [true, false, true]))

theorem dynHeadRightRow3_prog3Out (qi : ℕ) (b : Bool) (t c k : ℕ) :
    prog3Out (dynHeadRightRow3 qi b) t c k
      = encodeClause' (implClause (stateVar t qi, true) (headVar t k, true)
          (cellVar t k, b) (headVar (t + 1) (k + 1), true)) := by
  rw [encodeClause'_implWindow, encodeLit'_headVar, dynHeadRightRow3, sA1, sJ1]
  simp only [prog3Out_append, winPre3_prog3Out, prog3Out_bits, prog3Out_sA, prog3Out_sJ]
  simp [encodeNat, List.replicate_succ, List.append_assoc]

/-- The reset-mover head window: conclusion `headVar (t+1) 0`. -/
def dynHeadResetRow3 (qi : ℕ) (b : Bool) : List L3Instr :=
  winPre3 qi b ++ (sA1 ++ bitsI3 [false, true, false, true])

theorem dynHeadResetRow3_prog3Out (qi : ℕ) (b : Bool) (t c k : ℕ) :
    prog3Out (dynHeadResetRow3 qi b) t c k
      = encodeClause' (implClause (stateVar t qi, true) (headVar t k, true)
          (cellVar t k, b) (headVar (t + 1) 0, true)) := by
  rw [encodeClause'_implWindow, encodeLit'_headVar, dynHeadResetRow3, sA1]
  simp only [prog3Out_append, winPre3_prog3Out, prog3Out_bits, prog3Out_sA]
  simp [encodeNat, List.replicate_succ, List.append_assoc]

/-- The SHIFTED guard prefix: head/cell guards at `k + 1` (the left mover's padded loop). -/
def winPreL3 (qi : ℕ) (b : Bool) : List L3Instr :=
  bitsI3 [true, true, true, true, false] ++ (sA ++ (bitsI3 (encodeNat qi)
    ++ (bitsI3 [true, true, false, false] ++ (sA ++ (sJ1
      ++ (bitsI3 [true, false, false] ++ (sA ++ (sJ1 ++ bitsI3 [false, !b]))))))))

/-- The left-mover head window, shifted: guards at `k + 1`, conclusion `headVar (t+1) k`. -/
def dynHeadLeftRow3 (qi : ℕ) (b : Bool) : List L3Instr :=
  winPreL3 qi b ++ (sA1 ++ (sJ ++ bitsI3 [true, false, true]))

theorem dynHeadLeftRow3_prog3Out (qi : ℕ) (b : Bool) (t c k : ℕ) :
    prog3Out (dynHeadLeftRow3 qi b) t c k
      = encodeClause' (implClause (stateVar t qi, true) (headVar t (k + 1), true)
          (cellVar t (k + 1), b) (headVar (t + 1) k, true)) := by
  rw [encodeClause'_implWindow, encodeLit'_headVar, dynHeadLeftRow3, winPreL3, sA1, sJ1]
  simp only [prog3Out_append, prog3Out_bits, prog3Out_sA, prog3Out_sJ]
  simp [encodeNat, List.replicate_succ, List.append_assoc]

/-- The left-mover's `p = 0` head window: ALL position coordinates constant `0` —
one clause per `(t, q, b)`, emitted by the one-shot chain. -/
def leftHead0Body (qi : ℕ) (b : Bool) : List L3Instr :=
  (bitsI3 [true, true, true, true, false] ++ (sA ++ (bitsI3 (encodeNat qi)
    ++ (bitsI3 [true, true, false, false] ++ (sA ++ (bitsI3 [false]
      ++ (bitsI3 [true, false, false] ++ (sA ++ (bitsI3 [false] ++ bitsI3 [false, !b])))))))))
  ++ (sA1 ++ (bitsI3 [false] ++ bitsI3 [true, false, true]))

theorem leftHead0_prog3Out (qi : ℕ) (b : Bool) (t c k : ℕ) :
    prog3Out (leftHead0Body qi b) t c k
      = encodeClause' (implClause (stateVar t qi, true) (headVar t 0, true)
          (cellVar t 0, b) (headVar (t + 1) 0, true)) := by
  rw [encodeClause'_implWindow, encodeLit'_headVar, leftHead0Body, sA1]
  simp only [prog3Out_append, prog3Out_bits, prog3Out_sA]
  simp [encodeNat, List.replicate_succ, List.append_assoc]

/-! ## The move meta-selector

The move for `(q, b)` is a machine constant (`Move := Fin 4`; halting states self-loop, code
`2` = stay).  `mvN`/`nsN` are the ℕ-indexed total forms the chain bodies read. -/

/-- The move code at `(q̂, b)`: `0` left, `1` right, `2` stay (and halt), `3` reset. -/
noncomputable def mvN (M : Machine) (qi : ℕ) (b : Bool) : ℕ :=
  if h : qi < Fintype.card M.State then
    if M.halt ((Fintype.equivFin M.State).symm ⟨qi, h⟩) then 2
    else ((M.δ ((Fintype.equivFin M.State).symm ⟨qi, h⟩) b).2.2).val
  else 2

/-- The `δ`-next state index at `(q̂, b)` (head-independent). -/
noncomputable def nsN (M : Machine) (qi : ℕ) (b : Bool) : ℕ :=
  if h : qi < Fintype.card M.State then nextStateIdx M ⟨qi, h⟩ 0 b else 0

theorem mvN_lt (M : Machine) (qi : ℕ) (b : Bool) : mvN M qi b < 4 := by
  rw [mvN]
  split
  · split
    · omega
    · exact Fin.isLt _
  · omega

theorem nsN_eq (M : Machine) (q : Fin (Fintype.card M.State)) (p : ℕ) (b : Bool) :
    nsN M q.val b = nextStateIdx M q p b := by
  rw [nsN, dif_pos q.isLt]
  exact nextStateIdx_head_independent M q b 0 p

/-- **The move code reads `nextHead`**: each code value pins the head map uniformly in `p`. -/
theorem nextHead_of_mv (M : Machine) (q : Fin (Fintype.card M.State)) (b : Bool) (p : ℕ) :
    (mvN M q.val b = 0 → nextHead M q p b = p - 1)
    ∧ (mvN M q.val b = 1 → nextHead M q p b = p + 1)
    ∧ (mvN M q.val b = 2 → nextHead M q p b = p)
    ∧ (mvN M q.val b = 3 → nextHead M q p b = 0) := by
  simp only [mvN, dif_pos q.isLt, Fin.eta, nextHead, stepStateHead]
  by_cases hh : M.halt ((Fintype.equivFin M.State).symm q) = true
  · simp [hh]
  · simp only [hh, Bool.false_eq_true, if_false]
    generalize (M.δ ((Fintype.equivFin M.State).symm q) b).2.2 = m
    fin_cases m <;> simp [moveHead]

/-- The `p = 0` left head window concludes at `0` (ℕ-subtraction floor). -/
theorem nextHead_left_zero (M : Machine) (q : Fin (Fintype.card M.State)) (b : Bool)
    (h0 : mvN M q.val b = 0) : nextHead M q 0 b = 0 := by
  rw [(nextHead_of_mv M q b 0).1 h0]

/-! ## The chain bodies -/

/-- The head body per `(q̂, b)`, selected by the move code. -/
noncomputable def dynHeadSel (M : Machine) (qi : ℕ) (b : Bool) : List L3Instr :=
  if mvN M qi b = 0 then dynHeadLeftRow3 qi b
  else if mvN M qi b = 1 then dynHeadRightRow3 qi b
  else if mvN M qi b = 2 then dynHeadStayRow3 qi b
  else dynHeadResetRow3 qi b

/-- The per-`(q̂, b)` fused body: state window + selected head window. -/
noncomputable def dynQB (M : Machine) (qi : ℕ) (b : Bool) : List L3Instr :=
  dynStateRow3 qi (nsN M qi b) b ++ dynHeadSel M qi b

/-- The dynamics `q`-chain bodies: both `b` guards fused per round. -/
noncomputable def dynBodies (M : Machine) (qi : ℕ) : List L3Instr :=
  dynQB M qi false ++ dynQB M qi true

/-- The one-shot chain's per-`(q̂, b)` body: the `p = 0` window for left movers, else empty. -/
noncomputable def leftSel (M : Machine) (qi : ℕ) (b : Bool) : List L3Instr :=
  if mvN M qi b = 0 then leftHead0Body qi b else []

/-- The one-shot chain bodies. -/
noncomputable def leftBodies (M : Machine) (qi : ℕ) : List L3Instr :=
  leftSel M qi false ++ leftSel M qi true

/-! ## Per-round characterizations -/

theorem dynBodies_prog3Out (M : Machine) (qi t c k : ℕ) :
    prog3Out (dynBodies M qi) t c k
      = prog3Out (dynQB M qi false) t c k ++ prog3Out (dynQB M qi true) t c k := by
  rw [dynBodies, prog3Out_append]

theorem leftBodies_prog3Out (M : Machine) (qi t c k : ℕ) :
    prog3Out (leftBodies M qi) t c k
      = prog3Out (leftSel M qi false) t c k ++ prog3Out (leftSel M qi true) t c k := by
  rw [leftBodies, prog3Out_append]

/-- **The fused round IS the dynamics clause pair** — for non-left movers exactly the family's
`dynamicsClause M t q k b`; for the left mover the state window at `p = k` plus the family's
HEAD member at `p = k + 1` (its conclusion `nextHead M q (k+1) b = k`). -/
theorem dynQB_prog3Out (M : Machine) (q : Fin (Fintype.card M.State)) (b : Bool) (t c k : ℕ) :
    (mvN M q.val b ≠ 0 ∧ prog3Out (dynQB M q.val b) t c k
        = ((dynamicsClause M t q k b).map encodeClause').flatten)
    ∨ (mvN M q.val b = 0 ∧ prog3Out (dynQB M q.val b) t c k
        = encodeClause' (implClause (stateVar t q.val, true) (headVar t k, true)
            (cellVar t k, b) (stateVar (t + 1) (nextStateIdx M q k b), true))
          ++ encodeClause' (implClause (stateVar t q.val, true) (headVar t (k + 1), true)
              (cellVar t (k + 1), b) (headVar (t + 1) (nextHead M q (k + 1) b), true))) := by
  by_cases h0 : mvN M q.val b = 0
  · refine Or.inr ⟨h0, ?_⟩
    rw [dynQB, prog3Out_append, dynStateRow3_prog3Out, nsN_eq M q k b, dynHeadSel,
      if_pos h0, dynHeadLeftRow3_prog3Out,
      show nextHead M q (k + 1) b = k from by rw [(nextHead_of_mv M q b (k + 1)).1 h0]; omega]
  · refine Or.inl ⟨h0, ?_⟩
    rw [dynQB, prog3Out_append, dynStateRow3_prog3Out, nsN_eq M q k b, dynHeadSel, if_neg h0]
    by_cases h1 : mvN M q.val b = 1
    · rw [if_pos h1, dynHeadRightRow3_prog3Out]
      simp [dynamicsClause, (nextHead_of_mv M q b k).2.1 h1]
    · rw [if_neg h1]
      by_cases h2 : mvN M q.val b = 2
      · rw [if_pos h2, dynHeadStayRow3_prog3Out]
        simp [dynamicsClause, (nextHead_of_mv M q b k).2.2.1 h2]
      · have h3 : mvN M q.val b = 3 := by have := mvN_lt M q.val b; omega
        rw [if_neg h2, dynHeadResetRow3_prog3Out]
        simp [dynamicsClause, (nextHead_of_mv M q b k).2.2.2 h3]

/-- **The one-shot round IS the missing `p = 0` left head window** — the family's head member
of `dynamicsClause M t q 0 b` for left movers, empty otherwise. -/
theorem leftSel_prog3Out (M : Machine) (q : Fin (Fintype.card M.State)) (b : Bool) (t c k : ℕ) :
    (mvN M q.val b = 0 ∧ prog3Out (leftSel M q.val b) t c k
        = encodeClause' (implClause (stateVar t q.val, true) (headVar t 0, true)
            (cellVar t 0, b) (headVar (t + 1) (nextHead M q 0 b), true)))
    ∨ (mvN M q.val b ≠ 0 ∧ prog3Out (leftSel M q.val b) t c k = []) := by
  by_cases h0 : mvN M q.val b = 0
  · exact Or.inl ⟨h0, by
      rw [leftSel, if_pos h0, leftHead0_prog3Out, nextHead_left_zero M q b h0]⟩
  · exact Or.inr ⟨h0, by rw [leftSel, if_neg h0]; rfl⟩

/-- A bound-`1` pass loops exactly once. -/
theorem loop3Out_one (body : List L3Instr) (a c : ℕ) :
    loop3Out body a c 1 = prog3Out body a c 0 := by
  simp [loop3Out, loop3OutN]

/-! ## The two grand loops -/

/-- **Loop A**: the dynamics `q`-chain over all states, `B` grand rounds at the stale bound
`P + 1` — per round `k ≤ P`: state windows at `p = k` for all `(q, b)`; head windows at `p = k`
for non-left movers and at `p = k + 1` for left movers (so the left head windows sweep
`p = 1..P+1`: the family's `1..P` plus the harmless spurious `P + 1`). -/
theorem rep_dynFamily_run (M : Machine) (B P CB C1 C2 NV : ℕ)
    (hCB : P < CB) (hC2 : P < C2) (hNV : P < NV) (hBC1 : B ≤ C1) (out : List Bool) :
    run (repMachine (qcMachine (dynBodies M) 0 (Fintype.card M.State)))
      (repRounds (fun t =>
        qcClock (dynBodies M) B P CB C1 C2 NV t 0 (Fintype.card M.State)
          (out ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) t).length) B + (4 * B + 4))
      (init (repMachine (qcMachine (dynBodies M) 0 (Fintype.card M.State)))
        (cntT B 0 ++ (unaryD P ++ (jT CB (P + 1) ++ (jT C1 0 ++ (jT C2 1 ++ (jT NV 0
          ++ encodeD out)))))))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD P ++ (jT CB (P + 1) ++ (jT C1 B ++ (jT C2 1 ++ (jT NV 0
            ++ encodeD (out ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) B))))))⟩ :=
  rep_qcFamily_run (dynBodies M) (Fintype.card M.State) B P CB C1 C2 NV hCB hC2 hNV hBC1 out

/-- **Loop B**: the one-shot chain (`P := 0` — bound armed at `1`, each pass loops once),
`B` grand rounds — per round exactly one `p = 0` left head window per left `(q, b)`. -/
theorem rep_dynHead0_run (M : Machine) (B CB C1 C2 NV : ℕ)
    (hCB : 0 < CB) (hC2 : 0 < C2) (hNV : 0 < NV) (hBC1 : B ≤ C1) (out : List Bool) :
    run (repMachine (qcMachine (leftBodies M) 0 (Fintype.card M.State)))
      (repRounds (fun t =>
        qcClock (leftBodies M) B 0 CB C1 C2 NV t 0 (Fintype.card M.State)
          (out ++ qcEmitOut (leftBodies M) 0 (Fintype.card M.State) t).length) B + (4 * B + 4))
      (init (repMachine (qcMachine (leftBodies M) 0 (Fintype.card M.State)))
        (cntT B 0 ++ (unaryD 0 ++ (jT CB 1 ++ (jT C1 0 ++ (jT C2 1 ++ (jT NV 0
          ++ encodeD out)))))))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD 0 ++ (jT CB 1 ++ (jT C1 B ++ (jT C2 1 ++ (jT NV 0
            ++ encodeD (out ++ qcEmitOut (leftBodies M) 0 (Fintype.card M.State) B))))))⟩ :=
  rep_qcFamily_run (leftBodies M) (Fintype.card M.State) B 0 CB C1 C2 NV hCB hC2 hNV hBC1 out

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitDynFamily
