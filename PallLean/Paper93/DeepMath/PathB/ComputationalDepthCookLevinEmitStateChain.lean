import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitMaster

/-!
# Cook–Levin M2 emitter — E6 step 5: THE STATE ONE-HOT AS A CONSTANT CHAIN

The state one-hot's row mismatch (`card − 1 ≠ P`) dissolves: state indices are MACHINE
CONSTANTS, so the whole per-`t` block — `atLeastOne` then the `atMostOne` rows in lex order —
is emitted by a `q`-chain of one-shot bodies (`stBodies`: index `0` the alo, index `k + 1` the
amo row `k`), at row size `P`, bound `1`.  The stream is **BIT-EXACT**: `stOut_oneHot` reads
each round as `encodeClause'` of `stateOneHot M t` clause-for-clause, and
`stEmit_range` folds the grand rounds into the family prefix.

The `t = B` block (the families range `t ≤ B`, rep loops emit `t < B`) is closed by the
NO-BUMP pass: `nopMachine` (halts at start) closes the chain instead of `incT6`
(`qcnMachine`/`qcn_run`), so one-shot emissions stack at the same `t`-mirror value —
`stateTop_pass_run` emits the `t = B` block with the mirror untouched.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitStateChain

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
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
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSnoc6
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCellFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitWriteFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitDynFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAcceptInit
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitQcPass

/-! ## The bodies -/

theorem prog3Out_flatten_map {α : Type} (l : List α) (f : α → List L3Instr) (a c k : ℕ) :
    prog3Out ((l.map f).flatten) a c k = (l.map (fun x => prog3Out (f x) a c k)).flatten := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.flatten_cons, prog3Out_append, ih, List.map_cons,
      List.flatten_cons]

/-- One `atMostOne` pair clause: `¬state[qi] ∨ ¬state[qj]` at the spliced time. -/
def amoStPair (qi qj : ℕ) : List L3Instr :=
  bitsI3 [true, true, false]
    ++ ((sA ++ (bitsI3 (encodeNat qi) ++ bitsI3 [true, true, false, false]))
      ++ (sA ++ (bitsI3 (encodeNat qj) ++ bitsI3 [true, true, false, false])))

theorem amoStPair_prog3Out (qi qj a c k : ℕ) :
    prog3Out (amoStPair qi qj) a c k
      = encodeClause' [(stateVar a qi, false), (stateVar a qj, false)] := by
  simp only [amoStPair, prog3Out_append, prog3Out_bits, prog3Out_sA]
  simp [encodeClause', encodeLit'_stateVar, encodeNat, List.append_assoc]

/-- The amo row of `k` against its `len` later partners. -/
def amoStRow (k len : ℕ) : List L3Instr :=
  ((List.range len).map (fun d => amoStPair k (k + 1 + d))).flatten

theorem amoStRow_prog3Out (kk len a c k : ℕ) :
    prog3Out (amoStRow kk len) a c k
      = ((List.range len).map (fun d =>
          encodeClause' [(stateVar a kk, false), (stateVar a (kk + 1 + d), false)])).flatten := by
  rw [amoStRow, prog3Out_flatten_map]
  exact congrArg List.flatten (List.map_congr_left (fun d _ => amoStPair_prog3Out kk _ a c k))

/-- The `atLeastOne` body over `n` state constants. -/
def aloStBody (n : ℕ) : List L3Instr :=
  bitsI3 (encodeNat n)
    ++ ((List.range n).map (fun q =>
        sA ++ (bitsI3 (encodeNat q) ++ bitsI3 [true, true, false, true]))).flatten

theorem aloSt_prog3Out (n a c k : ℕ) :
    prog3Out (aloStBody n) a c k
      = encodeClause' (atLeastOne ((List.range n).map (stateVar a))) := by
  rw [aloStBody, prog3Out_append, prog3Out_bits, prog3Out_flatten_map, encodeClause',
    atLeastOne]
  simp [List.map_map, Function.comp_def, prog3Out_append, prog3Out_bits, prog3Out_sA,
    encodeLit'_stateVar, encodeNat, List.append_assoc]

/-- The state one-hot chain bodies: index `0` the alo, index `k + 1` the amo row `k`. -/
noncomputable def stBodies (M : Machine) (qi : ℕ) : List L3Instr :=
  if qi = 0 then aloStBody (Fintype.card M.State)
  else amoStRow (qi - 1) (Fintype.card M.State - qi)

/-! ## The stream is the one-hot, bit-exact -/

/-- The amo rows in chain order ARE `atMostOne` in definition order. -/
theorem amo_stream (a c k : ℕ) : ∀ (m k0 : ℕ),
    ((List.range m).map (fun i => prog3Out (amoStRow (k0 + i) (m - 1 - i)) a c k)).flatten
      = ((atMostOne ((List.range m).map (fun j => stateVar a (k0 + j)))).map
          encodeClause').flatten
  | 0, k0 => rfl
  | m + 1, k0 => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.flatten_cons,
      List.map_map, List.map_map]
    rw [show atMostOne (stateVar a (k0 + 0)
          :: List.map ((fun j => stateVar a (k0 + j)) ∘ (· + 1)) (List.range m))
        = (List.map ((fun j => stateVar a (k0 + j)) ∘ (· + 1)) (List.range m)).map
            (fun w => [(stateVar a (k0 + 0), false), (w, false)])
          ++ atMostOne (List.map ((fun j => stateVar a (k0 + j)) ∘ (· + 1))
              (List.range m)) from rfl,
      List.map_append, List.flatten_append]
    congr 1
    · rw [amoStRow_prog3Out, List.map_map, List.map_map,
        show m + 1 - 1 - 0 = m from by omega]
      refine congrArg List.flatten (List.map_congr_left (fun d _ => ?_))
      simp only [Function.comp, Nat.add_zero]
      rw [show k0 + 0 + 1 + d = k0 + (d + 1) from by omega]
    · rw [show List.map ((fun j => stateVar a (k0 + j)) ∘ (· + 1)) (List.range m)
          = List.map (fun j => stateVar a (k0 + 1 + j)) (List.range m) from
            List.map_congr_left (fun j _ => by
              simp only [Function.comp]
              rw [show k0 + (j + 1) = k0 + 1 + j from by omega]),
        ← amo_stream a c k m (k0 + 1)]
      refine congrArg List.flatten (List.map_congr_left (fun i _ => ?_))
      simp only [Function.comp]
      rw [show k0 + (i + 1) = k0 + 1 + i from by omega,
        show m + 1 - 1 - (i + 1) = m - 1 - i from by omega]

/-- **The per-`t` chain block IS the state one-hot, clause-for-clause.** -/
theorem stOut_oneHot (M : Machine) (t : ℕ) :
    qcOut (stBodies M) t 0 0 (Fintype.card M.State + 1)
      = ((stateOneHot M t).map encodeClause').flatten := by
  rw [qcOut_range (stBodies M) t 0 (Fintype.card M.State + 1) 0, List.range_succ_eq_map,
    List.map_cons, List.flatten_cons, List.map_map, stateOneHot, oneHot, List.map_cons,
    List.flatten_cons, loop3Out_one]
  congr 1
  · rw [show stBodies M (0 + 0) = aloStBody (Fintype.card M.State) from by
      simp [stBodies], aloSt_prog3Out]
  · rw [show List.map ((fun i => loop3Out (stBodies M (0 + i)) t 1 (0 + 1)) ∘ (· + 1))
        (List.range (Fintype.card M.State))
      = List.map (fun i =>
          prog3Out (amoStRow (0 + i) (Fintype.card M.State - 1 - i)) t 1 0)
        (List.range (Fintype.card M.State)) from
      List.map_congr_left (fun i _ => by
        simp only [Function.comp, Nat.zero_add]
        rw [loop3Out_one, show stBodies M (i + 1)
            = amoStRow i (Fintype.card M.State - (i + 1)) from by simp [stBodies],
          show Fintype.card M.State - (i + 1) = Fintype.card M.State - 1 - i from by
            omega]),
      amo_stream t 1 0 (Fintype.card M.State) 0]
    refine congrArg List.flatten (congrArg (List.map _) (congrArg atMostOne ?_))
    exact List.map_congr_left (fun j _ => by rw [Nat.zero_add])

/-- The grand rounds fold into the family prefix: `T` rounds emit the one-hots `t < T`. -/
theorem stEmit_range (M : Machine) : ∀ T : ℕ,
    qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) T
      = ((bigAnd ((List.range T).map (fun t => stateOneHot M t))).map encodeClause').flatten
  | 0 => by simp [qcEmitOut, bigAnd]
  | T + 1 => by
    rw [show qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) (T + 1)
        = qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) T
          ++ qcOut (stBodies M) T 0 0 (Fintype.card M.State + 1) from rfl,
      stEmit_range M T, stOut_oneHot, bigAnd, bigAnd, List.range_succ (n := T),
      List.map_append, List.flatten_append, List.map_append, List.flatten_append,
      List.map_cons, List.flatten_cons]
    simp

/-! ## The no-bump chain -/

/-- The trivial halting machine — the no-bump chain closer. -/
def nopMachine : Machine where
  State := Bool
  fin := inferInstance
  dec := inferInstance
  start := false
  halt := fun _ => true
  δ := fun s _ => (s, none, 2)
  accept := fun _ => false

/-- The `q`-chain closed by `nop`: one-shot emissions that leave the `t`-mirror untouched. -/
def qcnMachine (bodies : ℕ → List L3Instr) : ℕ → ℕ → Machine
  | _, 0 => nopMachine
  | q0, n + 1 => seqMachine (seqMachine (pairTMachine (bodies q0)) rearm6Machine)
      (qcnMachine bodies (q0 + 1) n)

def qcnFinal (bodies : ℕ → List L3Instr) : (q0 n : ℕ) → (qcnMachine bodies q0 n).State
  | _, 0 => false
  | q0, n + 1 => Sum.inr (qcnFinal bodies (q0 + 1) n)

theorem qcnFinal_halt (bodies : ℕ → List L3Instr) : ∀ q0 n,
    (qcnMachine bodies q0 n).halt (qcnFinal bodies q0 n) = true
  | _, 0 => rfl
  | q0, n + 1 => seq_halt_final _ _ _ (qcnFinal_halt bodies (q0 + 1) n)

def qcnClockD (bodies : ℕ → List L3Instr) (G R Q CB C1 C2 NV t : ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, 0, _ => 0
  | q0, n + 1, L =>
      (pairTClock (bodies q0) G R CB C1 C2 NV t 1 (Q + 1) L + 1
        + (2 * G + 2 * R + 2 * CB + 2 * C1 + 2 * C2 + 2 * (Q + 1) + 18)) + 1
        + qcnClockD bodies G R Q CB C1 C2 NV t (q0 + 1) n
            (L + (loop3Out (bodies q0) t 1 (Q + 1)).length)

set_option maxHeartbeats 1600000 in
/-- **THE NO-BUMP PASS**: every body's block emitted, the live re-armed between blocks, the
`t`-mirror UNTOUCHED — one-shot emissions stack at the same time value. -/
theorem qcn_run (bodies : ℕ → List L3Instr) (G g : ℕ) (hg : g ≤ G) (R Q CB C1 C2 NV t : ℕ)
    (hCB : Q < CB) (hC2 : 0 < C2) (hNV : Q < NV) (ht : t ≤ C1) :
    ∀ (q0 n : ℕ) (out : List Bool),
    run (qcnMachine bodies q0 n)
      (qcnClockD bodies G R Q CB C1 C2 NV t q0 n out.length)
      (init (qcnMachine bodies q0 n) (cntT G g ++ (unaryD R ++ (jT CB (Q + 1)
        ++ (jT C1 t ++ (jT C2 1 ++ (jT NV 0 ++ encodeD out)))))))
      = ⟨qcnFinal bodies q0 n, 0,
          cntT G g ++ (unaryD R ++ (jT CB (Q + 1) ++ (jT C1 t ++ (jT C2 1
            ++ (jT NV 0 ++ encodeD (out ++ qcOut bodies t Q q0 n))))))⟩
  | q0, 0, out => by
    simp only [show qcOut bodies t Q q0 0 = [] from rfl, List.append_nil]
    rfl
  | q0, n + 1, out => by
    have hPT := pairT_run (bodies q0) G g hg R 0 (by omega) CB C1 C2 NV
      (Q + 1) t 1 (by omega) ht (by omega) (by omega) out
    rw [cntT_zero R] at hPT
    have hR := rearm6_run G g hg R 0 (by omega) CB C1 C2 NV (Q + 1) t 1
      (Q + 1) (by omega) ht (by omega) (by omega) (by omega)
      (encodeD (out ++ loop3Out (bodies q0) t 1 (Q + 1)))
    rw [cntT_zero R] at hR
    have h1 := seq_run (pairTMachine (bodies q0)) rearm6Machine _ _ _ _ _ _ _ _ _
      hPT rfl hR rearm6_halt
    have hrec := qcn_run bodies G g hg R Q CB C1 C2 NV t hCB hC2 hNV ht (q0 + 1) n
      (out ++ loop3Out (bodies q0) t 1 (Q + 1))
    have h2 := seq_run _ (qcnMachine bodies (q0 + 1) n) _ _ _ _ _ _ _ _ _ h1
      (seq_halt_final _ rearm6Machine _ rearm6_halt) hrec
      (qcnFinal_halt bodies (q0 + 1) n)
    rw [List.length_append,
      show (out ++ loop3Out (bodies q0) t 1 (Q + 1)) ++ qcOut bodies t Q (q0 + 1) n
        = out ++ qcOut bodies t Q q0 (n + 1) from by rw [List.append_assoc]; rfl] at h2
    exact h2

/-! ## The state instantiations -/

/-- **The state grand loop**: `t = 0 … B − 1` one-hots, bit-exact, at row size `P`. -/
theorem rep_stateChain_run (M : Machine) (B P CB C1 C2 NV : ℕ)
    (hCB : 0 < CB) (hC2 : 0 < C2) (hNV : 0 < NV) (hBC1 : B ≤ C1) (out : List Bool) :
    run (repMachine (qcMachine (stBodies M) 0 (Fintype.card M.State + 1)))
      (repRounds (fun t =>
        qcClockD (stBodies M) B P 0 CB C1 C2 NV t 0 (Fintype.card M.State + 1)
          (out ++ qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) t).length) B
        + (4 * B + 4))
      (init (repMachine (qcMachine (stBodies M) 0 (Fintype.card M.State + 1)))
        (cntT B 0 ++ (unaryD P ++ (jT CB 1 ++ (jT C1 0 ++ (jT C2 1 ++ (jT NV 0
          ++ encodeD out)))))))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD P ++ (jT CB 1 ++ (jT C1 B ++ (jT C2 1 ++ (jT NV 0
            ++ encodeD (out
              ++ qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) B))))))⟩ :=
  rep_qcFamilyD_run (stBodies M) (Fintype.card M.State + 1) B P 0 CB C1 C2 NV
    hCB hC2 hNV hBC1 out

set_option maxHeartbeats 800000 in
/-- **The `t = B` state one-hot, no bump**: the missing top block, mirrors untouched. -/
theorem stateTop_pass_run (M : Machine) (B P CB C1 C2 NV : ℕ)
    (hCB : 0 < CB) (hC2 : 0 < C2) (hNV : 0 < NV) (hBC1 : B ≤ C1) (out : List Bool) :
    run (qcnMachine (stBodies M) 0 (Fintype.card M.State + 1))
      (qcnClockD (stBodies M) B P 0 CB C1 C2 NV B 0 (Fintype.card M.State + 1)
        out.length)
      (init (qcnMachine (stBodies M) 0 (Fintype.card M.State + 1))
        (unaryD B ++ (unaryD P ++ (jT CB 1 ++ (jT C1 B ++ (jT C2 1 ++ (jT NV 0
          ++ encodeD out)))))))
      = ⟨qcnFinal (stBodies M) 0 (Fintype.card M.State + 1), 0,
          unaryD B ++ (unaryD P ++ (jT CB 1 ++ (jT C1 B ++ (jT C2 1 ++ (jT NV 0
            ++ encodeD (out ++ ((stateOneHot M B).map encodeClause').flatten))))))⟩ := by
  have h := qcn_run (stBodies M) B 0 (by omega) P 0 CB C1 C2 NV B hCB hC2 hNV hBC1
    0 (Fintype.card M.State + 1) out
  rw [cntT_zero B, stOut_oneHot] at h
  exact h

/-- **The full state family stream**: loop prefix + top block = `stateFamily M B`. -/
theorem stEmit_stateFamily (M : Machine) (B : ℕ) :
    qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) B
        ++ ((stateOneHot M B).map encodeClause').flatten
      = ((stateFamily M B).map encodeClause').flatten := by
  rw [show qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) B
        ++ ((stateOneHot M B).map encodeClause').flatten
      = qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) B
        ++ qcOut (stBodies M) B 0 0 (Fintype.card M.State + 1) from by
    rw [stOut_oneHot],
    show qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) B
        ++ qcOut (stBodies M) B 0 0 (Fintype.card M.State + 1)
      = qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) (B + 1) from rfl,
    stEmit_range M (B + 1), stateFamily]

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitStateChain
