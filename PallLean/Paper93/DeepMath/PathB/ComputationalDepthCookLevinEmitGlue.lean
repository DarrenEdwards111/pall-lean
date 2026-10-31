import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitMaster2

/-!
# Cook–Levin M2 emitter — E6 step 8: THE STREAM-FORMULA THEOREM

The satisfiability glue's centerpiece: `masterOut2` read as `encodeClause'` of ONE explicit
formula, `emittedFormula` — every family named at the clause level.  The two dynamics streams
get their formula identities here (`dynQBF`/`qcEmitOut_dynAFormula` mirroring the write-family
fold; `leftFq`/`qcEmitOut_dynBFormula` for the one-shot chain), the head loop folds through
`headEmitOut_blocks`, and `masterOut2_encode` assembles all ten pieces.  Downstream, the
eval-level equivalence (forward soundness via the ∀-`t,p` clause soundness lemmas, backward
subset via clause membership) runs entirely on `emittedFormula`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitGlue

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinAssembly
open PallLean.Paper93.DeepMath.PathB.CookLevinConverse
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
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitDynFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAcceptInit
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitQcPass
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitStateChain
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitHeadTop
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMaster2

/-! ## The dynamics-A formula -/

/-- The per-`(t, q, b, k)` clause pair the fused round emits: for non-left movers exactly
`dynamicsClause M t q k b`; for the left mover the state window at `k` plus the family's head
member at `p = k + 1`. -/
noncomputable def dynQBF (M : Machine) (t : ℕ) (q : Fin (Fintype.card M.State)) (b : Bool)
    (k : ℕ) : Formula :=
  if mvN M q.val b = 0 then
    [implClause (stateVar t q.val, true) (headVar t k, true) (cellVar t k, b)
      (stateVar (t + 1) (nextStateIdx M q k b), true),
     implClause (stateVar t q.val, true) (headVar t (k + 1), true) (cellVar t (k + 1), b)
      (headVar (t + 1) (nextHead M q (k + 1) b), true)]
  else dynamicsClause M t q k b

theorem dynQBF_encode (M : Machine) (t : ℕ) (q : Fin (Fintype.card M.State)) (b : Bool)
    (c k : ℕ) :
    prog3Out (dynQB M q.val b) t c k = ((dynQBF M t q b k).map encodeClause').flatten := by
  rcases dynQB_prog3Out M q b t c k with ⟨h0, he⟩ | ⟨h0, he⟩
  · rw [he, dynQBF, if_neg h0]
  · rw [he, dynQBF, if_pos h0]
    simp

/-- The per-`(t, q)` block of the dynamics-A loop. -/
theorem dynBlock_encode (M : Machine) (t P : ℕ) (q : Fin (Fintype.card M.State)) :
    loop3Out (dynBodies M q.val) t 1 (P + 1)
      = ((bigAnd ((List.range (P + 1)).map (fun k =>
          dynQBF M t q false k ++ dynQBF M t q true k))).map encodeClause').flatten := by
  rw [bigAnd, flatten_map_flatten, List.map_map, loop3Out_eq_flatten]
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [Function.comp_def, dynBodies_prog3Out, dynQBF_encode, dynQBF_encode]
  simp [List.map_append, List.flatten_append]

/-- The dynamics-A family in emission order. -/
noncomputable def dynAFormula (M : Machine) (P B : ℕ) : Formula :=
  bigAnd ((List.range B).map (fun t =>
    bigAnd ((List.finRange (Fintype.card M.State)).map (fun q =>
      bigAnd ((List.range (P + 1)).map (fun k =>
        dynQBF M t q false k ++ dynQBF M t q true k))))))

/-- **The dynamics-A stream equals `encodeClause'` of `dynAFormula` — in order.** -/
theorem qcEmitOut_dynAFormula (M : Machine) (P : ℕ) : ∀ B,
    qcEmitOut (dynBodies M) P (Fintype.card M.State) B
      = ((dynAFormula M P B).map encodeClause').flatten
  | 0 => by simp [qcEmitOut, dynAFormula, bigAnd]
  | B + 1 => by
    have hstep : dynAFormula M P (B + 1)
        = dynAFormula M P B
          ++ bigAnd ((List.finRange (Fintype.card M.State)).map (fun q =>
              bigAnd ((List.range (P + 1)).map (fun k =>
                dynQBF M B q false k ++ dynQBF M B q true k)))) := by
      rw [dynAFormula, dynAFormula, bigAnd, bigAnd, List.range_succ (n := B),
        List.map_append, List.flatten_append]
      simp [bigAnd]
    rw [show qcEmitOut (dynBodies M) P (Fintype.card M.State) (B + 1)
        = qcEmitOut (dynBodies M) P (Fintype.card M.State) B
            ++ qcOut (dynBodies M) B P 0 (Fintype.card M.State) from rfl,
      qcEmitOut_dynAFormula M P B, hstep, List.map_append, List.flatten_append]
    congr 1
    rw [bigAnd, flatten_map_flatten, List.map_map,
      qcOut_range (dynBodies M) B P (Fintype.card M.State) 0]
    rw [show (fun i => loop3Out (dynBodies M (0 + i)) B 1 (P + 1))
        = (fun i => loop3Out (dynBodies M i) B 1 (P + 1)) from
          funext (fun i => by rw [Nat.zero_add]),
      ← finRange_map_val (Fintype.card M.State)
        (fun i => loop3Out (dynBodies M i) B 1 (P + 1))]
    congr 1
    apply List.map_congr_left
    intro q hq
    exact dynBlock_encode M B P q

/-! ## The dynamics-B formula -/

/-- The one-shot chain's clause: the family's `p = 0` head member for left movers. -/
noncomputable def leftFq (M : Machine) (t : ℕ) (q : Fin (Fintype.card M.State))
    (b : Bool) : Formula :=
  if mvN M q.val b = 0 then
    [implClause (stateVar t q.val, true) (headVar t 0, true) (cellVar t 0, b)
      (headVar (t + 1) (nextHead M q 0 b), true)]
  else []

theorem leftFq_encode (M : Machine) (t : ℕ) (q : Fin (Fintype.card M.State)) (b : Bool)
    (c k : ℕ) :
    prog3Out (leftSel M q.val b) t c k = ((leftFq M t q b).map encodeClause').flatten := by
  rcases leftSel_prog3Out M q b t c k with ⟨h0, he⟩ | ⟨h0, he⟩
  · rw [he, leftFq, if_pos h0]
    simp
  · rw [he, leftFq, if_neg h0]
    rfl

theorem dynBBlock_encode (M : Machine) (t : ℕ) (q : Fin (Fintype.card M.State)) :
    loop3Out (leftBodies M q.val) t 1 (0 + 1)
      = (((leftFq M t q false ++ leftFq M t q true)).map encodeClause').flatten := by
  rw [loop3Out_one, leftBodies_prog3Out, leftFq_encode, leftFq_encode,
    List.map_append, List.flatten_append]

/-- The dynamics-B family (the `p = 0` left head windows) in emission order. -/
noncomputable def dynBFormula (M : Machine) (B : ℕ) : Formula :=
  bigAnd ((List.range B).map (fun t =>
    bigAnd ((List.finRange (Fintype.card M.State)).map (fun q =>
      leftFq M t q false ++ leftFq M t q true))))

/-- **The dynamics-B stream equals `encodeClause'` of `dynBFormula` — in order.** -/
theorem qcEmitOut_dynBFormula (M : Machine) : ∀ B,
    qcEmitOut (leftBodies M) 0 (Fintype.card M.State) B
      = ((dynBFormula M B).map encodeClause').flatten
  | 0 => by simp [qcEmitOut, dynBFormula, bigAnd]
  | B + 1 => by
    have hstep : dynBFormula M (B + 1)
        = dynBFormula M B
          ++ bigAnd ((List.finRange (Fintype.card M.State)).map (fun q =>
              leftFq M B q false ++ leftFq M B q true)) := by
      rw [dynBFormula, dynBFormula, bigAnd, bigAnd, List.range_succ (n := B),
        List.map_append, List.flatten_append]
      simp [bigAnd]
    rw [show qcEmitOut (leftBodies M) 0 (Fintype.card M.State) (B + 1)
        = qcEmitOut (leftBodies M) 0 (Fintype.card M.State) B
            ++ qcOut (leftBodies M) B 0 0 (Fintype.card M.State) from rfl,
      qcEmitOut_dynBFormula M B, hstep, List.map_append, List.flatten_append]
    congr 1
    rw [bigAnd, flatten_map_flatten, List.map_map,
      qcOut_range (leftBodies M) B 0 (Fintype.card M.State) 0]
    rw [show (fun i => loop3Out (leftBodies M (0 + i)) B 1 (0 + 1))
        = (fun i => loop3Out (leftBodies M i) B 1 (0 + 1)) from
          funext (fun i => by rw [Nat.zero_add]),
      ← finRange_map_val (Fintype.card M.State)
        (fun i => loop3Out (leftBodies M i) B 1 (0 + 1))]
    congr 1
    apply List.map_congr_left
    intro q hq
    exact dynBBlock_encode M B q

/-! ## The head loop fold -/

theorem headEmitOut_formula (P B : ℕ) :
    headEmitOut P B
      = ((bigAnd ((List.range B).map (fun t => headOneHotEmit t P))).map
          encodeClause').flatten := by
  rw [headEmitOut_blocks, bigAnd, flatten_map_flatten, List.map_map]
  exact congrArg List.flatten (List.map_congr_left (fun t _ => by
    rw [Function.comp_def]))

/-! ## THE STREAM-FORMULA THEOREM -/

/-- The emitted formula: every clause of the master stream, named, in emission order. -/
noncomputable def emittedFormula (M : Machine) (P B : ℕ) : Formula :=
  tapeFamily P B
    ++ (writeFamily M P B
    ++ (dynAFormula M P B
    ++ (bigAnd ((List.range B).map (fun t => headOneHotEmit t P))
    ++ (bigAnd ((List.range B).map (fun t => stateOneHot M t))
    ++ (dynBFormula M B
    ++ (stateOneHot M B
    ++ (headOneHotEmit B P
    ++ (acceptFormula M B
    ++ [[(stateVar 0 (Fintype.equivFin M.State M.start).val, true)],
        [(headVar 0 0, true)]]))))))))

/-- **THE MASTER STREAM IS A FORMULA**: `masterOut2` equals `encodeClause'` of
`emittedFormula`, clause-for-clause, in order. -/
theorem masterOut2_encode (M : Machine) (P B : ℕ) :
    masterOut2 M P B = ((emittedFormula M P B).map encodeClause').flatten := by
  rw [masterOut2, emittedFormula]
  simp only [List.map_append, List.flatten_append]
  rw [cellEmitOut_tapeFamily, qcEmitOut_writeFamily, qcEmitOut_dynAFormula,
    headEmitOut_formula, stEmit_range, qcEmitOut_dynBFormula, headEmit_block]
  simp

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitGlue
