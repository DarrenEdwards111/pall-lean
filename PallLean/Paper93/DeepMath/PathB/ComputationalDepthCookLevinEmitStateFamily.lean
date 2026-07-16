import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitHeadFamily

/-!
# Cook–Levin M2 emitter — THE STATE ONE-HOT FAMILY, ALL TIMES, ONE MACHINE

The head family's interleave (brick 44), body-swapped to the state coordinates: the one-hot
is over the machine's `card` states, so the triangle runs `card - 1` rows and the stale bound
is `card` — structurally the head assembly at `P := card - 1`, with tag block `encodeNat 2`.
`rep_stateFamily_run` emits `⋃_{t<B} [amoTriState(t) ++ alo(t)]`; `stateOneHotEmit_perm`
(and its `card`-instantiated corollary `stateOneHotEmit_perm_card`) makes the emission order a
satisfaction-blind permutation of the tableau's `stateOneHot`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitStateFamily

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTemplates
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

/-! ## The state bodies and their Formula-level streams -/

/-- The state at-least-one literal body: tag `2`, sign `true`. -/
def aloRowStateBody : List L3Instr :=
  sA ++ (sJ ++ (bitsI3 [true, true, false] ++ bitsI3 [true]))

theorem aloRowState_prog3Out (t c k : ℕ) :
    prog3Out aloRowStateBody t c k
      = encodeNat t ++ (encodeNat k ++ (encodeNat 2 ++ [true])) := by
  rw [aloRowStateBody]
  simp only [prog3Out_append, prog3Out_bits, prog3Out_sA, prog3Out_sJ]
  simp [encodeNat, List.append_assoc]

theorem aloRowState_split (t c P : ℕ) :
    encodeClause' (atLeastOne ((List.range (P + 1)).map (stateVar t)))
      = encodeNat (P + 1) ++ loop3Out aloRowStateBody t c (P + 1) := by
  rw [encodeClause'_atLeastOne_state, loop3Out_eq_flatten]
  congr 2
  apply List.map_congr_left
  intro q hq
  exact (aloRowState_prog3Out t c q).symm

/-- The state at-most-one pairs in triangle order. -/
def amoTriState (t : ℕ) : ℕ → Formula
  | 0 => []
  | j + 1 => amoTriState t j ++ (List.range (j + 1)).map (fun k =>
      [(stateVar t k, false), (stateVar t (j + 1), false)])

theorem triRowOut_amoTriState (t : ℕ) : ∀ P,
    triRowOut amoPairRowStateBody t P = ((amoTriState t P).map encodeClause').flatten
  | 0 => rfl
  | P + 1 => by
    rw [show triRowOut amoPairRowStateBody t (P + 1)
        = triRowOut amoPairRowStateBody t P
            ++ loop3Out amoPairRowStateBody t (P + 1) (P + 1) from rfl,
      triRowOut_amoTriState t P, amoPairRowState_split,
      show amoTriState t (P + 1)
        = amoTriState t P ++ (List.range (P + 1)).map (fun k =>
            [(stateVar t k, false), (stateVar t (P + 1), false)]) from rfl,
      List.map_append, List.flatten_append, List.map_map]
    rfl

/-- **The state triangle order is a permutation of the tableau's `atMostOne`.** -/
theorem amoTriState_perm (t : ℕ) : ∀ P,
    (amoTriState t P).Perm (atMostOne ((List.range (P + 1)).map (stateVar t)))
  | 0 => by simp [amoTriState, atMostOne]
  | P + 1 => by
    rw [show amoTriState t (P + 1)
        = amoTriState t P ++ (List.range (P + 1)).map (fun k =>
            [(stateVar t k, false), (stateVar t (P + 1), false)]) from rfl,
      show P + 1 + 1 = (P + 1) + 1 from rfl, List.range_succ (n := P + 1),
      List.map_append]
    refine List.Perm.trans ?_ (atMostOne_snoc (stateVar t (P + 1))
      ((List.range (P + 1)).map (stateVar t))).symm
    refine List.Perm.append (amoTriState_perm t P) ?_
    rw [List.map_map]
    rfl

/-! ## The emission-ordered state one-hot -/

/-- Round `t`'s state block in emission order. -/
def stateOneHotEmit (t P : ℕ) : Formula :=
  amoTriState t P ++ [atLeastOne ((List.range (P + 1)).map (stateVar t))]

/-- **Emission order is a permutation of the state one-hot** (over `P + 1` states). -/
theorem stateOneHotEmit_perm (t P : ℕ) :
    (stateOneHotEmit t P).Perm
      (oneHot ((List.range (P + 1)).map (stateVar t))) := by
  rw [stateOneHotEmit, oneHot]
  exact List.Perm.trans
    (List.Perm.append_right _ (amoTriState_perm t P))
    (List.perm_append_singleton _ _)

/-- The `card`-instantiated corollary: at `P := card - 1` the emission block is a
satisfaction-blind permutation of the tableau's `stateOneHot M t`. -/
theorem stateOneHotEmit_perm_card (M : Machine) (t : ℕ)
    (hcard : 0 < Fintype.card M.State) :
    (stateOneHotEmit t (Fintype.card M.State - 1)).Perm (stateOneHot M t) := by
  have h := stateOneHotEmit_perm t (Fintype.card M.State - 1)
  rw [show Fintype.card M.State - 1 + 1 = Fintype.card M.State from by omega] at h
  exact h

theorem satisfiable_stateOneHotEmit (M : Machine) (t : ℕ)
    (hcard : 0 < Fintype.card M.State) :
    Satisfiable (stateOneHotEmit t (Fintype.card M.State - 1))
      ↔ Satisfiable (stateOneHot M t) :=
  satisfiable_perm (stateOneHotEmit_perm_card M t hcard)

/-- The accumulated state-family stream in emission order. -/
def stateEmitOut (P : ℕ) : ℕ → List Bool
  | 0 => []
  | t + 1 => stateEmitOut P t ++ (triRowOut amoPairRowStateBody t P
      ++ (List.replicate (P + 1) true
        ++ ([false] ++ loop3Out aloRowStateBody t (P + 1) (P + 1))))

theorem stateEmit_block (t P : ℕ) :
    triRowOut amoPairRowStateBody t P ++ (List.replicate (P + 1) true
        ++ ([false] ++ loop3Out aloRowStateBody t (P + 1) (P + 1)))
      = ((stateOneHotEmit t P).map encodeClause').flatten := by
  rw [stateOneHotEmit, List.map_append, List.flatten_append, triRowOut_amoTriState,
    show ((([atLeastOne ((List.range (P + 1)).map (stateVar t))]).map
        encodeClause').flatten)
      = encodeClause' (atLeastOne ((List.range (P + 1)).map (stateVar t))) from by simp,
    aloRowState_split t (P + 1) P,
    show encodeNat (P + 1) = List.replicate (P + 1) true ++ [false] from rfl]
  simp [List.append_assoc]

theorem stateEmitOut_blocks (P : ℕ) : ∀ B,
    stateEmitOut P B
      = ((List.range B).map (fun t =>
          ((stateOneHotEmit t P).map encodeClause').flatten)).flatten
  | 0 => rfl
  | B + 1 => by
    rw [show stateEmitOut P (B + 1)
        = stateEmitOut P B ++ (triRowOut amoPairRowStateBody B P
            ++ (List.replicate (P + 1) true
              ++ ([false] ++ loop3Out aloRowStateBody B (P + 1) (P + 1)))) from rfl,
      stateEmitOut_blocks P B, stateEmit_block, List.range_succ, List.map_append,
      List.flatten_append]
    simp

/-! ## THE INTERLEAVED STATE ROUND -/

/-- The per-round machine, state bodies. -/
def stateRoundMachine : Machine :=
  seqMachine (seqMachine (seqMachine (seqMachine (seqMachine (seqMachine
    (repPMachine (seqMachine (pairTMachine amoPairRowStateBody) interRowMachine))
    (pairTMachine cntTrueBody)) rearm6Machine) (snoc6Machine false))
    (pairTMachine aloRowStateBody)) rearm6Machine) interGrandMachine

set_option maxHeartbeats 3200000 in
/-- **One interleaved state round** — the `rep_run` hypothesis shape. -/
theorem stateRound_run (B P CB C1 C2 NV t : ℕ) (hP : 0 < P) (hCB : P < CB) (hC2 : P < C2)
    (hNV : P < NV) (ht : t < B) (hBC1 : B ≤ C1) (out : List Bool) :
    run stateRoundMachine
      (((((((repPRounds B (fun r =>
            pairTClock amoPairRowStateBody B P CB C1 C2 NV t (r + 1) (r + 1)
                (out ++ triRowOut amoPairRowStateBody t r).length + 1
              + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (r + 1) + 18)) P
          + (4 * B + 4 * P + 8)) + 1
        + pairTClock cntTrueBody B P CB C1 C2 NV t (P + 1) (P + 1)
            (out ++ triRowOut amoPairRowStateBody t P).length) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
          + 2 * ((out ++ triRowOut amoPairRowStateBody t P)
              ++ List.replicate (P + 1) true).length + 24)) + 1
        + pairTClock aloRowStateBody B P CB C1 C2 NV t (P + 1) (P + 1)
            (((out ++ triRowOut amoPairRowStateBody t P)
              ++ List.replicate (P + 1) true) ++ [false]).length) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 16))
      (init stateRoundMachine (cntT B (t + 1) ++ (unaryD P ++ (jT CB 1 ++ (jT C1 t
        ++ (jT C2 1 ++ (jT NV 0 ++ encodeD out)))))))
      = ⟨Sum.inr (29, false), 2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 10,
          cntT B (t + 1) ++ (unaryD P ++ (jT CB 1 ++ (jT C1 (t + 1) ++ (jT C2 1
            ++ (jT NV 0 ++ encodeD (out ++ (triRowOut amoPairRowStateBody t P
              ++ (List.replicate (P + 1) true
                ++ ([false] ++ loop3Out aloRowStateBody t (P + 1) (P + 1))))))))))⟩ := by
  have hRL := repP_pairRow_run amoPairRowStateBody B (t + 1) (by omega) P t CB C1 C2 NV
    (by omega) hCB hC2 (by omega) out
  rw [cntT_zero P] at hRL
  have hCNT := pairT_run cntTrueBody B (t + 1) (by omega) P 0 (by omega) CB C1 C2 NV
    (P + 1) t (P + 1) (by omega) (by omega) (by omega) (by omega)
    (out ++ triRowOut amoPairRowStateBody t P)
  rw [cntT_zero P, cnt3_split] at hCNT
  have hR1 := rearm6_run B (t + 1) (by omega) P 0 (by omega) CB C1 C2 NV (P + 1) t
    (P + 1) (P + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    (encodeD ((out ++ triRowOut amoPairRowStateBody t P) ++ List.replicate (P + 1) true))
  rw [cntT_zero P] at hR1
  have hS6 := snoc6_run false B (t + 1) (by omega) P 0 (by omega) CB C1 C2 NV (P + 1) t
    (P + 1) 0 (by omega) (by omega) (by omega) (by omega)
    ((out ++ triRowOut amoPairRowStateBody t P) ++ List.replicate (P + 1) true)
  rw [cntT_zero P] at hS6
  have hALO := pairT_run aloRowStateBody B (t + 1) (by omega) P 0 (by omega) CB C1 C2 NV
    (P + 1) t (P + 1) (by omega) (by omega) (by omega) (by omega)
    (((out ++ triRowOut amoPairRowStateBody t P) ++ List.replicate (P + 1) true)
      ++ [false])
  rw [cntT_zero P] at hALO
  have hR2 := rearm6_run B (t + 1) (by omega) P 0 (by omega) CB C1 C2 NV (P + 1) t
    (P + 1) (P + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    (encodeD ((((out ++ triRowOut amoPairRowStateBody t P)
      ++ List.replicate (P + 1) true) ++ [false])
        ++ loop3Out aloRowStateBody t (P + 1) (P + 1)))
  rw [cntT_zero P] at hR2
  have hIG := interGrand_run B (t + 1) (by omega) P 0 (by omega) CB C1 C2 NV (P + 1)
    (P + 1) t 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (encodeD ((((out ++ triRowOut amoPairRowStateBody t P)
      ++ List.replicate (P + 1) true) ++ [false])
        ++ loop3Out aloRowStateBody t (P + 1) (P + 1)))
  rw [cntT_zero P] at hIG
  have h1 := seq_run
    (repPMachine (seqMachine (pairTMachine amoPairRowStateBody) interRowMachine))
    (pairTMachine cntTrueBody) _ _ _ _ _ _ _ _ _ hRL
    (repP_halt_inl4 (seqMachine (pairTMachine amoPairRowStateBody) interRowMachine))
    hCNT rfl
  have h2 := seq_run _ rearm6Machine _ _ _ _ _ _ _ _ _ h1
    (seq_halt_final _ (pairTMachine cntTrueBody) _ rfl) hR1 rearm6_halt
  have h3 := seq_run _ (snoc6Machine false) _ _ _ _ _ _ _ _ _ h2
    (seq_halt_final _ rearm6Machine _ rearm6_halt) hS6 (snoc6_halt false)
  have h4 := seq_run _ (pairTMachine aloRowStateBody) _ _ _ _ _ _ _ _ _ h3
    (seq_halt_final _ (snoc6Machine false) _ (snoc6_halt false)) hALO rfl
  have h5 := seq_run _ rearm6Machine _ _ _ _ _ _ _ _ _ h4
    (seq_halt_final _ (pairTMachine aloRowStateBody) _ rfl) hR2 rearm6_halt
  have h6 := seq_run _ interGrandMachine _ _ _ _ _ _ _ _ _ h5
    (seq_halt_final _ rearm6Machine _ rearm6_halt) hIG interGrand_halt
  rw [show ((((out ++ triRowOut amoPairRowStateBody t P) ++ List.replicate (P + 1) true)
        ++ [false]) ++ loop3Out aloRowStateBody t (P + 1) (P + 1))
      = out ++ (triRowOut amoPairRowStateBody t P ++ (List.replicate (P + 1) true
          ++ ([false] ++ loop3Out aloRowStateBody t (P + 1) (P + 1))))
      from by simp [List.append_assoc]] at h6
  exact h6

theorem stateRound_halt :
    stateRoundMachine.halt (Sum.inr (29, false)) = true :=
  seq_halt_final _ interGrandMachine _ interGrand_halt

/-! ## THE STATE ONE-HOT FAMILY, ALL TIMES, ONE MACHINE -/

set_option maxHeartbeats 3200000 in
/-- **THE STATE FAMILY STREAM**: `B` interleaved grand rounds of the state block; with
`P := card - 1`, `stateEmitOut_blocks` + `stateOneHotEmit_perm_card` read the output as the
full state one-hot family, satisfaction-blind reordered.  One machine, self-halting. -/
theorem rep_stateFamily_run (B P CB C1 C2 NV : ℕ) (hP : 0 < P) (hCB : P < CB)
    (hC2 : P < C2) (hNV : P < NV) (hBC1 : B ≤ C1) (out : List Bool) :
    run (repMachine stateRoundMachine)
      (repRounds (fun t =>
        (((((((repPRounds B (fun r =>
              pairTClock amoPairRowStateBody B P CB C1 C2 NV t (r + 1) (r + 1)
                  ((out ++ stateEmitOut P t)
                    ++ triRowOut amoPairRowStateBody t r).length + 1
                + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (r + 1) + 18)) P
            + (4 * B + 4 * P + 8)) + 1
          + pairTClock cntTrueBody B P CB C1 C2 NV t (P + 1) (P + 1)
              ((out ++ stateEmitOut P t)
                ++ triRowOut amoPairRowStateBody t P).length) + 1
          + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
          + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
            + 2 * (((out ++ stateEmitOut P t) ++ triRowOut amoPairRowStateBody t P)
                ++ List.replicate (P + 1) true).length + 24)) + 1
          + pairTClock aloRowStateBody B P CB C1 C2 NV t (P + 1) (P + 1)
              ((((out ++ stateEmitOut P t) ++ triRowOut amoPairRowStateBody t P)
                ++ List.replicate (P + 1) true) ++ [false]).length) + 1
          + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
          + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 16))) B + (4 * B + 4))
      (init (repMachine stateRoundMachine)
        (cntT B 0 ++ (unaryD P ++ (jT CB 1 ++ (jT C1 0 ++ (jT C2 1 ++ (jT NV 0
          ++ encodeD out)))))))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD P ++ (jT CB 1 ++ (jT C1 B ++ (jT C2 1 ++ (jT NV 0
            ++ encodeD (out ++ stateEmitOut P B))))))⟩ := by
  have h := rep_run stateRoundMachine B
    (fun t => unaryD P ++ (jT CB 1 ++ (jT C1 t ++ (jT C2 1 ++ (jT NV 0
      ++ encodeD (out ++ stateEmitOut P t))))))
    (fun t =>
      (((((((repPRounds B (fun r =>
            pairTClock amoPairRowStateBody B P CB C1 C2 NV t (r + 1) (r + 1)
                ((out ++ stateEmitOut P t)
                  ++ triRowOut amoPairRowStateBody t r).length + 1
              + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (r + 1) + 18)) P
          + (4 * B + 4 * P + 8)) + 1
        + pairTClock cntTrueBody B P CB C1 C2 NV t (P + 1) (P + 1)
            ((out ++ stateEmitOut P t) ++ triRowOut amoPairRowStateBody t P).length) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
          + 2 * (((out ++ stateEmitOut P t) ++ triRowOut amoPairRowStateBody t P)
              ++ List.replicate (P + 1) true).length + 24)) + 1
        + pairTClock aloRowStateBody B P CB C1 C2 NV t (P + 1) (P + 1)
            ((((out ++ stateEmitOut P t) ++ triRowOut amoPairRowStateBody t P)
              ++ List.replicate (P + 1) true) ++ [false]).length) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 16)))
    (fun _ => Sum.inr (29, false))
    (fun _ => 2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 10)
    (fun t ht => by
      constructor
      · have hrd := stateRound_run B P CB C1 C2 NV t hP hCB hC2 hNV ht hBC1
          (out ++ stateEmitOut P t)
        rw [show (out ++ stateEmitOut P t) ++ (triRowOut amoPairRowStateBody t P
              ++ (List.replicate (P + 1) true
                ++ ([false] ++ loop3Out aloRowStateBody t (P + 1) (P + 1))))
            = out ++ stateEmitOut P (t + 1) from by rw [List.append_assoc]; rfl] at hrd
        exact hrd
      · exact stateRound_halt)
  simp only [show stateEmitOut P 0 = [] from rfl, List.append_nil] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitStateFamily
