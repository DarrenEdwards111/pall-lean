import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitTriangleHead
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitSnoc6

/-!
# Cook–Levin M2 emitter — THE HEAD ONE-HOT FAMILY, ALL TIMES, ONE MACHINE

The stale-bound interleave (brick 43's choreography, with the `t`-mirror timing fixed): each
grand round runs

`[row loop] ⨟ [count-trues] ⨟ [rearm6] ⨟ [snoc6 F] ⨟ [alo-literals] ⨟ [rearm6] ⨟ [interGrand]`

— the row loop (rows `1..P`) emits time-`t`'s at-most-one pairs and leaves both mirrors STALE
at `P+1`; the two pairT passes at that stale bound then emit the at-least-one clause's count
block (`P+1` spliced trues, closed by `snoc6 false`) and its `P+1` literals; the grand
interstitial re-arms and advances `t`.  Round `t`'s stream is `amo(t) ++ alo(t)` — the
rotation of `headOneHot t = alo(t) :: amo(t)`, satisfaction-blind by `headOneHotEmit_perm`.
`rep_headFamily_run` wraps `B` rounds: the complete head one-hot family stream, one
self-halting machine.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitHeadFamily

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

/-! ## The two stale-bound bodies -/

/-- The count-block body: one spliced `true` per inner round. -/
def cntTrueBody : List L3Instr := bitsI3 [true]

theorem cnt3_split (a c N : ℕ) :
    loop3Out cntTrueBody a c N = List.replicate N true := by
  rw [loop3Out_eq_flatten]
  have h : ∀ k, prog3Out cntTrueBody a c k = [true] := fun k => by
    rw [cntTrueBody]
    simp [prog3Out_bits]
  rw [List.map_congr_left (fun k _ => h k)]
  induction N with
  | zero => rfl
  | succ N ih => rw [List.range_succ, List.map_append, List.flatten_append, ih]; simp [List.replicate_succ']

/-- The head at-least-one literal body: coordinates `t` (source) and `k` (live), tag `1`,
sign `true`. -/
def aloRowHeadBody : List L3Instr :=
  sA ++ (sJ ++ (bitsI3 [true, false] ++ bitsI3 [true]))

theorem aloRowHead_prog3Out (t c k : ℕ) :
    prog3Out aloRowHeadBody t c k
      = encodeNat t ++ (encodeNat k ++ (encodeNat 1 ++ [true])) := by
  rw [aloRowHeadBody]
  simp only [prog3Out_append, prog3Out_bits, prog3Out_sA, prog3Out_sJ]
  simp [encodeNat, List.append_assoc]

/-- **The at-least-one clause factors through the stale-bound loop**: count block plus the
per-`k` literal stream. -/
theorem aloRowHead_split (t c P : ℕ) :
    encodeClause' (atLeastOne ((List.range (P + 1)).map (headVar t)))
      = encodeNat (P + 1) ++ loop3Out aloRowHeadBody t c (P + 1) := by
  rw [encodeClause'_atLeastOne_head, loop3Out_eq_flatten]
  congr 2
  apply List.map_congr_left
  intro p hp
  exact (aloRowHead_prog3Out t c p).symm

/-! ## The emission-ordered head one-hot, at the `Formula` level -/

/-- Round `t`'s head block in emission order: the triangle-ordered pairs, then the
at-least-one — the rotation of `headOneHot`. -/
def headOneHotEmit (t P : ℕ) : Formula :=
  amoTriHead t P ++ [atLeastOne ((List.range (P + 1)).map (headVar t))]

/-- **Emission order is a permutation of the tableau's `headOneHot`.** -/
theorem headOneHotEmit_perm (t P : ℕ) :
    (headOneHotEmit t P).Perm (headOneHot t P) := by
  rw [headOneHotEmit, headOneHot, oneHot]
  exact List.Perm.trans
    (List.Perm.append_right _ (amoTriHead_perm t P))
    (List.perm_append_singleton _ _)

theorem satisfiable_headOneHotEmit (t P : ℕ) :
    Satisfiable (headOneHotEmit t P) ↔ Satisfiable (headOneHot t P) :=
  satisfiable_perm (headOneHotEmit_perm t P)

/-- The accumulated head-family stream in emission order. -/
def headEmitOut (P : ℕ) : ℕ → List Bool
  | 0 => []
  | t + 1 => headEmitOut P t ++ (triRowOut amoPairRowHeadBody t P
      ++ (List.replicate (P + 1) true
        ++ ([false] ++ loop3Out aloRowHeadBody t (P + 1) (P + 1))))

/-- Round `t`'s slice IS the emission-ordered block's clause encodings. -/
theorem headEmit_block (t P : ℕ) :
    triRowOut amoPairRowHeadBody t P ++ (List.replicate (P + 1) true
        ++ ([false] ++ loop3Out aloRowHeadBody t (P + 1) (P + 1)))
      = ((headOneHotEmit t P).map encodeClause').flatten := by
  rw [headOneHotEmit, List.map_append, List.flatten_append, triRowOut_amoTriHead,
    show ((([atLeastOne ((List.range (P + 1)).map (headVar t))]).map
        encodeClause').flatten)
      = encodeClause' (atLeastOne ((List.range (P + 1)).map (headVar t))) from by simp,
    aloRowHead_split t (P + 1) P,
    show encodeNat (P + 1) = List.replicate (P + 1) true ++ [false] from rfl]
  simp [List.append_assoc]

/-- The full stream: every round's emission-ordered block, in order. -/
theorem headEmitOut_blocks (P : ℕ) : ∀ B,
    headEmitOut P B
      = ((List.range B).map (fun t =>
          ((headOneHotEmit t P).map encodeClause').flatten)).flatten
  | 0 => rfl
  | B + 1 => by
    rw [show headEmitOut P (B + 1)
        = headEmitOut P B ++ (triRowOut amoPairRowHeadBody B P
            ++ (List.replicate (P + 1) true
              ++ ([false] ++ loop3Out aloRowHeadBody B (P + 1) (P + 1)))) from rfl,
      headEmitOut_blocks P B, headEmit_block, List.range_succ, List.map_append,
      List.flatten_append]
    simp

/-! ## THE INTERLEAVED GRAND ROUND -/

/-- The per-round machine: the row loop, the two stale-bound passes with their re-arms and
the count block's closing bit, the grand interstitial. -/
def headRoundMachine : Machine :=
  seqMachine (seqMachine (seqMachine (seqMachine (seqMachine (seqMachine
    (repPMachine (seqMachine (pairTMachine amoPairRowHeadBody) interRowMachine))
    (pairTMachine cntTrueBody)) rearm6Machine) (snoc6Machine false))
    (pairTMachine aloRowHeadBody)) rearm6Machine) interGrandMachine

set_option maxHeartbeats 3200000 in
/-- **One interleaved grand round**: from the re-armed layout at time `t`, emit
`amo(t) ++ encodeClause'(alo(t))` and re-arm for `t+1` — the `rep_run` hypothesis shape. -/
theorem headRound_run (B P CB C1 C2 NV t : ℕ) (hP : 0 < P) (hCB : P < CB) (hC2 : P < C2)
    (hNV : P < NV) (ht : t < B) (hBC1 : B ≤ C1) (out : List Bool) :
    run headRoundMachine
      (((((((repPRounds B (fun r =>
            pairTClock amoPairRowHeadBody B P CB C1 C2 NV t (r + 1) (r + 1)
                (out ++ triRowOut amoPairRowHeadBody t r).length + 1
              + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (r + 1) + 18)) P
          + (4 * B + 4 * P + 8)) + 1
        + pairTClock cntTrueBody B P CB C1 C2 NV t (P + 1) (P + 1)
            (out ++ triRowOut amoPairRowHeadBody t P).length) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
          + 2 * ((out ++ triRowOut amoPairRowHeadBody t P)
              ++ List.replicate (P + 1) true).length + 24)) + 1
        + pairTClock aloRowHeadBody B P CB C1 C2 NV t (P + 1) (P + 1)
            (((out ++ triRowOut amoPairRowHeadBody t P)
              ++ List.replicate (P + 1) true) ++ [false]).length) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 16))
      (init headRoundMachine (cntT B (t + 1) ++ (unaryD P ++ (jT CB 1 ++ (jT C1 t
        ++ (jT C2 1 ++ (jT NV 0 ++ encodeD out)))))))
      = ⟨Sum.inr (29, false), 2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 10,
          cntT B (t + 1) ++ (unaryD P ++ (jT CB 1 ++ (jT C1 (t + 1) ++ (jT C2 1
            ++ (jT NV 0 ++ encodeD (out ++ (triRowOut amoPairRowHeadBody t P
              ++ (List.replicate (P + 1) true
                ++ ([false] ++ loop3Out aloRowHeadBody t (P + 1) (P + 1))))))))))⟩ := by
  have hRL := repP_pairRow_run amoPairRowHeadBody B (t + 1) (by omega) P t CB C1 C2 NV
    (by omega) hCB hC2 (by omega) out
  rw [cntT_zero P] at hRL
  have hCNT := pairT_run cntTrueBody B (t + 1) (by omega) P 0 (by omega) CB C1 C2 NV
    (P + 1) t (P + 1) (by omega) (by omega) (by omega) (by omega)
    (out ++ triRowOut amoPairRowHeadBody t P)
  rw [cntT_zero P, cnt3_split] at hCNT
  have hR1 := rearm6_run B (t + 1) (by omega) P 0 (by omega) CB C1 C2 NV (P + 1) t
    (P + 1) (P + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    (encodeD ((out ++ triRowOut amoPairRowHeadBody t P) ++ List.replicate (P + 1) true))
  rw [cntT_zero P] at hR1
  have hS6 := snoc6_run false B (t + 1) (by omega) P 0 (by omega) CB C1 C2 NV (P + 1) t
    (P + 1) 0 (by omega) (by omega) (by omega) (by omega)
    ((out ++ triRowOut amoPairRowHeadBody t P) ++ List.replicate (P + 1) true)
  rw [cntT_zero P] at hS6
  have hALO := pairT_run aloRowHeadBody B (t + 1) (by omega) P 0 (by omega) CB C1 C2 NV
    (P + 1) t (P + 1) (by omega) (by omega) (by omega) (by omega)
    (((out ++ triRowOut amoPairRowHeadBody t P) ++ List.replicate (P + 1) true)
      ++ [false])
  rw [cntT_zero P] at hALO
  have hR2 := rearm6_run B (t + 1) (by omega) P 0 (by omega) CB C1 C2 NV (P + 1) t
    (P + 1) (P + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    (encodeD ((((out ++ triRowOut amoPairRowHeadBody t P)
      ++ List.replicate (P + 1) true) ++ [false])
        ++ loop3Out aloRowHeadBody t (P + 1) (P + 1)))
  rw [cntT_zero P] at hR2
  have hIG := interGrand_run B (t + 1) (by omega) P 0 (by omega) CB C1 C2 NV (P + 1)
    (P + 1) t 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (encodeD ((((out ++ triRowOut amoPairRowHeadBody t P)
      ++ List.replicate (P + 1) true) ++ [false])
        ++ loop3Out aloRowHeadBody t (P + 1) (P + 1)))
  rw [cntT_zero P] at hIG
  have h1 := seq_run
    (repPMachine (seqMachine (pairTMachine amoPairRowHeadBody) interRowMachine))
    (pairTMachine cntTrueBody) _ _ _ _ _ _ _ _ _ hRL
    (repP_halt_inl4 (seqMachine (pairTMachine amoPairRowHeadBody) interRowMachine))
    hCNT rfl
  have h2 := seq_run _ rearm6Machine _ _ _ _ _ _ _ _ _ h1
    (seq_halt_final _ (pairTMachine cntTrueBody) _ rfl) hR1 rearm6_halt
  have h3 := seq_run _ (snoc6Machine false) _ _ _ _ _ _ _ _ _ h2
    (seq_halt_final _ rearm6Machine _ rearm6_halt) hS6 (snoc6_halt false)
  have h4 := seq_run _ (pairTMachine aloRowHeadBody) _ _ _ _ _ _ _ _ _ h3
    (seq_halt_final _ (snoc6Machine false) _ (snoc6_halt false)) hALO rfl
  have h5 := seq_run _ rearm6Machine _ _ _ _ _ _ _ _ _ h4
    (seq_halt_final _ (pairTMachine aloRowHeadBody) _ rfl) hR2 rearm6_halt
  have h6 := seq_run _ interGrandMachine _ _ _ _ _ _ _ _ _ h5
    (seq_halt_final _ rearm6Machine _ rearm6_halt) hIG interGrand_halt
  rw [show ((((out ++ triRowOut amoPairRowHeadBody t P) ++ List.replicate (P + 1) true)
        ++ [false]) ++ loop3Out aloRowHeadBody t (P + 1) (P + 1))
      = out ++ (triRowOut amoPairRowHeadBody t P ++ (List.replicate (P + 1) true
          ++ ([false] ++ loop3Out aloRowHeadBody t (P + 1) (P + 1))))
      from by simp [List.append_assoc]] at h6
  exact h6

theorem headRound_halt :
    headRoundMachine.halt (Sum.inr (29, false)) = true :=
  seq_halt_final _ interGrandMachine _ interGrand_halt

/-! ## THE HEAD ONE-HOT FAMILY, ALL TIMES, ONE MACHINE -/

set_option maxHeartbeats 3200000 in
/-- **THE HEAD FAMILY STREAM**: `B` interleaved grand rounds — round `t` emits time-`t`'s
at-most-one pairs (triangle order) followed by its at-least-one clause, i.e. the emission
rotation of `headOneHot t P`; `headEmitOut_blocks` + `headOneHotEmit_perm` read the output as
the full head one-hot family, satisfaction-blind reordered.  One machine, self-halting. -/
theorem rep_headFamily_run (B P CB C1 C2 NV : ℕ) (hP : 0 < P) (hCB : P < CB)
    (hC2 : P < C2) (hNV : P < NV) (hBC1 : B ≤ C1) (out : List Bool) :
    run (repMachine headRoundMachine)
      (repRounds (fun t =>
        (((((((repPRounds B (fun r =>
              pairTClock amoPairRowHeadBody B P CB C1 C2 NV t (r + 1) (r + 1)
                  ((out ++ headEmitOut P t) ++ triRowOut amoPairRowHeadBody t r).length + 1
                + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (r + 1) + 18)) P
            + (4 * B + 4 * P + 8)) + 1
          + pairTClock cntTrueBody B P CB C1 C2 NV t (P + 1) (P + 1)
              ((out ++ headEmitOut P t) ++ triRowOut amoPairRowHeadBody t P).length) + 1
          + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
          + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
            + 2 * (((out ++ headEmitOut P t) ++ triRowOut amoPairRowHeadBody t P)
                ++ List.replicate (P + 1) true).length + 24)) + 1
          + pairTClock aloRowHeadBody B P CB C1 C2 NV t (P + 1) (P + 1)
              ((((out ++ headEmitOut P t) ++ triRowOut amoPairRowHeadBody t P)
                ++ List.replicate (P + 1) true) ++ [false]).length) + 1
          + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
          + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 16))) B + (4 * B + 4))
      (init (repMachine headRoundMachine)
        (cntT B 0 ++ (unaryD P ++ (jT CB 1 ++ (jT C1 0 ++ (jT C2 1 ++ (jT NV 0
          ++ encodeD out)))))))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD P ++ (jT CB 1 ++ (jT C1 B ++ (jT C2 1 ++ (jT NV 0
            ++ encodeD (out ++ headEmitOut P B))))))⟩ := by
  have h := rep_run headRoundMachine B
    (fun t => unaryD P ++ (jT CB 1 ++ (jT C1 t ++ (jT C2 1 ++ (jT NV 0
      ++ encodeD (out ++ headEmitOut P t))))))
    (fun t =>
      (((((((repPRounds B (fun r =>
            pairTClock amoPairRowHeadBody B P CB C1 C2 NV t (r + 1) (r + 1)
                ((out ++ headEmitOut P t) ++ triRowOut amoPairRowHeadBody t r).length + 1
              + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (r + 1) + 18)) P
          + (4 * B + 4 * P + 8)) + 1
        + pairTClock cntTrueBody B P CB C1 C2 NV t (P + 1) (P + 1)
            ((out ++ headEmitOut P t) ++ triRowOut amoPairRowHeadBody t P).length) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
          + 2 * (((out ++ headEmitOut P t) ++ triRowOut amoPairRowHeadBody t P)
              ++ List.replicate (P + 1) true).length + 24)) + 1
        + pairTClock aloRowHeadBody B P CB C1 C2 NV t (P + 1) (P + 1)
            ((((out ++ headEmitOut P t) ++ triRowOut amoPairRowHeadBody t P)
              ++ List.replicate (P + 1) true) ++ [false]).length) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 16)))
    (fun _ => Sum.inr (29, false))
    (fun _ => 2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 10)
    (fun t ht => by
      constructor
      · have hrd := headRound_run B P CB C1 C2 NV t hP hCB hC2 hNV ht hBC1
          (out ++ headEmitOut P t)
        rw [show (out ++ headEmitOut P t) ++ (triRowOut amoPairRowHeadBody t P
              ++ (List.replicate (P + 1) true
                ++ ([false] ++ loop3Out aloRowHeadBody t (P + 1) (P + 1))))
            = out ++ headEmitOut P (t + 1) from by rw [List.append_assoc]; rfl] at hrd
        exact hrd
      · exact headRound_halt)
  simp only [show headEmitOut P 0 = [] from rfl, List.append_nil] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitHeadFamily
