import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitClockBounds3

/-!
# Cook–Levin M2 emitter — E6 step 22: BODY LENGTHS AND THE LAST KIT PIECES

Every chain body's length bounded (`O(card)`–`O(card²)` machine constants; the fixed triangle
bodies by `decide`), the entry-stream (`cellStream`) length, and `PB_pow` — the final
ingredients before the `masterClock2` assembly.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitBodyLens

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTemplates
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTriangleHead
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitHeadFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCellFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitWriteFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitDynFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAcceptInit
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitStateChain
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPipeline
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitBits (flatten_map_length_le)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitClockBounds3

/-! ## The fixed triangle bodies -/

theorem cellCopyRowBody_length_le : cellCopyRowBody.length ≤ 100 := by decide

theorem amoPairRowHeadBody_length_le : amoPairRowHeadBody.length ≤ 100 := by decide

theorem cntTrueBody_length_le : cntTrueBody.length ≤ 100 := by decide

theorem aloRowHeadBody_length_le : aloRowHeadBody.length ≤ 100 := by decide

/-! ## The machine-dependent bodies -/

theorem winPre3_length (qi : ℕ) (b : Bool) : (winPre3 qi b).length = qi + 25 := by
  simp [winPre3, sA, sJ, bitsI3, encodeNat]

theorem winPreL3_length (qi : ℕ) (b : Bool) : (winPreL3 qi b).length = qi + 27 := by
  simp [winPreL3, sA, sJ, sJ1, bitsI3, encodeNat]

theorem writeBodies_length_le (M : Machine) (q : ℕ) :
    (writeBodies M q).length ≤ 2 * q + 70 := by
  simp [writeBodies, writePairBody, writeRowBody, winPre3, sA1, sA, sJ, bitsI3, encodeNat]
  omega

theorem nsN_le (M : Machine) (qi : ℕ) (b : Bool) :
    nsN M qi b ≤ Fintype.card M.State := by
  rw [nsN]
  split
  · rw [nextStateIdx]
    exact le_of_lt (Fin.isLt _)
  · omega

theorem dynHeadSel_length_le (M : Machine) (qi : ℕ) (b : Bool) :
    (dynHeadSel M qi b).length ≤ qi + 40 := by
  rw [dynHeadSel]
  split_ifs
  · simp [dynHeadLeftRow3, winPreL3, sA1, sJ1, sA, sJ, bitsI3, encodeNat]
  · simp [dynHeadRightRow3, winPre3, sA1, sJ1, sA, sJ, bitsI3, encodeNat]
  · simp [dynHeadStayRow3, winPre3, sA1, sA, sJ, bitsI3, encodeNat]
  · simp [dynHeadResetRow3, winPre3, sA1, sA, sJ, bitsI3, encodeNat]

theorem dynBodies_length_le (M : Machine) (qi : ℕ) :
    (dynBodies M qi).length ≤ 4 * qi + 2 * Fintype.card M.State + 160 := by
  have hQB : ∀ b, (dynQB M qi b).length ≤ 2 * qi + Fintype.card M.State + 80 := by
    intro b
    rw [dynQB, List.length_append]
    have h1 : (dynStateRow3 qi (nsN M qi b) b).length
        = qi + nsN M qi b + 33 := by
      simp [dynStateRow3, winPre3, sA1, sA, sJ, bitsI3, encodeNat]
      omega
    have h2 := dynHeadSel_length_le M qi b
    have h3 := nsN_le M qi b
    omega
  rw [dynBodies, List.length_append]
  have := hQB false
  have := hQB true
  omega

theorem amoStPair_length (qi qj : ℕ) : (amoStPair qi qj).length = qi + qj + 17 := by
  simp [amoStPair, sA, bitsI3, encodeNat]
  omega

theorem stBodies_length_le (M : Machine) (qi : ℕ) (hqi : qi ≤ Fintype.card M.State) :
    (stBodies M qi).length
      ≤ 3 * Fintype.card M.State * Fintype.card M.State + 30 * Fintype.card M.State
        + 10 := by
  set s := Fintype.card M.State with hs
  rw [stBodies]
  split_ifs with h0
  · -- the alo body
    rw [aloStBody, List.length_append]
    have hfl := flatten_map_length_le (List.range s)
      (fun q => sA ++ (bitsI3 (encodeNat q) ++ bitsI3 [true, true, false, true]))
      (s + 7) (by
        intro q hq
        rw [List.mem_range] at hq
        simp [sA, bitsI3, encodeNat]
        omega)
    rw [List.length_range] at hfl
    have hn : (bitsI3 (encodeNat s)).length = s + 1 := by simp [bitsI3, encodeNat]
    nlinarith [Nat.zero_le s]
  · -- an amo row
    rw [amoStRow]
    have hfl := flatten_map_length_le (List.range (s - qi))
      (fun d => amoStPair (qi - 1) (qi - 1 + 1 + d)) (3 * s + 20) (by
        intro d hd
        rw [List.mem_range] at hd
        rw [amoStPair_length]
        omega)
    rw [List.length_range] at hfl
    nlinarith [Nat.zero_le s, Nat.sub_le s qi]

theorem leftBodies_length_le (M : Machine) (qi : ℕ) :
    (leftBodies M qi).length ≤ 2 * qi + 80 := by
  have hSel : ∀ b, (leftSel M qi b).length ≤ qi + 40 := by
    intro b
    rw [leftSel]
    split_ifs
    · simp [leftHead0Body, sA1, sA, bitsI3, encodeNat]
    · simp
  rw [leftBodies, List.length_append]
  have := hSel false
  have := hSel true
  omega

theorem acceptBody_length_le (M : Machine) :
    (acceptBody M).length
      ≤ Fintype.card M.State * Fintype.card M.State + 10 * Fintype.card M.State
        + 10 := by
  set s := Fintype.card M.State with hs
  have hasLen : (acceptStates M).length ≤ s := by
    rw [acceptStates]
    exact le_trans (List.length_filter_le _ _) (le_of_eq List.length_finRange)
  rw [acceptBody, List.length_append, acceptLitBlocks]
  have hfl := flatten_map_length_le (acceptStates M)
    (fun q => sA ++ (bitsI3 (encodeNat q.val) ++ bitsI3 [true, true, false, true]))
    (s + 7) (by
      intro q _
      have := q.isLt
      simp [sA, bitsI3, encodeNat]
      omega)
  have hn : (bitsI3 (encodeNat (acceptStates M).length)).length
      = (acceptStates M).length + 1 := by simp [bitsI3, encodeNat]
  nlinarith [Nat.zero_le s, hasLen]

theorem initConstBody_length_le (M : Machine) :
    (initConstBody M).length ≤ Fintype.card M.State + 20 := by
  rw [initConstBody]
  have hidx := Fin.isLt (Fintype.equivFin M.State M.start)
  rw [show (bitsI3 (encodeClause' [(stateVar 0
      (Fintype.equivFin M.State M.start).val, true)]
      ++ encodeClause' [(headVar 0 0, true)])).length
    = (encodeClause' [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)]).length
      + (encodeClause' [(headVar 0 0, true)]).length from by
    simp [bitsI3]]
  rw [encodeClause'_unit_state, encodeClause'_unit_head]
  simp [encodeNat]
  omega

/-! ## The entry stream -/

theorem cellStream_length_le (x : List Bool) (P : ℕ) :
    (cellStream x P).length ≤ (P + 1) * (P + 10) := by
  rw [cellStream]
  have hfl := flatten_map_length_le (List.range (P + 1))
    (fun p => encodeClause' [(cellVar 0 p, x.getD p false)]) (P + 10) (by
      intro p hp
      rw [List.mem_range] at hp
      show (encodeClause' [(cellVar 0 p, x.getD p false)]).length ≤ P + 10
      rw [encodeClause'_unit_cell]
      simp [encodeNat]
      omega)
  rwa [List.length_range] at hfl

/-! ## The last kit piece -/

theorem PB_pow {f : ℕ → ℕ} (hf : PolyBounded f) : ∀ k,
    PolyBounded (fun n => f n ^ k)
  | 0 => PB_le (fun n => by simp) (PB_const 1)
  | k + 1 =>
    PB_le (fun n => le_of_eq (pow_succ (f n) k))
      (PB_mul (PB_pow hf k) hf)

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitBodyLens
