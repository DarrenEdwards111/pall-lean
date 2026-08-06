import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeOutputSourceLocator

/-!
# Fixed consumed-prefix to lookup-workspace locator

At runtime-source origin, the evolved consumed prefix has grammar

`11* 01 (11 (00|11)* 01)*`

and the completed canonical lookup workspace begins with `10`.  This file
defines one fixed finite controller which parses that grammar and backs up one
cell after recognizing the workspace token, halting exactly at its low cell.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceLocator

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinMasterRound
open PallLean.Paper93.DeepMath.PathB.CookLevinRendShift
open PallLean.Paper93.DeepMath.PathB.CookLevinRoundInvariant
open PallLean.Paper93.DeepMath.PathB.CookLevinWholeRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation

inductive RuntimeWorkspaceLocatorState
  | countLo
  | countHi (lo : Bool)
  | blockLo
  | blockHi
  | dataLo
  | dataHi (lo : Bool)
  | done
  deriving DecidableEq, Fintype

open RuntimeWorkspaceLocatorState

/-- Constant-state parser for the consumed runtime-source prefix. -/
def runtimeWorkspaceLocatorMachine : Machine where
  State := RuntimeWorkspaceLocatorState
  fin := inferInstance
  dec := inferInstance
  start := .countLo
  halt := fun s => decide (s = .done)
  δ := fun s b =>
    match s with
    | .countLo => (.countHi b, none, 1)
    | .countHi lo =>
        if lo && b then (.countLo, none, 1)
        else if !lo && b then (.blockLo, none, 1)
        else (.done, none, 2)
    | .blockLo =>
        if b then (.blockHi, none, 1)
        else (.done, none, 2)
    | .blockHi =>
        if b then (.dataLo, none, 1)
        else (.done, none, 0)
    | .dataLo => (.dataHi b, none, 1)
    | .dataHi lo =>
        if lo = b then (.dataLo, none, 1)
        else if !lo && b then (.blockLo, none, 1)
        else (.done, none, 2)
    | .done => (.done, none, 2)
  accept := fun _ => false

theorem workspace_run_countPair (T : List Bool) (p : Nat)
    (h0 : T.getD p false = true)
    (h1 : T.getD (p + 1) false = true) :
    run runtimeWorkspaceLocatorMachine 2 ⟨countLo, p, T⟩ =
      ⟨countLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, runtimeWorkspaceLocatorMachine, moveHead, h0, h1]

theorem workspace_run_countPairs (T : List Bool) (q k : Nat)
    (h : ∀ i, i < k →
      T.getD (q + 2 * i) false = true ∧
      T.getD (q + 2 * i + 1) false = true) :
    run runtimeWorkspaceLocatorMachine (2 * k) ⟨countLo, q, T⟩ =
      ⟨countLo, q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk := h k (by omega)
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, run_add,
        ih (fun i hi => h i (by omega)),
        workspace_run_countPair T (q + 2 * k) hk.1 (by
          simpa [Nat.add_assoc] using hk.2)]
      congr 1

theorem workspace_run_countBoundary (T : List Bool) (p : Nat)
    (h0 : T.getD p false = false)
    (h1 : T.getD (p + 1) false = true) :
    run runtimeWorkspaceLocatorMachine 2 ⟨countLo, p, T⟩ =
      ⟨blockLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, runtimeWorkspaceLocatorMachine, moveHead, h0, h1]

theorem workspace_run_blockHeader (T : List Bool) (p : Nat)
    (h0 : T.getD p false = true)
    (h1 : T.getD (p + 1) false = true) :
    run runtimeWorkspaceLocatorMachine 2 ⟨blockLo, p, T⟩ =
      ⟨dataLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, runtimeWorkspaceLocatorMachine, moveHead, h0, h1]

theorem workspace_run_dataPair (T : List Bool) (p : Nat)
    (h : T.getD p false = T.getD (p + 1) false) :
    run runtimeWorkspaceLocatorMachine 2 ⟨dataLo, p, T⟩ =
      ⟨dataLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [run_succ, step, runtimeWorkspaceLocatorMachine, moveHead, h]

theorem workspace_run_dataPairs (T : List Bool) (q k : Nat)
    (h : ∀ i, i < k →
      T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run runtimeWorkspaceLocatorMachine (2 * k) ⟨dataLo, q, T⟩ =
      ⟨dataLo, q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk := h k (by omega)
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, run_add,
        ih (fun i hi => h i (by omega)),
        workspace_run_dataPair T (q + 2 * k) (by
          simpa [Nat.add_assoc] using hk)]
      congr 1

theorem workspace_run_blockBoundary (T : List Bool) (p : Nat)
    (h0 : T.getD p false = false)
    (h1 : T.getD (p + 1) false = true) :
    run runtimeWorkspaceLocatorMachine 2 ⟨dataLo, p, T⟩ =
      ⟨blockLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, runtimeWorkspaceLocatorMachine, moveHead, h0, h1]

theorem workspace_run_startToken (T : List Bool) (p : Nat)
    (h0 : T.getD p false = true)
    (h1 : T.getD (p + 1) false = false) :
    run runtimeWorkspaceLocatorMachine 2 ⟨blockLo, p, T⟩ =
      ⟨done, p, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1
  simp [run_succ, step, runtimeWorkspaceLocatorMachine, moveHead, h0, h1]

theorem flattenPairs_passedSourceBlock (bits : List Bool) :
    flattenPairs (passedSourceBlock bits) =
      [true, true] ++ encodeD bits := by
  change true :: true ::
      flattenPairs (dataPairs bits ++ [(false, true)]) =
    true :: true :: encodeD bits
  rw [flattenPairs_dataPairs]

theorem getD_append_middle (pre mid tail : List Bool) (i : Nat)
    (hi : i < mid.length) :
    (pre ++ mid ++ tail).getD (pre.length + i) false =
      mid.getD i false := by
  rw [show pre ++ mid ++ tail = pre ++ (mid ++ tail) by
    simp [List.append_assoc]]
  rw [List.getD_append_right (h := by omega)]
  rw [show pre.length + i - pre.length = i by omega]
  rw [List.getD_append (h := hi)]

theorem workspace_prefixed_block_run (pre bits tail : List Bool) :
    let T := pre ++ [true, true] ++ encodeD bits ++ tail
    run runtimeWorkspaceLocatorMachine (2 * bits.length + 4)
        ⟨blockLo, pre.length, T⟩ =
      ⟨blockLo, pre.length + 2 * bits.length + 4, T⟩ := by
  dsimp only
  let T := pre ++ [true, true] ++ encodeD bits ++ tail
  have hh := workspace_run_blockHeader T pre.length
    (by simp [T]) (by simp [T])
  have hd := workspace_run_dataPairs T (pre.length + 2) bits.length
    (fun i hi => by
      have hlo := getD_append_middle (pre ++ [true, true])
        (encodeD bits) tail (2 * i) (by rw [encodeD_length]; omega)
      have hhi := getD_append_middle (pre ++ [true, true])
        (encodeD bits) tail (2 * i + 1) (by rw [encodeD_length]; omega)
      simp only [List.length_append, List.length_cons, List.length_nil] at hlo hhi
      rw [show pre.length + 2 + 2 * i =
          (pre.length + (0 + 1 + 1)) + 2 * i by omega,
        show pre.length + 2 + 2 * i + 1 =
          (pre.length + (0 + 1 + 1)) + (2 * i + 1) by omega,
        show T = (pre ++ [true, true]) ++ encodeD bits ++ tail by
          simp [T, List.append_assoc], hlo, hhi]
      exact encodeD_data_eq bits i hi)
  have ht := workspace_run_blockBoundary T
    (pre.length + 2 + 2 * bits.length)
    (by
      have h := getD_append_middle (pre ++ [true, true])
        (encodeD bits) tail (2 * bits.length) (by rw [encodeD_length]; omega)
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      rw [show T = (pre ++ [true, true]) ++ encodeD bits ++ tail by
        simp [T, List.append_assoc], show pre.length + 2 + 2 * bits.length =
        (pre.length + (0 + 1 + 1)) + 2 * bits.length by omega, h]
      exact encodeD_mark_lo bits)
    (by
      have h := getD_append_middle (pre ++ [true, true])
        (encodeD bits) tail (2 * bits.length + 1) (by rw [encodeD_length]; omega)
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      rw [show T = (pre ++ [true, true]) ++ encodeD bits ++ tail by
        simp [T, List.append_assoc], show pre.length + 2 + 2 * bits.length + 1 =
        (pre.length + (0 + 1 + 1)) + (2 * bits.length + 1) by omega, h]
      exact encodeD_mark_hi bits)
  rw [show 2 * bits.length + 4 = 2 + (2 * bits.length + 2) by omega,
    run_add, hh, run_add, hd]
  convert ht using 1 <;> simp [T, Nat.add_assoc, List.append_assoc] <;> omega

def passedBlocksClock : List (List Bool) → Nat
  | [] => 0
  | bits :: rest => 2 * bits.length + 4 + passedBlocksClock rest

theorem passedBlocksClock_eq (blocks : List (List Bool)) :
    passedBlocksClock blocks =
      (flattenPairs (blocks.flatMap passedSourceBlock)).length := by
  induction blocks with
  | nil => rfl
  | cons bits rest ih =>
      simp [passedBlocksClock, List.flatMap_cons, flattenPairs_append,
        flattenPairs_passedSourceBlock, encodeD_length, ih]
      omega

theorem workspace_run_passedBlocks (pre workspace : List Bool)
    (blocks : List (List Bool)) :
    let archive := flattenPairs (blocks.flatMap passedSourceBlock)
    let T := pre ++ archive ++ workspace
    run runtimeWorkspaceLocatorMachine (passedBlocksClock blocks)
        ⟨blockLo, pre.length, T⟩ =
      ⟨blockLo, pre.length + archive.length, T⟩ := by
  induction blocks generalizing pre with
  | nil => simp [passedBlocksClock]
  | cons bits rest ih =>
      dsimp only
      let block := [true, true] ++ encodeD bits
      let archive := flattenPairs (rest.flatMap passedSourceBlock)
      let T := pre ++ block ++ archive ++ workspace
      have hshape : flattenPairs ((bits :: rest).flatMap passedSourceBlock) =
          block ++ archive := by
        simp [block, archive, flattenPairs_append,
          flattenPairs_passedSourceBlock]
      rw [hshape]
      simp only [passedBlocksClock]
      change run runtimeWorkspaceLocatorMachine
          (2 * bits.length + 4 + passedBlocksClock rest)
          ⟨blockLo, pre.length, pre ++ (block ++ archive) ++ workspace⟩ =
        ⟨blockLo, pre.length + (block ++ archive).length,
          pre ++ (block ++ archive) ++ workspace⟩
      rw [run_add]
      have hb := workspace_prefixed_block_run pre bits (archive ++ workspace)
      have hb' : run runtimeWorkspaceLocatorMachine (2 * bits.length + 4)
          ⟨blockLo, pre.length, pre ++ (block ++ archive) ++ workspace⟩ =
          ⟨blockLo, pre.length + 2 * bits.length + 4,
            pre ++ (block ++ archive) ++ workspace⟩ := by
        simpa [block, List.append_assoc] using hb
      rw [hb']
      have hr := ih (pre ++ block)
      have hblocklen : (pre ++ block).length =
          pre.length + 2 * bits.length + 4 := by
        simp [block, encodeD_length]
        omega
      have hr' : run runtimeWorkspaceLocatorMachine (passedBlocksClock rest)
          ⟨blockLo, pre.length + 2 * bits.length + 4,
            pre ++ (block ++ archive) ++ workspace⟩ =
          ⟨blockLo, pre.length + 2 * bits.length + 4 + archive.length,
            pre ++ (block ++ archive) ++ workspace⟩ := by
        simpa only [hblocklen, List.append_assoc] using hr
      rw [hr']
      congr 1
      simp [block, archive, encodeD_length]
      omega

/-- Complete fixed traversal of the canonical consumed prefix. -/
theorem runtimeWorkspaceLocator_run (d : Nat)
    (preBlocks : List (List Bool)) (workspace : List Bool)
    (h0 : workspace.getD 0 false = true)
    (h1 : workspace.getD 1 false = false) :
    let pre := selectedPrefix d preBlocks
    let T := pre ++ workspace
    run runtimeWorkspaceLocatorMachine (pre.length + 2)
        (init runtimeWorkspaceLocatorMachine T) =
      ⟨done, pre.length, T⟩ := by
  dsimp only
  let n := preBlocks.length + d
  let cnt := List.replicate n (true, true)
  let archive := preBlocks.flatMap passedSourceBlock
  let pre := selectedPrefix d preBlocks
  let T := pre ++ workspace
  have hpre : pre = flattenPairs cnt ++ [false, true] ++
      flattenPairs archive := by
    dsimp [pre, cnt, archive]
    rw [selectedPrefix, selectedPrefixPairs, ← List.replicate_add,
      flattenPairs_append, flattenPairs_append]
    rfl
  have hcnt : run runtimeWorkspaceLocatorMachine (2 * n)
      (init runtimeWorkspaceLocatorMachine T) =
      ⟨countLo, 2 * n, T⟩ := by
    simpa using workspace_run_countPairs T 0 n (fun i hi => by
      have hT : T = flattenPairs cnt ++
          ([false, true] ++ flattenPairs archive ++ workspace) := by
        simp [T, hpre, List.append_assoc]
      constructor
      · simp only [Nat.zero_add]
        rw [hT, List.getD_append (h := by simp [cnt]; omega),
          flattenPairs_getD_lo cnt i (by simpa [cnt] using hi)]
        simp [cnt, hi]
      · simp only [Nat.zero_add]
        rw [hT, List.getD_append (h := by simp [cnt]; omega),
          flattenPairs_getD_hi cnt i (by simpa [cnt] using hi)]
        simp [cnt, hi])
  have hboundary : run runtimeWorkspaceLocatorMachine 2
      ⟨countLo, 2 * n, T⟩ = ⟨blockLo, 2 * n + 2, T⟩ := by
    apply workspace_run_countBoundary
    · simp [T, hpre, cnt, flattenPairs_length]
    · simp [T, hpre, cnt, flattenPairs_length]
  have harchive := workspace_run_passedBlocks
    (flattenPairs cnt ++ [false, true]) workspace preBlocks
  have harchive' : run runtimeWorkspaceLocatorMachine
      (passedBlocksClock preBlocks) ⟨blockLo, 2 * n + 2, T⟩ =
      ⟨blockLo, pre.length, T⟩ := by
    have hcntlen : (flattenPairs cnt ++ [false, true]).length = 2 * n + 2 := by
      simp [cnt, flattenPairs_length]
    have hplen : pre.length = 2 * n + 2 +
        (flattenPairs archive).length := by
      rw [hpre]
      simp only [List.length_append, List.length_cons, List.length_nil,
        flattenPairs_length]
      simp only [cnt, List.length_replicate]
    have hT : T = (flattenPairs cnt ++ [false, true]) ++
        flattenPairs archive ++ workspace := by
      simp [T, hpre, List.append_assoc]
    rw [hT]
    simpa only [hcntlen, hplen] using harchive
  have hstart : run runtimeWorkspaceLocatorMachine 2
      ⟨blockLo, pre.length, T⟩ = ⟨done, pre.length, T⟩ := by
    apply workspace_run_startToken
    · rw [List.getD_append_right (h := le_rfl)]
      simpa using h0
    · rw [List.getD_append_right (h := by omega)]
      simpa using h1
  have hclock : pre.length + 2 =
      2 * n + (2 + (passedBlocksClock preBlocks + 2)) := by
    rw [hpre, passedBlocksClock_eq]
    simp [cnt, archive, flattenPairs_length]
    omega
  rw [hclock, run_add, hcnt, run_add, hboundary, run_add, harchive', hstart]

/-! The completed master workspace really retains the `10` token at its
origin.  This is not merely a grammar assumption: every destructive round
writes from relative cell two onward, and the terminal read performs no
writes. -/

theorem roundTape_startToken (T : List Bool) (k D : Nat)
    (hk : 1 ≤ k) :
    let T' := rsTape (rsTape T (2 * k + 4) D) (2 * k) (D + 1)
    T'.getD 0 false = T.getD 0 false ∧
      T'.getD 1 false = T.getD 1 false := by
  dsimp only
  constructor
  · rw [rsTape_getD_before _ (2 * k) _ 0 (by omega),
      rsTape_getD_before _ (2 * k + 4) _ 0 (by omega)]
  · rw [rsTape_getD_before _ (2 * k) _ 1 (by omega),
      rsTape_getD_before _ (2 * k + 4) _ 1 (by omega)]

theorem rounds_startToken (v : Nat) : ∀ (T : List Bool) (D : Nat),
    v ≤ D → RoundInv T v D →
    ∃ T', run masterM (clockSum v D)
        ⟨(1, 0, false, false), 2 * v + 2, T⟩ =
        ⟨(1, 0, false, false), 2, T'⟩ ∧
      RoundInv T' 0 (D - v) ∧
      T'.getD 0 false = T.getD 0 false ∧
      T'.getD 1 false = T.getD 1 false := by
  intro T D hv hinv
  induction v generalizing T D with
  | zero =>
      refine ⟨T, ?_, by simpa using hinv, rfl, rfl⟩
      simp [clockSum]
  | succ v ih =>
      have hk : 1 ≤ v + 1 := by omega
      have hD : 1 ≤ D := by omega
      let T1 := rsTape (rsTape T (2 * (v + 1) + 4) D)
        (2 * (v + 1)) (D + 1)
      have hrun1 : run masterM
          ((2 + 1 + 2 + (8 * (D - 1) + 8) + 1) +
            ((2 * (D - 1 + 1) + 2) + 1 + 1 + (8 * D + 8) + 1 +
              (2 * D + 2) + 1))
          ⟨(1, 0, false, false), 2 * (v + 1) + 2, T⟩ =
          ⟨(1, 0, false, false), 2 * v + 2, T1⟩ := by
        simpa [T1] using
          roundInv_step T (v + 1) D hk hD hinv
      have hinv1 : RoundInv T1 v (D - 1) := by
        simpa [T1] using roundInv_preserved T (v + 1) D hk hD hinv
      have htoken1 := roundTape_startToken T (v + 1) D hk
      obtain ⟨T', hrun2, hinv2, hzero2, hone2⟩ :=
        ih T1 (D - 1) (by omega) hinv1
      refine ⟨T', ?_, ?_, hzero2.trans ?_, hone2.trans ?_⟩
      · simp only [clockSum]
        rw [run_add, show roundClock D =
          ((2 + 1 + 2 + (8 * (D - 1) + 8) + 1) +
            ((2 * (D - 1 + 1) + 2) + 1 + 1 + (8 * D + 8) + 1 +
              (2 * D + 2) + 1)) by rfl, hrun1]
        exact hrun2
      · simpa [show D - (v + 1) = D - 1 - v by omega] using hinv2
      · simpa [T1] using htoken1.1
      · simpa [T1] using htoken1.2

theorem masterM_literal_startToken (w : List Bool) (l : Lit)
    (trailer : List Bool) :
    let bits := literalLookupTape w l
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    mcf.tp.getD 0 false = true ∧ mcf.tp.getD 1 false = false := by
  dsimp only
  let bits := literalLookupTape w l
  let A := signedLookupAssignment w l.1 l.2
  have hv : l.1 ≤ A.length := by
    dsimp [A]
    rw [signedLookupAssignment_length]
    omega
  have hinv : RoundInv (bits ++ trailer) l.1 A.length := by
    dsimp [bits, A]
    exact literalLookupTape_append_roundInv w l trailer
  obtain ⟨T', hrounds, hinv', hzero, hone⟩ :=
    rounds_startToken l.1 (bits ++ trailer) A.length hv hinv
  have htail : run masterM 7
      ⟨(1, 0, false, false), 2, T'⟩ =
      ⟨(9, 0, T'.getD 4 false, false), 4, T'⟩ := by
    exact tail_read (s := 2) (tape := T') (by omega)
      (by simpa using hinv'.lsent)
  have hrun : run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer)) =
      ⟨(9, 0, T'.getD 4 false, false), 4, T'⟩ := by
    rw [literalLookupClock, master_forced_init, run_add,
      PallLean.Paper93.DeepMath.PathB.CookLevinInP.init_phase
        (bits ++ trailer) l.1 A.length hinv,
      run_add, hrounds]
    exact htail
  rw [hrun]
  constructor
  · rw [hzero]
    simp [bits, literalLookupTape,
      PallLean.Paper93.DeepMath.PathB.CookLevinInP.encode]
  · rw [hone]
    exact hinv.lsent

/-- The fixed locator specializes unconditionally to the real destructive
runtime lookup result: the semantic source-origin tape is traversed to the
actual nested `masterM` workspace, whose start token is proved above. -/
theorem sourceRuntimeLookup_workspaceLocate (d : Nat)
    (preBlocks : List (List Bool)) (w : List Bool) (l : Lit)
    (rest : List (List Bool)) :
    let bits := literalLookupTape w l
    let pre := selectedPrefix d preBlocks
    let cf := run sourceRuntimeLookupCore
      (sourceRuntimeLookupClock d preBlocks w l)
      (init sourceRuntimeLookupCore
        (flattenPairs (progressPairs d [] preBlocks (bits :: rest))))
    run runtimeWorkspaceLocatorMachine (pre.length + 2)
        (init runtimeWorkspaceLocatorMachine cf.tp) =
      ⟨done, pre.length, cf.tp⟩ := by
  dsimp only
  let bits := literalLookupTape w l
  let pre := selectedPrefix d preBlocks
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ selectedTail rest
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let cf := run sourceRuntimeLookupCore
    (sourceRuntimeLookupClock d preBlocks w l)
    (init sourceRuntimeLookupCore
      (flattenPairs (progressPairs d [] preBlocks (bits :: rest))))
  have hshape : cf.tp = pre ++ mcf.tp := by
    have hr := sourceRuntimeLookup_run_shape d preBlocks w l rest
    simpa [bits, pre, trailer, mcf, cf] using congrArg Cfg.tp hr
  have htoken : mcf.tp.getD 0 false = true ∧
      mcf.tp.getD 1 false = false := by
    simpa [bits, trailer, mcf] using masterM_literal_startToken w l trailer
  have hr := runtimeWorkspaceLocator_run d preBlocks mcf.tp
    htoken.1 htoken.2
  rw [hshape]
  simpa [pre] using hr

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceLocator

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceLocator.workspace_prefixed_block_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceLocator.runtimeWorkspaceLocator_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceLocator.masterM_literal_startToken
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceLocator.sourceRuntimeLookup_workspaceLocate
