import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeArchiveReturnWriter
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeRebaseLocator

/-!
# Fixed archive-counted unary rebase writer

The surviving archive is its own runtime block-count oracle.  This controller
marks each visited block header, returns through the marked prefix, extends a
left-moving unary frontier by one `11` pair, and repeats.  A final forward pass
restores every header byte-for-byte.  Thus no remaining-block count is present
in finite control.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUnaryRebaseWriter

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeZeroCopyRebase
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRebaseLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveLocator

inductive RuntimeUnaryRebaseState
  | init1 | init2 | init3 | init4 | init5 | init6 | init7 | init8
  | firstLo | firstHi (lo : Bool) | firstMarkLo | firstMarkHi
  | headerLo | headerHi (lo : Bool)
  | dataLo (fresh : Bool) | dataHi (fresh lo : Bool)
  | checkNext
  | revTermHi (last : Bool) | revTermLo (last : Bool)
  | revHi (last : Bool) | revLo (last hi : Bool)
  | boundaryHi (last : Bool)
  | boundaryHeaderLo (last : Bool)
  | boundaryHeaderHi (last lo : Bool)
  | interBackHeaderLo (last : Bool)
  | interBackBoundaryHi (last : Bool)
  | interBackBoundaryLo (last : Bool)
  | originBackHeaderLo (last : Bool)
  | originBackSeedHi (last : Bool)
  | originBackSeedLo (last : Bool)
  | tallyHi (last : Bool) | tallyLo (last hi : Bool)
  | newFrontierHi (last : Bool) | newFrontierLo (last : Bool)
  | returnRight (last : Bool) | returnSeedHi (last : Bool)
  | restoreFirstLo | restoreFirstHi
  | restoreDataLo | restoreDataHi (lo : Bool)
  | restoreNext | restoreHeaderHi
  | done | reject
  deriving DecidableEq, Fintype

open RuntimeUnaryRebaseState

/-- One fixed finite controller.  The only persistent runtime memory is on the
tape: processed headers and the moving `01` unary frontier. -/
def runtimeUnaryRebaseMachine : Machine where
  State := RuntimeUnaryRebaseState
  fin := inferInstance
  dec := inferInstance
  start := .init1
  halt := fun s => decide (s = .done ∨ s = .reject)
  δ := fun s b =>
    match s with
    | .init1 => (.init2, none, 0)
    | .init2 => (.init3, none, 0)
    | .init3 => (.init4, none, 0)
    | .init4 => (.init5, some true, 0)
    | .init5 => (.init6, some false, 1)
    | .init6 => (.init7, none, 1)
    | .init7 => (.init8, none, 1)
    | .init8 => (.firstLo, none, 1)
    | .firstLo => (.firstHi b, none, 1)
    | .firstHi lo =>
        if !lo && !b then (.dataLo false, none, 1)
        else if lo && !b then (.firstMarkLo, none, 0)
        else (.reject, none, 2)
    | .firstMarkLo => (.firstMarkHi, some false, 1)
    | .firstMarkHi => (.dataLo true, none, 1)
    | .headerLo => (.headerHi b, none, 1)
    | .headerHi lo =>
        if lo && b then (.dataLo false, none, 1)
        else if lo && !b then (.dataLo true, some true, 1)
        else (.reject, none, 2)
    | .dataLo fresh => (.dataHi fresh b, none, 1)
    | .dataHi fresh lo =>
        if b = lo then (.dataLo fresh, none, 1)
        else if !lo && b then
          if fresh then (.checkNext, none, 1)
          else (.headerLo, none, 1)
        else (.reject, none, 2)
    | .checkNext => (.revTermHi (!b), none, 0)
    | .revTermHi last => (.revTermLo last, none, 0)
    | .revTermLo last => (.revHi last, none, 0)
    | .revHi last => (.revLo last b, none, 0)
    | .revLo last hi =>
        if b = hi then (.revHi last, none, 0)
        else if !b && hi then (.boundaryHi last, none, 1)
        else (.reject, none, 2)
    | .boundaryHi last => (.boundaryHeaderLo last, none, 1)
    | .boundaryHeaderLo last => (.boundaryHeaderHi last b, none, 1)
    | .boundaryHeaderHi last lo =>
        if !lo && !b then (.originBackHeaderLo last, none, 0)
        else if lo && b then (.interBackHeaderLo last, none, 0)
        else (.reject, none, 2)
    | .interBackHeaderLo last => (.interBackBoundaryHi last, none, 0)
    | .interBackBoundaryHi last => (.interBackBoundaryLo last, none, 0)
    | .interBackBoundaryLo last => (.revHi last, none, 0)
    | .originBackHeaderLo last => (.originBackSeedHi last, none, 0)
    | .originBackSeedHi last => (.originBackSeedLo last, none, 0)
    | .originBackSeedLo last => (.tallyHi last, none, 0)
    | .tallyHi last => (.tallyLo last b, none, 0)
    | .tallyLo last hi =>
        if b && hi then (.tallyHi last, none, 0)
        else if !b && hi then (.newFrontierHi last, some true, 0)
        else (.reject, none, 2)
    | .newFrontierHi last => (.newFrontierLo last, some true, 0)
    | .newFrontierLo last => (.returnRight last, some false, 1)
    | .returnRight last =>
        if b then (.returnRight last, none, 1)
        else (.returnSeedHi last, none, 1)
    | .returnSeedHi last =>
        if b then
          if last then (.restoreFirstLo, none, 1)
          else (.firstLo, none, 1)
        else (.reject, none, 2)
    | .restoreFirstLo => (.restoreFirstHi, some true, 1)
    | .restoreFirstHi => (.restoreDataLo, some false, 1)
    | .restoreDataLo => (.restoreDataHi b, none, 1)
    | .restoreDataHi lo =>
        if b = lo then (.restoreDataLo, none, 1)
        else if !lo && b then (.restoreNext, none, 1)
        else (.reject, none, 2)
    | .restoreNext =>
        if b then (.restoreHeaderHi, some true, 1)
        else (.done, none, 2)
    | .restoreHeaderHi => (.restoreDataLo, some false, 1)
    | .done => (.done, none, 2)
    | .reject => (.reject, none, 2)
  accept := fun _ => false

/-- Boolean tape for a block whose header has been marked as processed. -/
def markedSourceBlock (first : Bool) (bits : List Bool) : List Bool :=
  (if first then [false, false] else [true, true]) ++ encodeD bits

def markedArchive : List (List Bool) → List Bool
  | [] => []
  | bits :: rest => markedSourceBlock true bits ++
      rest.flatMap (markedSourceBlock false)

def unaryRebaseFrontier (k : Nat) : List Bool :=
  [false, true] ++ List.replicate (2 * k) true ++ [false, true]

theorem unaryRebaseFrontier_zero : unaryRebaseFrontier 0 =
    [false, true, false, true] := by rfl

theorem unaryRebaseFrontier_succ (k : Nat) :
    unaryRebaseFrontier (k + 1) =
      [false, true] ++ [true, true] ++
        List.replicate (2 * k) true ++ [false, true] := by
  unfold unaryRebaseFrontier
  rw [show 2 * (k + 1) = 2 + 2 * k by omega,
    List.replicate_add]
  rfl

/-! ## Exact atomic runs -/

theorem runtimeUnaryRebase_run_init
    (pre archive : List Bool) (a b : Bool) :
    let R := pre.length + 4
    let T0 := pre ++ [a, b, false, true] ++ archive
    let T1 := pre ++ [false, true, false, true] ++ archive
    run runtimeUnaryRebaseMachine 8 ⟨init1, R, T0⟩ =
      ⟨firstLo, R, T1⟩ := by
  dsimp only
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, writeAt]

theorem runtimeUnaryRebase_run_equalPair
    (T : List Bool) (p : Nat) (fresh lo : Bool)
    (hlo : T.getD p false = lo)
    (hhi : T.getD (p + 1) false = lo) :
    run runtimeUnaryRebaseMachine 2 ⟨dataLo fresh, p, T⟩ =
      ⟨dataLo fresh, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, hlo, hhi]

theorem runtimeUnaryRebase_run_terminator_processed
    (T : List Bool) (p : Nat)
    (hlo : T.getD p false = false)
    (hhi : T.getD (p + 1) false = true) :
    run runtimeUnaryRebaseMachine 2 ⟨dataLo false, p, T⟩ =
      ⟨headerLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, hlo, hhi]

theorem runtimeUnaryRebase_run_terminator_fresh
    (T : List Bool) (p : Nat)
    (hlo : T.getD p false = false)
    (hhi : T.getD (p + 1) false = true) :
    run runtimeUnaryRebaseMachine 2 ⟨dataLo true, p, T⟩ =
      ⟨checkNext, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, hlo, hhi]

theorem runtimeUnaryRebase_run_encodeData
    (pre bits tail : List Bool) (fresh : Bool) :
    let T := pre ++ encodeD bits ++ tail
    run runtimeUnaryRebaseMachine (2 * bits.length)
        ⟨dataLo fresh, pre.length, T⟩ =
      ⟨dataLo fresh, pre.length + 2 * bits.length, T⟩ := by
  dsimp only
  induction bits generalizing pre with
  | nil => rfl
  | cons bit bits ih =>
      let T := pre ++ bit :: bit :: encodeD bits ++ tail
      have hp := runtimeUnaryRebase_run_equalPair T pre.length fresh bit
        (by simp [T]) (by simp [T])
      have hr := ih (pre ++ [bit, bit])
      rw [show 2 * (bit :: bits).length = 2 + 2 * bits.length by simp; omega,
        run_add]
      rw [show pre ++ encodeD (bit :: bits) ++ tail = T by
        simp [T, encodeD, List.append_assoc]]
      rw [hp]
      convert hr using 1 <;> simp [T, List.append_assoc] <;> omega

theorem prefixed_encodeD_markLo (pre bits tail : List Bool) :
    (pre ++ encodeD bits ++ tail).getD
      (pre.length + 2 * bits.length) false = false := by
  rw [List.append_assoc, List.getD_append_right (h := by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getD_append (h := by rw [encodeD_length]; omega)]
  exact encodeD_mark_lo bits

theorem prefixed_encodeD_markHi (pre bits tail : List Bool) :
    (pre ++ encodeD bits ++ tail).getD
      (pre.length + 2 * bits.length + 1) false = true := by
  rw [List.append_assoc, List.getD_append_right (h := by omega)]
  rw [show pre.length + 2 * bits.length + 1 - pre.length =
    2 * bits.length + 1 by omega]
  rw [List.getD_append (h := by rw [encodeD_length]; omega)]
  exact encodeD_mark_hi bits

theorem runtimeUnaryRebase_run_encodeD_processed
    (pre bits tail : List Bool) :
    let T := pre ++ encodeD bits ++ tail
    run runtimeUnaryRebaseMachine (2 * bits.length + 2)
        ⟨dataLo false, pre.length, T⟩ =
      ⟨headerLo, pre.length + 2 * bits.length + 2, T⟩ := by
  dsimp only
  let T := pre ++ encodeD bits ++ tail
  have hd := runtimeUnaryRebase_run_encodeData pre bits tail false
  have ht := runtimeUnaryRebase_run_terminator_processed T
    (pre.length + 2 * bits.length) (by
      simpa [T, List.append_assoc] using
        prefixed_encodeD_markLo pre bits tail)
    (by simpa [T, List.append_assoc] using
      prefixed_encodeD_markHi pre bits tail)
  rw [run_add, hd]
  exact ht

theorem runtimeUnaryRebase_run_encodeD_fresh
    (pre bits tail : List Bool) :
    let T := pre ++ encodeD bits ++ tail
    run runtimeUnaryRebaseMachine (2 * bits.length + 2)
        ⟨dataLo true, pre.length, T⟩ =
      ⟨checkNext, pre.length + 2 * bits.length + 2, T⟩ := by
  dsimp only
  let T := pre ++ encodeD bits ++ tail
  have hd := runtimeUnaryRebase_run_encodeData pre bits tail true
  have ht := runtimeUnaryRebase_run_terminator_fresh T
    (pre.length + 2 * bits.length) (by
      simpa [T, List.append_assoc] using
        prefixed_encodeD_markLo pre bits tail)
    (by simpa [T, List.append_assoc] using
      prefixed_encodeD_markHi pre bits tail)
  rw [run_add, hd]
  exact ht

theorem runtimeUnaryRebase_run_markFirstHeader
    (pre bits tail : List Bool) :
    let T0 := pre ++ [true, false] ++ encodeD bits ++ tail
    let T1 := pre ++ [false, false] ++ encodeD bits ++ tail
    run runtimeUnaryRebaseMachine 4 ⟨firstLo, pre.length, T0⟩ =
      ⟨dataLo true, pre.length + 2, T1⟩ := by
  dsimp only
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, writeAt]

theorem runtimeUnaryRebase_run_skipFirstHeader
    (pre bits tail : List Bool) :
    let T := pre ++ [false, false] ++ encodeD bits ++ tail
    run runtimeUnaryRebaseMachine 2 ⟨firstLo, pre.length, T⟩ =
      ⟨dataLo false, pre.length + 2, T⟩ := by
  dsimp only
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead]

theorem runtimeUnaryRebase_run_markHeader
    (pre bits tail : List Bool) :
    let T0 := pre ++ [true, false] ++ encodeD bits ++ tail
    let T1 := pre ++ [true, true] ++ encodeD bits ++ tail
    run runtimeUnaryRebaseMachine 2 ⟨headerLo, pre.length, T0⟩ =
      ⟨dataLo true, pre.length + 2, T1⟩ := by
  dsimp only
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, writeAt]

theorem runtimeUnaryRebase_run_skipHeader
    (pre bits tail : List Bool) :
    let T := pre ++ [true, true] ++ encodeD bits ++ tail
    run runtimeUnaryRebaseMachine 2 ⟨headerLo, pre.length, T⟩ =
      ⟨dataLo false, pre.length + 2, T⟩ := by
  dsimp only
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead]

theorem runtimeUnaryRebase_run_processedFirstBlock
    (pre bits tail : List Bool) :
    let T := pre ++ markedSourceBlock true bits ++ tail
    run runtimeUnaryRebaseMachine (2 * bits.length + 4)
        ⟨firstLo, pre.length, T⟩ =
      ⟨headerLo, pre.length + 2 * bits.length + 4, T⟩ := by
  dsimp only
  let T := pre ++ [false, false] ++ encodeD bits ++ tail
  have hh := runtimeUnaryRebase_run_skipFirstHeader pre bits tail
  have hd := runtimeUnaryRebase_run_encodeD_processed
    (pre ++ [false, false]) bits tail
  have hd' : run runtimeUnaryRebaseMachine (2 * bits.length + 2)
      ⟨dataLo false, pre.length + 2, T⟩ =
      ⟨headerLo, pre.length + 2 * bits.length + 4, T⟩ := by
    convert hd using 1 <;> simp [T, List.append_assoc] <;> omega
  rw [show 2 * bits.length + 4 = 2 + (2 * bits.length + 2) by omega,
    run_add]
  simpa [markedSourceBlock, T, List.append_assoc] using
    congrArg (run runtimeUnaryRebaseMachine (2 * bits.length + 2)) hh |>.trans hd'

theorem runtimeUnaryRebase_run_processedBlock
    (pre bits tail : List Bool) :
    let T := pre ++ markedSourceBlock false bits ++ tail
    run runtimeUnaryRebaseMachine (2 * bits.length + 4)
        ⟨headerLo, pre.length, T⟩ =
      ⟨headerLo, pre.length + 2 * bits.length + 4, T⟩ := by
  dsimp only
  let T := pre ++ [true, true] ++ encodeD bits ++ tail
  have hh := runtimeUnaryRebase_run_skipHeader pre bits tail
  have hd := runtimeUnaryRebase_run_encodeD_processed
    (pre ++ [true, true]) bits tail
  have hd' : run runtimeUnaryRebaseMachine (2 * bits.length + 2)
      ⟨dataLo false, pre.length + 2, T⟩ =
      ⟨headerLo, pre.length + 2 * bits.length + 4, T⟩ := by
    convert hd using 1 <;> simp [T, List.append_assoc] <;> omega
  rw [show 2 * bits.length + 4 = 2 + (2 * bits.length + 2) by omega,
    run_add]
  simpa [markedSourceBlock, T, List.append_assoc] using
    congrArg (run runtimeUnaryRebaseMachine (2 * bits.length + 2)) hh |>.trans hd'

theorem runtimeUnaryRebase_run_freshFirstBlock
    (pre bits tail : List Bool) (nextLo : Bool)
    (hnext : tail.getD 0 false = nextLo) :
    let T0 := pre ++ [true, false] ++ encodeD bits ++ tail
    let T1 := pre ++ markedSourceBlock true bits ++ tail
    run runtimeUnaryRebaseMachine (2 * bits.length + 7)
        ⟨firstLo, pre.length, T0⟩ =
      ⟨revTermHi (!nextLo), pre.length + 2 * bits.length + 3, T1⟩ := by
  dsimp only
  let T0 := pre ++ [true, false] ++ encodeD bits ++ tail
  let T1 := pre ++ [false, false] ++ encodeD bits ++ tail
  have hh := runtimeUnaryRebase_run_markFirstHeader pre bits tail
  have hd := runtimeUnaryRebase_run_encodeD_fresh
    (pre ++ [false, false]) bits tail
  have hn : T1.getD (pre.length + 2 * bits.length + 4) false = nextLo := by
    rw [show pre.length + 2 * bits.length + 4 =
      (pre ++ [false, false] ++ encodeD bits).length by simp [encodeD_length]; omega]
    rw [List.getD_append_right (h := le_rfl), Nat.sub_self]
    exact hnext
  rw [show 2 * bits.length + 7 =
      4 + ((2 * bits.length + 2) + 1) by omega,
    run_add, hh, run_add]
  have hd' : run runtimeUnaryRebaseMachine (2 * bits.length + 2)
      ⟨dataLo true, pre.length + 2, T1⟩ =
      ⟨checkNext, pre.length + 2 * bits.length + 4, T1⟩ := by
    convert hd using 1 <;> simp [T1, List.append_assoc] <;> omega
  rw [hd', run_succ, run_zero]
  have hn' : (pre ++ false :: false :: (encodeD bits ++ tail)).getD
      (pre.length + 2 * bits.length + 4) false = nextLo := by
    simpa [T1, List.append_assoc] using hn
  rw [List.getD_eq_getElem?_getD] at hn'
  simp [step, runtimeUnaryRebaseMachine, moveHead, hn',
    markedSourceBlock, T1]

theorem runtimeUnaryRebase_run_freshBlock
    (pre bits tail : List Bool) (nextLo : Bool)
    (hnext : tail.getD 0 false = nextLo) :
    let T0 := pre ++ [true, false] ++ encodeD bits ++ tail
    let T1 := pre ++ markedSourceBlock false bits ++ tail
    run runtimeUnaryRebaseMachine (2 * bits.length + 5)
        ⟨headerLo, pre.length, T0⟩ =
      ⟨revTermHi (!nextLo), pre.length + 2 * bits.length + 3, T1⟩ := by
  dsimp only
  let T1 := pre ++ [true, true] ++ encodeD bits ++ tail
  have hh := runtimeUnaryRebase_run_markHeader pre bits tail
  have hd := runtimeUnaryRebase_run_encodeD_fresh
    (pre ++ [true, true]) bits tail
  have hn : T1.getD (pre.length + 2 * bits.length + 4) false = nextLo := by
    rw [show pre.length + 2 * bits.length + 4 =
      (pre ++ [true, true] ++ encodeD bits).length by simp [encodeD_length]; omega]
    rw [List.getD_append_right (h := le_rfl), Nat.sub_self]
    exact hnext
  rw [show 2 * bits.length + 5 =
      2 + ((2 * bits.length + 2) + 1) by omega,
    run_add, hh, run_add]
  have hd' : run runtimeUnaryRebaseMachine (2 * bits.length + 2)
      ⟨dataLo true, pre.length + 2, T1⟩ =
      ⟨checkNext, pre.length + 2 * bits.length + 4, T1⟩ := by
    convert hd using 1 <;> simp [T1, List.append_assoc] <;> omega
  rw [hd', run_succ, run_zero]
  have hn' : (pre ++ true :: true :: (encodeD bits ++ tail)).getD
      (pre.length + 2 * bits.length + 4) false = nextLo := by
    simpa [T1, List.append_assoc] using hn
  rw [List.getD_eq_getElem?_getD] at hn'
  simp [step, runtimeUnaryRebaseMachine, moveHead, hn',
    markedSourceBlock, T1]

/-! ## Reverse traversal of the marked prefix -/

theorem runtimeUnaryRebase_run_revEqualPair
    (T : List Bool) (p : Nat) (last hi : Bool) (hp : 1 ≤ p)
    (hhi : T.getD p false = hi)
    (hlo : T.getD (p - 1) false = hi) :
    run runtimeUnaryRebaseMachine 2 ⟨revHi last, p, T⟩ =
      ⟨revHi last, p - 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hhi hlo
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, hhi, hlo]
  omega

theorem runtimeUnaryRebase_run_revPairs
    (T : List Bool) (H n : Nat) (last : Bool) (hH : 1 ≤ H)
    (heq : ∀ i, i < n →
      T.getD (H + 2 * i) false = T.getD (H + 2 * i + 1) false) :
    run runtimeUnaryRebaseMachine (2 * n)
        ⟨revHi last, H + (2 * n) - 1, T⟩ =
      ⟨revHi last, H - 1, T⟩ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn := heq n (by omega)
      have hs := runtimeUnaryRebase_run_revEqualPair T
        (H + 2 * (n + 1) - 1) last
        (T.getD (H + 2 * n) false) (by omega)
        (by convert hn.symm using 1 <;> omega)
        (by convert rfl using 2 <;> omega)
      have hs' : run runtimeUnaryRebaseMachine 2
          ⟨revHi last, H + (2 * (n + 1)) - 1, T⟩ =
          ⟨revHi last, H + (2 * n) - 1, T⟩ := by
        convert hs using 1 <;> omega
      calc
        run runtimeUnaryRebaseMachine (2 * (n + 1))
            ⟨revHi last, H + (2 * (n + 1)) - 1, T⟩ =
            run runtimeUnaryRebaseMachine (2 * n)
              (run runtimeUnaryRebaseMachine 2
                ⟨revHi last, H + (2 * (n + 1)) - 1, T⟩) := by
              rw [show 2 * (n + 1) = 2 + 2 * n by omega]
              simpa only [Nat.mul_add, Nat.mul_one] using
                run_add runtimeUnaryRebaseMachine 2 (2 * n)
                  ⟨revHi last, H + (2 + 2 * n) - 1, T⟩
        _ = run runtimeUnaryRebaseMachine (2 * n)
              ⟨revHi last, H + (2 * n) - 1, T⟩ := by rw [hs']
        _ = ⟨revHi last, H - 1, T⟩ :=
          ih (fun i hi => heq i (by omega))

theorem markedRegion_pair_eq
    (pre bits tail : List Bool) (first : Bool) (i : Nat)
    (hi : i < bits.length + 1) :
    let T := pre ++ markedSourceBlock first bits ++ tail
    T.getD (pre.length + 2 * i) false =
      T.getD (pre.length + 2 * i + 1) false := by
  dsimp only
  have core (x : Bool) (i : Nat) (hi : i < bits.length + 1) :
      (pre ++ [x, x] ++ encodeD bits ++ tail).getD
          (pre.length + 2 * i) false =
        (pre ++ [x, x] ++ encodeD bits ++ tail).getD
          (pre.length + 2 * i + 1) false := by
    cases i with
    | zero => simp
    | succ j =>
        have hj : j < bits.length := by omega
        have hget (c : Nat) (hc : c < (encodeD bits).length) :
            (pre ++ [x, x] ++ encodeD bits ++ tail).getD
                (pre.length + 2 + c) false =
              (encodeD bits).getD c false := by
          simp only [List.append_assoc]
          rw [List.getD_append_right (h := by omega)]
          rw [show pre.length + 2 + c - pre.length = 2 + c by omega]
          rw [List.getD_append_right (h := by simp)]
          rw [show 2 + c - [x, x].length = c by simp]
          rw [List.getD_append (h := hc)]
        have e0 : pre.length + 2 * (j + 1) =
            pre.length + 2 + 2 * j := by omega
        have e1 : pre.length + 2 + 2 * j + 1 =
            pre.length + 2 + (2 * j + 1) := by omega
        rw [e0, e1,
          hget (2 * j) (by rw [encodeD_length]; omega),
          hget (2 * j + 1) (by rw [encodeD_length]; omega),
          encodeD_data_eq bits j hj]
  cases first
  · simpa [markedSourceBlock] using core true i hi
  · simpa [markedSourceBlock] using core false i hi

theorem runtimeUnaryRebase_run_boundaryInter
    (pre tail : List Bool) (last : Bool) (hpre : 4 ≤ pre.length) :
    let T := pre ++ [false, true, true, true] ++ tail
    run runtimeUnaryRebaseMachine 8
        ⟨revHi last, pre.length + 1, T⟩ =
      ⟨revHi last, pre.length - 1, T⟩ := by
  dsimp only
  have h0 : (pre ++ [false, true, true, true] ++ tail).getD
      pre.length false = false := by simp
  have h1 : (pre ++ [false, true, true, true] ++ tail).getD
      (pre.length + 1) false = true := by simp
  have h2 : (pre ++ [false, true, true, true] ++ tail).getD
      (pre.length + 2) false = true := by simp
  have h3 : (pre ++ [false, true, true, true] ++ tail).getD
      (pre.length + 3) false = true := by simp
  rw [List.getD_eq_getElem?_getD] at h0 h1 h2 h3
  have h0' : (pre ++ [false, true, true, true] ++ tail)[pre.length + 1 - 1]?.getD false = false := by
    simpa using h0
  have h2' : (pre ++ [false, true, true, true] ++ tail)[pre.length + 1 + 1]?.getD false = true := by
    simpa [Nat.add_assoc] using h2
  have h3' : (pre ++ [false, true, true, true] ++ tail)[pre.length + 1 + 1 + 1]?.getD false = true := by
    simpa [Nat.add_assoc] using h3
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead,
    h0, h1, h2, h3, h0', h2', h3', Nat.add_assoc]

theorem runtimeUnaryRebase_run_boundaryOrigin
    (pre tail : List Bool) (last : Bool) (hpre : 4 ≤ pre.length) :
    let T := pre ++ [false, true, false, false] ++ tail
    run runtimeUnaryRebaseMachine 8
        ⟨revHi last, pre.length + 1, T⟩ =
      ⟨tallyHi last, pre.length - 1, T⟩ := by
  dsimp only
  have h0 : (pre ++ [false, true, false, false] ++ tail).getD
      pre.length false = false := by simp
  have h1 : (pre ++ [false, true, false, false] ++ tail).getD
      (pre.length + 1) false = true := by simp
  have h2 : (pre ++ [false, true, false, false] ++ tail).getD
      (pre.length + 2) false = false := by simp
  have h3 : (pre ++ [false, true, false, false] ++ tail).getD
      (pre.length + 3) false = false := by simp
  rw [List.getD_eq_getElem?_getD] at h0 h1 h2 h3
  have h0' : (pre ++ [false, true, false, false] ++ tail)[pre.length + 1 - 1]?.getD false = false := by
    simpa using h0
  have h2' : (pre ++ [false, true, false, false] ++ tail)[pre.length + 1 + 1]?.getD false = false := by
    simpa [Nat.add_assoc] using h2
  have h3' : (pre ++ [false, true, false, false] ++ tail)[pre.length + 1 + 1 + 1]?.getD false = false := by
    simpa [Nat.add_assoc] using h3
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead,
    h0, h1, h2, h3, h0', h2', h3', Nat.add_assoc]

theorem markedSourceBlock_length (first : Bool) (bits : List Bool) :
    (markedSourceBlock first bits).length = 2 * bits.length + 4 := by
  cases first <;> simp [markedSourceBlock, encodeD_length] <;> omega

theorem runtimeUnaryRebase_run_revTerm
    (T : List Bool) (p : Nat) (last : Bool) (hp : 2 ≤ p) :
    run runtimeUnaryRebaseMachine 2 ⟨revTermHi last, p, T⟩ =
      ⟨revHi last, p - 2, T⟩ := by
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead]
  omega

/-- Starting on a processed block's terminal `01` high cell, the fixed
reverse parser crosses the terminal, every doubled datum, and the marked
header, stopping on the preceding boundary's high cell. -/
theorem runtimeUnaryRebase_run_reverseMarkedBlock
    (pre bits tail : List Bool) (first last : Bool) (hpre : 1 ≤ pre.length) :
    let T := pre ++ markedSourceBlock first bits ++ tail
    run runtimeUnaryRebaseMachine (2 + 2 * (bits.length + 1))
        ⟨revTermHi last, pre.length + 2 * bits.length + 3, T⟩ =
      ⟨revHi last, pre.length - 1, T⟩ := by
  dsimp only
  let T := pre ++ markedSourceBlock first bits ++ tail
  have ht := runtimeUnaryRebase_run_revTerm T
    (pre.length + 2 * bits.length + 3) last (by omega)
  have ht' : run runtimeUnaryRebaseMachine 2
      ⟨revTermHi last, pre.length + 2 * bits.length + 3, T⟩ =
      ⟨revHi last, pre.length + 2 * (bits.length + 1) - 1, T⟩ := by
    convert ht using 1 <;> omega
  rw [run_add, ht']
  apply runtimeUnaryRebase_run_revPairs T pre.length (bits.length + 1) last hpre
  intro i hi
  exact markedRegion_pair_eq pre bits tail first i hi

/-! ## Exact unary-frontier extension -/

theorem runtimeUnaryRebase_run_tallyTruePair
    (T : List Bool) (p : Nat) (last : Bool) (hp : 1 ≤ p)
    (hhi : T.getD p false = true)
    (hlo : T.getD (p - 1) false = true) :
    run runtimeUnaryRebaseMachine 2 ⟨tallyHi last, p, T⟩ =
      ⟨tallyHi last, p - 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hhi hlo
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, hhi, hlo]
  omega

theorem runtimeUnaryRebase_run_tallyTruePairs
    (T : List Bool) (H n : Nat) (last : Bool) (hH : 1 ≤ H)
    (htrue : ∀ i, i < 2 * n → T.getD (H + i) false = true) :
    run runtimeUnaryRebaseMachine (2 * n)
        ⟨tallyHi last, H + 2 * n - 1, T⟩ =
      ⟨tallyHi last, H - 1, T⟩ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := runtimeUnaryRebase_run_tallyTruePair T
        (H + 2 * (n + 1) - 1) last (by omega)
        (by convert htrue (2 * n + 1) (by omega) using 1 <;> omega) (by
          convert htrue (2 * n) (by omega) using 1 <;> omega)
      have hs' : run runtimeUnaryRebaseMachine 2
          ⟨tallyHi last, H + 2 * (n + 1) - 1, T⟩ =
          ⟨tallyHi last, H + 2 * n - 1, T⟩ := by
        convert hs using 1 <;> omega
      calc
        run runtimeUnaryRebaseMachine (2 * (n + 1))
            ⟨tallyHi last, H + 2 * (n + 1) - 1, T⟩ =
            run runtimeUnaryRebaseMachine (2 * n)
              (run runtimeUnaryRebaseMachine 2
                ⟨tallyHi last, H + 2 * (n + 1) - 1, T⟩) := by
              rw [show 2 * (n + 1) = 2 + 2 * n by omega]
              simpa only [Nat.mul_add, Nat.mul_one] using
                run_add runtimeUnaryRebaseMachine 2 (2 * n)
                  ⟨tallyHi last, H + (2 + 2 * n) - 1, T⟩
        _ = run runtimeUnaryRebaseMachine (2 * n)
              ⟨tallyHi last, H + 2 * n - 1, T⟩ := by rw [hs']
        _ = ⟨tallyHi last, H - 1, T⟩ :=
          ih (fun i hi => htrue i (by omega))

theorem runtimeUnaryRebase_run_frontierWrite
    (pre tail : List Bool) (a b last : Bool) :
    let T0 := pre ++ [a, b, false, true] ++ tail
    let T1 := pre ++ [false, true, true, true] ++ tail
    run runtimeUnaryRebaseMachine 4
        ⟨tallyHi last, pre.length + 3, T0⟩ =
      ⟨returnRight last, pre.length + 1, T1⟩ := by
  dsimp only
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, writeAt]

theorem runtimeUnaryRebase_run_returnTrueCells
    (pre tail : List Bool) (n : Nat) (last : Bool) :
    let T := pre ++ List.replicate n true ++ tail
    run runtimeUnaryRebaseMachine n
        ⟨returnRight last, pre.length, T⟩ =
      ⟨returnRight last, pre.length + n, T⟩ := by
  dsimp only
  induction n generalizing pre with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ]
      rw [show n + 1 = 1 + n by omega, run_add]
      have hread : (pre ++ true :: List.replicate n true ++ tail).getD
          pre.length false = true := by simp
      rw [List.getD_eq_getElem?_getD] at hread
      simp [run_succ, step, runtimeUnaryRebaseMachine, hread, moveHead]
      have H := ih (pre ++ [true])
      simpa [List.append_assoc, Nat.add_assoc] using H

theorem runtimeUnaryRebase_run_returnSeed
    (pre archive : List Bool) (last : Bool) :
    let T := pre ++ [false, true] ++ archive
    run runtimeUnaryRebaseMachine 2
        ⟨returnRight last, pre.length, T⟩ =
      ⟨if last then restoreFirstLo else firstLo,
        pre.length + 2, T⟩ := by
  dsimp only
  cases last <;>
    simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead]

theorem prefixed_replicate_true
    (pre tail : List Bool) (n i : Nat) (hi : i < n) :
    (pre ++ List.replicate n true ++ tail).getD
      (pre.length + i) false = true := by
  rw [List.append_assoc, List.getD_append_right (h := by omega)]
  rw [Nat.add_sub_cancel_left]
  rw [List.getD_append (h := by simp; omega)]
  simp [List.getD_replicate, hi]

/-- One completed archive-block visit extends the left-moving frontier by
exactly one `11` pair and returns to the archive origin. -/
theorem runtimeUnaryRebase_run_extendFrontier
    (pre archive : List Bool) (a b last : Bool) (k : Nat) :
    let T0 := pre ++ [a, b] ++ unaryRebaseFrontier k ++ archive
    let T1 := pre ++ unaryRebaseFrontier (k + 1) ++ archive
    run runtimeUnaryRebaseMachine (4 * k + 9)
        ⟨tallyHi last, pre.length + 2 * k + 3, T0⟩ =
      ⟨if last then restoreFirstLo else firstLo,
        pre.length + 2 * k + 6, T1⟩ := by
  dsimp only
  let T0 := pre ++ [a, b] ++ unaryRebaseFrontier k ++ archive
  let Tmid := pre ++ [false, true, true, true] ++
    List.replicate (2 * k) true ++ [false, true] ++ archive
  have ht : run runtimeUnaryRebaseMachine (2 * k)
      ⟨tallyHi last, pre.length + 2 * k + 3, T0⟩ =
      ⟨tallyHi last, pre.length + 3, T0⟩ := by
    have H := runtimeUnaryRebase_run_tallyTruePairs T0
      (pre.length + 4) k last (by omega) (by
        intro i hi
        have := prefixed_replicate_true
          (pre ++ [a, b, false, true]) ([false, true] ++ archive)
          (2 * k) i hi
        simpa [T0, unaryRebaseFrontier, List.append_assoc] using this)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using H
  have hw := runtimeUnaryRebase_run_frontierWrite pre
    (List.replicate (2 * k) true ++ [false, true] ++ archive) a b last
  have hw' : run runtimeUnaryRebaseMachine 4
      ⟨tallyHi last, pre.length + 3, T0⟩ =
      ⟨returnRight last, pre.length + 1, Tmid⟩ := by
    simpa [T0, Tmid, unaryRebaseFrontier, List.append_assoc] using hw
  let P := pre ++ [false]
  have hr := runtimeUnaryRebase_run_returnTrueCells P
    ([false, true] ++ archive) (2 * k + 3) last
  have hTmid : Tmid =
      P ++ List.replicate (2 * k + 3) true ++ [false, true] ++ archive := by
    rw [show 2 * k + 3 = 3 + 2 * k by omega, List.replicate_add]
    simp [P, Tmid, List.append_assoc]
  have hr' : run runtimeUnaryRebaseMachine (2 * k + 3)
      ⟨returnRight last, pre.length + 1, Tmid⟩ =
      ⟨returnRight last, pre.length + 2 * k + 4, Tmid⟩ := by
    rw [hTmid]
    simpa [P, List.append_assoc, Nat.add_assoc,
      show 1 + (2 * k + 3) = 2 * k + 4 by omega] using hr
  have hs := runtimeUnaryRebase_run_returnSeed
    (pre ++ [false, true, true, true] ++ List.replicate (2 * k) true)
    archive last
  have hs' : run runtimeUnaryRebaseMachine 2
      ⟨returnRight last, pre.length + 2 * k + 4, Tmid⟩ =
      ⟨if last then restoreFirstLo else firstLo,
        pre.length + 2 * k + 6, Tmid⟩ := by
    simpa [Tmid, List.append_assoc, Nat.add_assoc,
      show 1 + (1 + (1 + (1 + 2 * k))) = 2 * k + 4 by omega,
      show 1 + (1 + (1 + (1 + (2 + 2 * k)))) = 2 * k + 6 by omega]
      using hs
  rw [show 4 * k + 9 = 2 * k + (4 + ((2 * k + 3) + 2)) by omega,
    run_add, ht, run_add, hw', run_add, hr', hs']
  congr 2
  simp [Tmid, unaryRebaseFrontier_succ, List.append_assoc]

/-! ## Restoration of temporary archive headers -/

theorem runtimeUnaryRebase_run_restoreEqualPair
    (T : List Bool) (p : Nat) (lo : Bool)
    (hlo : T.getD p false = lo)
    (hhi : T.getD (p + 1) false = lo) :
    run runtimeUnaryRebaseMachine 2 ⟨restoreDataLo, p, T⟩ =
      ⟨restoreDataLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, hlo, hhi]

theorem runtimeUnaryRebase_run_restoreEncodeData
    (pre bits tail : List Bool) :
    let T := pre ++ encodeD bits ++ tail
    run runtimeUnaryRebaseMachine (2 * bits.length)
        ⟨restoreDataLo, pre.length, T⟩ =
      ⟨restoreDataLo, pre.length + 2 * bits.length, T⟩ := by
  dsimp only
  induction bits generalizing pre with
  | nil => rfl
  | cons bit bits ih =>
      let T := pre ++ bit :: bit :: encodeD bits ++ tail
      have hp := runtimeUnaryRebase_run_restoreEqualPair T pre.length bit
        (by simp [T]) (by simp [T])
      have hr := ih (pre ++ [bit, bit])
      rw [show 2 * (bit :: bits).length = 2 + 2 * bits.length by simp; omega,
        run_add]
      rw [show pre ++ encodeD (bit :: bits) ++ tail = T by
        simp [T, encodeD, List.append_assoc]]
      rw [hp]
      convert hr using 1 <;> simp [T, List.append_assoc] <;> omega

theorem runtimeUnaryRebase_run_restoreTerminator
    (T : List Bool) (p : Nat)
    (hlo : T.getD p false = false)
    (hhi : T.getD (p + 1) false = true) :
    run runtimeUnaryRebaseMachine 2 ⟨restoreDataLo, p, T⟩ =
      ⟨restoreNext, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, hlo, hhi]

theorem runtimeUnaryRebase_run_restoreEncodeD
    (pre bits tail : List Bool) :
    let T := pre ++ encodeD bits ++ tail
    run runtimeUnaryRebaseMachine (2 * bits.length + 2)
        ⟨restoreDataLo, pre.length, T⟩ =
      ⟨restoreNext, pre.length + 2 * bits.length + 2, T⟩ := by
  dsimp only
  let T := pre ++ encodeD bits ++ tail
  have hd := runtimeUnaryRebase_run_restoreEncodeData pre bits tail
  have ht := runtimeUnaryRebase_run_restoreTerminator T
    (pre.length + 2 * bits.length)
    (by simpa [T, List.append_assoc] using
      prefixed_encodeD_markLo pre bits tail)
    (by simpa [T, List.append_assoc] using
      prefixed_encodeD_markHi pre bits tail)
  rw [run_add, hd]
  exact ht

theorem runtimeUnaryRebase_run_restoreFirstHeader
    (pre bits tail : List Bool) :
    let T0 := pre ++ [false, false] ++ encodeD bits ++ tail
    let T1 := pre ++ [true, false] ++ encodeD bits ++ tail
    run runtimeUnaryRebaseMachine 2 ⟨restoreFirstLo, pre.length, T0⟩ =
      ⟨restoreDataLo, pre.length + 2, T1⟩ := by
  dsimp only
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, writeAt]

theorem runtimeUnaryRebase_run_restoreLaterHeader
    (pre bits tail : List Bool) :
    let T0 := pre ++ [true, true] ++ encodeD bits ++ tail
    let T1 := pre ++ [true, false] ++ encodeD bits ++ tail
    run runtimeUnaryRebaseMachine 2 ⟨restoreNext, pre.length, T0⟩ =
      ⟨restoreDataLo, pre.length + 2, T1⟩ := by
  dsimp only
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, writeAt]

theorem runtimeUnaryRebase_run_restoreFirstBlock
    (pre bits : List Bool) (rest : List (List Bool)) :
    let T0 := pre ++ markedSourceBlock true bits ++
      rest.flatMap (markedSourceBlock false)
    let T1 := pre ++ [true, false] ++ encodeD bits ++
      rest.flatMap (markedSourceBlock false)
    run runtimeUnaryRebaseMachine (2 * bits.length + 4)
        ⟨restoreFirstLo, pre.length, T0⟩ =
      ⟨restoreNext, pre.length + 2 * bits.length + 4, T1⟩ := by
  dsimp only
  have hh := runtimeUnaryRebase_run_restoreFirstHeader pre bits
    (rest.flatMap (markedSourceBlock false))
  have hd := runtimeUnaryRebase_run_restoreEncodeD
    (pre ++ [true, false]) bits (rest.flatMap (markedSourceBlock false))
  rw [show 2 * bits.length + 4 = 2 + (2 * bits.length + 2) by omega,
    run_add]
  rw [show pre ++ markedSourceBlock true bits ++
      rest.flatMap (markedSourceBlock false) =
      pre ++ [false, false] ++ encodeD bits ++
        rest.flatMap (markedSourceBlock false) by
    simp [markedSourceBlock, List.append_assoc]]
  rw [hh]
  convert hd using 1 <;> simp [List.append_assoc] <;> omega

theorem runtimeUnaryRebase_run_restoreLaterBlock
    (pre bits : List Bool) (rest : List (List Bool)) :
    let T0 := pre ++ markedSourceBlock false bits ++
      rest.flatMap (markedSourceBlock false)
    let T1 := pre ++ [true, false] ++ encodeD bits ++
      rest.flatMap (markedSourceBlock false)
    run runtimeUnaryRebaseMachine (2 * bits.length + 4)
        ⟨restoreNext, pre.length, T0⟩ =
      ⟨restoreNext, pre.length + 2 * bits.length + 4, T1⟩ := by
  dsimp only
  have hh := runtimeUnaryRebase_run_restoreLaterHeader pre bits
    (rest.flatMap (markedSourceBlock false))
  have hd := runtimeUnaryRebase_run_restoreEncodeD
    (pre ++ [true, false]) bits (rest.flatMap (markedSourceBlock false))
  rw [show 2 * bits.length + 4 = 2 + (2 * bits.length + 2) by omega,
    run_add]
  rw [show pre ++ markedSourceBlock false bits ++
      rest.flatMap (markedSourceBlock false) =
      pre ++ [true, true] ++ encodeD bits ++
        rest.flatMap (markedSourceBlock false) by
    simp [markedSourceBlock, List.append_assoc]]
  rw [hh]
  convert hd using 1 <;> simp [List.append_assoc] <;> omega

def restoreArchiveClock (rest : List (List Bool)) : Nat :=
  (rest.map (fun bits => 2 * bits.length + 4)).sum

theorem runtimeUnaryRebase_run_restoreLaterArchive
    (pre : List Bool) (rest : List (List Bool)) :
    let T0 := pre ++ rest.flatMap (markedSourceBlock false)
    let T1 := pre ++ selectedTail rest
    run runtimeUnaryRebaseMachine (restoreArchiveClock rest)
        ⟨restoreNext, pre.length, T0⟩ =
      ⟨restoreNext, pre.length + (selectedTail rest).length, T1⟩ := by
  dsimp only
  induction rest generalizing pre with
  | nil => simp [restoreArchiveClock, selectedTail, flattenPairs]
  | cons bits rest ih =>
      have hb := runtimeUnaryRebase_run_restoreLaterBlock pre bits rest
      have hr := ih (pre ++ [true, false] ++ encodeD bits)
      have hb' : run runtimeUnaryRebaseMachine (2 * bits.length + 4)
          ⟨restoreNext, pre.length,
            pre ++ (markedSourceBlock false bits ++
              rest.flatMap (markedSourceBlock false))⟩ =
          ⟨restoreNext, pre.length + 2 * bits.length + 4,
            pre ++ [true, false] ++ encodeD bits ++
              rest.flatMap (markedSourceBlock false)⟩ := by
        simpa [List.append_assoc] using hb
      have hc : restoreArchiveClock (bits :: rest) =
          (2 * bits.length + 4) + restoreArchiveClock rest := by
        simp [restoreArchiveClock]
      rw [hc, run_add]
      simp only [List.flatMap_cons, List.append_assoc]
      rw [hb']
      simpa [selectedTail_cons, encodeD_length, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        show 1 + (1 + (2 + 2 * bits.length)) =
          2 * bits.length + 4 by omega,
        show 1 + (1 + (2 + (2 * bits.length +
            (selectedTail rest).length))) =
          2 * bits.length + (4 + (selectedTail rest).length) by omega] using hr

theorem runtimeUnaryRebase_run_restoreEnd (T : List Bool) (p : Nat)
    (hblank : T.getD p false = false) :
    run runtimeUnaryRebaseMachine 1 ⟨restoreNext, p, T⟩ =
      ⟨done, p, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hblank
  simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, hblank]

/-- The final pass restores every temporary header and halts on the blank
immediately after the byte-for-byte canonical archive. -/
theorem runtimeUnaryRebase_run_restoreArchive
    (pre bits : List Bool) (rest : List (List Bool)) :
    let T0 := pre ++ markedArchive (bits :: rest)
    let T1 := pre ++ selectedTail (bits :: rest)
    run runtimeUnaryRebaseMachine
        (2 * bits.length + 4 + restoreArchiveClock rest + 1)
        ⟨restoreFirstLo, pre.length, T0⟩ =
      ⟨done, pre.length + (selectedTail (bits :: rest)).length, T1⟩ := by
  dsimp only
  have hb := runtimeUnaryRebase_run_restoreFirstBlock pre bits rest
  have hb' : run runtimeUnaryRebaseMachine (2 * bits.length + 4)
      ⟨restoreFirstLo, pre.length, pre ++ markedArchive (bits :: rest)⟩ =
      ⟨restoreNext, pre.length + 2 * bits.length + 4,
        pre ++ [true, false] ++ encodeD bits ++
          rest.flatMap (markedSourceBlock false)⟩ := by
    simpa [markedArchive, List.append_assoc] using hb
  let P := pre ++ [true, false] ++ encodeD bits
  have hr := runtimeUnaryRebase_run_restoreLaterArchive P rest
  let T1 := pre ++ selectedTail (bits :: rest)
  have he := runtimeUnaryRebase_run_restoreEnd T1
    (pre.length + (selectedTail (bits :: rest)).length) (by
      simp [T1])
  rw [show 2 * bits.length + 4 + restoreArchiveClock rest + 1 =
      (2 * bits.length + 4) + (restoreArchiveClock rest + 1) by omega,
    run_add, hb', run_add]
  have hr' : run runtimeUnaryRebaseMachine (restoreArchiveClock rest)
      ⟨restoreNext, pre.length + 2 * bits.length + 4,
        pre ++ [true, false] ++ encodeD bits ++
          rest.flatMap (markedSourceBlock false)⟩ =
      ⟨restoreNext, pre.length + (selectedTail (bits :: rest)).length,
        T1⟩ := by
    simpa [P, T1, selectedTail_cons, encodeD_length, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      show 1 + (1 + (2 + 2 * bits.length)) =
        2 * bits.length + 4 by omega,
      show 1 + (1 + (2 + (2 * bits.length +
          (selectedTail rest).length))) =
        2 * bits.length + (4 + (selectedTail rest).length) by omega] using hr
  rw [hr']
  exact he

/-! ## Whole marked-prefix reverse traversal -/

theorem markedArchive_append_last (init : List (List Bool))
    (bits : List Bool) (hne : init ≠ []) :
    markedArchive (init ++ [bits]) =
      markedArchive init ++ markedSourceBlock false bits := by
  obtain ⟨first, more, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp [markedArchive, List.flatMap_append, List.append_assoc]

theorem encodeD_eq_core_term (bits : List Bool) :
    ∃ core, encodeD bits = core ++ [false, true] := by
  induction bits with
  | nil => exact ⟨[], rfl⟩
  | cons bit bits ih =>
      obtain ⟨core, hcore⟩ := ih
      refine ⟨[bit, bit] ++ core, ?_⟩
      simp [encodeD, hcore, List.append_assoc]

theorem markedArchive_eq_core_term (rest : List (List Bool))
    (hne : rest ≠ []) :
    ∃ core, markedArchive rest = core ++ [false, true] := by
  induction rest using List.reverseRecOn with
  | nil => exact absurd rfl hne
  | @append_singleton init bits ih =>
      by_cases hinit : init = []
      · subst init
        obtain ⟨core, hcore⟩ := encodeD_eq_core_term bits
        refine ⟨[false, false] ++ core, ?_⟩
        simp [markedArchive, markedSourceBlock, hcore, List.append_assoc]
      · obtain ⟨core, hcore⟩ := encodeD_eq_core_term bits
        refine ⟨markedArchive init ++ [true, true] ++ core, ?_⟩
        rw [markedArchive_append_last init bits hinit]
        simp [markedSourceBlock, hcore, List.append_assoc]

set_option maxHeartbeats 800000 in
/-- Reverse all marked block bodies from the last data/header pair back to
the seed boundary.  The theorem is existential in the clock because only
the operational composition—not a closed arithmetic normal form—is needed
by the outer round controller. -/
theorem runtimeUnaryRebase_run_reverseMarkedBodies
    (pre tail : List Bool) (rest : List (List Bool)) (last : Bool)
    (hne : rest ≠ []) (hpre : 4 ≤ pre.length) :
    let T := pre ++ [false, true] ++ markedArchive rest ++ tail
    ∃ n, run runtimeUnaryRebaseMachine n
        ⟨revHi last,
          pre.length + 2 + (markedArchive rest).length - 3, T⟩ =
      ⟨tallyHi last, pre.length - 1, T⟩ := by
  dsimp only
  induction rest using List.reverseRecOn generalizing tail with
  | nil => exact absurd rfl hne
  | @append_singleton init bits ih =>
      by_cases hinit : init = []
      · subst init
        let T := pre ++ [false, true] ++ markedSourceBlock true bits ++ tail
        have hp := runtimeUnaryRebase_run_revPairs T
          (pre.length + 2) (bits.length + 1) last (by omega) (by
            intro i hi
            have H := markedRegion_pair_eq
              (pre ++ [false, true]) bits tail true i hi
            simpa [T, List.append_assoc, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using H)
        have hp' : run runtimeUnaryRebaseMachine (2 * (bits.length + 1))
            ⟨revHi last,
              pre.length + 2 + (markedSourceBlock true bits).length - 3, T⟩ =
            ⟨revHi last, pre.length + 1, T⟩ := by
          simpa [markedSourceBlock_length, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using hp
        have hb := runtimeUnaryRebase_run_boundaryOrigin pre
          (encodeD bits ++ tail) last hpre
        have hb' : run runtimeUnaryRebaseMachine 8
            ⟨revHi last, pre.length + 1, T⟩ =
            ⟨tallyHi last, pre.length - 1, T⟩ := by
          simpa [T, markedSourceBlock, List.append_assoc] using hb
        have hrun : run runtimeUnaryRebaseMachine
            (2 * (bits.length + 1) + 8)
            ⟨revHi last,
              pre.length + 2 + (markedSourceBlock true bits).length - 3, T⟩ =
          ⟨tallyHi last, pre.length - 1, T⟩ := by
            rw [run_add, hp', hb']
        refine ⟨2 * (bits.length + 1) + 8, ?_⟩
        simpa [T, markedArchive] using hrun
      · have hneInit : init ≠ [] := hinit
        obtain ⟨core, hcore⟩ := markedArchive_eq_core_term init hneInit
        let P := pre ++ [false, true] ++ core
        let T := pre ++ [false, true] ++ markedArchive (init ++ [bits]) ++ tail
        have hTblock : T =
            (pre ++ [false, true] ++ markedArchive init) ++
              markedSourceBlock false bits ++ tail := by
          simp [T, markedArchive_append_last init bits hinit,
            List.append_assoc]
        have hp := runtimeUnaryRebase_run_revPairs T
          (pre.length + 2 + (markedArchive init).length)
          (bits.length + 1) last (by omega) (by
            intro i hi
            have H := markedRegion_pair_eq
              (pre ++ [false, true] ++ markedArchive init) bits tail false i hi
            rw [hTblock]
            simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm,
              show 1 + (1 + (2 * i + (markedArchive init).length)) =
                2 + (2 * i + (markedArchive init).length) by omega,
              show 1 + (1 + (1 + (2 * i + (markedArchive init).length))) =
                1 + (2 + (2 * i + (markedArchive init).length)) by omega]
              using H)
        have hp' : run runtimeUnaryRebaseMachine (2 * (bits.length + 1))
            ⟨revHi last,
              pre.length + 2 + (markedArchive (init ++ [bits])).length - 3,
              T⟩ =
            ⟨revHi last,
              pre.length + 2 + (markedArchive init).length - 1, T⟩ := by
          rw [markedArchive_append_last init bits hinit, List.length_append,
            markedSourceBlock_length]
          rw [show pre.length + 2 +
              ((markedArchive init).length + (2 * bits.length + 4)) - 3 =
              pre.length + 2 + (markedArchive init).length +
                2 * (bits.length + 1) - 1 by omega]
          exact hp
        have hb := runtimeUnaryRebase_run_boundaryInter P
          (encodeD bits ++ tail) last (by simp [P]; omega)
        have hb' : run runtimeUnaryRebaseMachine 8
            ⟨revHi last,
              pre.length + 2 + (markedArchive init).length - 1, T⟩ =
            ⟨revHi last,
              pre.length + 2 + (markedArchive init).length - 3, T⟩ := by
          have hT : T = P ++ [false, true, true, true] ++
              encodeD bits ++ tail := by
            simp [T, P, markedArchive_append_last init bits hinit,
              markedSourceBlock, hcore, List.append_assoc]
          rw [hT]
          simpa [P, hcore, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hb
        have hi := ih (markedSourceBlock false bits ++ tail) hneInit
        have hi' : ∃ n, run runtimeUnaryRebaseMachine n
            ⟨revHi last,
              pre.length + 2 + (markedArchive init).length - 3, T⟩ =
            ⟨tallyHi last, pre.length - 1, T⟩ := by
          simpa [T, markedArchive_append_last init bits hinit,
            List.append_assoc] using hi
        obtain ⟨n, hn⟩ := hi'
        have hrun : run runtimeUnaryRebaseMachine
            (2 * (bits.length + 1) + 8 + n)
            ⟨revHi last,
              pre.length + 2 + (markedArchive (init ++ [bits])).length - 3,
              T⟩ =
          ⟨tallyHi last, pre.length - 1, T⟩ := by
            rw [show 2 * (bits.length + 1) + 8 + n =
              2 * (bits.length + 1) + (8 + n) by omega,
              run_add, hp', run_add, hb', hn]
        exact ⟨2 * (bits.length + 1) + 8 + n, hrun⟩

/-! ## Forward processed-prefix scan and one complete visit -/

theorem runtimeUnaryRebase_run_processedLaterArchive
    (pre tail : List Bool) (rest : List (List Bool)) :
    ∃ n, run runtimeUnaryRebaseMachine n
        ⟨headerLo, pre.length,
          pre ++ rest.flatMap (markedSourceBlock false) ++ tail⟩ =
      ⟨headerLo,
        pre.length + (rest.flatMap (markedSourceBlock false)).length,
        pre ++ rest.flatMap (markedSourceBlock false) ++ tail⟩ := by
  induction rest generalizing pre with
  | nil => exact ⟨0, rfl⟩
  | cons bits rest ih =>
      have hb := runtimeUnaryRebase_run_processedBlock pre bits
        (rest.flatMap (markedSourceBlock false) ++ tail)
      obtain ⟨n, hn⟩ := ih (pre ++ markedSourceBlock false bits)
      have hn' : run runtimeUnaryRebaseMachine n
          ⟨headerLo, pre.length + (markedSourceBlock false bits).length,
            pre ++ markedSourceBlock false bits ++
              rest.flatMap (markedSourceBlock false) ++ tail⟩ =
          ⟨headerLo,
            pre.length + (markedSourceBlock false bits).length +
              (rest.flatMap (markedSourceBlock false)).length,
            pre ++ markedSourceBlock false bits ++
              rest.flatMap (markedSourceBlock false) ++ tail⟩ := by
        simpa [List.append_assoc] using hn
      have hb' : run runtimeUnaryRebaseMachine (2 * bits.length + 4)
          ⟨headerLo, pre.length,
            pre ++ markedSourceBlock false bits ++
              rest.flatMap (markedSourceBlock false) ++ tail⟩ =
          ⟨headerLo, pre.length + (markedSourceBlock false bits).length,
            pre ++ markedSourceBlock false bits ++
              rest.flatMap (markedSourceBlock false) ++ tail⟩ := by
        simpa [markedSourceBlock_length, List.append_assoc] using hb
      have hrun : run runtimeUnaryRebaseMachine (2 * bits.length + 4 + n)
          ⟨headerLo, pre.length,
            pre ++ markedSourceBlock false bits ++
              rest.flatMap (markedSourceBlock false) ++ tail⟩ =
          ⟨headerLo,
            pre.length + (markedSourceBlock false bits).length +
              (rest.flatMap (markedSourceBlock false)).length,
            pre ++ markedSourceBlock false bits ++
              rest.flatMap (markedSourceBlock false) ++ tail⟩ := by
        rw [run_add, hb', hn']
      refine ⟨2 * bits.length + 4 + n, ?_⟩
      simpa [List.flatMap_cons, List.append_assoc, Nat.add_assoc] using hrun

theorem runtimeUnaryRebase_run_processedArchive
    (pre tail : List Bool) (first : List Bool)
    (more : List (List Bool)) :
    ∃ n, run runtimeUnaryRebaseMachine n
        ⟨firstLo, pre.length,
          pre ++ markedArchive (first :: more) ++ tail⟩ =
      ⟨headerLo, pre.length + (markedArchive (first :: more)).length,
        pre ++ markedArchive (first :: more) ++ tail⟩ := by
  have hf := runtimeUnaryRebase_run_processedFirstBlock pre first
    (more.flatMap (markedSourceBlock false) ++ tail)
  obtain ⟨n, hn⟩ := runtimeUnaryRebase_run_processedLaterArchive
    (pre ++ markedSourceBlock true first) tail more
  refine ⟨2 * first.length + 4 + n, ?_⟩
  rw [run_add]
  have hf' : run runtimeUnaryRebaseMachine (2 * first.length + 4)
      ⟨firstLo, pre.length,
        pre ++ markedArchive (first :: more) ++ tail⟩ =
      ⟨headerLo, pre.length + (markedSourceBlock true first).length,
        pre ++ markedArchive (first :: more) ++ tail⟩ := by
    simpa [markedArchive, markedSourceBlock_length,
      List.append_assoc] using hf
  rw [hf']
  simpa [markedArchive, List.append_assoc, Nat.add_assoc] using hn

theorem selectedTail_head (bits : List Bool) (rest : List (List Bool)) :
    (selectedTail (bits :: rest)).getD 0 false = true := by
  rw [selectedTail_cons]
  simp

theorem selectedTail_nil : selectedTail [] = [] := by
  simp [selectedTail, flattenPairs]

theorem markedArchive_append_singleton_length
    (done : List (List Bool)) (bits : List Bool) :
    4 ≤ (markedArchive (done ++ [bits])).length := by
  cases done with
  | nil => simp [markedArchive, markedSourceBlock_length]
  | cons first later =>
      rw [markedArchive_append_last (first :: later) bits (by simp),
        List.length_append, markedSourceBlock_length]
      omega

set_option maxHeartbeats 1000000 in
theorem runtimeUnaryRebase_run_markNext
    (pre : List Bool) (done : List (List Bool))
    (bits : List Bool) (more : List (List Bool)) :
    let T0 := pre ++ markedArchive done ++ selectedTail (bits :: more)
    let T1 := pre ++ markedArchive (done ++ [bits]) ++ selectedTail more
    ∃ n, run runtimeUnaryRebaseMachine n
        ⟨firstLo, pre.length, T0⟩ =
      ⟨revTermHi (more = []),
        pre.length + (markedArchive (done ++ [bits])).length - 1, T1⟩ := by
  dsimp only
  let T0 := pre ++ markedArchive done ++ selectedTail (bits :: more)
  let T1 := pre ++ markedArchive (done ++ [bits]) ++ selectedTail more
  cases done with
  | nil =>
      cases more with
      | nil =>
          have H := runtimeUnaryRebase_run_freshFirstBlock pre bits [] false (by simp)
          refine ⟨2 * bits.length + 7, ?_⟩
          have hT0 : T0 = pre ++ [true, false] ++ encodeD bits := by
            simp [T0, markedArchive, selectedTail_cons, selectedTail_nil,
              List.append_assoc]
          have hT1 : T1 = pre ++ markedSourceBlock true bits := by
            simp [T1, markedArchive, selectedTail_nil]
          simpa [markedArchive, selectedTail_cons, selectedTail_nil,
            markedSourceBlock_length, List.append_assoc] using H
      | cons next more =>
          have H := runtimeUnaryRebase_run_freshFirstBlock pre bits
            (selectedTail (next :: more)) true (selectedTail_head next more)
          refine ⟨2 * bits.length + 7, ?_⟩
          have hT0 : T0 = pre ++ [true, false] ++ encodeD bits ++
              selectedTail (next :: more) := by
            simp [T0, markedArchive, selectedTail_cons, List.append_assoc]
          have hT1 : T1 = pre ++ markedSourceBlock true bits ++
              selectedTail (next :: more) := by
            simp [T1, markedArchive, List.append_assoc]
          simpa [markedArchive, selectedTail_cons,
            markedSourceBlock_length, List.append_assoc] using H
  | cons first later =>
      obtain ⟨ns, hs⟩ := runtimeUnaryRebase_run_processedArchive pre
        (selectedTail (bits :: more)) first later
      have happ : markedArchive (first :: later ++ [bits]) =
          markedArchive (first :: later) ++ markedSourceBlock false bits := by
        simpa using markedArchive_append_last (first :: later) bits (by simp)
      cases more with
      | nil =>
          have hf := runtimeUnaryRebase_run_freshBlock
            (pre ++ markedArchive (first :: later)) bits [] false (by simp)
          refine ⟨ns + (2 * bits.length + 5), ?_⟩
          rw [run_add, hs]
          rw [happ]
          convert hf using 1 <;> simp [T0, T1,
            selectedTail_cons, selectedTail_nil,
            List.append_assoc, markedSourceBlock_length] <;> omega
      | cons next more =>
          have hf := runtimeUnaryRebase_run_freshBlock
            (pre ++ markedArchive (first :: later)) bits
            (selectedTail (next :: more)) true (selectedTail_head next more)
          refine ⟨ns + (2 * bits.length + 5), ?_⟩
          rw [run_add, hs]
          rw [happ]
          convert hf using 1 <;> simp [T0, T1,
            selectedTail_cons, List.append_assoc, markedSourceBlock_length,
            Bool.not_true] <;> omega

set_option maxHeartbeats 1000000 in
theorem runtimeUnaryRebase_run_returnMarked
    (pre : List Bool) (a b : Bool) (done : List (List Bool))
    (bits : List Bool) (more : List (List Bool)) :
    let A := pre ++ [a, b] ++ unaryRebaseFrontier done.length
    let T := A ++ markedArchive (done ++ [bits]) ++ selectedTail more
    ∃ n, run runtimeUnaryRebaseMachine n
        ⟨revTermHi (more = []),
          A.length + (markedArchive (done ++ [bits])).length - 1, T⟩ =
      ⟨tallyHi (more = []), pre.length + 2 * done.length + 3, T⟩ := by
  dsimp only
  let A := pre ++ [a, b] ++ unaryRebaseFrontier done.length
  let T := A ++ markedArchive (done ++ [bits]) ++ selectedTail more
  let P := pre ++ [a, b] ++ [false, true] ++
    List.replicate (2 * done.length) true
  have hm := markedArchive_append_singleton_length done bits
  have ht := runtimeUnaryRebase_run_revTerm T
    (A.length + (markedArchive (done ++ [bits])).length - 1)
    (more = []) (by simp [A, unaryRebaseFrontier]; omega)
  obtain ⟨nr, hr⟩ := runtimeUnaryRebase_run_reverseMarkedBodies P
    (selectedTail more) (done ++ [bits]) (more = []) (by simp)
    (by simp [P]; omega)
  have hstart : P.length + 2 + (markedArchive (done ++ [bits])).length - 3 =
      A.length + (markedArchive (done ++ [bits])).length - 3 := by
    simp [P, A, unaryRebaseFrontier]
    omega
  have hphead : P.length - 1 = pre.length + 2 * done.length + 3 := by
    simp [P]
    omega
  rw [hstart, hphead] at hr
  refine ⟨2 + nr, ?_⟩
  rw [run_add, ht]
  have hsub : A.length + (markedArchive (done ++ [bits])).length - 1 - 2 =
      A.length + (markedArchive (done ++ [bits])).length - 3 := by omega
  rw [hsub]
  simpa [A, P, T, unaryRebaseFrontier, List.append_assoc] using hr

theorem runtimeUnaryRebase_run_markReturn
    (pre : List Bool) (a b : Bool) (done : List (List Bool))
    (bits : List Bool) (more : List (List Bool)) :
    let A := pre ++ [a, b] ++ unaryRebaseFrontier done.length
    let T0 := A ++ markedArchive done ++ selectedTail (bits :: more)
    let T1 := A ++ markedArchive (done ++ [bits]) ++ selectedTail more
    ∃ n, run runtimeUnaryRebaseMachine n ⟨firstLo, A.length, T0⟩ =
      ⟨tallyHi (more = []), pre.length + 2 * done.length + 3, T1⟩ := by
  dsimp only
  obtain ⟨nf, hf⟩ := runtimeUnaryRebase_run_markNext
    (pre ++ [a, b] ++ unaryRebaseFrontier done.length) done bits more
  obtain ⟨nb, hb⟩ := runtimeUnaryRebase_run_returnMarked
    pre a b done bits more
  refine ⟨nf + nb, ?_⟩
  rw [run_add, hf, hb]

theorem runtimeUnaryRebase_run_extendMarked
    (pre : List Bool) (a b : Bool) (done : List (List Bool))
    (bits : List Bool) (more : List (List Bool)) :
    let T0 := pre ++ [a, b] ++ unaryRebaseFrontier done.length ++
      markedArchive (done ++ [bits]) ++ selectedTail more
    let T1 := pre ++ unaryRebaseFrontier (done.length + 1) ++
      markedArchive (done ++ [bits]) ++ selectedTail more
    run runtimeUnaryRebaseMachine (4 * done.length + 9)
        ⟨tallyHi (more = []), pre.length + 2 * done.length + 3, T0⟩ =
      ⟨if more = [] then restoreFirstLo else firstLo,
        pre.length + 2 * done.length + 6, T1⟩ := by
  dsimp only
  simpa [List.append_assoc] using
    runtimeUnaryRebase_run_extendFrontier pre
      (markedArchive (done ++ [bits]) ++ selectedTail more)
      a b (more = []) done.length

set_option maxHeartbeats 1000000 in
/-- One complete visit: scan the marked prefix, mark the next fresh block,
reverse the entire enlarged prefix, and emit one unary pair. -/
theorem runtimeUnaryRebase_run_visit
    (pre : List Bool) (a b : Bool) (done : List (List Bool))
    (bits : List Bool) (more : List (List Bool)) :
    let k := done.length
    let T0 := pre ++ [a, b] ++ unaryRebaseFrontier k ++
      markedArchive done ++ selectedTail (bits :: more)
    let T1 := pre ++ unaryRebaseFrontier (k + 1) ++
      markedArchive (done ++ [bits]) ++ selectedTail more
    ∃ n, run runtimeUnaryRebaseMachine n
        ⟨firstLo, pre.length + 2 * k + 6, T0⟩ =
      ⟨if more = [] then restoreFirstLo else firstLo,
        pre.length + 2 * k + 6, T1⟩ := by
  dsimp only
  let A := pre ++ [a, b] ++ unaryRebaseFrontier done.length
  let T0 := A ++ markedArchive done ++ selectedTail (bits :: more)
  obtain ⟨nm, hm⟩ := runtimeUnaryRebase_run_markReturn
    pre a b done bits more
  have hhead : (pre ++ [a, b] ++ unaryRebaseFrontier done.length).length =
      pre.length + 2 * done.length + 6 := by
    simp [unaryRebaseFrontier]
    omega
  rw [hhead] at hm
  have he := runtimeUnaryRebase_run_extendMarked pre a b done bits more
  refine ⟨nm + (4 * done.length + 9), ?_⟩
  rw [run_add, hm, he]

theorem split_last_two {xs : List Bool} {n : Nat}
    (hlen : xs.length = n + 2) :
    ∃ pre a b, xs = pre ++ [a, b] ∧ pre.length = n := by
  have hxs : xs ≠ [] := by
    intro h
    subst xs
    simp at hlen
  let ys := xs.dropLast
  have hyslen : ys.length = n + 1 := by
    simp [ys, List.length_dropLast, hlen]
  have hys : ys ≠ [] := by
    intro h
    have hz := congrArg List.length h
    simp [ys, List.length_dropLast, hlen] at hz
  let b := xs.getLast hxs
  let a := ys.getLast hys
  let pre := ys.dropLast
  have hpre : pre.length = n := by
    simp [pre, List.length_dropLast, hyslen]
  have hxb := List.dropLast_append_getLast hxs
  have hya := List.dropLast_append_getLast hys
  refine ⟨pre, a, b, ?_, hpre⟩
  calc
    xs = ys ++ [b] := by simpa [ys, b] using hxb.symm
    _ = (pre ++ [a]) ++ [b] := by rw [show pre ++ [a] = ys by
      simpa [pre, a] using hya]
    _ = pre ++ [a, b] := by simp [List.append_assoc]

set_option maxHeartbeats 1000000 in
theorem runtimeUnaryRebase_run_visits
    (base scratch : List Bool) (done todo : List (List Bool))
    (htodo : todo ≠ []) (hscratch : scratch.length = 2 * todo.length) :
    let R := base.length + scratch.length + 2 * done.length + 4
    let T0 := base ++ scratch ++ unaryRebaseFrontier done.length ++
      markedArchive done ++ selectedTail todo
    let T1 := base ++ unaryRebaseFrontier (done.length + todo.length) ++
      markedArchive (done ++ todo)
    ∃ n, run runtimeUnaryRebaseMachine n ⟨firstLo, R, T0⟩ =
      ⟨restoreFirstLo, R, T1⟩ := by
  dsimp only
  induction todo generalizing scratch done with
  | nil => exact absurd rfl htodo
  | cons bits more ih =>
      have hslen : scratch.length = 2 * more.length + 2 := by
        simpa using hscratch
      obtain ⟨pre, a, b, hshape, hpre⟩ := split_last_two hslen
      subst scratch
      obtain ⟨nv, hv⟩ := runtimeUnaryRebase_run_visit
        (base ++ pre) a b done bits more
      have hdoneLen : (done ++ [bits]).length = done.length + 1 := by simp
      cases more with
      | nil =>
          have htodoLen : [bits].length = 1 := rfl
          have hpnil : pre = [] :=
            List.eq_nil_of_length_eq_zero (by simpa using hpre)
          subst pre
          refine ⟨nv, ?_⟩
          convert hv using 2 <;> simp [selectedTail_nil, List.append_assoc,
            List.length_cons, List.length_nil, Nat.add_assoc,
            hdoneLen, htodoLen, Nat.add_comm, Nat.add_left_comm] <;> omega
      | cons next later =>
          have htodoLen : (bits :: next :: later).length =
              (next :: later).length + 1 := rfl
          have hprelen : pre.length = 2 * (next :: later).length := by
            simpa using hpre
          obtain ⟨ni, hi⟩ := ih pre (done ++ [bits]) (by simp) hprelen
          have hv' : run runtimeUnaryRebaseMachine nv
              ⟨firstLo,
                base.length + (pre ++ [a, b]).length +
                  2 * done.length + 4,
                base ++ (pre ++ [a, b]) ++
                  unaryRebaseFrontier done.length ++ markedArchive done ++
                  selectedTail (bits :: next :: later)⟩ =
              ⟨firstLo,
                base.length + pre.length +
                  2 * (done ++ [bits]).length + 4,
                base ++ pre ++ unaryRebaseFrontier (done ++ [bits]).length ++
                  markedArchive (done ++ [bits]) ++
                  selectedTail (next :: later)⟩ := by
            convert hv using 2 <;> simp [List.append_assoc, Nat.add_assoc,
              List.length_cons, List.length_nil, Nat.add_comm,
              hdoneLen, htodoLen, Nat.add_left_comm] <;> omega
          refine ⟨nv + ni, ?_⟩
          rw [run_add]
          rw [hv']
          convert hi using 1 <;> simp [List.append_assoc, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] <;> omega

set_option maxHeartbeats 1000000 in
theorem runtimeUnaryRebase_run_complete
    (base scratch : List Bool) (a b : Bool)
    (bits : List Bool) (more : List (List Bool))
    (hscratch : scratch.length = 2 * (bits :: more).length) :
    let R := base.length + scratch.length + 4
    let T0 := base ++ scratch ++ [a, b, false, true] ++
      selectedTail (bits :: more)
    let T1 := base ++ unaryRebaseFrontier (bits :: more).length ++
      selectedTail (bits :: more)
    ∃ n, run runtimeUnaryRebaseMachine n ⟨init1, R, T0⟩ =
      ⟨done, R + (selectedTail (bits :: more)).length, T1⟩ := by
  dsimp only
  have hi := runtimeUnaryRebase_run_init (base ++ scratch)
    (selectedTail (bits :: more)) a b
  obtain ⟨nv, hv⟩ := runtimeUnaryRebase_run_visits base scratch []
    (bits :: more) (by simp) hscratch
  have hr := runtimeUnaryRebase_run_restoreArchive
    (base ++ unaryRebaseFrontier (bits :: more).length) bits more
  let nc := 2 * bits.length + 4 + restoreArchiveClock more + 1
  have hi' : run runtimeUnaryRebaseMachine 8
      ⟨init1, base.length + scratch.length + 4,
        base ++ scratch ++ [a, b, false, true] ++
          selectedTail (bits :: more)⟩ =
      ⟨firstLo, base.length + scratch.length + 4,
        base ++ scratch ++ unaryRebaseFrontier 0 ++
          selectedTail (bits :: more)⟩ := by
    simpa [unaryRebaseFrontier_zero, List.append_assoc] using hi
  have hv' : run runtimeUnaryRebaseMachine nv
      ⟨firstLo, base.length + scratch.length + 4,
        base ++ scratch ++ unaryRebaseFrontier 0 ++
          selectedTail (bits :: more)⟩ =
      ⟨restoreFirstLo, base.length + scratch.length + 4,
        base ++ unaryRebaseFrontier (bits :: more).length ++
          markedArchive (bits :: more)⟩ := by
    simpa [List.append_assoc] using hv
  have hpre : (base ++ unaryRebaseFrontier (bits :: more).length).length =
      base.length + scratch.length + 4 := by
    simp [unaryRebaseFrontier, hscratch]
    omega
  have hr' := hr
  rw [hpre] at hr'
  refine ⟨8 + nv + nc, ?_⟩
  rw [show 8 + nv + nc = 8 + (nv + nc) by omega,
    run_add, hi', run_add, hv']
  simpa [nc, selectedTail_nil, List.append_assoc, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using hr'

theorem flattenPairs_replicate_true (d : Nat) :
    flattenPairs (List.replicate d (true, true)) =
      List.replicate (2 * d) true := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [List.replicate_succ]
      simp only [flattenPairs, List.flatMap_cons]
      rw [ih, show 2 * (d + 1) = 2 + 2 * d by omega,
        List.replicate_add]
      rfl

theorem unaryRebaseFrontier_eq_boundary_prefix (d : Nat) :
    unaryRebaseFrontier d =
      [false, true] ++ zeroCopyRebasePrefix d := by
  simp [unaryRebaseFrontier, zeroCopyRebasePrefix,
    flattenPairs_append, flattenPairs_replicate_true, flattenPairs,
    List.append_assoc]

set_option maxHeartbeats 1000000 in
theorem runtimeUnaryRebase_run_physical
    (phys : List Bool) (bits : List Bool) (more : List (List Bool))
    (hfit : 2 * (bits :: more).length + 2 ≤ phys.length) :
    let R := phys.length + 2
    let T0 := phys ++ [false, true] ++ selectedTail (bits :: more)
    ∃ base n,
      base.length = phys.length - (2 * (bits :: more).length + 2) ∧
      run runtimeUnaryRebaseMachine n ⟨init1, R, T0⟩ =
        ⟨done, R + (selectedTail (bits :: more)).length,
          base ++ [false, true] ++
            sourceSelectorInput (bits :: more).length 0 (bits :: more)⟩ := by
  dsimp only
  let L := 2 * (bits :: more).length + 2
  let p := phys.length - L
  let suffix := phys.drop p
  have hsuffix : suffix.length = 2 * (bits :: more).length + 2 := by
    simp only [suffix, List.length_drop]
    change phys.length - (phys.length - L) = L
    omega
  obtain ⟨scratch, a, b, hs, hscratch⟩ := split_last_two hsuffix
  let base := phys.take p
  have hphys : phys = base ++ scratch ++ [a, b] := by
    have H := List.take_append_drop p phys
    rw [show phys.drop p = suffix by rfl, hs] at H
    simpa [base, List.append_assoc] using H.symm
  obtain ⟨n, hn⟩ := runtimeUnaryRebase_run_complete
    base scratch a b bits more hscratch
  refine ⟨base, n, ?_, ?_⟩
  · have hp : p ≤ phys.length := by simp [p]
    simp [base, List.length_take, hp, p, L]
  · have hR : phys.length + 2 = base.length + scratch.length + 4 := by
      rw [hphys]
      simp
      omega
    have hT : phys ++ [false, true] ++ selectedTail (bits :: more) =
        base ++ scratch ++ [a, b, false, true] ++
          selectedTail (bits :: more) := by
      rw [hphys]
      simp [List.append_assoc]
    have hn' := hn
    rw [unaryRebaseFrontier_eq_boundary_prefix] at hn'
    have hout : base ++
          ([false, true] ++ zeroCopyRebasePrefix (bits :: more).length) ++
          selectedTail (bits :: more) =
        base ++ [false, true] ++
          sourceSelectorInput (bits :: more).length 0 (bits :: more) := by
      rw [show base ++
          ([false, true] ++ zeroCopyRebasePrefix (bits :: more).length) ++
          selectedTail (bits :: more) =
        base ++ [false, true] ++
          (zeroCopyRebasePrefix (bits :: more).length ++
            selectedTail (bits :: more)) by simp [List.append_assoc],
        zeroCopyRebasePrefix_archive]
    rw [hout] at hn'
    rw [hR, hT]
    simpa [List.append_assoc] using hn'

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUnaryRebaseWriter
