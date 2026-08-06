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
      simp only [List.flatMap_cons]
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

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUnaryRebaseWriter
