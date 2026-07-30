import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUnaryDupMachine

/-!
# MCSP verifier, phase 2a: a finite-control unary `2^n` loop

The MCSP verifier must separate its raw truth table from the appended circuit
certificate.  Its table has exactly `2^n` bits, so this file supplies the
missing arithmetic loop as an actual `ComposableMachine.Machine`.

The tape invariant is

`[TT]^a FF 0^W [FF]^done [TT]^todo TF rest`.

`a` is the current accumulator, the doubled counter records completed and
remaining rounds, and `TF` is an unambiguous end sentinel.  One round:

1. marks one live counter unit;
2. runs the already verified `dupMachine` on the accumulator;
3. overwrites the old middle separator, merging the two copies;
4. resets and repeats.

The reserved zero workspace

`workspace a k = 2*(a+1)*(2^k-1)`

is exact for `k` remaining rounds.  Each merge implements
`a ↦ 2*a+1`; from zero this reaches `2^n-1`, and the terminal `TF`
unit supplies the final `+1`, giving exactly `2^n` countable units.
No semantic function is hidden in the transition table.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPTwoPowMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.DIndexMachine
  (flat2 getD_at writeAt_boundary run_one)
open PallLean.Paper93.DeepMath.PathB.UnaryDupMachine

/-- Control states for the counter scan, embedded duplicator, and merge. -/
inductive PowState
  | skipAcc
  | seekCounter
  | inspectCounter
  | eraseCounterFirst
  | dup (q : dupMachine.State)
  | enterMerge
  | mergeFirst
  | mergeSecond
  | done
  deriving DecidableEq, Fintype

/-- The exact blank budget for `k` future doublings of accumulator `a`. -/
def workspace (a k : ℕ) : ℕ :=
  2 * (a + 1) * (2 ^ k - 1)

theorem workspace_zero (a : ℕ) : workspace a 0 = 0 := by
  simp [workspace]

/-- One round consumes `2*a+2` blanks and leaves the exact budget for the
doubled accumulator. -/
theorem workspace_succ (a k : ℕ) :
    workspace a (k + 1) =
      2 * a + 2 + workspace (2 * a + 1) k := by
  have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hrepr : 2 ^ k = (2 ^ k - 1) + 1 :=
    (Nat.sub_add_cancel hpow).symm
  have hsucc : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
    rw [pow_succ, hrepr]
    omega
  unfold workspace
  rw [hsucc]
  ring

/-- Canonical loop tape. -/
def powTape (a done todo : ℕ) (rest : List Bool) : List Bool :=
  flat2 (List.replicate a true) ++
    false :: false ::
      (List.replicate (workspace a todo) false ++
        (List.replicate (2 * done) false ++
          (flat2 (List.replicate todo true) ++ true :: false :: rest)))

/-- The finite-control unary exponentiation machine. -/
def powMachine : Machine where
  State := PowState
  fin := inferInstance
  dec := inferInstance
  start := .skipAcc
  halt
    | .done => true
    | _ => false
  δ q b :=
    match q with
    | .skipAcc =>
        if b then (.skipAcc, none, 1) else (.seekCounter, none, 1)
    | .seekCounter =>
        if b then (.inspectCounter, none, 1) else (.seekCounter, none, 1)
    | .inspectCounter =>
        if b then (.eraseCounterFirst, some false, 0)
        else (.done, none, 2)
    | .eraseCounterFirst => (.dup dupMachine.start, some false, 3)
    | .dup s =>
        if dupMachine.halt s then (.enterMerge, none, 2)
        else
          let tr := dupMachine.δ s b
          (.dup tr.1, tr.2.1, tr.2.2)
    | .enterMerge => (.mergeFirst, none, 2)
    | .mergeFirst => (.mergeSecond, some true, 1)
    | .mergeSecond => (.skipAcc, some true, 3)
    | .done => (.done, none, 2)
  accept
    | .done => true
    | _ => false

/-- Embed a duplicator configuration in the exponentiation machine. -/
def embedDup (c : Cfg dupMachine) : Cfg powMachine :=
  ⟨.dup c.st, c.hd, c.tp⟩

theorem pow_halt_dup (q : dupMachine.State) :
    powMachine.halt (.dup q) = false := rfl

theorem step_embedDup (c : Cfg dupMachine)
    (h : dupMachine.halt c.st = false) :
    step powMachine (embedDup c) = embedDup (step dupMachine c) := by
  simp [step, embedDup, powMachine, h]

/-- Simulation of a duplicator prefix before its first halt. -/
theorem run_embedDup (c : Cfg dupMachine) (t : ℕ)
    (h : ∀ u, u < t → dupMachine.halt (run dupMachine u c).st = false) :
    run powMachine t (embedDup c) = embedDup (run dupMachine t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, ih (fun u hu => h u (by omega)),
        step_embedDup _ (h t (by omega)), ← run_succ]

/-- Any proved duplicator run can be lifted up to its first halting instant. -/
theorem lift_dup_to_halt {c : Cfg dupMachine} {t : ℕ}
    {q : dupMachine.State} {p : ℕ} {T : List Bool}
    (hrun : run dupMachine t c = ⟨q, p, T⟩)
    (hh : dupMachine.halt q = true) :
    ∃ u, u ≤ t ∧ run powMachine u (embedDup c) = embedDup ⟨q, p, T⟩ := by
  have hex : ∃ u, dupMachine.halt (run dupMachine u c).st = true := by
    exact ⟨t, by rw [hrun]; exact hh⟩
  let u := Nat.find hex
  have hu : u ≤ t := Nat.find_le (by rw [hrun]; exact hh)
  have hhalt : dupMachine.halt (run dupMachine u c).st = true :=
    Nat.find_spec hex
  have hfreeze : run dupMachine u c = ⟨q, p, T⟩ := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hu
    rw [run_add, run_of_halted dupMachine hhalt] at hrun
    exact hrun
  have hpre : ∀ v, v < u → dupMachine.halt (run dupMachine v c).st = false := by
    intro v hv
    simpa using Nat.find_min hex hv
  refine ⟨u, hu, ?_⟩
  rw [run_embedDup c u hpre, hfreeze]

/-! ## Exact counter-entry scan -/

theorem step_skip_true {p : ℕ} {T : List Bool}
    (h : T.getD p false = true) :
    step powMachine ⟨.skipAcc, p, T⟩ = ⟨.skipAcc, p + 1, T⟩ := by
  simp only [step, powMachine, h, moveHead]
  rfl

theorem step_skip_false {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) :
    step powMachine ⟨.skipAcc, p, T⟩ = ⟨.seekCounter, p + 1, T⟩ := by
  simp only [step, powMachine, h, moveHead]
  rfl

theorem step_seek_false {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) :
    step powMachine ⟨.seekCounter, p, T⟩ =
      ⟨.seekCounter, p + 1, T⟩ := by
  simp only [step, powMachine, h, moveHead]
  rfl

theorem step_seek_true {p : ℕ} {T : List Bool}
    (h : T.getD p false = true) :
    step powMachine ⟨.seekCounter, p, T⟩ =
      ⟨.inspectCounter, p + 1, T⟩ := by
  simp only [step, powMachine, h, moveHead]
  rfl

theorem step_inspect_true {p : ℕ} {T : List Bool}
    (h : T.getD p false = true) :
    step powMachine ⟨.inspectCounter, p, T⟩ =
      ⟨.eraseCounterFirst, p - 1, writeAt T p false⟩ := by
  simp only [step, powMachine, h, moveHead]
  rfl

theorem step_erase_first {p : ℕ} {T : List Bool} :
    step powMachine ⟨.eraseCounterFirst, p, T⟩ =
      embedDup ⟨dupMachine.start, 0, writeAt T p false⟩ := by
  simp only [step, powMachine, embedDup, moveHead]
  rfl

theorem walk_skip_true (P Z : List Bool) (k : ℕ) :
    run powMachine k
      ⟨.skipAcc, P.length, P ++ (List.replicate k true ++ Z)⟩ =
      ⟨.skipAcc, P.length + k, P ++ (List.replicate k true ++ Z)⟩ := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
      simp only [List.replicate_succ]
      rw [show k + 1 = 1 + k by omega, run_add, run_one]
      change run powMachine k
        (step powMachine
          ⟨.skipAcc, P.length,
            P ++ (true :: (List.replicate k true ++ Z))⟩) = _
      rw [step_skip_true (getD_at P true _)]
      have H := ih (P ++ [true])
      convert H using 1 <;> simp [List.append_assoc] <;> omega

theorem walk_seek_false (P Z : List Bool) (k : ℕ) :
    run powMachine k
      ⟨.seekCounter, P.length, P ++ (List.replicate k false ++ Z)⟩ =
      ⟨.seekCounter, P.length + k, P ++ (List.replicate k false ++ Z)⟩ := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
      simp only [List.replicate_succ]
      rw [show k + 1 = 1 + k by omega, run_add, run_one]
      change run powMachine k
        (step powMachine
          ⟨.seekCounter, P.length,
            P ++ (false :: (List.replicate k false ++ Z))⟩) = _
      rw [step_seek_false (getD_at P false _)]
      have H := ih (P ++ [false])
      convert H using 1 <;> simp [List.append_assoc] <;> omega

/-- Mark one live doubled counter unit and enter the duplicator. -/
theorem mark_counter_pair (P R : List Bool) :
    run powMachine 2
      ⟨.inspectCounter, P.length + 1, P ++ true :: true :: R⟩ =
      embedDup ⟨dupMachine.start, 0, P ++ false :: false :: R⟩ := by
  rw [show 2 = 1 + 1 by omega, run_add, run_one]
  rw [run_one]
  have hsecond :
      (P ++ true :: true :: R).getD (P.length + 1) false = true := by
    rw [show P ++ true :: true :: R = (P ++ [true]) ++ true :: R by simp,
      show P.length + 1 = (P ++ [true]).length by simp]
    exact getD_at (P ++ [true]) true R
  rw [step_inspect_true hsecond]
  rw [show P ++ true :: true :: R = (P ++ [true]) ++ true :: R by simp,
    show P.length + 1 = (P ++ [true]).length by simp,
    writeAt_boundary]
  simp only [List.length_append, List.length_singleton]
  rw [show P.length + 1 - 1 = P.length by omega, step_erase_first]
  rw [show P ++ [true] ++ false :: R = P ++ true :: false :: R by simp]
  rw [writeAt_boundary]

/-- Starting from an accumulator run followed by zeros and a live doubled
counter cell, reach the embedded duplicator with that cell changed `TT ↦ FF`. -/
theorem enter_dup (A Z : ℕ) (R : List Bool) :
    run powMachine (A + 1 + Z + 1 + 2)
      ⟨.skipAcc, 0,
        List.replicate A true ++ false ::
          (List.replicate Z false ++ true :: true :: R)⟩ =
      embedDup
        ⟨dupMachine.start, 0,
          List.replicate A true ++ false ::
            (List.replicate Z false ++ false :: false :: R)⟩ := by
  rw [show A + 1 + Z + 1 + 2 = A + (1 + (Z + (1 + 2))) by omega,
    run_add]
  have hs := walk_skip_true [] (false ::
    (List.replicate Z false ++ true :: true :: R)) A
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at hs
  rw [hs, run_add, run_one]
  have hterm :
      (List.replicate A true ++ false ::
        (List.replicate Z false ++ true :: true :: R)).getD A false = false := by
    simpa using getD_at (List.replicate A true) false
      (List.replicate Z false ++ true :: true :: R)
  rw [step_skip_false hterm]
  have hz := walk_seek_false
    (List.replicate A true ++ [false])
    (true :: true :: R) Z
  simp only [List.length_append, List.length_replicate,
    List.length_singleton] at hz
  have hz' :
      run powMachine Z
        ⟨.seekCounter, A + 1,
          List.replicate A true ++ false ::
            (List.replicate Z false ++ true :: true :: R)⟩ =
        ⟨.seekCounter, A + 1 + Z,
          List.replicate A true ++ false ::
            (List.replicate Z false ++ true :: true :: R)⟩ := by
    simpa [List.append_assoc] using hz
  rw [run_add]
  rw [hz', run_add, run_one]
  have hseek :
      (List.replicate A true ++ false ::
        (List.replicate Z false ++ true :: true :: R)).getD
          (A + 1 + Z) false = true := by
    let P := (List.replicate A true ++ [false]) ++ List.replicate Z false
    have htape :
        List.replicate A true ++ false ::
            (List.replicate Z false ++ true :: true :: R) =
          P ++ true :: true :: R := by
      simp [P, List.append_assoc]
    rw [htape, show A + 1 + Z = P.length by simp [P]; omega]
    exact getD_at P true (true :: R)
  rw [step_seek_true hseek]
  let P := (List.replicate A true ++ [false]) ++ List.replicate Z false
  have hmark := mark_counter_pair P R
  have htape :
      List.replicate A true ++ false ::
          (List.replicate Z false ++ true :: true :: R) =
        P ++ true :: true :: R := by
    simp [P, List.append_assoc]
  have hout :
      List.replicate A true ++ false ::
          (List.replicate Z false ++ false :: false :: R) =
        P ++ false :: false :: R := by
    simp [P, List.append_assoc]
  rw [show A + 1 + Z + 1 = P.length + 1 by simp [P]; omega, htape]
  simpa [hout] using hmark

/-! ## Embedded duplication and separator merge -/

/-- Lift the verified unary duplicator on the exact tape shape used by one
exponentiation round. -/
theorem run_embedded_dup (a z : ℕ) (rest : List Bool) :
    ∃ t, t ≤ (a + 1) * (4 * a + 12) + 4 * a + 3 ∧
      run powMachine t
        (embedDup
          ⟨dupMachine.start, 0,
            dupTape 0 a 0 (z + 2 * a) rest⟩) =
        embedDup
          ⟨(6, false), 2 * a, dupTape 0 a a z rest⟩ := by
  obtain ⟨t, ht, hr⟩ := dupM_run a z rest false
  obtain ⟨u, hu, hur⟩ :=
    lift_dup_to_halt (c :=
      ⟨dupMachine.start, 0, dupTape 0 a 0 (z + 2 * a) rest⟩)
      (t := t) (q := (6, false)) (p := 2 * a)
      (T := dupTape 0 a a z rest) hr (by simp [dupMachine])
  exact ⟨u, hu.trans ht, hur⟩

theorem step_dup_finished {p : ℕ} {T : List Bool} :
    step powMachine (embedDup ⟨(6, false), p, T⟩) =
      ⟨.enterMerge, p, T⟩ := by
  simp [step, embedDup, powMachine, dupMachine, moveHead]

theorem step_enter_merge {p : ℕ} {T : List Bool} :
    step powMachine ⟨.enterMerge, p, T⟩ =
      ⟨.mergeFirst, p, T⟩ := by
  rfl

theorem step_merge_first {p : ℕ} {T : List Bool} :
    step powMachine ⟨.mergeFirst, p, T⟩ =
      ⟨.mergeSecond, p + 1, writeAt T p true⟩ := by
  rfl

theorem step_merge_second {p : ℕ} {T : List Bool} :
    step powMachine ⟨.mergeSecond, p, T⟩ =
      ⟨.skipAcc, 0, writeAt T p true⟩ := by
  rfl

theorem writeAt_after_replicate (n : ℕ) (v b w : Bool) (R : List Bool) :
    writeAt (List.replicate n v ++ b :: R) n w =
      List.replicate n v ++ w :: R := by
  simpa using
    (writeAt_boundary (P := List.replicate n v) (b := b) (R := R) (w := w))

theorem writeAt_after_replicate_true_extra (n : ℕ) (R : List Bool) :
    writeAt
        ((List.replicate n true ++ [true]) ++ false :: R)
        (n + 1) true =
      (List.replicate n true ++ [true]) ++ true :: R := by
  simpa using
    (writeAt_boundary
      (P := List.replicate n true ++ [true])
      (b := false) (R := R) (w := true))

set_option maxHeartbeats 2000000 in
/-- The wrapper replaces the old doubled separator by one live doubled unit.
Thus the physical accumulator recurrence is `a ↦ 2a+1`. -/
theorem finish_merge (a z : ℕ) (rest : List Bool) :
    run powMachine 4
      (embedDup
        ⟨(6, false), 2 * a, dupTape 0 a a z rest⟩) =
      ⟨.skipAcc, 0,
        flat2 (List.replicate (2 * a + 1) true) ++
          List.replicate z false ++ rest⟩ := by
  rw [show 4 = 1 + (1 + (1 + 1)) by omega,
    run_add, run_one, run_add, run_one, run_add, run_one, run_one]
  rw [step_dup_finished, step_enter_merge, step_merge_first]
  unfold dupTape
  simp only [List.replicate_zero, flat2, List.nil_append]
  rw [flat2_replicate_true]
  rw [show (List.replicate (2 * a) true ++ false :: false ::
      (List.replicate (2 * a) true ++
        (List.replicate z false ++ rest))) =
      List.replicate (2 * a) true ++
        false :: (false :: (List.replicate (2 * a) true ++
          (List.replicate z false ++ rest))) by rfl]
  rw [writeAt_after_replicate]
  rw [step_merge_second]
  rw [show List.replicate (2 * a) true ++
      true :: (false :: (List.replicate (2 * a) true ++
        (List.replicate z false ++ rest))) =
      (List.replicate (2 * a) true ++ [true]) ++
        false :: (List.replicate (2 * a) true ++
          (List.replicate z false ++ rest)) by simp]
  rw [writeAt_after_replicate_true_extra]
  rw [flat2_replicate_true]
  congr 1
  rw [show 2 * (2 * a + 1) = (2 * a + 1) + (2 * a + 1) by omega]
  rw [List.replicate_add]
  have hs :
      List.replicate (2 * a + 1) true =
        List.replicate (2 * a) true ++ [true] := by
    rw [List.replicate_succ']
  have hcomm :
      true :: List.replicate (2 * a) true =
        List.replicate (2 * a) true ++ [true] := by
    rw [← List.replicate_succ, hs]
  have hcomm_tail (R : List Bool) :
      true :: (List.replicate (2 * a) true ++ R) =
        List.replicate (2 * a) true ++ true :: R := by
    calc
      _ = (true :: List.replicate (2 * a) true) ++ R := rfl
      _ = (List.replicate (2 * a) true ++ [true]) ++ R := by rw [hcomm]
      _ = _ := by simp [List.append_assoc]
  rw [hs]
  rw [hcomm_tail]
  simp [List.append_assoc]

/-- One complete live-counter round.  The counter contributes one unit to the
affine recurrence `a ↦ 2a+1`; the workspace equation makes the residual tape
exactly canonical for the remaining rounds. -/
theorem pow_round (a done k : ℕ) (rest : List Bool) :
    ∃ t,
      t ≤
        (2 * a + 1 + workspace a (k + 1) + 2 * done + 5) +
        ((a + 1) * (4 * a + 12) + 4 * a + 3) + 4 ∧
      run powMachine t
        ⟨.skipAcc, 0, powTape a done (k + 1) rest⟩ =
      ⟨.skipAcc, 0, powTape (2 * a + 1) (done + 1) k rest⟩ := by
  let tail :=
    flat2 (List.replicate k true) ++ true :: false :: rest
  let z := workspace (2 * a + 1) k + 2 * done + 4
  have hws :
      workspace a (k + 1) + 2 * done + 2 =
        2 * a + z := by
    simp only [z, workspace_succ]
    omega
  have henter := enter_dup (2 * a)
    (1 + workspace a (k + 1) + 2 * done)
    tail
  have hstart :
      powTape a done (k + 1) rest =
        List.replicate (2 * a) true ++ false ::
          (List.replicate
              (1 + workspace a (k + 1) + 2 * done) false ++
            true :: true :: tail) := by
    have hk :
        List.replicate (2 * (k + 1)) true =
          true :: true :: List.replicate (2 * k) true := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega,
        List.replicate_succ, List.replicate_succ]
    have hz :
        false :: (List.replicate (workspace a (k + 1)) false ++
          (List.replicate (2 * done) false ++
            (true :: true :: List.replicate (2 * k) true ++
              true :: false :: rest))) =
        List.replicate (1 + workspace a (k + 1) + 2 * done) false ++
          true :: true :: (List.replicate (2 * k) true ++
            true :: false :: rest) := by
      rw [show 1 + workspace a (k + 1) + 2 * done =
        1 + (workspace a (k + 1) + 2 * done) by omega,
        List.replicate_add,
        show workspace a (k + 1) + 2 * done =
          workspace a (k + 1) + 2 * done by rfl,
        List.replicate_add]
      simp
      rw [← List.append_assoc, ← List.replicate_add]
    simp only [powTape, tail, flat2_replicate_true, hk]
    rw [hz]
  have hdupTape :
      List.replicate (2 * a) true ++ false ::
          (List.replicate
              (1 + workspace a (k + 1) + 2 * done) false ++
            false :: false :: tail) =
        dupTape 0 a 0 (z + 2 * a) tail := by
    have hn :
        1 + workspace a (k + 1) + 2 * done + 2 =
          1 + (z + 2 * a) := by
      omega
    have hz :
        List.replicate (1 + workspace a (k + 1) + 2 * done) false ++
        false :: false :: tail =
          false :: (List.replicate (z + 2 * a) false ++ tail) := by
      calc
        _ = List.replicate
              (1 + workspace a (k + 1) + 2 * done + 2) false ++ tail := by
            rw [show 1 + workspace a (k + 1) + 2 * done + 2 =
              (1 + workspace a (k + 1) + 2 * done) + 1 + 1 by omega,
              List.replicate_succ', List.replicate_succ']
            simp
        _ = List.replicate (1 + (z + 2 * a)) false ++ tail := by rw [hn]
        _ = _ := by
          rw [show 1 + (z + 2 * a) = (z + 2 * a) + 1 by omega,
            List.replicate_succ]
          simp only [List.cons_append]
    unfold dupTape
    simp only [List.replicate_zero, flat2, List.nil_append, Nat.zero_add,
      flat2_replicate_true]
    rw [hz]
  rw [← hstart] at henter
  rw [hdupTape] at henter
  obtain ⟨td, htd, hdup⟩ := run_embedded_dup a z tail
  refine ⟨
    (2 * a + 1 + (1 + workspace a (k + 1) + 2 * done) + 1 + 2) +
      td + 4,
    by
      have he :
          2 * a + 1 + (1 + workspace a (k + 1) + 2 * done) + 1 + 2 ≤
            2 * a + 1 + workspace a (k + 1) + 2 * done + 5 := by
        omega
      exact Nat.add_le_add_right (Nat.add_le_add he htd) 4,
    ?_⟩
  rw [show
      (2 * a + 1 + (1 + workspace a (k + 1) + 2 * done) + 1 + 2) +
          td + 4 =
        (2 * a + 1 + (1 + workspace a (k + 1) + 2 * done) + 1 + 2) +
          (td + 4) by omega,
    run_add, henter, run_add, hdup, finish_merge]
  have hzfinal :
      List.replicate z false =
        false :: false ::
          (List.replicate (workspace (2 * a + 1) k) false ++
            List.replicate (2 * (done + 1)) false) := by
    simp only [z]
    rw [show workspace (2 * a + 1) k + 2 * done + 4 =
      2 + (workspace (2 * a + 1) k + 2 * (done + 1)) by omega,
      List.replicate_add,
      show workspace (2 * a + 1) k + 2 * (done + 1) =
        workspace (2 * a + 1) k + 2 * (done + 1) by rfl,
      List.replicate_add]
    simp
  simp only [powTape, tail]
  rw [hzfinal]
  congr 1
  simp only [List.cons_append, List.append_assoc]

/-! ## Iteration and the final `2^n` boundary -/

/-- Accumulator value after `k` affine-doubling rounds. -/
def iterAcc : ℕ → ℕ → ℕ
  | a, 0 => a
  | a, k + 1 => iterAcc (2 * a + 1) k

@[simp] theorem iterAcc_zero (a : ℕ) : iterAcc a 0 = a := rfl

@[simp] theorem iterAcc_succ (a k : ℕ) :
    iterAcc a (k + 1) = iterAcc (2 * a + 1) k := rfl

theorem iterAcc_closed (a k : ℕ) :
    iterAcc a k + 1 = (a + 1) * 2 ^ k := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [iterAcc_succ, ih]
    rw [pow_succ]
    ring

theorem iterAcc_from_zero (k : ℕ) :
    iterAcc 0 k = 2 ^ k - 1 := by
  have h := iterAcc_closed 0 k
  simp only [Nat.zero_add, Nat.one_mul] at h
  omega

/-- A compositional clock for the affine-doubling phase. -/
def powCost : ℕ → ℕ → ℕ → ℕ
  | _, _, 0 => 0
  | a, done, k + 1 =>
      ((2 * a + 1 + workspace a (k + 1) + 2 * done + 5) +
        ((a + 1) * (4 * a + 12) + 4 * a + 3) + 4) +
      powCost (2 * a + 1) (done + 1) k

/-- Iterate all live counter pairs. -/
theorem pow_phase : ∀ (k a done : ℕ) (rest : List Bool),
    ∃ t, t ≤ powCost a done k ∧
      run powMachine t
        ⟨.skipAcc, 0, powTape a done k rest⟩ =
      ⟨.skipAcc, 0,
        powTape (iterAcc a k) (done + k) 0 rest⟩ := by
  intro k
  induction k with
  | zero =>
      intro a done rest
      exact ⟨0, by simp [powCost], by simp⟩
  | succ k ih =>
      intro a done rest
      obtain ⟨t₁, ht₁, hr₁⟩ := pow_round a done k rest
      obtain ⟨t₂, ht₂, hr₂⟩ := ih (2 * a + 1) (done + 1) rest
      refine ⟨t₁ + t₂, ?_, ?_⟩
      · simp only [powCost]
        exact Nat.add_le_add ht₁ ht₂
      · rw [run_add, hr₁, hr₂]
        rw [iterAcc_succ]
        congr 2
        omega

theorem step_inspect_false {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) :
    step powMachine ⟨.inspectCounter, p, T⟩ =
      ⟨.done, p, T⟩ := by
  simp only [step, powMachine, h, moveHead]
  rfl

theorem step_skip_replicate_false (n : ℕ) (R : List Bool) :
    step powMachine
        ⟨.skipAcc, n, List.replicate n true ++ false :: R⟩ =
      ⟨.seekCounter, n + 1,
        List.replicate n true ++ false :: R⟩ := by
  apply step_skip_false
  simpa using getD_at (List.replicate n true) false R

/-- Once no live pair remains, scan the completed counter and halt at its
`TF` terminal unit without changing the tape. -/
theorem finish_counter (a done : ℕ) (rest : List Bool) :
    run powMachine (2 * a + 2 * done + 4)
      ⟨.skipAcc, 0, powTape a done 0 rest⟩ =
      ⟨.done, 2 * a + 2 * done + 3, powTape a done 0 rest⟩ := by
  have hs := walk_skip_true []
    (false :: false :: (List.replicate (2 * done) false ++ true :: false :: rest))
    (2 * a)
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at hs
  have hseek := walk_seek_false
    (List.replicate (2 * a) true ++ [false])
    (true :: false :: rest) (1 + 2 * done)
  simp only [List.length_append, List.length_replicate,
    List.length_singleton] at hseek
  have htape :
      powTape a done 0 rest =
        List.replicate (2 * a) true ++
          false :: (List.replicate (1 + 2 * done) false ++
            true :: false :: rest) := by
    simp only [powTape, workspace_zero, List.replicate_zero, flat2,
      List.nil_append, flat2_replicate_true]
    rw [show 1 + 2 * done = 1 + 2 * done by rfl,
      List.replicate_add]
    rfl
  rw [show 2 * a + 2 * done + 4 =
      2 * a + (1 + (1 + 2 * done) + (1 + 1)) by omega,
    run_add]
  rw [htape]
  have hs' :
      run powMachine (2 * a)
        ⟨.skipAcc, 0,
          List.replicate (2 * a) true ++
            false :: (List.replicate (1 + 2 * done) false ++
              true :: false :: rest)⟩ =
        ⟨.skipAcc, 2 * a,
          List.replicate (2 * a) true ++
            false :: (List.replicate (1 + 2 * done) false ++
              true :: false :: rest)⟩ := by
    convert hs using 1 <;>
      simp [List.replicate_add, List.append_assoc]
  rw [hs']
  rw [show 1 + (1 + 2 * done) + (1 + 1) =
      1 + ((1 + 2 * done) + 2) by omega,
    run_add, run_one]
  rw [step_skip_replicate_false]
  have hseek' :
      run powMachine (1 + 2 * done)
        ⟨.seekCounter, 2 * a + 1,
          List.replicate (2 * a) true ++
            false :: (List.replicate (1 + 2 * done) false ++
              true :: false :: rest)⟩ =
        ⟨.seekCounter, 2 * a + 1 + (1 + 2 * done),
          List.replicate (2 * a) true ++
            false :: (List.replicate (1 + 2 * done) false ++
              true :: false :: rest)⟩ := by
    simpa [List.append_assoc] using hseek
  rw [show (1 + 2 * done) + 2 = (1 + 2 * done) + (1 + 1) by omega,
    run_add, hseek', run_add, run_one]
  have htrue :
      (List.replicate (2 * a) true ++
        false :: (List.replicate (1 + 2 * done) false ++
          true :: false :: rest)).getD
        (2 * a + 1 + (1 + 2 * done)) false = true := by
    let P :=
      (List.replicate (2 * a) true ++ [false]) ++
        List.replicate (1 + 2 * done) false
    rw [show List.replicate (2 * a) true ++
        false :: (List.replicate (1 + 2 * done) false ++
          true :: false :: rest) =
      P ++ true :: false :: rest by simp [P, List.append_assoc],
      show 2 * a + 1 + (1 + 2 * done) = P.length by simp [P]; omega]
    exact getD_at P true (false :: rest)
  rw [run_one, step_seek_true htrue]
  have hfalse :
      (List.replicate (2 * a) true ++
        false :: (List.replicate (1 + 2 * done) false ++
          true :: false :: rest)).getD
        (2 * a + 1 + (1 + 2 * done) + 1) false = false := by
    let P :=
      ((List.replicate (2 * a) true ++ [false]) ++
        List.replicate (1 + 2 * done) false) ++ [true]
    rw [show List.replicate (2 * a) true ++
        false :: (List.replicate (1 + 2 * done) false ++
          true :: false :: rest) =
      P ++ false :: rest by simp [P, List.append_assoc],
      show 2 * a + 1 + (1 + 2 * done) + 1 = P.length by simp [P]; omega]
    exact getD_at P false rest
  rw [step_inspect_false hfalse]
  congr 1
  omega

/-- End-to-end exponentiation surface: the terminal unit together with the
`2^n-1` regular units represents exactly `2^n`. -/
theorem twoPow_run (n : ℕ) (rest : List Bool) :
    ∃ t, t ≤ powCost 0 0 n + (2 * (2 ^ n - 1) + 2 * n + 4) ∧
      run powMachine t
        ⟨.skipAcc, 0, powTape 0 0 n rest⟩ =
      ⟨.done, 2 * (2 ^ n - 1) + 2 * n + 3,
        powTape (2 ^ n - 1) n 0 rest⟩ := by
  obtain ⟨t₁, ht₁, hr₁⟩ := pow_phase n 0 0 rest
  refine ⟨t₁ + (2 * (2 ^ n - 1) + 2 * n + 4),
    Nat.add_le_add_right ht₁ _, ?_⟩
  rw [run_add, hr₁]
  simp only [Nat.zero_add, iterAcc_from_zero]
  exact finish_counter (2 ^ n - 1) n rest

/-! ## Polynomial clock calibration -/

/-- The canonical non-payload tape length. -/
def mass (a done k : ℕ) : ℕ :=
  2 * a + workspace a k + 2 * done + 2 * k + 4

theorem powTape_length (a done k : ℕ) (rest : List Bool) :
    (powTape a done k rest).length = mass a done k + rest.length := by
  simp [powTape, mass,
    PallLean.Paper93.DeepMath.PathB.DIndexMachine.flat2_length]
  omega

theorem mass_round (a done k : ℕ) :
    mass (2 * a + 1) (done + 1) k = mass a done (k + 1) := by
  simp only [mass, workspace_succ]
  omega

set_option maxHeartbeats 800000 in
private theorem roundCost_le (a done k : ℕ) :
    (2 * a + 1 + workspace a (k + 1) + 2 * done + 5) +
        ((a + 1) * (4 * a + 12) + 4 * a + 3) + 4
      ≤ 32 * (mass a done (k + 1) + 1) ^ 2 := by
  let S := mass a done (k + 1) + 1
  have hSa : a + 1 ≤ S := by
    simp only [S, mass]
    omega
  have hSlin :
      2 * a + 1 + workspace a (k + 1) + 2 * done + 5 ≤ S + 4 := by
    simp only [S, mass]
    omega
  have hfour : 4 * a + 12 ≤ 12 * S := by
    nlinarith
  have hprod :
      (a + 1) * (4 * a + 12) ≤ 12 * S ^ 2 := by
    calc
      _ ≤ S * (12 * S) := Nat.mul_le_mul hSa hfour
      _ = 12 * S ^ 2 := by ring
  have htail : 4 * a + 3 ≤ 4 * S := by
    nlinarith
  have hSpos : 1 ≤ S := by simp [S]
  calc
    _ ≤ (S + 4) + (12 * S ^ 2 + 4 * S) + 4 := by
      exact Nat.add_le_add_right
        (Nat.add_le_add hSlin (Nat.add_le_add hprod htail)) 4
    _ ≤ 32 * S ^ 2 := by nlinarith

theorem powCost_le_mass : ∀ (k a done : ℕ),
    powCost a done k ≤ 32 * k * (mass a done k + 1) ^ 2 := by
  intro k
  induction k with
  | zero => intro a done; simp [powCost]
  | succ k ih =>
      intro a done
      simp only [powCost]
      have hr := roundCost_le a done k
      have hi := ih (2 * a + 1) (done + 1)
      rw [mass_round] at hi
      calc
        _ ≤ 32 * (mass a done (k + 1) + 1) ^ 2 +
            32 * k * (mass a done (k + 1) + 1) ^ 2 :=
          Nat.add_le_add hr hi
        _ = 32 * (k + 1) * (mass a done (k + 1) + 1) ^ 2 := by ring

theorem powCost_initial_cubic (n : ℕ) (rest : List Bool) :
    powCost 0 0 n ≤ 32 * ((powTape 0 0 n rest).length + 1) ^ 3 := by
  have hc := powCost_le_mass n 0 0
  have hk : n ≤ mass 0 0 n + rest.length + 1 := by
    simp only [mass]
    omega
  have hlen := powTape_length 0 0 n rest
  rw [hlen]
  calc
    powCost 0 0 n
        ≤ 32 * n * (mass 0 0 n + 1) ^ 2 := hc
    _ ≤ 32 * (mass 0 0 n + rest.length + 1) *
          (mass 0 0 n + rest.length + 1) ^ 2 := by
      gcongr <;> omega
    _ = 32 * (mass 0 0 n + rest.length + 1) ^ 3 := by ring

/-- A uniform cubic clock in total tape length. -/
def twoPowClock (N : ℕ) : ℕ := 36 * (N + 1) ^ 3

theorem twoPowClock_poly :
    PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant.PolyBounded
      twoPowClock :=
  ⟨36, 3, fun N => by simp [twoPowClock]⟩

end PallLean.Paper93.DeepMath.PathB.MCSPTwoPowMachine

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTwoPowMachine.workspace_succ
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTwoPowMachine.pow_round
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTwoPowMachine.pow_phase
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTwoPowMachine.twoPow_run
