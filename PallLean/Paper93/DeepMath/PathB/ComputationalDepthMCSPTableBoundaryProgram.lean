import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFiniteControlCompiler
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPDoubledCodec

/-!
# Compiled MCSP verifier: detectable truth-table boundary

This finite-control program scans the doubled table representation from
`MCSPDoubledCodec`.  It remembers the first bit of each pair in its finite
control:

* `00` and `11` are data and advance to the next pair;
* `01` is the unique end marker and accepts;
* `10` is malformed and rejects.

On `encodeD table ++ witness` it preserves the complete tape, consumes exactly
`2 * table.length + 2` cells, and halts with the head on the first witness bit.
The compiler theorem then transports this exact source run to the faithful
`ComposableMachine` model.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPTableBoundaryProgram

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.FiniteControlCompiler
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled

inductive TableState
  | first
  | sawFalse
  | sawTrue
  | accept
  | reject
  deriving DecidableEq, Fintype

def moveRight (q : TableState) : Action TableState :=
  ⟨q, none, 1⟩

/-- Pairwise boundary scanner. -/
def tableProgram : Program where
  Label := TableState
  fin := inferInstance
  dec := inferInstance
  start := .first
  code
    | .first => .act (moveRight .sawFalse) (moveRight .sawTrue)
    | .sawFalse => .act (moveRight .first) (moveRight .accept)
    | .sawTrue => .act (moveRight .reject) (moveRight .first)
    | .accept => .halt true
    | .reject => .halt false

def tableMachine : Machine :=
  compile tableProgram

theorem step_first_false {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) :
    asmStep tableProgram ⟨.first, p, T⟩ =
      ⟨.sawFalse, p + 1, T⟩ := by
  unfold asmStep
  rw [show tableProgram.code .first =
    .act (moveRight .sawFalse) (moveRight .sawTrue) from rfl]
  rw [h]
  rfl

theorem step_first_true {p : ℕ} {T : List Bool}
    (h : T.getD p false = true) :
    asmStep tableProgram ⟨.first, p, T⟩ =
      ⟨.sawTrue, p + 1, T⟩ := by
  unfold asmStep
  rw [show tableProgram.code .first =
    .act (moveRight .sawFalse) (moveRight .sawTrue) from rfl]
  rw [h]
  rfl

theorem step_sawFalse_false {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) :
    asmStep tableProgram ⟨.sawFalse, p, T⟩ =
      ⟨.first, p + 1, T⟩ := by
  unfold asmStep
  rw [show tableProgram.code .sawFalse =
    .act (moveRight .first) (moveRight .accept) from rfl]
  rw [h]
  rfl

theorem step_sawFalse_true {p : ℕ} {T : List Bool}
    (h : T.getD p false = true) :
    asmStep tableProgram ⟨.sawFalse, p, T⟩ =
      ⟨.accept, p + 1, T⟩ := by
  unfold asmStep
  rw [show tableProgram.code .sawFalse =
    .act (moveRight .first) (moveRight .accept) from rfl]
  rw [h]
  rfl

theorem step_sawTrue_false {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) :
    asmStep tableProgram ⟨.sawTrue, p, T⟩ =
      ⟨.reject, p + 1, T⟩ := by
  unfold asmStep
  rw [show tableProgram.code .sawTrue =
    .act (moveRight .reject) (moveRight .first) from rfl]
  rw [h]
  rfl

theorem step_sawTrue_true {p : ℕ} {T : List Bool}
    (h : T.getD p false = true) :
    asmStep tableProgram ⟨.sawTrue, p, T⟩ =
      ⟨.first, p + 1, T⟩ := by
  unfold asmStep
  rw [show tableProgram.code .sawTrue =
    .act (moveRight .reject) (moveRight .first) from rfl]
  rw [h]
  rfl

private theorem getD_boundary (P : List Bool) (b : Bool) (R : List Bool) :
    (P ++ b :: R).getD P.length false = b := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  simp

/-- One equal data pair is consumed without altering the tape. -/
theorem scan_one_pair (P R : List Bool) (b : Bool) :
    asmRun tableProgram 2
      ⟨.first, P.length, P ++ b :: b :: R⟩ =
      ⟨.first, P.length + 2, P ++ b :: b :: R⟩ := by
  rw [show 2 = 1 + 1 by omega, asmRun_add]
  change asmStep tableProgram
      (asmStep tableProgram ⟨.first, P.length, P ++ b :: b :: R⟩) = _
  cases b with
  | false =>
      rw [step_first_false (getD_boundary P false (false :: R))]
      have h :
          (P ++ false :: false :: R).getD (P.length + 1) false = false := by
        rw [show P ++ false :: false :: R =
          (P ++ [false]) ++ false :: R by simp]
        simpa using getD_boundary (P ++ [false]) false R
      rw [step_sawFalse_false h]
  | true =>
      rw [step_first_true (getD_boundary P true (true :: R))]
      have h :
          (P ++ true :: true :: R).getD (P.length + 1) false = true := by
        rw [show P ++ true :: true :: R =
          (P ++ [true]) ++ true :: R by simp]
        simpa using getD_boundary (P ++ [true]) true R
      rw [step_sawTrue_true h]

/-- Scan all doubled data pairs, stopping just before their unequal marker. -/
theorem scan_data_pairs (P table rest : List Bool) :
    asmRun tableProgram (2 * table.length)
      ⟨.first, P.length, P ++ encodeD table ++ rest⟩ =
      ⟨.first, P.length + 2 * table.length,
        P ++ encodeD table ++ rest⟩ := by
  induction table generalizing P with
  | nil =>
      simp
  | cons b table ih =>
      rw [encodeD]
      rw [show 2 * (b :: table).length = 2 + 2 * table.length by simp; omega,
        asmRun_add]
      have hpair := scan_one_pair P (encodeD table ++ rest) b
      rw [show P ++ b :: b :: encodeD table ++ rest =
        P ++ b :: b :: (encodeD table ++ rest) by simp [List.append_assoc]]
      rw [hpair]
      have H := ih (P ++ [b, b])
      convert H using 1 <;> simp [List.append_assoc] <;> omega

/-- The canonical `01` marker is consumed and enters the accepting halt state. -/
theorem consume_marker (P rest : List Bool) :
    asmRun tableProgram 2
      ⟨.first, P.length, P ++ false :: true :: rest⟩ =
      ⟨.accept, P.length + 2, P ++ false :: true :: rest⟩ := by
  rw [show 2 = 1 + 1 by omega, asmRun_add]
  change asmStep tableProgram
      (asmStep tableProgram
        ⟨.first, P.length, P ++ false :: true :: rest⟩) = _
  rw [step_first_false (getD_boundary P false (true :: rest))]
  have h :
      (P ++ false :: true :: rest).getD (P.length + 1) false = true := by
    rw [show P ++ false :: true :: rest =
      (P ++ [false]) ++ true :: rest by simp]
    simpa using getD_boundary (P ++ [false]) true rest
  rw [step_sawFalse_true h]

/-- Expanded shape of the doubled representation. -/
theorem encodeD_eq_flatPairs (table : List Bool) :
    encodeD table =
      table.flatMap (fun b => [b, b]) ++ [false, true] := by
  induction table with
  | nil => rfl
  | cons b table ih =>
      simp [encodeD, ih, List.append_assoc]

/-- Exact source run: the head lands on the first witness bit. -/
theorem asmRun_table (table witness : List Bool) :
    asmRun tableProgram (2 * table.length + 2)
      (asmInit tableProgram (encodeD table ++ witness)) =
      ⟨.accept, 2 * table.length + 2, encodeD table ++ witness⟩ := by
  rw [asmRun_add]
  have hscan := scan_data_pairs [] table witness
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at hscan
  change asmRun tableProgram 2
      (asmRun tableProgram (2 * table.length)
        ⟨.first, 0, encodeD table ++ witness⟩) = _
  rw [hscan]
  rw [show encodeD table ++ witness =
      (table.flatMap fun b => [b, b]) ++ false :: true :: witness by
    rw [encodeD_eq_flatPairs]
    simp [List.append_assoc]]
  have hmark :=
    consume_marker (table.flatMap fun b => [b, b]) witness
  have hlen :
      (table.flatMap fun b => [b, b]).length = 2 * table.length := by
    induction table with
    | nil => rfl
    | cons b table ih => simp [ih]; omega
  simpa [hlen] using hmark

/-- Exact compiled-machine run on a canonical doubled table. -/
theorem machine_run_table (table witness : List Bool) :
    run tableMachine (2 * table.length + 2)
      (init tableMachine (encodeD table ++ witness)) =
      ⟨.accept, 2 * table.length + 2, encodeD table ++ witness⟩ := by
  unfold tableMachine
  rw [compile_run_init, asmRun_table]
  rfl

theorem machine_halts_table (table witness : List Bool) :
    HaltsBy tableMachine (encodeD table ++ witness)
      (2 * table.length + 2) := by
  unfold HaltsBy
  rw [machine_run_table]
  rfl

theorem machine_accepts_table (table witness : List Bool) :
    decideOut tableMachine (encodeD table ++ witness)
      (2 * table.length + 2) = true := by
  unfold decideOut
  rw [machine_run_table]
  rfl

/-- `10` is rejected as a malformed boundary/data pair. -/
theorem machine_rejects_bad_pair (rest : List Bool) :
    decideOut tableMachine (true :: false :: rest) 2 = false := by
  unfold decideOut tableMachine
  rw [compile_run_init]
  change asmAccept tableProgram
    (asmRun tableProgram 2
      (asmInit tableProgram (true :: false :: rest))).pc = false
  rw [show 2 = 1 + 1 by omega, asmRun_add]
  change asmAccept tableProgram
    (asmStep tableProgram
      (asmStep tableProgram
        ⟨.first, 0, true :: false :: rest⟩)).pc = false
  rw [step_first_true (by rfl), step_sawTrue_false (by rfl)]
  rfl

end PallLean.Paper93.DeepMath.PathB.MCSPTableBoundaryProgram

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTableBoundaryProgram.asmRun_table
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTableBoundaryProgram.machine_run_table
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTableBoundaryProgram.machine_rejects_bad_pair
