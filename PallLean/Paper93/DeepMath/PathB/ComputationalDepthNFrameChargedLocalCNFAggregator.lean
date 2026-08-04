import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalNPBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEvalMachine

/-!
# A charged local nested-CNF aggregation machine

This file implements the Boolean-control half of the concrete SAT verifier.
The input is a self-delimiting stream of already-looked-up literal truth
values.  A clause is a flagged list of values and a formula is a flagged list
of clauses.  One finite-control `ComposableMachine` computes OR inside each
clause and AND across clauses.

The machine is total even on malformed inputs: the model's false padding
closes an unfinished value, clause, and formula within three extra steps.  It
therefore decides its total language in a linear clock.  On canonical nested
encodings it agrees exactly with `List.all (List.any id)`.

This discharges clause iteration, formula iteration, delimiter parsing, and
Boolean aggregation.  It does not yet decode literal indices or weld this
loop to the already-proved indexed-assignment lookup machine.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalCNFAggregator

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.CookLevinEvalMachine (getD_pad)

/-- Phase `0`: formula flag; `1`: clause flag; `2`: literal value; `3`: halt.
The two Boolean registers are the formula-AND and current clause-OR. -/
def cnfAggregator : Machine where
  State := Fin 4 × (Bool × Bool)
  fin := inferInstance
  dec := inferInstance
  start := (0, (true, false))
  halt := fun s => decide (s.1 = 3)
  δ := fun s b =>
    if s.1 = 0 then
      if b then ((1, (s.2.1, false)), none, 1)
      else ((3, s.2), none, 2)
    else if s.1 = 1 then
      if b then ((2, s.2), none, 1)
      else ((0, (s.2.1 && s.2.2, false)), none, 1)
    else if s.1 = 2 then
      ((1, (s.2.1, s.2.2 || b)), none, 1)
    else
      ((3, s.2), none, 2)
  accept := fun s => s.2.1

theorem step_formula_more {A C : Bool} {p : Nat} {T : List Bool}
    (h : T.getD p false = true) :
    step cnfAggregator ⟨(0, (A, C)), p, T⟩ =
      ⟨(1, (A, false)), p + 1, T⟩ := by
  change T[p]?.getD false = true at h
  simp [step, cnfAggregator, h, moveHead]

theorem step_formula_done {A C : Bool} {p : Nat} {T : List Bool}
    (h : T.getD p false = false) :
    step cnfAggregator ⟨(0, (A, C)), p, T⟩ =
      ⟨(3, (A, C)), p, T⟩ := by
  change T[p]?.getD false = false at h
  simp [step, cnfAggregator, h, moveHead]

theorem step_clause_more {A C : Bool} {p : Nat} {T : List Bool}
    (h : T.getD p false = true) :
    step cnfAggregator ⟨(1, (A, C)), p, T⟩ =
      ⟨(2, (A, C)), p + 1, T⟩ := by
  change T[p]?.getD false = true at h
  simp [step, cnfAggregator, h, moveHead]

theorem step_clause_done {A C : Bool} {p : Nat} {T : List Bool}
    (h : T.getD p false = false) :
    step cnfAggregator ⟨(1, (A, C)), p, T⟩ =
      ⟨(0, (A && C, false)), p + 1, T⟩ := by
  change T[p]?.getD false = false at h
  simp [step, cnfAggregator, h, moveHead]

theorem step_literal {A C : Bool} {p : Nat} {T : List Bool} :
    step cnfAggregator ⟨(2, (A, C)), p, T⟩ =
      ⟨(1, (A, C || T.getD p false)), p + 1, T⟩ := by
  simp [step, cnfAggregator, moveHead]

theorem aggregator_run_one (c : Cfg cnfAggregator) :
    run cnfAggregator 1 c = step cnfAggregator c := by
  rw [run_succ, run_zero]

/-! ## Canonical nested truth-value encoding -/

/-- A clause: `(true,value)` pairs terminated by a false flag. -/
def encodeClauseValues : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: encodeClauseValues bs

/-- A formula: true flag plus each encoded clause, terminated by false. -/
def encodeFormulaValues : List (List Bool) → List Bool
  | [] => [false]
  | c :: cs => true :: (encodeClauseValues c ++ encodeFormulaValues cs)

theorem encodeClauseValues_length (c : List Bool) :
    (encodeClauseValues c).length = 2 * c.length + 1 := by
  induction c with
  | nil => rfl
  | cons b c ih => simp [encodeClauseValues, ih]; omega

theorem encodeFormulaValues_length (F : List (List Bool)) :
    (encodeFormulaValues F).length =
      1 + (F.map fun c => 2 * c.length + 2).sum := by
  induction F with
  | nil => rfl
  | cons c F ih =>
      simp [encodeFormulaValues, encodeClauseValues_length, ih]
      omega

theorem getD_append_boundary (P : List Bool) (b : Bool) (R : List Bool) :
    (P ++ b :: R).getD P.length false = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

/-- Exact execution of one clause behind an arbitrary consumed prefix. -/
theorem run_clause (P c rest : List Bool) (A C : Bool) :
    run cnfAggregator (2 * c.length + 1)
      ⟨(1, (A, C)), P.length, P ++ encodeClauseValues c ++ rest⟩ =
    ⟨(0, (A && (C || c.any id), false)),
      P.length + 2 * c.length + 1,
      P ++ encodeClauseValues c ++ rest⟩ := by
  induction c generalizing P C with
  | nil =>
      rw [show 2 * [].length + 1 = 1 by simp, run_succ, run_zero]
      simp only [encodeClauseValues]
      rw [show P ++ [false] ++ rest = P ++ false :: rest by simp,
        step_clause_done (getD_append_boundary P false rest)]
      simp
  | cons b c ih =>
      let P' := P ++ [true, b]
      have hP' : P'.length = P.length + 2 := by simp [P']
      have hTape : P ++ encodeClauseValues (b :: c) ++ rest =
          P' ++ encodeClauseValues c ++ rest := by
        simp [P', encodeClauseValues, List.append_assoc]
      have hflag : (P ++ encodeClauseValues (b :: c) ++ rest).getD P.length false = true := by
        rw [show P ++ encodeClauseValues (b :: c) ++ rest =
          P ++ true :: (b :: encodeClauseValues c ++ rest) by
            simp [encodeClauseValues, List.append_assoc]]
        exact getD_append_boundary P true _
      have hval : (P ++ encodeClauseValues (b :: c) ++ rest).getD (P.length + 1) false = b := by
        rw [show P ++ encodeClauseValues (b :: c) ++ rest =
          (P ++ [true]) ++ b :: (encodeClauseValues c ++ rest) by
            simp [encodeClauseValues, List.append_assoc]]
        simp [getD_append_boundary]
      have hfirst : run cnfAggregator 2
          ⟨(1, (A, C)), P.length, P ++ encodeClauseValues (b :: c) ++ rest⟩ =
          ⟨(1, (A, C || b)), P'.length,
            P ++ encodeClauseValues (b :: c) ++ rest⟩ := by
        have hone1 : run cnfAggregator 1
            ⟨(1, (A, C)), P.length,
              P ++ encodeClauseValues (b :: c) ++ rest⟩ =
            ⟨(2, (A, C)), P.length + 1,
              P ++ encodeClauseValues (b :: c) ++ rest⟩ := by
          rw [aggregator_run_one, step_clause_more hflag]
        have hone2 : run cnfAggregator 1
            ⟨(2, (A, C)), P.length + 1,
              P ++ encodeClauseValues (b :: c) ++ rest⟩ =
            ⟨(1, (A, C || b)), P'.length,
              P ++ encodeClauseValues (b :: c) ++ rest⟩ := by
          rw [aggregator_run_one, step_literal, hval, hP']
        rw [show 2 = 1 + 1 by omega, run_add, hone1, hone2]
      rw [show 2 * (b :: c).length + 1 = 2 + (2 * c.length + 1) by simp; omega,
        run_add, hfirst, hTape, ih P' (C || b)]
      simp [Bool.or_assoc]
      omega

/-- Exact execution of the whole encoded formula. -/
theorem run_formula (P : List Bool) (F : List (List Bool)) (rest : List Bool) (A : Bool) :
    run cnfAggregator (encodeFormulaValues F).length
      ⟨(0, (A, false)), P.length, P ++ encodeFormulaValues F ++ rest⟩ =
    ⟨(3, (A && F.all (fun c => c.any id), false)),
      P.length + (encodeFormulaValues F).length - 1,
      P ++ encodeFormulaValues F ++ rest⟩ := by
  induction F generalizing P A with
  | nil =>
      simp only [encodeFormulaValues, List.length_singleton]
      rw [run_succ, run_zero,
        show P ++ [false] ++ rest = P ++ false :: rest by simp,
        step_formula_done (getD_append_boundary P false rest)]
      simp
  | cons c F ih =>
      let P1 := P ++ [true]
      let P2 := P1 ++ encodeClauseValues c
      have hP1 : P1.length = P.length + 1 := by simp [P1]
      have hP2 : P2.length = P.length + 1 + (2 * c.length + 1) := by
        simp [P2, P1, encodeClauseValues_length]
        omega
      have hTape : P ++ encodeFormulaValues (c :: F) ++ rest =
          P1 ++ encodeClauseValues c ++ encodeFormulaValues F ++ rest := by
        simp [P1, encodeFormulaValues, List.append_assoc]
      have hflag : (P ++ encodeFormulaValues (c :: F) ++ rest).getD P.length false = true := by
        rw [show P ++ encodeFormulaValues (c :: F) ++ rest =
          P ++ true :: (encodeClauseValues c ++ encodeFormulaValues F ++ rest) by
            simp [encodeFormulaValues, List.append_assoc]]
        exact getD_append_boundary P true _
      have hfirst : run cnfAggregator 1
          ⟨(0, (A, false)), P.length, P ++ encodeFormulaValues (c :: F) ++ rest⟩ =
          ⟨(1, (A, false)), P1.length,
            P ++ encodeFormulaValues (c :: F) ++ rest⟩ := by
        rw [run_succ, run_zero, step_formula_more hflag, hP1]
      have hTail : P1 ++ encodeClauseValues c ++ (encodeFormulaValues F ++ rest) =
          P2 ++ encodeFormulaValues F ++ rest := by simp [P2, List.append_assoc]
      have hTail' : P1 ++ (encodeClauseValues c ++ (encodeFormulaValues F ++ rest)) =
          P2 ++ encodeFormulaValues F ++ rest := by
        simpa [List.append_assoc] using hTail
      rw [show (encodeFormulaValues (c :: F)).length =
          1 + ((2 * c.length + 1) + (encodeFormulaValues F).length) by
            simp [encodeFormulaValues, encodeClauseValues_length]; omega,
        run_add, hfirst, hTape,
        run_add]
      have hcl := run_clause P1 c (encodeFormulaValues F ++ rest) A false
      simp only [List.append_assoc] at hcl ⊢
      rw [hcl]
      simp only [Bool.false_or]
      rw [show P1.length + 2 * c.length + 1 = P2.length by omega,
        hTail', ih P2 (A && c.any id)]
      simp only [List.all_cons]
      congr 2
      · simp [Bool.and_assoc]
      · omega

/-! ## Totality and linear-time membership -/

/-- At every nonhalting step the head advances one cell; otherwise the next
configuration is halted. -/
theorem step_halts_or_advances (c : Cfg cnfAggregator) :
    cnfAggregator.halt (step cnfAggregator c).st = true ∨
      (step cnfAggregator c).hd = c.hd + 1 := by
  rcases c with ⟨⟨ph, A, C⟩, p, T⟩
  by_cases h0 : ph = 0
  · subst ph
    cases h : T.getD p false
    · left
      rw [step_formula_done h]
      rfl
    · right
      rw [step_formula_more h]
  by_cases h1 : ph = 1
  · subst ph
    cases h : T.getD p false
    · right
      rw [step_clause_done h]
    · right
      rw [step_clause_more h]
  by_cases h2 : ph = 2
  · subst ph
    right
    rw [step_literal]
  have h3 : ph = 3 := by
    apply Fin.ext
    omega
  subst ph
  left
  rw [step_of_halted cnfAggregator (by rfl)]
  rfl

/-- The aggregator never writes, so every run preserves its input tape. -/
theorem step_tape_eq (c : Cfg cnfAggregator) :
    (step cnfAggregator c).tp = c.tp := by
  rcases c with ⟨⟨ph, A, C⟩, p, T⟩
  by_cases h0 : ph = 0
  · subst ph
    cases h : T.getD p false
    · rw [step_formula_done h]
    · rw [step_formula_more h]
  by_cases h1 : ph = 1
  · subst ph
    cases h : T.getD p false
    · rw [step_clause_done h]
    · rw [step_clause_more h]
  by_cases h2 : ph = 2
  · subst ph
    rw [step_literal]
  have h3 : ph = 3 := by apply Fin.ext; omega
  subst ph
  rw [step_of_halted cnfAggregator (by rfl)]

theorem run_tape_eq (x : List Bool) (t : Nat) :
    (run cnfAggregator t (init cnfAggregator x)).tp = x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ]
    rw [step_tape_eq, ih]

/-- After `t` steps the machine has halted or has advanced at least `t`
cells. -/
theorem run_halted_or_head_ge (x : List Bool) (t : Nat) :
    cnfAggregator.halt (run cnfAggregator t (init cnfAggregator x)).st = true ∨
      t ≤ (run cnfAggregator t (init cnfAggregator x)).hd := by
  induction t with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ t ih =>
      rcases ih with hhalt | hhead
      · left
        rw [run_succ, step_of_halted cnfAggregator hhalt]
        exact hhalt
      · rw [run_succ]
        rcases step_halts_or_advances (run cnfAggregator t (init cnfAggregator x)) with hhalt | hadv
        · exact Or.inl hhalt
        · exact Or.inr (by omega)

/-- Once the head reaches false padding, every phase halts within three
steps. -/
theorem run_three_halts_on_padding (x : List Bool) (c : Cfg cnfAggregator)
    (hpos : x.length ≤ c.hd) (htape : c.tp = x) :
    cnfAggregator.halt (run cnfAggregator 3 c).st = true := by
  subst htape
  rcases c with ⟨⟨ph, A, C⟩, p, x⟩
  change x.length ≤ p at hpos
  have h0 : x.getD p false = false := getD_pad x hpos
  have h1 : x.getD (p + 1) false = false := getD_pad x (by omega)
  have h2 : x.getD (p + 2) false = false := getD_pad x (by omega)
  by_cases hp0 : ph = 0
  · subst ph
    change cnfAggregator.halt
      (run cnfAggregator (1 + 2) ⟨(0, (A, C)), p, x⟩).st = true
    rw [run_add, aggregator_run_one, step_formula_done h0,
      run_of_halted cnfAggregator (by rfl)]
    rfl
  by_cases hp1 : ph = 1
  · subst ph
    let c0 : Cfg cnfAggregator := ⟨(1, (A, C)), p, x⟩
    let c1 : Cfg cnfAggregator := ⟨(0, (A && C, false)), p + 1, x⟩
    let c2 : Cfg cnfAggregator := ⟨(3, (A && C, false)), p + 1, x⟩
    have hs0 : run cnfAggregator 1 c0 = c1 := by
      rw [aggregator_run_one, step_clause_done h0]
    have hs1 : run cnfAggregator 1 c1 = c2 := by
      rw [aggregator_run_one, step_formula_done h1]
    have hs2 : run cnfAggregator 1 c2 = c2 :=
      run_of_halted cnfAggregator (by rfl) 1
    change cnfAggregator.halt (run cnfAggregator 3 c0).st = true
    rw [show 3 = 1 + (1 + 1) by omega, run_add, run_add, hs0, hs1, hs2]
    rfl
  by_cases hp2 : ph = 2
  · subst ph
    let c0 : Cfg cnfAggregator := ⟨(2, (A, C)), p, x⟩
    let c1 : Cfg cnfAggregator := ⟨(1, (A, C)), p + 1, x⟩
    let c2 : Cfg cnfAggregator := ⟨(0, (A && C, false)), p + 2, x⟩
    let c3 : Cfg cnfAggregator := ⟨(3, (A && C, false)), p + 2, x⟩
    have hs0 : run cnfAggregator 1 c0 = c1 := by
      rw [aggregator_run_one, step_literal, h0]
      simp [c1]
    have hs1 : run cnfAggregator 1 c1 = c2 := by
      rw [aggregator_run_one, step_clause_done h1]
    have hs2 : run cnfAggregator 1 c2 = c3 := by
      rw [aggregator_run_one, step_formula_done h2]
    change cnfAggregator.halt (run cnfAggregator 3 c0).st = true
    rw [show 3 = 1 + (1 + 1) by omega, run_add, run_add, hs0, hs1, hs2]
    rfl
  have hp3 : ph = 3 := by apply Fin.ext; omega
  subst ph
  rw [run_of_halted cnfAggregator (by rfl)]
  rfl

theorem cnfAggregator_halts (x : List Bool) :
    HaltsBy cnfAggregator x (x.length + 3) := by
  rcases run_halted_or_head_ge x x.length with hhalt | hhead
  · have hstable := run_of_halted cnfAggregator hhalt 3
    unfold HaltsBy
    rw [show x.length + 3 = x.length + 3 from rfl, run_add, hstable]
    exact hhalt
  · unfold HaltsBy
    rw [run_add]
    apply run_three_halts_on_padding x
    · exact hhead
    · exact run_tape_eq x x.length

/-- The total language decided by the aggregator's linear-clock execution. -/
def cnfAggregateLanguage (x : List Bool) : Bool :=
  decideOut cnfAggregator x (x.length + 3)

theorem cnfAggregator_decides :
    Decides cnfAggregator cnfAggregateLanguage (fun n => n + 3) := by
  intro x
  exact ⟨cnfAggregator_halts x, rfl⟩

theorem cnfAggregateLanguage_inP : InP cnfAggregateLanguage := by
  exact ⟨cnfAggregator, fun n => n + 3,
    ⟨4, 1, fun n => by simp only [pow_one]; omega⟩,
    cnfAggregator_decides⟩

/-- On canonical inputs the total decided language is exactly nested
clause-OR/formula-AND. -/
theorem cnfAggregateLanguage_encode (F : List (List Bool)) :
    cnfAggregateLanguage (encodeFormulaValues F) =
      F.all (fun c => c.any id) := by
  have hrun := run_formula [] F [] true
  simp only [List.length_nil, List.nil_append, List.append_nil, Bool.true_and] at hrun
  have hhalt : cnfAggregator.halt
      (run cnfAggregator (encodeFormulaValues F).length
        (init cnfAggregator (encodeFormulaValues F))).st = true := by
    change cnfAggregator.halt
      (run cnfAggregator (encodeFormulaValues F).length
        ⟨(0, (true, false)), 0, encodeFormulaValues F⟩).st = true
    rw [hrun]
    rfl
  have hstable := run_stable cnfAggregator (encodeFormulaValues F)
    (show (encodeFormulaValues F).length ≤ (encodeFormulaValues F).length + 3 by omega) hhalt
  unfold cnfAggregateLanguage decideOut
  rw [hstable]
  change cnfAggregator.accept
    (run cnfAggregator (encodeFormulaValues F).length
      ⟨(0, (true, false)), 0, encodeFormulaValues F⟩).st =
        F.all (fun c => c.any id)
  rw [hrun]
  rfl

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalCNFAggregator

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalCNFAggregator.run_clause
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalCNFAggregator.run_formula
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalCNFAggregator.cnfAggregator_halts
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalCNFAggregator.cnfAggregateLanguage_inP
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalCNFAggregator.cnfAggregateLanguage_encode
