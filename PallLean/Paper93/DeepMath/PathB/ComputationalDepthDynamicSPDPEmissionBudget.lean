import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicSPDPGlobalGodMove

/-!
# Local emission budget for additive dynamic SPDP

The current positive dynamic-SPDP model accumulates event ranks by addition.  This
file proves the exact local-to-global budget for that model.

If every event in a `time`-step prefix has rank at most `cap`, then the accumulated
rank is at most `time * cap`.  Consequently an exponential global minor on a
polynomial-step run cannot arise from uniformly polynomial local events: some
single transition must already emit rank above the local cap (or the run itself
must exceed the proposed time budget).

This is a useful non-circular replacement for the refuted all-size emission socket.
It does not assert that SAT correctness creates a large event.  It isolates that
claim as a concrete transition-level theorem which can be tested against the
physical Cook--Levin machine.
-/

namespace PallLean.Paper93.DeepMath.PathB.DynamicSPDPEmissionBudget

open PvsNPDynamicSPDPGlobalGodMove
open PvsNPRunIndexedFaithfulTPhi

variable {Input State : Type*}

/-- A uniform cap on every event in a prefix. -/
def EventsBoundedBefore
    {R : ActualDecisionRun Input State}
    (S : DynamicPositiveSPDP R) (time cap : ℕ) (x : Input) : Prop :=
  ∀ t, t < time → S.eventRank t x ≤ cap

/-- Additive local-to-global accounting: `time` events of rank at most `cap`
accumulate rank at most `time * cap`. -/
theorem prefixRank_le_time_mul_cap
    {R : ActualDecisionRun Input State}
    (S : DynamicPositiveSPDP R) (time cap : ℕ) (x : Input)
    (hbounded : EventsBoundedBefore S time cap x) :
    S.prefixRank time x ≤ time * cap := by
  induction time with
  | zero => simp [DynamicPositiveSPDP.prefixRank]
  | succ time ih =>
      rw [DynamicPositiveSPDP.prefixRank_succ]
      have hprefix : EventsBoundedBefore S time cap x := by
        intro t ht
        exact hbounded t (Nat.lt_succ_of_lt ht)
      have hevent : S.eventRank time x ≤ cap :=
        hbounded time (Nat.lt_succ_self time)
      have hih := ih hprefix
      calc
        S.prefixRank time x + S.eventRank time x ≤ time * cap + cap :=
          Nat.add_le_add hih hevent
        _ = (time + 1) * cap := by simp [Nat.add_mul]

/-- Complete-run specialization of the additive budget. -/
theorem globalGodMoveRank_le_steps_mul_cap
    {R : ActualDecisionRun Input State}
    (S : DynamicPositiveSPDP R) (cap : ℕ) (x : Input)
    (hbounded : EventsBoundedBefore S R.steps cap x) :
    S.globalGodMoveRank x ≤ R.steps * cap := by
  exact prefixRank_le_time_mul_cap S R.steps cap x hbounded

/-- If global accumulated rank exceeds the additive budget, some actual transition
already exceeds the proposed local cap. -/
theorem exists_large_event_of_budget_lt_global
    {R : ActualDecisionRun Input State}
    (S : DynamicPositiveSPDP R) (cap : ℕ) (x : Input)
    (hlarge : R.steps * cap < S.globalGodMoveRank x) :
    ∃ t, t < R.steps ∧ cap < S.eventRank t x := by
  by_contra hno
  push_neg at hno
  have hbounded : EventsBoundedBefore S R.steps cap x := by
    intro t ht
    exact hno t ht
  have hupper := globalGodMoveRank_le_steps_mul_cap S cap x hbounded
  omega

/-- An exponential minor above the additive budget forces a transition carrying a
locally super-cap event.  This is the precise transition-level obligation for a
future physical Cook--Levin/SPDP emission proof. -/
theorem exponential_minor_forces_large_event
    {R : ActualDecisionRun Input State}
    (S : DynamicPositiveSPDP R) (n cap : ℕ) (x : Input)
    (hminor : 2 ^ n ≤ S.globalGodMoveRank x)
    (hgap : R.steps * cap < 2 ^ n) :
    ∃ t, t < R.steps ∧ cap < S.eventRank t x := by
  exact exists_large_event_of_budget_lt_global S cap x
    (lt_of_lt_of_le hgap hminor)

/-- Contrapositive form: a polynomial-step/local-cap description rules out the
exponential global minor in the additive model. -/
theorem no_exponential_minor_of_local_budget
    {R : ActualDecisionRun Input State}
    (S : DynamicPositiveSPDP R) (n cap : ℕ) (x : Input)
    (hbounded : EventsBoundedBefore S R.steps cap x)
    (hgap : R.steps * cap < 2 ^ n) :
    ¬ 2 ^ n ≤ S.globalGodMoveRank x := by
  intro hminor
  have hupper := globalGodMoveRank_le_steps_mul_cap S cap x hbounded
  omega

end PallLean.Paper93.DeepMath.PathB.DynamicSPDPEmissionBudget

#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDPEmissionBudget.prefixRank_le_time_mul_cap
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDPEmissionBudget.globalGodMoveRank_le_steps_mul_cap
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDPEmissionBudget.exists_large_event_of_budget_lt_global
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDPEmissionBudget.exponential_minor_forces_large_event
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDPEmissionBudget.no_exponential_minor_of_local_budget
