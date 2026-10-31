import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUnaryCmpMachine
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCondSeqMachine

/-!
# The compare → branch bridge

Wires `cmpMachine` into `condSeqMachine`: running `condSeqMachine cmpMachine Mt Mf` on the
compare tape dispatches to `Mt` when `t < p` and to `Mf` otherwise, because `cmpMachine`'s
accept bit *is* `decide (t < p)`.  This closes the pair-assembly's **control flow** — the
two branch arms `Mt` (computing `p²+t`) and `Mf` (computing `t²+t+p`) plug in as ordinary
follow-on machines with their own run lemmas; the dispatch is proved once here.

`cmpBranch_true` / `cmpBranch_false`: given the chosen arm's run on `cmpFinal` (the tape
`cmpMachine` leaves), the composite reaches the arm's final configuration at a single clock.
The compare consumes its blocks into `[T,F]`-marks that preserve the counts, so a branch arm
recovers `t`, `p` by healing — the arms' internal business, opaque to the dispatch.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CmpBranchBridge

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.UnaryCmpMachine
open PallLean.Paper93.DeepMath.PathB.CondSeqMachine

/-- `cmpMachine` halts at state `10` regardless of the answer. -/
theorem cmp_halt (b : Bool) : cmpMachine.halt ((10 : Fin 11), b) = true := rfl

/-- `cmpMachine`'s accept bit is the second state component. -/
theorem cmp_accept (b : Bool) : cmpMachine.accept ((10 : Fin 11), b) = b := rfl

/-- **The `true` branch.**  When `t < p`, the compare dispatches to `Mt`. -/
theorem cmpBranch_true (Mt Mf : Machine) (t' p' i : ℕ) (rest : List Bool)
    (hlt : t' < p') (t2 : ℕ) (s2f : Mt.State) (p2 : ℕ) (T2 : List Bool)
    (h2 : run Mt t2 (init Mt (cmpFinal i t' p' rest)) = ⟨s2f, p2, T2⟩)
    (hh2 : Mt.halt s2f = true) :
    ∃ T, run (condSeqMachine cmpMachine Mt Mf) T
        (init (condSeqMachine cmpMachine Mt Mf) (cmpTape i t' i p' rest))
      = ⟨Sum.inr (Sum.inl s2f), p2, T2⟩ := by
  obtain ⟨t1, _, pos, hrun⟩ := cmpM_run t' p' i rest false
  have hdec : decide (t' < p') = true := decide_eq_true hlt
  rw [hdec] at hrun
  refine ⟨t1 + 1 + t2, ?_⟩
  exact condSeq_run_true (M1 := cmpMachine) (Mt := Mt) (Mf := Mf)
    (cmpTape i t' i p' rest) (cmpFinal i t' p' rest) T2 t1 t2
    ((10 : Fin 11), true) pos s2f p2
    hrun (cmp_halt true) (cmp_accept true) h2 hh2

/-- **The `false` branch.**  When `¬ t < p`, the compare dispatches to `Mf`. -/
theorem cmpBranch_false (Mt Mf : Machine) (t' p' i : ℕ) (rest : List Bool)
    (hge : ¬ t' < p') (t2 : ℕ) (s2f : Mf.State) (p2 : ℕ) (T2 : List Bool)
    (h2 : run Mf t2 (init Mf (cmpFinal i t' p' rest)) = ⟨s2f, p2, T2⟩)
    (hh2 : Mf.halt s2f = true) :
    ∃ T, run (condSeqMachine cmpMachine Mt Mf) T
        (init (condSeqMachine cmpMachine Mt Mf) (cmpTape i t' i p' rest))
      = ⟨Sum.inr (Sum.inr s2f), p2, T2⟩ := by
  obtain ⟨t1, _, pos, hrun⟩ := cmpM_run t' p' i rest false
  have hdec : decide (t' < p') = false := decide_eq_false hge
  rw [hdec] at hrun
  refine ⟨t1 + 1 + t2, ?_⟩
  exact condSeq_run_false (M1 := cmpMachine) (Mt := Mt) (Mf := Mf)
    (cmpTape i t' i p' rest) (cmpFinal i t' p' rest) T2 t1 t2
    ((10 : Fin 11), false) pos s2f p2
    hrun (cmp_halt false) (cmp_accept false) h2 hh2

end PallLean.Paper93.DeepMath.PathB.CmpBranchBridge
