import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMulBlockMachine

/-!
# Iterated `mulBlock`: accumulator scaling (`×2`, `×3`)

`mulBlock` accumulates (`v += a·b`) and preserves both operand blocks, so *iterating* it on
the same tape scales the accumulator: `k` applications give `v += k·(a·b)`.  With `b = a`
this is the `×3` the pair-assembly arms need — `3p²` is three squarings into one
accumulator, no operand repositioning:

  `thriceMulBlock :  mulTape a b s (Z + 3ab) rest  ↦  mulTape a b (s + 3ab) Z rest`.

Each step is a `seqMachine` composition of `mulBlockMachine` with the remaining iterations,
proved by chaining `seq_run` against `mulBlockM_run`; the frontier zeros deplete `ab` per
step.  `thriceSqBlock` is the `3a²` case — the squaring-and-triple the arms run on `p` (and
on `t`).

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MulBlockIter

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq (seqMachine seq_run seq_halt_inr)
open PallLean.Paper93.DeepMath.PathB.UnaryMulMachine (mulTape)
open PallLean.Paper93.DeepMath.PathB.UnaryHealMachine (healMachine)
open PallLean.Paper93.DeepMath.PathB.MulBlockMachine (mulBlockMachine mulBlockM_run)

/-- `mulBlockMachine` halts at its inner `healMachine`'s halt state. -/
theorem mulBlock_halt : mulBlockMachine.halt (Sum.inr ((2 : Fin 3), false)) = true := rfl

/-- **`×2`**: two `mulBlock`s scale the accumulator by `2ab`. -/
def twiceMulBlockMachine : Machine := seqMachine mulBlockMachine mulBlockMachine

theorem twiceMulBlockM_run (a b s Z : ℕ) (rest : List Bool) :
    ∃ t, run twiceMulBlockMachine t
        (init twiceMulBlockMachine (mulTape (List.replicate a true) 0 b s (Z + 2 * (a * b)) rest))
      = ⟨Sum.inr (Sum.inr ((2 : Fin 3), false)), 2 * a,
          mulTape (List.replicate a true) 0 b (s + 2 * (a * b)) Z rest⟩ := by
  obtain ⟨t1, h1⟩ := mulBlockM_run a b s (Z + a * b) rest
  obtain ⟨t2, h2⟩ := mulBlockM_run a b (s + a * b) Z rest
  rw [show Z + a * b + a * b = Z + 2 * (a * b) from by ring] at h1
  rw [show s + a * b + a * b = s + 2 * (a * b) from by ring] at h2
  refine ⟨t1 + 1 + t2, ?_⟩
  exact seq_run mulBlockMachine mulBlockMachine
    (mulTape (List.replicate a true) 0 b s (Z + 2 * (a * b)) rest)
    (mulTape (List.replicate a true) 0 b (s + a * b) (Z + a * b) rest)
    (mulTape (List.replicate a true) 0 b (s + 2 * (a * b)) Z rest) t1 t2
    (Sum.inr ((2 : Fin 3), false)) (2 * a) (Sum.inr ((2 : Fin 3), false)) (2 * a)
    h1 mulBlock_halt h2 mulBlock_halt

theorem twiceMulBlock_halt :
    twiceMulBlockMachine.halt (Sum.inr (Sum.inr ((2 : Fin 3), false))) = true := rfl

/-- **`×3`**: three `mulBlock`s scale the accumulator by `3ab`. -/
def thriceMulBlockMachine : Machine := seqMachine mulBlockMachine twiceMulBlockMachine

theorem thriceMulBlockM_run (a b s Z : ℕ) (rest : List Bool) :
    ∃ t, run thriceMulBlockMachine t
        (init thriceMulBlockMachine (mulTape (List.replicate a true) 0 b s (Z + 3 * (a * b)) rest))
      = ⟨Sum.inr (Sum.inr (Sum.inr ((2 : Fin 3), false))), 2 * a,
          mulTape (List.replicate a true) 0 b (s + 3 * (a * b)) Z rest⟩ := by
  obtain ⟨t1, h1⟩ := mulBlockM_run a b s (Z + 2 * (a * b)) rest
  obtain ⟨t2, h2⟩ := twiceMulBlockM_run a b (s + a * b) Z rest
  rw [show Z + 2 * (a * b) + a * b = Z + 3 * (a * b) from by ring] at h1
  rw [show s + a * b + 2 * (a * b) = s + 3 * (a * b) from by ring] at h2
  refine ⟨t1 + 1 + t2, ?_⟩
  exact seq_run mulBlockMachine twiceMulBlockMachine
    (mulTape (List.replicate a true) 0 b s (Z + 3 * (a * b)) rest)
    (mulTape (List.replicate a true) 0 b (s + a * b) (Z + 2 * (a * b)) rest)
    (mulTape (List.replicate a true) 0 b (s + 3 * (a * b)) Z rest) t1 t2
    (Sum.inr ((2 : Fin 3), false)) (2 * a)
    (Sum.inr (Sum.inr ((2 : Fin 3), false))) (2 * a)
    h1 mulBlock_halt h2 twiceMulBlock_halt

/-- **The squaring-and-triple** the arms run: `v += 3a²`, operand live. -/
theorem thriceSqBlockM_run (a s Z : ℕ) (rest : List Bool) :
    ∃ t, run thriceMulBlockMachine t
        (init thriceMulBlockMachine (mulTape (List.replicate a true) 0 a s (Z + 3 * (a * a)) rest))
      = ⟨Sum.inr (Sum.inr (Sum.inr ((2 : Fin 3), false))), 2 * a,
          mulTape (List.replicate a true) 0 a (s + 3 * (a * a)) Z rest⟩ :=
  thriceMulBlockM_run a a s Z rest

end PallLean.Paper93.DeepMath.PathB.MulBlockIter
