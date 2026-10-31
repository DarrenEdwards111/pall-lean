import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUnaryHealMachine
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitSeq

/-!
# The shared-layout multiply: `mulBlock`

`mulMachine` grows the accumulator by `a·b` but leaves its outer operand marked; on the
shared layout every operand must stay live and reusable.  `mulBlockMachine` fixes this —
it is `mulMachine ⨟ healMachine`, healing the outer block back to live afterward:

  `mulBlock :  [T,T]^a [F,F] [T,T]^b [F,F] 1^v 0^(z+a·b) rest
             ↦ [T,T]^a [F,F] [T,T]^b [F,F] 1^(v+a·b) 0^z rest`.

Both operand blocks emerge live; the accumulator grows by `a·b`.  Proved by `seq_run` from
`mulM_run` (compute `a·b`, mark the outer, heal the inner) and `healM_run` (unmark the
outer, at the front).  With `b = a` this is **squaring** on the shared layout with no debris;
`×3` is `mulBlock 3`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MulBlockMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq (seqMachine seq_run)
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (flat2)
open PallLean.Paper93.DeepMath.PathB.UnaryMulMachine (mulMachine mulTape mulM_run)
open PallLean.Paper93.DeepMath.PathB.UnaryHealMachine (healMachine healM_run)

/-- `mulTape` with a `0`-marked outer block, in heal-ready form (the outer block is a plain
`flat2` prefix followed by its terminator). -/
theorem mulTape_heal (bit : Bool) (a b v z : ℕ) (rest : List Bool) :
    mulTape (List.replicate a bit) 0 b v z rest
      = flat2 (List.replicate a bit)
          ++ false :: false :: (flat2 (List.replicate b true)
            ++ false :: false :: (List.replicate v true ++ (List.replicate z false ++ rest))) := by
  unfold mulTape
  simp [flat2, List.replicate]

/-- The shared-layout multiplier: reusable operands, accumulator grows by `a·b`. -/
def mulBlockMachine : Machine := seqMachine mulMachine healMachine

/-- **`mulBlock` computes `v += a·b`** on the shared layout, leaving both operand blocks
live. -/
theorem mulBlockM_run (a b s z : ℕ) (rest : List Bool) :
    ∃ t, run mulBlockMachine t
        (init mulBlockMachine (mulTape (List.replicate a true) 0 b s (z + a * b) rest))
      = ⟨Sum.inr ((2 : Fin 3), false), 2 * a,
          mulTape (List.replicate a true) 0 b (s + a * b) z rest⟩ := by
  obtain ⟨t1, _, hmul⟩ := mulM_run a b s z rest false
  obtain ⟨t2, _, hheal⟩ := healM_run a
    (false :: (flat2 (List.replicate b true)
      ++ false :: false :: (List.replicate (s + a * b) true
        ++ (List.replicate z false ++ rest)))) false
  have hh1 : mulMachine.halt ((17 : Fin 18), false) = true := rfl
  have hh2 : healMachine.halt ((2 : Fin 3), false) = true := rfl
  refine ⟨t1 + 1 + t2, ?_⟩
  rw [← mulTape_heal false a b (s + a * b) z rest,
    ← mulTape_heal true a b (s + a * b) z rest] at hheal
  show run (seqMachine mulMachine healMachine) (t1 + 1 + t2)
      (init (seqMachine mulMachine healMachine)
        (mulTape (List.replicate a true) 0 b s (z + a * b) rest)) = _
  exact seq_run mulMachine healMachine
    (mulTape (List.replicate a true) 0 b s (z + a * b) rest)
    (mulTape (List.replicate a false) 0 b (s + a * b) z rest)
    (mulTape (List.replicate a true) 0 b (s + a * b) z rest) t1 t2
    ((17 : Fin 18), false) (2 * a) ((2 : Fin 3), false) (2 * a)
    hmul hh1 hheal hh2

/-- The shared-layout **squaring**: `v += a²`, operand live. -/
theorem sqBlockM_run (a s z : ℕ) (rest : List Bool) :
    ∃ t, run mulBlockMachine t
        (init mulBlockMachine (mulTape (List.replicate a true) 0 a s (z + a * a) rest))
      = ⟨Sum.inr ((2 : Fin 3), false), 2 * a,
          mulTape (List.replicate a true) 0 a (s + a * a) z rest⟩ :=
  mulBlockM_run a a s z rest

end PallLean.Paper93.DeepMath.PathB.MulBlockMachine
