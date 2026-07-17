import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUnaryCmpMachine
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitSeq

/-!
# The multiplication sub-arc, brick 5: the squaring machine

**The first assembly composite.**  Squaring `t ↦ t²` is `dupMachine ⨟ mulMachine`, proved
here as a genuine `seqMachine` composition of the two well-formed-run machines — the first
demonstration that the sub-arc's pipeline-internal machines chain end to end.

The key is that `dup`'s output *is* `mul`'s squaring input:

  `dup :  [T,T]^a [F,F] 0^(z+a²+2a+2) rest  ↦  [T,T]^a [F,F] [T,T]^a 0^(z+a²+2) rest`

and, splitting `0^(z+a²+2) = [F,F] ++ 0^(z+a²)`, that final tape is *literally*

  `mulTape (1^a) 0 a 0 (z+a²) rest = [T,T]^a [F,F] [T,T]^a [F,F] 1^0 0^(z+a²) rest`

— the healed source is `mul`'s outer block, the fresh copy its inner block, the leftover
zeros its terminator and frontier (`dup_mul_bridge`).  `mul` then grows the run by `a·a`:

  `mul :  … ↦ mulTape (0-marks) 0 a a² z rest = [F,F]^a [F,F] [T,T]^a [F,F] 1^(a²) 0^z rest`.

`sqM_run` composes these by `seq_run` (exact clock `t₁ + 1 + t₂`), giving a proven `t²`
operation.  The remaining pair-assembly (branch on `t < p` via `cmpMachine`, then
`p²+t` / `t²+t+p`, then `×3` and `+tag`) builds on this composite and `cmpM_run`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UnarySquareMachine

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq (seqMachine seq_run)
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (flat2)
open PallLean.Paper93.DeepMath.PathB.UnaryMulMachine (mulTape mulM_run mulMachine)
open PallLean.Paper93.DeepMath.PathB.UnaryDupMachine (dupTape dupM_run dupMachine)

/-- **The bridge**: `dup`'s output tape is exactly `mul`'s squaring input tape. -/
theorem dup_mul_bridge (a W : ℕ) (rest : List Bool) :
    dupTape 0 a a (W + 2) rest = mulTape (List.replicate a true) 0 a 0 W rest := by
  have hz : List.replicate (W + 2) false
      = false :: false :: List.replicate W false := by
    rw [List.replicate_succ, List.replicate_succ]
  unfold dupTape mulTape
  rw [hz]
  simp [flat2]

/-- The squaring machine. -/
def sqMachine : Machine := seqMachine dupMachine mulMachine

/-- **The squaring machine computes `t²`**: on the doubled block `[T,T]^a` with adequate
scratch zeros, the run region grows to `1^(a²)`.  Proved by `seq_run` composition. -/
theorem sqM_run (a z : ℕ) (rest : List Bool) :
    ∃ t, run sqMachine t
        (init sqMachine (dupTape 0 a 0 (z + a * a + 2 + 2 * a) rest))
      = ⟨Sum.inr (17, false), 2 * a, mulTape (List.replicate a false) 0 a (a * a) z rest⟩ := by
  obtain ⟨t1, _, hd⟩ := dupM_run a (z + a * a + 2) rest false
  obtain ⟨t2, _, hm⟩ := mulM_run a a 0 z rest false
  rw [Nat.zero_add] at hm
  rw [← dup_mul_bridge a (z + a * a) rest] at hm
  have hh1 : dupMachine.halt ((6 : Fin 10), false) = true := by decide
  have hh2 : mulMachine.halt ((17 : Fin 18), false) = true := by decide
  refine ⟨t1 + 1 + t2, ?_⟩
  show run (seqMachine dupMachine mulMachine) (t1 + 1 + t2)
      (init (seqMachine dupMachine mulMachine)
        (dupTape 0 a 0 (z + a * a + 2 + 2 * a) rest)) = _
  exact seq_run dupMachine mulMachine
    (dupTape 0 a 0 (z + a * a + 2 + 2 * a) rest)
    (dupTape 0 a a (z + a * a + 2) rest)
    (mulTape (List.replicate a false) 0 a (a * a) z rest)
    t1 t2 ((6 : Fin 10), false) (2 * a) ((17 : Fin 18), false) (2 * a)
    hd hh1 hm hh2

end PallLean.Paper93.DeepMath.PathB.UnarySquareMachine
