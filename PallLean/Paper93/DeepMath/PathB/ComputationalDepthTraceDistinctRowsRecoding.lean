import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceDistinctRowsSearch

/-!
# Step 4: representation-dependence of `distinctRows`

Can the same algorithm be simulated while collapsing tape-snapshot diversity?  This file probes the
extreme case and reads off what a collapse costs.

**`distinctRows` is representation-dependent — it can be collapsed all the way to `1`.**  A machine
that never writes keeps its tape constant (`run_tp_const`), so it visits exactly one distinct tape
snapshot (`distinctTapes_writeFree`).  So `distinctRows` is *not* an invariant of the computed
function: a write-free re-encoding drives it to the floor.

**But the total collapse forbids SAT.**  With `distinctTapes = 1`, the structural bound
degenerates to `time + 1 ≤ |State| · #headPositions` (`writeFree_time_le`): a write-free machine is
exactly a two-way finite automaton (a head moving over a fixed tape), whose running time is linear
in its head range and which decides *only regular languages*.  SAT is not regular, so **no
write-free machine decides SAT**.  The diversity removed from the tape cannot be recovered from
head movement alone.

**Verdict on step 4.**  `distinctRows` is representation-dependent, but the recoding that collapses
it to `O(1)` — write-freeness — also collapses the machine to the regular regime, which cannot
solve SAT.  A *partial*, SAT-preserving collapse to polynomially-many (not `O(1)`) distinct tapes
would, by `TraceDistinctRowsSearch`, require superpolynomial head range, and runs into the
head-as-data obstruction (using the head position as the assignment requires writing to read it
back).  That obstruction is still the open question; the total collapse is not a valid SAT
simulation, so — again — **no kill**.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This file proves no SAT lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceDistinctRowsRecoding

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.TraceDistinctRows
open PallLean.Paper93.DeepMath.PathB.TraceDistinctRowsSearch

attribute [local instance] Classical.propDecidable

variable {M : Machine}

/-- A machine is **write-free** if every step leaves the tape unchanged. -/
def WriteFree (M : Machine) : Prop := ∀ c : Cfg M, (step M c).tp = c.tp

/-- A write-free machine keeps its tape constant along the whole run. -/
theorem run_tp_const (hW : WriteFree M) (c : Cfg M) (t : ℕ) : (run M t c).tp = c.tp := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, hW, ih]

/-- **The maximal collapse.**  A write-free machine visits exactly one distinct tape snapshot, so
`distinctRows = 1` — driven to the floor regardless of running time. -/
theorem distinctTapes_writeFree (hW : WriteFree M) (x : List Bool) (T : ℕ) :
    distinctTapes M x T = 1 := by
  rw [distinctTapes, Finset.card_eq_one]
  refine ⟨(init M x).tp, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · rw [Finset.mem_image]
    refine ⟨init M x, ?_, rfl⟩
    rw [visitedConfigs, Finset.mem_image]
    exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos T), rfl⟩
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨d, hd, rfl⟩ := hy
    rw [visitedConfigs, Finset.mem_image] at hd
    obtain ⟨t, _, rfl⟩ := hd
    exact run_tp_const hW (init M x) t

/-- **The cost of the collapse.**  With `distinctTapes = 1`, the structural bound degenerates to
`time + 1 ≤ |State| · #headPositions` — a write-free machine's running time is bounded by its head
range alone (it is a two-way finite automaton, deciding only regular languages). -/
theorem writeFree_time_le (hW : WriteFree M) (x : List Bool) {T : ℕ}
    (hhalt : M.halt (run M T (init M x)).st = true)
    (hpre : ∀ k, k < T → M.halt (run M k (init M x)).st = false) :
    T + 1 ≤ Fintype.card M.State * headCount M x T := by
  have h := time_le' x hhalt hpre
  rw [distinctTapes_writeFree hW] at h
  simpa using h

end PallLean.Paper93.DeepMath.PathB.TraceDistinctRowsRecoding
