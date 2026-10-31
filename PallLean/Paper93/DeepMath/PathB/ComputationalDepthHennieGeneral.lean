import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEmptySpaceHennie

/-!
# The blank-traversal bound for general machines (blank-phase form)

`EmptySpaceHennie` checked "no computation in empty space" for a write-free machine on empty input.
This file lifts the mechanism to **arbitrary machines**: the write-free and empty-input hypotheses
are replaced by the single condition that the head *reads `false`* at every active step.  This is
the form the moving-frontier argument needs — it applies to any machine's blank phase, whatever it
did before.

* `run_st_blankNext` — while a run reads `false` at every active step, its state is exactly the
  `blankNext`-iterate, independent of the tape and head.
* `blank_reads_false_run` — **a run that reads `false` at every active step halts within `|State|`
  steps or never halts.**  (`writeFree_empty_halts_fast` is the special case of empty input.)
* `blank_suffix_halts_fast` — the same, time-shifted: once a machine reads only `false` from time
  `t₀` on (a *blank phase*, e.g. the head is beyond the rightmost written cell in the semi-infinite
  blank region), its halting is decided by step `t₀ + |State|`.

This is the exact reason the head cannot outrun its frontier: past the rightmost landmark everything
is blank forever, so by `blank_suffix_halts_fast` the head either halts within `|State|` steps or
never — it cannot productively wander superpolynomially far into empty space.

**What remains for the full `time ≤ poly(distinctTapes, |x|)` bound.**  One must additionally track
that (i) each maximal blank *excursion* (head strictly right of the rightmost landmark) that does
not halt must return leftward within `|State|` steps, bounding the head by `frontier + |State|`, and
(ii) every extension of the frontier writes a cell that was never non-blank before, hence a distinct
tape, so there are at most `distinctTapes` extensions each of size `≤ |State|`.  That excursion /
landmark bookkeeping is not carried out here; this file provides its load-bearing lemma.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This file proves no SAT lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.HennieGeneral

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.EmptySpaceHennie (blankNext step_st_blank orbit_bounded)

variable {M : Machine}

/-- While a run reads `false` at every not-yet-halted step, its state is the `blankNext`-iterate. -/
theorem run_st_blankNext (d : Cfg M)
    (hread : ∀ k, M.halt (run M k d).st = false →
        (run M k d).tp.getD (run M k d).hd false = false)
    (k : ℕ) (hpre : ∀ j, j < k → M.halt ((blankNext M)^[j] d.st) = false) :
    (run M k d).st = (blankNext M)^[k] d.st := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ihv := ih (fun j hj => hpre j (by omega))
    have hnh : M.halt (run M k d).st = false := by rw [ihv]; exact hpre k (by omega)
    rw [run_succ, step_st_blank hnh (hread k hnh), ihv, Function.iterate_succ_apply']

/-- **The general blank-traversal bound.**  A run that reads `false` at every active step either
halts within `|State|` steps or never halts — no machine computes for longer than its state count
while reading only blanks. -/
theorem blank_reads_false_run (d : Cfg M)
    (hread : ∀ k, M.halt (run M k d).st = false →
        (run M k d).tp.getD (run M k d).hd false = false) :
    (∃ k ≤ Fintype.card M.State, M.halt (run M k d).st = true)
      ∨ (∀ k, M.halt (run M k d).st = false) := by
  by_cases h : ∀ k, M.halt ((blankNext M)^[k] d.st) = false
  · right
    intro k
    rw [run_st_blankNext d hread k (fun j _ => h j)]
    exact h k
  · left
    have hex : ∃ k, M.halt ((blankNext M)^[k] d.st) = true := by
      push_neg at h
      obtain ⟨k0, hk0⟩ := h
      exact ⟨k0, by cases hh : M.halt ((blankNext M)^[k0] d.st) <;> simp_all⟩
    have hpre : ∀ j, j < Nat.find hex → M.halt ((blankNext M)^[j] d.st) = false := by
      intro j hj
      have hm := Nat.find_min hex hj
      cases hb : M.halt ((blankNext M)^[j] d.st) <;> simp_all
    have hcard : Nat.find hex ≤ Fintype.card M.State := by
      obtain ⟨t', ht'le, ht'eq⟩ := orbit_bounded (blankNext M) d.st (Nat.find hex)
      by_contra hgt
      push_neg at hgt
      have hf := hpre t' (by omega)
      rw [← ht'eq, Nat.find_spec hex] at hf
      simp at hf
    exact ⟨Nat.find hex, hcard, by rw [run_st_blankNext d hread _ hpre]; exact Nat.find_spec hex⟩

/-- **The blank-phase bound (time-shifted).**  If a machine reads only `false` from time `t₀` on,
its halting is decided by step `t₀ + |State|`: it halts within `|State|` steps of entering the
blank phase, or never.  This is why the head cannot wander superpolynomially far past its frontier —
the region past the rightmost landmark is blank forever. -/
theorem blank_suffix_halts_fast (c : Cfg M) (t0 : ℕ)
    (hread : ∀ k, M.halt (run M (t0 + k) c).st = false →
        (run M (t0 + k) c).tp.getD (run M (t0 + k) c).hd false = false) :
    (∃ k ≤ Fintype.card M.State, M.halt (run M (t0 + k) c).st = true)
      ∨ (∀ k, M.halt (run M (t0 + k) c).st = false) := by
  have hrw : ∀ k, run M k (run M t0 c) = run M (t0 + k) c := fun k => (run_add M t0 k c).symm
  have key := blank_reads_false_run (run M t0 c) (by
    intro k
    rw [hrw k]
    exact hread k)
  rcases key with ⟨k, hk, hhalt⟩ | hnever
  · left; exact ⟨k, hk, by rw [← hrw k]; exact hhalt⟩
  · right; intro k; rw [← hrw k]; exact hnever k

end PallLean.Paper93.DeepMath.PathB.HennieGeneral
