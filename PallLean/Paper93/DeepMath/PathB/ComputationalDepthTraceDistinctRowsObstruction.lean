import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSuperAdditiveKills
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceDistinctRows
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHenniePeak

/-!
# Settling the head-as-data obstruction

## Status correction after the local-peak audit

The global-final-frontier part is now machine-checked below, including the exact bridge to
`distinctRows`.  It proves a time bound in terms of **final tape length** and distinct rows.  The
stronger moving-frontier claim in the older prose below is still open: `HenniePeak` requires its
chosen frontier to remain blank throughout the halting run, so it cannot be applied directly at a
frontier that is written later.  The remaining theorem is therefore a local constant-tape excursion
and frontier-growth bound, not Finset bookkeeping.  Until that theorem lands, `NoEmptySpaceComputation`
and the claimed polynomial equivalence are not proved.

Step 4 left one question: can a SAT decider have polynomially many distinct tape snapshots with
superpolynomially many head positions — using head position as data without writing to the tape?
This file settles it at the level of mathematics and records the exact formalization boundary.

## The obstruction resolves — and it kills `distinctRows` either way

The obstruction is precisely the implication `poly distinctTapes ⟹ poly time`.  Both possible
answers eliminate `distinctRows` as a *useful* proxy:

* **If the obstruction holds** (no superpolynomial-time machine has polynomial distinct-tape count):
  then, since `distinctTapes ≤ time` always, `distinctTapes` is **polynomially equivalent to time**.
  A `distinctRows` lower bound then says nothing a time lower bound does not — it is *content-free*,
  equivalent to the separation itself, with no structural handle beyond time.
* **If the obstruction fails** (some superpolynomial-time machine has polynomial distinct-tape
  count): then, since SAT is polynomial-space (`traceRank`'s killer), there is a SAT decider with
  polynomial `distinctRows`, so `distinctRows` is **not SAT-hard** — it is outright killed, like
  rank.

So `distinctRows` is not viable in either branch.  The formal anchor below records the "sufficient"
direction that always holds; the branch analysis is honest prose, and the deciding lemma is stated
but not formalized (see the boundary note).

## The formalization boundary

The obstruction is the classical **"no computation in empty space"** fact: to reach head position
`H` a halting machine needs a non-blank landmark in every `|State|`-window of `[|x|, H]` (it cannot
traverse more than `|State|` consecutive blank cells while halting — a pigeonhole on states forces a
non-halting drift or loop), and each new rightmost landmark is a distinct tape.  Hence
`H ≤ |x| + |State|·distinctTapes`, giving `time ≤ poly(distinctTapes, |x|)` via the structural bound
— i.e. the obstruction *holds*.  This is a Hennie-machine-style crossing-sequence argument; I was
**not** able to formalize the blank-traversal liveness step cleanly in this session, so the
settlement here is at the level of mathematical argument, not a machine-checked proof of the
implication.  What is machine-checked is the sufficiency direction and the size-domination.

## Verdict

`distinctRows` is dual to tableau rank: **rank ≤ space is too weak** (space-cheap SAT killed it);
**distinctRows ≈ time is too strong** (content-free) if the obstruction holds, or killed if it
fails.  A viable proxy must sit *strictly between* space and time — which is exactly the hard
regime this whole line keeps returning to.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This file proves no SAT lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceDistinctRowsObstruction

open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics (NPObs PolyCollapse)
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge (InvHard)
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.TraceSchemaCeiling (sizeDominated_hard_iff_sep)
open PallLean.Paper93.DeepMath.PathB.SuperAdditiveNarrow (rows_le_traceSize)
open PallLean.Paper93.DeepMath.PathB.SuperAdditiveKills (distinctRows)
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.TraceDistinctRows

attribute [local instance] Classical.propDecidable

/-! ## Exact bridge from the trace list to visited tape snapshots -/

/-- The tape snapshots appearing in `visitedConfigs` are exactly the rows of `traceObj`, viewed as
a finset.  This is the representation bridge needed to use the structural configuration bound with
the trace-level `distinctRows` measure. -/
theorem visitedTapes_eq_traceObj_toFinset (M : Machine) (x : List Bool) (T : ℕ) :
    (visitedConfigs (init M x) T).image (fun d => d.tp) = (traceObj M T x).toFinset := by
  ext tp
  simp [visitedConfigs, traceObj]

/-- **Exact distinct-tape bridge.**  The number of distinct tape snapshots in the configuration
finset is precisely `distinctRows (traceObj M T x)`. -/
theorem visitedTapes_card_eq_distinctRows (M : Machine) (x : List Bool) (T : ℕ) :
    ((visitedConfigs (init M x) T).image (fun d => d.tp)).card =
      distinctRows (traceObj M T x) := by
  rw [visitedTapes_eq_traceObj_toFinset]
  unfold distinctRows
  rw [← List.toFinset_card_of_nodup (List.nodup_dedup (traceObj M T x))]
  congr 1
  ext tp
  simp

/-! ## Global-final-frontier accounting -/

/-- A machine step never shortens its list tape. -/
theorem step_tp_length_mono (M : Machine) (c : Cfg M) :
    c.tp.length ≤ (step M c).tp.length := by
  unfold step
  split
  · exact Nat.le_refl _
  · rcases hwrite : (M.δ c.st (c.tp.getD c.hd false)).2.1 with _ | w
    · simp only [hwrite]
      exact Nat.le_refl _
    · simp only [hwrite, TraceMeasureSchema.writeAt_length]
      exact le_max_left _ _

/-- Tape length is monotone along a run. -/
theorem run_tp_length_mono (M : Machine) (c : Cfg M) {a b : ℕ} (hab : a ≤ b) :
    (run M a c).tp.length ≤ (run M b c).tp.length := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => simp
  | succ d ih =>
      rw [show a + (d + 1) = (a + d) + 1 by omega, run_succ]
      exact (ih (by omega)).trans (step_tp_length_mono M (run M (a + d) c))

/-- Once a run first-halts at `T`, every time (including after `T`) has tape length at most the
final tape length. -/
theorem run_tp_length_le_final (M : Machine) (c : Cfg M) {T : ℕ}
    (hhalt : M.halt (run M T c).st = true) (t : ℕ) :
    (run M t c).tp.length ≤ (run M T c).tp.length := by
  rcases le_total t T with ht | ht
  · exact run_tp_length_mono M c ht
  · rw [show t = T + (t - T) by omega, run_add, run_of_halted M hhalt]

/-- The final tape supplies a genuinely global blank frontier: every position at or beyond
`finalLength + 1` reads `false` at every time. -/
theorem reads_false_beyond_final (M : Machine) (c : Cfg M) {T : ℕ}
    (hhalt : M.halt (run M T c).st = true) (t p : ℕ)
    (hp : (run M T c).tp.length + 1 ≤ p) :
    (run M t c).tp.getD p false = false := by
  have hlen : (run M t c).tp.length ≤ p :=
    (run_tp_length_le_final M c hhalt t).trans (by omega)
  simp [List.getD, List.getElem?_eq_none hlen]

/-- **Checked global head accounting.**  In a first-halting run, every visited head is below the
final tape length plus one plus the number of states.  This is the valid use of `HenniePeak`: the
chosen frontier remains blank for the whole run, unlike the still-open moving-frontier argument. -/
theorem head_lt_finalTape_add_states (M : Machine) (x : List Bool) {T : ℕ}
    (hhalt : M.halt (run M T (init M x)).st = true)
    (hfirst : ∀ j, j < T → M.halt (run M j (init M x)).st = false)
    (t : ℕ) (ht : t ≤ T) :
    (run M t (init M x)).hd <
      (run M T (init M x)).tp.length + 1 + Fintype.card M.State := by
  let R := (run M T (init M x)).tp.length + 1
  apply HenniePeak.head_lt_of_blank (M := M) (init M x) R T (by simp [R])
    (by simp [R, init]) hhalt hfirst
  · intro s hs
    exact reads_false_beyond_final M (init M x) hhalt s _ hs
  · exact ht

/-- The number of visited head positions is bounded by the same final-frontier quantity. -/
theorem visitedHeads_card_le_finalTape_add_states (M : Machine) (x : List Bool) {T : ℕ}
    (hhalt : M.halt (run M T (init M x)).st = true)
    (hfirst : ∀ j, j < T → M.halt (run M j (init M x)).st = false) :
    ((visitedConfigs (init M x) T).image (fun d => d.hd)).card ≤
      (run M T (init M x)).tp.length + 1 + Fintype.card M.State := by
  let B := (run M T (init M x)).tp.length + 1 + Fintype.card M.State
  calc
    ((visitedConfigs (init M x) T).image (fun d => d.hd)).card
        ≤ (Finset.range B).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_image] at hp
          obtain ⟨d, hd, rfl⟩ := hp
          simp only [visitedConfigs, Finset.mem_image, Finset.mem_range] at hd
          obtain ⟨t, ht, rfl⟩ := hd
          rw [Finset.mem_range]
          exact head_lt_finalTape_add_states M x hhalt hfirst t (by omega)
    _ = B := Finset.card_range B

/-- **The fully checked bound up to the moving-frontier obligation.**  Halt time is bounded by
states times `(final tape length + 1 + states)` times the exact trace-level distinct-row count.
The only missing ingredient for polynomial equivalence is now a bound on final tape length in terms
of input length and distinct rows. -/
theorem time_le_finalTape_mul_distinctRows (M : Machine) (x : List Bool) {T : ℕ}
    (hhalt : M.halt (run M T (init M x)).st = true)
    (hfirst : ∀ j, j < T → M.halt (run M j (init M x)).st = false) :
    T + 1 ≤ Fintype.card M.State
      * ((run M T (init M x)).tp.length + 1 + Fintype.card M.State)
      * distinctRows (traceObj M T x) := by
  have htime := TraceDistinctRows.time_le (init M x) hhalt hfirst
  rw [visitedTapes_card_eq_distinctRows] at htime
  exact htime.trans (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_left _ (visitedHeads_card_le_finalTape_add_states M x hhalt hfirst)))

/-- `distinctRows` is size-dominated: the number of distinct configurations is at most the trace
size (the cash-out side — the *desirable* property). -/
theorem distinctRows_sizeDominated : SizeDominated distinctRows :=
  fun tr => (List.Sublist.length_le (List.dedup_sublist tr)).trans (rows_le_traceSize tr)

/-- **The sufficiency direction (always holds).**  A `distinctRows` lower bound on all SAT deciders
implies the separation: since `distinctRows` is size-dominated, its hardness plugs into the
completeness result.  So proving `distinctRows` hard is *no easier* than the separation — it implies
it.  (The converse — that the separation implies `distinctRows` hardness — is the obstruction, whose
resolution makes the two equivalent; see the module note.) -/
theorem distinctRows_hard_imp_sep (SATV : NPObs) (hH : InvHard SATV (traceInv distinctRows)) :
    ¬ PolyCollapse SATV :=
  (sizeDominated_hard_iff_sep SATV).mp ⟨distinctRows, distinctRows_sizeDominated, hH⟩

/-- **The remaining obstruction, named.**  `poly distinctTapes ⟹ poly time`: no machine runs
superpolynomially long with only polynomially many distinct tape snapshots.  The checked theorem
`time_le_finalTape_mul_distinctRows` reduces it to controlling final frontier growth.  The required
local constant-tape excursion/frontier-growth theorem is not machine-checked here. -/
def NoEmptySpaceComputation : Prop :=
  ∀ (M : ComposableMachine.Machine) (p : ℕ → ℕ),
    (∀ x T, M.halt (ComposableMachine.run M T (ComposableMachine.init M x)).st = true →
        (∀ k, k < T → M.halt (ComposableMachine.run M k (ComposableMachine.init M x)).st = false) →
        distinctRows (traceObj M T x) ≤ p x.length) →
    ∃ q : ℕ → ℕ, ∀ x T, M.halt (ComposableMachine.run M T (ComposableMachine.init M x)).st = true →
      (∀ k, k < T → M.halt (ComposableMachine.run M k (ComposableMachine.init M x)).st = false) →
      T ≤ q x.length

end PallLean.Paper93.DeepMath.PathB.TraceDistinctRowsObstruction
