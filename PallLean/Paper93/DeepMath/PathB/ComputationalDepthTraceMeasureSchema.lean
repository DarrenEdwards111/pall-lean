import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDIndexMachine

/-!
# S1: the trace-measure schema and the generic-soundness transfer theorem

**Step 5, brick S1.**  The no-gos (`SeparationNoGo`) proved that all content of an
invariant route must enter through a *concrete machine-level* measure whose generic
soundness is a real transfer theorem; the kill (`LangRankKill`/`DIndexMachine`) proved
language-level extractions cannot be generically sound.  This brick builds the surviving
schema natively in the faithful model:

* `traceObj M t x` — the **trace**: the machine's full tape evolution over `t+1` steps,
  the concrete object every trace-level measure reads.  (E6's emitted tableau is an
  encoding of exactly this data for the simulated model; working with the trace directly
  avoids any model bridge and fences nothing.)
* `traceSize` — its total cell count, with the *proved* growth bounds: the head moves at
  most one cell per step (`run_hd_le`) and the tape grows at most one cell per step
  (`run_tp_le`), so `traceSize ≤ (t+1)·(n+t) + (t+1)`.
* `minHalt M n` — the canonical clock: the least single time by which `M` halts on every
  length-`n` input (`0` if none); bounded by any uniform halting clock (`minHalt_le`).
* `traceInv μ` — **the schema**: the per-length worst-case measure
  `n ↦ max_{|x|=n} μ(traceObj M (minHalt M n) x)`, an honest `Invariant`.

**The transfer theorem** (`traceInv_genSound`): for every size-dominated `μ`
(`μ ≤ traceSize`), `traceInv μ` is generically sound — polynomial on *every*
polynomial-time machine, whatever it computes.  This is the first genuine
generic-soundness theorem in the corpus: the axis that `minTimeInv` showed carries all
the route's content is now discharged *for the entire size-dominated measure family at
once*, with no correctness or SAT hypotheses.

**What remains is exactly S2** (`traceMeasure_route`): for any size-dominated `μ`,
`InvHard SATV (traceInv μ)` — every SAT-decider has superpolynomial worst-case trace
measure — yields `¬ PolyCollapse SATV`.  By `genSound_route_iff_sep` this pair is, as
always, logically equivalent to the separation; its sole possible value is that the
hardness half is a statement about concrete, structured trace families, attackable by
algebra rather than diagonalization.  No hardness is claimed for any `μ` here.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge
open PallLean.Paper93.DeepMath.PathB.SeparationNoGo
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-! ## The trace object and its size -/

/-- The trace: the tape at each time `0, …, t`. -/
def traceObj (M : Machine) (t : ℕ) (x : List Bool) : List (List Bool) :=
  (List.range (t + 1)).map fun i => (run M i (init M x)).tp

/-- Total cell count of a trace (rows counted too, so row-counting measures are
dominated as well). -/
def traceSize (tr : List (List Bool)) : ℕ := (tr.map List.length).sum + tr.length

/-! ## Growth bounds: the head and the tape move at most one cell per step -/

theorem moveHead_le (h : ℕ) (m : Move) : moveHead h m ≤ h + 1 := by
  unfold moveHead
  repeat' split
  all_goals omega

theorem writeAt_length (tape : List Bool) (p : ℕ) (w : Bool) :
    (writeAt tape p w).length = max tape.length (p + 1) := by
  unfold writeAt
  rw [List.length_set, List.length_append, List.length_replicate]
  omega

theorem step_hd_le (M : Machine) (c : Cfg M) : (step M c).hd ≤ c.hd + 1 := by
  unfold step
  split
  · omega
  · show moveHead c.hd (M.δ c.st (c.tp.getD c.hd false)).2.2 ≤ c.hd + 1
    exact moveHead_le _ _

theorem step_tp_length (M : Machine) (c : Cfg M) :
    (step M c).tp.length ≤ max c.tp.length (c.hd + 1) := by
  unfold step
  split
  · exact le_max_left _ _
  · show (match (M.δ c.st (c.tp.getD c.hd false)).2.1 with
        | none => c.tp
        | some w => writeAt c.tp c.hd w).length ≤ max c.tp.length (c.hd + 1)
    rcases (M.δ c.st (c.tp.getD c.hd false)).2.1 with _ | w
    · exact le_max_left _ _
    · rw [writeAt_length]

/-- The head is at position at most `t` after `t` steps. -/
theorem run_hd_le (M : Machine) (x : List Bool) : ∀ t, (run M t (init M x)).hd ≤ t
  | 0 => Nat.le_refl 0
  | t + 1 => by
    rw [run_succ]
    exact (step_hd_le _ _).trans (Nat.succ_le_succ (run_hd_le M x t))

/-- The tape has grown by at most `t` cells after `t` steps. -/
theorem run_tp_length (M : Machine) (x : List Bool) :
    ∀ t, (run M t (init M x)).tp.length ≤ x.length + t
  | 0 => Nat.le_refl _
  | t + 1 => by
    rw [run_succ]
    refine (step_tp_length _ _).trans ?_
    have h1 := run_tp_length M x t
    have h2 := run_hd_le M x t
    omega

/-- **The trace-size bound**: at most `(t+1)` rows of at most `n+t` cells each. -/
theorem traceSize_le (M : Machine) (x : List Bool) (t : ℕ) :
    traceSize (traceObj M t x) ≤ (t + 1) * (x.length + t) + (t + 1) := by
  unfold traceSize traceObj
  have hsum : (((List.range (t + 1)).map fun i => (run M i (init M x)).tp).map
      List.length).sum ≤ (t + 1) * (x.length + t) := by
    have hb : ∀ y ∈ ((List.range (t + 1)).map fun i => (run M i (init M x)).tp).map
        List.length, y ≤ x.length + t := by
      intro y hy
      simp only [List.mem_map, List.mem_range] at hy
      obtain ⟨_, ⟨i, hi, rfl⟩, rfl⟩ := hy
      exact (run_tp_length M x i).trans (by omega)
    have := List.sum_le_card_nsmul _ _ hb
    simpa [smul_eq_mul] using this
  have hlen : (((List.range (t + 1)).map fun i => (run M i (init M x)).tp).map
      List.length).length = t + 1 := by simp
  have hlen2 : ((List.range (t + 1)).map fun i => (run M i (init M x)).tp).length
      = t + 1 := by simp
  omega

/-! ## The canonical clock: minimal uniform halting time -/

/-- `M` halts on every length-`n` input by time `t`. -/
def HaltsAllAt (M : Machine) (n t : ℕ) : Prop :=
  ∀ x : List Bool, x.length = n → HaltsBy M x t

/-- The least uniform halting time per length (`0` where none exists). -/
noncomputable def minHalt (M : Machine) (n : ℕ) : ℕ :=
  if h : ∃ t, HaltsAllAt M n t then Nat.find h else 0

/-- Any uniform halting clock dominates the canonical one. -/
theorem minHalt_le {M : Machine} {T : ℕ → ℕ} (hH : ∀ x, HaltsBy M x (T x.length))
    (n : ℕ) : minHalt M n ≤ T n := by
  have hsolved : HaltsAllAt M n (T n) := by
    intro x hx
    have := hH x
    rwa [hx] at this
  show (if h : ∃ t, HaltsAllAt M n t then Nat.find h else 0) ≤ T n
  rw [dif_pos ⟨T n, hsolved⟩]
  exact Nat.find_le hsolved

/-! ## The schema and the transfer theorem -/

/-- **The trace-measure schema**: the per-length worst case of `μ` on `M`'s traces at
the canonical clock. -/
noncomputable def traceInv (μ : List (List Bool) → ℕ) : Invariant := fun M n =>
  Finset.univ.sup fun v : Fin n → Bool => μ (traceObj M (minHalt M n) (List.ofFn v))

/-- A measure is size-dominated if it never exceeds the total trace size. -/
def SizeDominated (μ : List (List Bool) → ℕ) : Prop := ∀ tr, μ tr ≤ traceSize tr

/-- The size itself is trivially size-dominated (sanity witness). -/
theorem sizeDominated_traceSize : SizeDominated traceSize := fun _ => Nat.le_refl _

/-- **THE TRANSFER THEOREM.**  Every size-dominated trace measure is generically sound:
polynomial on every polynomial-time machine, with no correctness hypothesis.  The
polynomial-time machine's canonical clock is bounded by its halting clock
(`minHalt_le`), its traces are polynomially small (`traceSize_le`), and the worst case
over inputs is bounded uniformly. -/
theorem traceInv_genSound (μ : List (List Bool) → ℕ) (hμ : SizeDominated μ) :
    InvGenSound (traceInv μ) := by
  intro M hM
  obtain ⟨T, hT, hH⟩ := hM
  have hbound : ∀ n, traceInv μ M n ≤ 3 * (T n + n + 1) ^ 2 := by
    intro n
    apply Finset.sup_le
    intro v _
    have h1 := hμ (traceObj M (minHalt M n) (List.ofFn v))
    have h2 := traceSize_le M (List.ofFn v) (minHalt M n)
    have h3 := minHalt_le hH n
    have h4 : (List.ofFn v).length = n := by simp
    rw [h4] at h2
    have h5 : (minHalt M n + 1) * (n + minHalt M n) + (minHalt M n + 1)
        ≤ (T n + 1) * (n + T n) + (T n + 1) :=
      Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    have h6 : (T n + 1) * (n + T n) + (T n + 1) ≤ 3 * (T n + n + 1) ^ 2 := by
      have e1 : (T n + 1) * (n + T n) = T n * n + T n * T n + n + T n := by ring
      have e2 : 3 * (T n + n + 1) ^ 2
          = 3 * (T n * T n) + 3 * (n * n) + 6 * (T n * n) + 6 * T n + 6 * n + 3 := by
        ring
      omega
    omega
  exact polyBounded_of_le hbound (polyBounded_time_comp 3 2 hT)

/-! ## The S2 interface -/

/-- **The route, reduced to its sole remaining open half.**  For any size-dominated
measure, SAT-hardness of its worst-case trace profile forces the boundary out of P.
Generic soundness is *proved* (`traceInv_genSound`); the hardness hypothesis — every
SAT-decider has superpolynomial worst-case trace measure — is S2's target, a statement
about concrete structured trace families.  By `genSound_route_iff_sep` the pair remains
logically equivalent to the separation: the schema buys an attack surface, never a
discount. -/
theorem traceMeasure_route (SATV : NPObs) (μ : List (List Bool) → ℕ)
    (hμ : SizeDominated μ) (hHard : InvHard SATV (traceInv μ)) :
    ¬ PolyCollapse SATV :=
  invariant_bridge SATV (traceInv μ)
    (invSound_of_genSound SATV (traceInv μ) (traceInv_genSound μ hμ)) hHard

end PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
