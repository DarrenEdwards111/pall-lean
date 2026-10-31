import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBranchingObserver

/-!
# A concrete SAT instance through the hypercube witness observer

We instantiate the `BranchingObserver` abstraction on a concrete SAT instance and exhibit **both regimes**
the Option-B picture predicts, on the *same* witness set:

* a **faithful (transcript) observer** that keeps every witness apart — its boundary is forced `≥ n`;
* a **lossy low-boundary observer** (a single-coordinate projection) that **merges** the witnesses — showing
  the non-mergeability hypothesis is genuinely non-trivial, and that this (easy) instance does **not** force
  boundary on every observer.

This is the concrete content behind `sat_sectors_conditionally_force_boundary`: the conditional bound is
real (a faithful observer is forced up), and its hypothesis can *fail* (a lossy observer escapes) — exactly
the gap a separation would have to close for a *correct decider's* observer.

## The instance

On `n+1` Boolean variables, the formula is the single literal `φ(x) = x₀` ("the first variable is true").
Its witness set `W = { x : x₀ = true }` has `≥ 2ⁿ` elements (the other `n` coordinates are free).

## What is proved (all clean axioms, no `sorry`)

* `witnesses_card_ge` — `2ⁿ ≤ |W|`.
* `witnesses_force_boundary` — **any** observer that keeps `W` non-mergeable has boundary entropy `≥ n`.
* `transcript_nonmergeable` — the full-transcript observer (entropy `n+1`) keeps `W` non-mergeable, so the
  bound is realized (and essentially tight): distinguishing the `2ⁿ` witnesses needs `≥ n` boundary bits.
* `projection_merges` — for `n ≥ 2` the single-coordinate projection observer (entropy `1`) **cannot** keep
  `W` non-mergeable: too many witnesses for its capacity.  A low-boundary observer escapes — because `φ` is
  trivially easy.

## Honest scope

The faithful bound is genuine but unsurprising (a transcript observer *is* high-boundary).  The lossy
observer's escape is the point: it shows boundary is forced only when the observer **cannot** merge — and for
an easy instance like `x₀` it can.  The open content (Option B / the central conjecture) is whether the
observer induced by a *correct, efficient* SAT-decider on a *hard* instance is forced to be faithful under
*every* admissible decomposition.  Nothing here asserts that.
-/

namespace PallLean.Paper93.DeepMath.PathB.HypercubeWitness

open PallLean.Paper93.DeepMath.PathB

/-- The concrete SAT instance on `n+1` variables: the single literal `x₀`. -/
def phi {n : ℕ} (x : Fin (n + 1) → Bool) : Bool := x 0

/-- The witness hypercube: assignments satisfying `φ` (i.e. `x₀ = true`). -/
def witnesses (n : ℕ) : Finset (Fin (n + 1) → Bool) :=
  Finset.univ.filter (fun x => phi x = true)

/-- `Fin.cons true y` is a witness for every tail `y` (its `0`-th coordinate is `true`). -/
theorem cons_true_mem_witnesses {n : ℕ} (y : Fin n → Bool) :
    (Fin.cons true y : Fin (n + 1) → Bool) ∈ witnesses n := by
  simp [witnesses, phi, Fin.cons_zero]

/-- **`2ⁿ ≤ |W|`.**  The map `y ↦ Fin.cons true y` injects the `2ⁿ` tails into the witness set. -/
theorem witnesses_card_ge (n : ℕ) : 2 ^ n ≤ (witnesses n).card := by
  have hinj : Set.InjOn (fun y : Fin n → Bool => (Fin.cons true y : Fin (n + 1) → Bool))
      (Finset.univ : Finset (Fin n → Bool)) := by
    intro y _ z _ h
    funext i
    simpa [Fin.cons_succ] using congrFun h i.succ
  have hmaps : ∀ y ∈ (Finset.univ : Finset (Fin n → Bool)),
      (Fin.cons true y : Fin (n + 1) → Bool) ∈ witnesses n :=
    fun y _ => cons_true_mem_witnesses y
  have hcU : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    simp [Finset.card_univ, Fintype.card_fun]
  calc 2 ^ n = (Finset.univ : Finset (Fin n → Bool)).card := hcU.symm
    _ ≤ (witnesses n).card := Finset.card_le_card_of_injOn _ hmaps hinj

/-- **Any non-mergeable observer of `W` needs boundary `≥ n`.**  Direct from the branching principle: `W` has
`≥ 2ⁿ` witnesses, so keeping them apart costs `≥ n` boundary bits. -/
theorem witnesses_force_boundary {n : ℕ} (O : BranchingObserver (Fin (n + 1) → Bool))
    (hnm : O.Nonmergeable (witnesses n)) : n ≤ O.entropy :=
  O.exp_nonmergeable_sectors_force_boundary (witnesses n) hnm (witnesses_card_ge n)

/-! ### The faithful (transcript) observer realizes the bound -/

/-- The **transcript observer** on `m` variables: it records the whole assignment, mapping each into one of
`2^m` boundary states via the canonical `(Fin m → Bool) ≃ Fin (2^m)` encoding.  Boundary entropy `m`. -/
def transcript (m : ℕ) : BranchingObserver (Fin m → Bool) where
  entropy := m
  view := fun x => finFunctionFinEquiv (fun i => if x i then (1 : Fin 2) else 0)

theorem transcript_view_injective (m : ℕ) : Function.Injective (transcript m).view := by
  intro x y h
  have h2 := finFunctionFinEquiv.injective h
  funext i
  have hi := congrFun h2 i
  by_cases hx : x i <;> by_cases hy : y i <;>
    simp_all [hx, hy] <;> exact absurd hi (by decide)

/-- The transcript observer keeps **every** set of assignments non-mergeable (its view is injective). -/
theorem transcript_nonmergeable (m : ℕ) (T : Finset (Fin m → Bool)) :
    (transcript m).Nonmergeable T :=
  (transcript_view_injective m).injOn

/-- **Realization (faithful observer).**  The transcript observer keeps `W` non-mergeable and has boundary
entropy `n + 1`; the forced bound `n ≤ n + 1` holds.  So distinguishing the `2ⁿ` witnesses of this instance
costs `≥ n` boundary bits, and a faithful observer attains it (up to `+1`). -/
theorem transcript_realizes_bound (n : ℕ) :
    n ≤ (transcript (n + 1)).entropy ∧ (transcript (n + 1)).Nonmergeable (witnesses n) :=
  ⟨witnesses_force_boundary (transcript (n + 1)) (transcript_nonmergeable (n + 1) (witnesses n)),
   transcript_nonmergeable (n + 1) (witnesses n)⟩

/-! ### A lossy low-boundary observer escapes (the hypothesis can fail) -/

/-- The **projection observer**: it remembers only the first coordinate `x₀`.  Boundary entropy `1`
(two states, `Fin (2^1) = Fin 2`). -/
def projection (m : ℕ) : BranchingObserver (Fin (m + 1) → Bool) where
  entropy := 1
  view := fun x => if x 0 then (1 : Fin (2 ^ 1)) else 0

/-- **The lossy observer merges the witnesses.**  For `n ≥ 2`, the projection observer (entropy `1`, capacity
`2`) cannot keep the `≥ 2ⁿ > 2` witnesses non-mergeable — it collapses them.  A low-boundary observer of
this easy instance escapes the bound; the formula `x₀` does not force boundary on every observer. -/
theorem projection_merges {n : ℕ} (hn : 2 ≤ n) :
    ¬ (projection n).Nonmergeable (witnesses n) := by
  apply (projection n).not_nonmergeable_of_card_gt
  have hcap : (2 : ℕ) ^ (projection n).entropy = 2 := by simp [projection]
  rw [hcap]
  have h2n : 2 ^ n ≤ (witnesses n).card := witnesses_card_ge n
  have : (2 : ℕ) < 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ < 2 ^ n := by exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

end PallLean.Paper93.DeepMath.PathB.HypercubeWitness

#print axioms PallLean.Paper93.DeepMath.PathB.HypercubeWitness.witnesses_force_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.HypercubeWitness.transcript_realizes_bound
#print axioms PallLean.Paper93.DeepMath.PathB.HypercubeWitness.projection_merges
