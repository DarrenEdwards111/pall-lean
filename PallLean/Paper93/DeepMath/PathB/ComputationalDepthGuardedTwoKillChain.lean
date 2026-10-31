import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDAGTwoKill

/-!
# The guarded two-kill chain: two gates per restriction step

The iteration engine over `cbudget_twokill`.  A `GuardedChain` is a restriction
schedule each of whose steps satisfies the two-kill guard — both restrictions
nonconstant, neither equal nor pointwise complementary.  Unlike the one-kill
`LiveChain` residual engine, no side conditions are needed: the guard itself
supplies every hypothesis of the step theorem.

* `GuardedStep` / `GuardedChain` — the schedule predicate;
* **`cbudget_guardedchain_residual` (proved)**: `2L + cbudget (restrictAll f steps)
  ≤ cbudget f` — two gates banked per step, residual kept;
* **`cbudget_guardedchain` (proved)**: `2L ≤ cbudget f`;
* `liveChain_of_guardedChain` — the guard strictly refines liveness;
* **`cbudget_guardedchain_cone` (proved)**: the harness
  `2L + 2·deps(residual) ≤ cbudget f + 1`, composing with the cone bound.

## Honest accounting

A full-length guarded chain reaches `2n − O(1)` by **pure gate elimination**,
independent of the cone/parent-edge argument — a second, independent proof
technique at the `2n` scale.  It does not exceed it: each guarded coordinate is
also a dependent coordinate, so `L + deps(residual) ≤ n` caps the harness at
`2n`.  The harness is the conversion vehicle: any future `k`-kill step theorem
(`k ≥ 3`, Schnorr/FGHK-style amortized case analysis) plugged into this chain
yields `> 2n` floors directly.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor

/-- The two-kill guard at one variable. -/
def GuardedStep {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  (∃ x y, restrictF f i false x ≠ restrictF f i false y) ∧
  (∃ x y, restrictF f i true x ≠ restrictF f i true y) ∧
  restrictF f i true ≠ restrictF f i false ∧
  restrictF f i true ≠ fun x => !(restrictF f i false x)

/-- A restriction schedule whose every step satisfies the two-kill guard. -/
def GuardedChain {n : ℕ} : ((Fin n → Bool) → Bool) → List (Fin n × Bool) → Prop
  | _, [] => True
  | f, s :: rest => GuardedStep f s.1 ∧ GuardedChain (restrictF f s.1 s.2) rest

/-- One guarded step kills two gates (either restriction constant). -/
theorem cbudget_guardedstep {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) (b : Bool)
    (h : GuardedStep f i) :
    cbudget (restrictF f i b) + 2 ≤ cbudget f :=
  cbudget_twokill f i b h.1 h.2.1 h.2.2.1 h.2.2.2

/-- **The guarded chain engine (proved)**: two gates banked per step, residual kept. -/
theorem cbudget_guardedchain_residual {n : ℕ} :
    ∀ (steps : List (Fin n × Bool)) (f : (Fin n → Bool) → Bool),
      GuardedChain f steps →
      2 * steps.length + cbudget (restrictAll f steps) ≤ cbudget f := by
  intro steps
  induction steps with
  | nil =>
    intro f _
    show 2 * 0 + cbudget f ≤ cbudget f
    omega
  | cons s rest ih =>
    intro f h
    obtain ⟨hstep, hchain⟩ :=
      (h : GuardedStep f s.1 ∧ GuardedChain (restrictF f s.1 s.2) rest)
    have hkill := cbudget_guardedstep f s.1 s.2 hstep
    have hih := ih (restrictF f s.1 s.2) hchain
    show 2 * (rest.length + 1) + cbudget (restrictAll (restrictF f s.1 s.2) rest) ≤ cbudget f
    omega

/-- **Two gates per step (proved)**: `2L ≤ cbudget f`. -/
theorem cbudget_guardedchain {n : ℕ} (steps : List (Fin n × Bool))
    (f : (Fin n → Bool) → Bool) (h : GuardedChain f steps) :
    2 * steps.length ≤ cbudget f := by
  have := cbudget_guardedchain_residual steps f h
  omega

/-- The guard strictly refines liveness. -/
theorem liveChain_of_guardedChain {n : ℕ} :
    ∀ (steps : List (Fin n × Bool)) (f : (Fin n → Bool) → Bool),
      GuardedChain f steps → LiveChain f steps := by
  intro steps
  induction steps with
  | nil => intro f _; trivial
  | cons s rest ih =>
    intro f h
    obtain ⟨hstep, hchain⟩ :=
      (h : GuardedStep f s.1 ∧ GuardedChain (restrictF f s.1 s.2) rest)
    refine ⟨?_, ih (restrictF f s.1 s.2) hchain⟩
    obtain ⟨x, hx⟩ : ∃ x, restrictF f s.1 true x ≠ restrictF f s.1 false x := by
      by_contra hall
      push_neg at hall
      exact hstep.2.2.1 (funext hall)
    exact ⟨Function.update x s.1 true, Function.update x s.1 false,
      fun c' hc' => by
        by_contra hcne
        exact hc' (by rw [Function.update_of_ne hcne, Function.update_of_ne hcne]),
      hx⟩

/-- **The harness (proved)**: guarded banking composed with the cone bound on the
residual — the conversion vehicle for any future `k ≥ 3` kill step. -/
theorem cbudget_guardedchain_cone {n : ℕ} (steps : List (Fin n × Bool))
    (f : (Fin n → Bool) → Bool) (h : GuardedChain f steps) :
    2 * steps.length + 2 * (depSet (restrictAll f steps)).card ≤ cbudget f + 1 := by
  have h1 := cbudget_guardedchain_residual steps f h
  have h2 := cone_bound (restrictAll f steps)
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_guardedchain_residual
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_guardedchain
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_guardedchain_cone
