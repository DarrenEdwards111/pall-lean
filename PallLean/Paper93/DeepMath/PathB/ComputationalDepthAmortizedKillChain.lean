import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGuardedTwoKillChain

/-!
# The amortized accounting framework: kill schedules and the rate harness

The three-kill no-go closed the per-step ladder at two kills per variable, for
every variable.  The classical route past `2n` (Schnorr `2.5n`, FGHK/Li–Yang
`3n+`) is **amortized**: an invariant class of functions and an
existence-of-a-good-variable lemma — some restriction kills `k` gates while the
invariant survives.  This file builds the accounting that converts such lemmas
into floors:

* `KillChain` — a schedule whose every step carries a **certified** kill count;
* **`cbudget_killchain_residual` (proved)** — banked kills plus the residual
  budget bound the original: `killSum + cbudget (residual) ≤ cbudget f`;
* `killChain_of_guardedChain` — guarded chains are rate-2 kill chains;
* **`cbudget_killchain_cone` (proved)** — composition with the cone bound;
* **`cbudget_of_rate` (proved), the rate harness** — any invariant `P` with a
  rate-`k` good-variable step (kills `k`, keeps `P`, drops dependence by at most
  one) iterates to `k · d ≤ cbudget f` for `d ≤ deps(f)`.

## Honest scope

The harness carries no lower bound by itself: the open mathematics is the rate
lemma — for `k ≥ 3` it must argue existence of a good variable from circuit
structure (fanout/top-gate case analysis with a potential function), which the
no-go shows cannot be a per-variable semantic theorem.  Rate 2 is instantiated
(guarded chains); rate 3 on a class containing the SAT slices would give `3n`-scale
floors through this file unchanged.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor

/-- A kill schedule: each step is a variable, a value, and a kill count certified
against `cbudget`. -/
def KillChain {n : ℕ} : ((Fin n → Bool) → Bool) → List (Fin n × Bool × ℕ) → Prop
  | _, [] => True
  | f, s :: rest => (cbudget (restrictF f s.1 s.2.1) + s.2.2 ≤ cbudget f) ∧
      KillChain (restrictF f s.1 s.2.1) rest

/-- Total banked kills. -/
def killSum {n : ℕ} (steps : List (Fin n × Bool × ℕ)) : ℕ :=
  (steps.map (fun s => s.2.2)).sum

/-- The residual after a kill schedule. -/
def restrictKC {n : ℕ} : ((Fin n → Bool) → Bool) → List (Fin n × Bool × ℕ) →
    ((Fin n → Bool) → Bool)
  | f, [] => f
  | f, s :: rest => restrictKC (restrictF f s.1 s.2.1) rest

/-- **The banking theorem (proved)**: certified kills accumulate on top of the
residual's own budget. -/
theorem cbudget_killchain_residual {n : ℕ} :
    ∀ (steps : List (Fin n × Bool × ℕ)) (f : (Fin n → Bool) → Bool),
      KillChain f steps → killSum steps + cbudget (restrictKC f steps) ≤ cbudget f := by
  intro steps
  induction steps with
  | nil =>
    intro f _
    show killSum [] + cbudget f ≤ cbudget f
    simp [killSum]
  | cons s rest ih =>
    intro f h
    obtain ⟨hkill, hchain⟩ :=
      (h : (cbudget (restrictF f s.1 s.2.1) + s.2.2 ≤ cbudget f) ∧
        KillChain (restrictF f s.1 s.2.1) rest)
    have hih := ih (restrictF f s.1 s.2.1) hchain
    show s.2.2 + killSum rest + cbudget (restrictKC (restrictF f s.1 s.2.1) rest) ≤ cbudget f
    omega

theorem cbudget_killchain {n : ℕ} (steps : List (Fin n × Bool × ℕ))
    (f : (Fin n → Bool) → Bool) (h : KillChain f steps) :
    killSum steps ≤ cbudget f := by
  have := cbudget_killchain_residual steps f h
  omega

/-- Guarded chains are rate-2 kill chains. -/
theorem killChain_of_guardedChain {n : ℕ} :
    ∀ (steps : List (Fin n × Bool)) (f : (Fin n → Bool) → Bool),
      GuardedChain f steps → KillChain f (steps.map (fun s => (s.1, s.2, 2))) := by
  intro steps
  induction steps with
  | nil => intro f _; trivial
  | cons s rest ih =>
    intro f h
    obtain ⟨hstep, hchain⟩ :=
      (h : GuardedStep f s.1 ∧ GuardedChain (restrictF f s.1 s.2) rest)
    exact ⟨cbudget_guardedstep f s.1 s.2 hstep, ih (restrictF f s.1 s.2) hchain⟩

/-- Composition with the cone bound on the residual. -/
theorem cbudget_killchain_cone {n : ℕ} (steps : List (Fin n × Bool × ℕ))
    (f : (Fin n → Bool) → Bool) (h : KillChain f steps) :
    killSum steps + 2 * (depSet (restrictKC f steps)).card ≤ cbudget f + 1 := by
  have h1 := cbudget_killchain_residual steps f h
  have h2 := cone_bound (restrictKC f steps)
  omega

/-- **THE RATE HARNESS (proved).**  An invariant class `P` with a rate-`k`
good-variable step — some restriction kills `k` gates, keeps `P`, and drops the
dependence count by at most one — iterates to `k · d ≤ cbudget f` whenever
`d ≤ deps(f)`.  Any future amortized rate-3 lemma on a class containing the SAT
slices converts to `3n`-scale floors through this theorem unchanged. -/
theorem cbudget_of_rate {n : ℕ} (P : ((Fin n → Bool) → Bool) → Prop) (k : ℕ)
    (hstep : ∀ f, P f → 1 ≤ (depSet f).card →
      ∃ i b, cbudget (restrictF f i b) + k ≤ cbudget f ∧ P (restrictF f i b) ∧
        (depSet f).card ≤ (depSet (restrictF f i b)).card + 1) :
    ∀ (d : ℕ) (f : (Fin n → Bool) → Bool), P f → d ≤ (depSet f).card →
      k * d ≤ cbudget f := by
  intro d
  induction d with
  | zero =>
    intro f _ _
    simp
  | succ d ih =>
    intro f hP hd
    obtain ⟨i, b, hkill, hP', hdrop⟩ := hstep f hP (by omega)
    have hih := ih (restrictF f i b) hP' (by omega)
    have hmul : k * (d + 1) = k * d + k := by ring
    omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_killchain_residual
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killChain_of_guardedChain
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_of_rate
