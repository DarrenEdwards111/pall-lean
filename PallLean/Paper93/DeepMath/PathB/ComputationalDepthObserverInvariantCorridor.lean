import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDIndexMachine
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverInvariantBridge

/-!
# The observer-invariant corridor: why representation-independent complexity is not sound

The non-circular hard direction is: exhibit a *representation-independent observer invariant* that
must grow superpolynomially on every SAT decider.  Such an invariant has to be both **sound**
(polynomially bounded on every poly-time decider — the cash-out side) and **hard** (superpolynomial
on SAT).  This file machine-checks the *upper wall* of that corridor: the representation-independent
function-complexity measures that the Res(⊕)/communication toolbox lower-bounds are **not sound** —
they are superpolynomial on a language that is already in `P`.

Concretely, `dIndexLang ∈ P` (`dIndexInP`), yet its Nečiporuk subfunction profile is not
polynomially bounded (`subfunProfile_dIndex_not_polyBounded`).  So:

* `repIndep_complexity_superpoly_on_P` — there is a P-language whose representation-independent
  complexity is superpolynomial.
* `no_sound_observer_dominates_subfun` — no *sound* observer invariant can dominate that
  representation-independent complexity: on a poly-time decider of `dIndexLang` soundness forces it
  bounded, while domination forces it superpolynomial.  Hence the function-complexity technique, on
  its own, cannot be a sound observer invariant — it would certify the *easy* language `dIndexLang`
  as hard.

## The corridor

* **Upper wall (this file):** representation-independent function-complexity (subfunction /
  communication / `Res(⊕)` rank) is superpolynomial on some P-languages, so it is not sound.
* **Lower wall (earlier):** space-bounded measures (`traceRank ≤ rowMax`) are too weak — SAT is
  space-cheap, so they need not grow on SAT.
* **The target** must therefore be size-dominated (sound, unlike subfunction measures) *and* grow on
  SAT (hard, unlike space measures) — strictly between space and time.  And size-dominated + hard
  `⟺` the separation (`sizeDominated_hard_iff_sep`).  So threading the corridor is exactly the open
  problem; this file pins the upper wall and explains why the `Res(⊕)`/function-complexity programme
  does not cover all observers.

Nothing here proves a separation or that any invariant is hard.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverInvariantCorridor

open PallLean.Paper93.DeepMath.PathB.ComposableMachine (Machine Decides InP)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.LangRankKill
  (subfunProfile dIndexLang subfunProfile_dIndex_not_polyBounded)
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (dIndexInP)
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge (polyBounded_of_le)

/-- A representation-independent complexity measure superpolynomial on a *P-language*: `dIndexLang`
is in `P`, yet its subfunction profile is not polynomially bounded. -/
theorem repIndep_complexity_superpoly_on_P :
    ∃ L : List Bool → Bool, InP L ∧ ¬ PolyBounded (subfunProfile L) :=
  ⟨dIndexLang, dIndexInP, subfunProfile_dIndex_not_polyBounded⟩

/-- An observer invariant is *sound* if it stays polynomially bounded on every poly-time decider of
every language — the cash-out property any P-vs-NP invariant must have. -/
def ObserverSound (Inv : Machine → ℕ → ℕ) : Prop :=
  ∀ (L : List Bool → Bool) (M : Machine) (T : ℕ → ℕ),
    PolyBounded T → Decides M L T → PolyBounded (Inv M)

/-- **The corridor's upper wall.**  No sound observer invariant can dominate the
representation-independent subfunction complexity: soundness on a poly-time decider of
`dIndexLang ∈ P` forces it polynomially bounded, but domination forces it superpolynomial.  So the
function-complexity technique cannot itself be a sound observer invariant — it would certify the
easy language `dIndexLang` as hard. -/
theorem no_sound_observer_dominates_subfun
    (Inv : Machine → ℕ → ℕ) (hsound : ObserverSound Inv) :
    ¬ (∀ (M : Machine) (T : ℕ → ℕ), Decides M dIndexLang T →
        ∀ n, subfunProfile dIndexLang n ≤ Inv M n) := by
  intro hdom
  obtain ⟨M, T, hT, hdec⟩ := (dIndexInP : InP dIndexLang)
  exact subfunProfile_dIndex_not_polyBounded
    (polyBounded_of_le (hdom M T hdec) (hsound dIndexLang M T hT hdec))

#print axioms repIndep_complexity_superpoly_on_P
#print axioms no_sound_observer_dominates_subfun

end PallLean.Paper93.DeepMath.PathB.ObserverInvariantCorridor
