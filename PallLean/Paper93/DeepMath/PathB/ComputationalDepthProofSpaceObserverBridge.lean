import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResLinLiftedTseitinInterface
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSeparationTarget

/-!
# The proof-space → observer bridge is the separation

This file wires the two tracks together and machine-checks the claim from the audit: the bridge that
would let a `Res(⊕)` size lower bound imply `SAT ∉ P` is not a lemma *below* P vs NP — given the
(open) lower bound, it is **equivalent** to `SAT ∉ P`.

## What the bridge is, honestly

The real bridge would say: a polynomial-time SAT observer, run on an unsatisfiable formula, yields a
short refutation of it in the lower-bounded system.  We do **not** construct that observer→proof map
— constructing it is precisely the false/hard step (a poly-time *certifying* refuter would give the
hard family short proofs, contradicting the lower bound whenever `SAT ∈ P`).  We formalize only its
logical content:

`ProofSpaceBridge F sizeFloor := InP SATLang → ∃ m P, P.size < sizeFloor m`

i.e. "if SAT ∈ P then the hard family has a short refutation."  `InP`/`SATLang`/`SAT_not_in_P` are
the actual observer-track definitions from `SeparationTarget`; `FamilyRefutation`/`sizeFloor` are the
actual `Res(⊕)` proof-track objects.

## The result

* `proofSpaceBridge_eq` — unconditionally, the bridge says exactly "SAT ∈ P forces the unrestricted
  lower bound to fail."
* `bridge_iff_separation` — given the (open) unrestricted lower bound `lb`, the bridge holds **iff**
  `SAT_not_in_P`.  So it is the destination, not a stepping stone: building it is proving P ≠ NP.

Note the bridge is downstream of two open statements — `lb` (the unrestricted `Res(⊕)` bound, open)
and `SAT_not_in_P` (the separation, open) — and is provably equal to the second.  Nothing here
proves either.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This file proves no separation and no lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.ProofSpaceObserverBridge

open PallLean.Paper93.DeepMath.PathB.SeparationTarget (InP SATLang SAT_not_in_P)
open PallLean.Paper93.DeepMath.PathB.ResLinParity

/-- The proof-space→observer bridge, as logical content only: a poly-time SAT decider yields a short
refutation of the hard family.  The observer→proof construction is deliberately *not* supplied — it
is the hard/false step. -/
def ProofSpaceBridge (F : LiftedTseitinFamily) (sizeFloor : ℕ → ℕ) : Prop :=
  InP SATLang → ∃ (m : ℕ) (P : FamilyRefutation F m), P.size < sizeFloor m

/-- Unconditionally, the bridge is exactly "SAT ∈ P forces the unrestricted lower bound to fail." -/
theorem proofSpaceBridge_eq (F : LiftedTseitinFamily) (sizeFloor : ℕ → ℕ) :
    ProofSpaceBridge F sizeFloor ↔
      (InP SATLang → ¬ HasUnrestrictedSizeLowerBound F sizeFloor) := by
  constructor
  · intro h hInP hlb
    obtain ⟨m, P, hP⟩ := h hInP
    have := hlb m P
    omega
  · intro h hInP
    have hne := h hInP
    unfold HasUnrestrictedSizeLowerBound at hne
    push_neg at hne
    exact hne

/-- **The bridge is the separation.**  Given the (open) unrestricted `Res(⊕)` lower bound, the
proof-space→observer bridge holds iff `SAT ∉ P`.  Building the bridge is therefore proving P ≠ NP —
it is the destination, not a step below it. -/
theorem bridge_iff_separation {F : LiftedTseitinFamily} {sizeFloor : ℕ → ℕ}
    (lb : HasUnrestrictedSizeLowerBound F sizeFloor) :
    ProofSpaceBridge F sizeFloor ↔ SAT_not_in_P := by
  unfold ProofSpaceBridge SAT_not_in_P
  constructor
  · intro hb hInP
    obtain ⟨m, P, hP⟩ := hb hInP
    have := lb m P
    omega
  · intro hsep hInP
    exact absurd hInP hsep

#print axioms proofSpaceBridge_eq
#print axioms bridge_iff_separation

end PallLean.Paper93.DeepMath.PathB.ProofSpaceObserverBridge
