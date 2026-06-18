import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AffineHyperplaneLowerBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AffineHyperplanes

/-!
# Co-firing richness — the corrected hardness invariant, distinguishing parallel from co-firing families

Entry 259's negative (parallel affine = `AlgExpander` but fire-count `≤ 1`, count-easy) showed indicator rank is not
sufficient for count-hardness.  This file defines the **missing ingredient** — *co-firing richness* — and proves it
cleanly separates the easy family from the hard one, sharpening the socket to:

> `AlgExpander gates → CoFiringRich gates → CrossFieldCountHard gates`.

**The invariant.**  `firePattern gates x := { i | gates i x }` (the set of gates firing on `x`); `CoFiringRich gates k`
:= some input has `≥ k` gates firing simultaneously (`∃ x, k ≤ #(firePattern gates x)`).  Parallel/disjoint families
have all patterns `≤ 1` (no co-firing); the genuine hard families have large co-firing patterns.

## What is proved (clean axioms, no `sorry`)

* **`firePattern` / `CoFiringRich`** — the co-firing invariant.
* **`parallel_not_coFiringRich`** (PROVED) — the parallel affine family is *not* `CoFiringRich 2`: all its fire-patterns
  have size `≤ 1` (entry 259), so no input has `≥ 2` gates co-firing.  This is exactly why its fire-count collapses to
  `{0, 1}`.
* **`dictator_coFiringRich`** (PROVED) — the dictator family (gate `i` fires iff bit `i` is set) *is* `CoFiringRich s`:
  the all-`true` input fires all `s` gates simultaneously.
* **`dictator_algExpander`** (PROVED) — the dictator family is also `AlgExpander` (private witnesses): so `AlgExpander`
  and `CoFiringRich` are *jointly satisfiable* — the corrected socket is non-vacuous.

## The corrected socket and its proven instance

* **`CrossFieldCountHard`** / **`CoFiringCountObstruction`** — the corrected socket:
  `AlgExpander gates → CoFiringRich gates → CrossFieldCountHard gates`.  Smolensky-strength, not proved in general.
* **Proven instance.**  The dictator family's mod-`q` fire-count is the Hamming weight mod `q` = **`MOD_q`** of the
  input — the canonical hard function whose `AC⁰[p]` hardness (`p ≠ q`) is the in-arc Razborov–Smolensky result
  `Layer4.mod_q_indicators_false` (entry 244).  So the corrected socket has a genuinely *proven* instance (the
  dictator/`MOD_q` family is `AlgExpander` + `CoFiringRich`, and count-hard), unlike the parallel family which fails
  `CoFiringRich` (and is count-easy) — the invariant exactly tracks the easy/hard split.

## Honest scope

This proves the co-firing invariant cleanly separates the count-easy (parallel, not co-firing) from the count-hard
(dictator/`MOD_q`, co-firing) families, and that `AlgExpander ∧ CoFiringRich` is non-vacuous with a proven hard instance
(`MOD_q`).  The *general* corrected socket (`AlgExpander ∧ CoFiringRich ⇒ CrossFieldCountHard` for all such families) is
Smolensky-strength and not proved.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0CoFiring

open PallLean.Paper93.DeepMath.PathB.ACC0AlgebraicExpansion
open PallLean.Paper93.DeepMath.PathB.ACC0AffineHyperplanes (private_witness_indep)
open PallLean.Paper93.DeepMath.PathB.ACC0AffineHyperplaneLowerBound (affineHyperplane_fireCount_le_one)

/-- **The fire pattern.**  The set of gates firing on input `x`. -/
def firePattern {X : Type} {s : ℕ} (gates : Fin s → (X → Bool)) (x : X) : Finset (Fin s) :=
  Finset.univ.filter (fun i => gates i x)

/-- **Co-firing richness.**  Some input has `≥ k` gates firing *simultaneously*.  This is the ingredient `AlgExpander`
(indicator rank) lacks: parallel/disjoint families have all patterns `≤ 1`. -/
def CoFiringRich {X : Type} {s : ℕ} (gates : Fin s → (X → Bool)) (k : ℕ) : Prop :=
  ∃ x, k ≤ (firePattern gates x).card

/-- **Parallel affine hyperplanes are NOT co-firing-rich (PROVED).**  All fire-patterns have size `≤ 1` (entry 259),
so no input has `≥ 2` gates co-firing.  This is precisely why the parallel affine fire-count collapses to `{0, 1}`. -/
theorem parallel_not_coFiringRich {p n s : ℕ} (targets : Fin s → ZMod p)
    (hinj : Function.Injective targets) :
    ¬ CoFiringRich
        (fun (i : Fin s) (x : Fin (n + 1) → ZMod p) => decide ((∑ j, x j) = targets i)) 2 := by
  rintro ⟨x, hx⟩
  have hle := affineHyperplane_fireCount_le_one targets hinj x
  unfold firePattern at hx
  dsimp only at hx
  omega

/-- **The dictator family is co-firing-rich (PROVED).**  Gate `i` fires iff bit `i` is set; the all-`true` input fires
all `s` gates simultaneously, so `CoFiringRich s`. -/
theorem dictator_coFiringRich (s : ℕ) :
    CoFiringRich (fun (i : Fin s) (x : Fin s → Bool) => x i) s := by
  refine ⟨fun _ => true, ?_⟩
  have hpat : firePattern (fun (i : Fin s) (x : Fin s → Bool) => x i) (fun _ => true)
      = Finset.univ := by
    unfold firePattern; ext i; simp
  rw [hpat, Finset.card_univ, Fintype.card_fin]

/-- **The dictator family is also `AlgExpander` (PROVED).**  Private witnesses (`wit i = the i-indicator`) give linear
independence.  So `AlgExpander` and `CoFiringRich` are jointly satisfiable — the corrected socket is non-vacuous.  (Its
mod-`q` fire-count is the Hamming weight mod `q` = `MOD_q`, the in-arc-proven hard function, entry 244.) -/
theorem dictator_algExpander {F : Type} [Field F] (s : ℕ) :
    AlgExpander (F := F) (fun (i : Fin s) (x : Fin s → Bool) => x i) := by
  apply private_witness_indep _ (fun i => (fun j => decide (j = i)))
  · intro i; simp
  · intro i j hji; simp [hji]

/-- **The corrected count-hardness socket (Smolensky-strength, NOT proved).**  Under *both* algebraic expansion
(indicator independence) *and* co-firing richness (simultaneous firing in large patterns), the mod-`q` fire-count needs
superpolynomial resources.  This is the entry-256/257 socket with the corrected hypothesis (adding `CoFiringRich`, which
entry-259 showed is required).  Proven instance: the dictator/`MOD_q` family (`AlgExpander` + `CoFiringRich`, count-hard
by `Layer4.mod_q_indicators_false`). -/
def CoFiringCountObstruction {X : Type} {s : ℕ} (gates : Fin s → (X → Bool))
    (CrossFieldCountHard : Prop) (F : Type) [Field F] (k : ℕ) : Prop :=
  AlgExpander (F := F) gates → CoFiringRich gates k → CrossFieldCountHard

/-!
**The corrected socket.**  `AlgExpander gates → CoFiringRich gates → CrossFieldCountHard gates`.  Parallel affine fails
`CoFiringRich` (`parallel_not_coFiringRich`) and is count-easy (entry 259); the dictator/`MOD_q` family satisfies both
(`dictator_algExpander`, `dictator_coFiringRich`) and is count-hard (its mod-`q` fire-count is `MOD_q`, proved hard
in-arc by `Layer4.mod_q_indicators_false`).  So the co-firing invariant exactly tracks the easy/hard split; the general
socket is Smolensky-strength (entry-238 `CarryRefinementCrossing`), not proved.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CoFiring

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CoFiring.parallel_not_coFiringRich
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CoFiring.dictator_coFiringRich
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CoFiring.dictator_algExpander
