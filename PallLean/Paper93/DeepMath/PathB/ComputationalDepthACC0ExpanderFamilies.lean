import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ExpanderCountObstruction

/-!
# Special expander families — instantiating `ExpanderIncidence`, and an honest test of the socket

Entry 254 socketed the general count lower bound (`ExpanderCountObstruction`, Smolensky-strength) and proved the
DP-restricted bound.  This file does the next step: **instantiate `ExpanderIncidence` for concrete families** and
probe the socket on them.  Two genuine results, and one honest refinement:

* **High pairwise gate-intersection ⇒ `ExpanderIncidence` (PROVED).**  If every two distinct gates share `≥ d`
  variables, then *every* separator has size `≥ d` (a separator must contain the cross-part intersection).  So dense
  pairwise-intersecting families are separator-expanders.
* **The full-support family is maximally expander (PROVED).**  If every gate depends on all `n` variables, every
  separator has size `≥ n` — there is *no* small separator at all.
* **Honest refinement — separator-expansion is necessary for DP-failure but NOT sufficient for count-hardness.**  The
  full-support family is a separator-expander (`fullSupport_expander`), yet its mod-`q` fire-count is plausibly
  *easy*: when all gates share the same support, the fire-count is a simple symmetric function of one shared
  sub-computation, with no genuine cross-field mixing.  So `ExpanderIncidence` *alone* does **not** imply the count
  obstruction.  This sharpens the bridge: the candidate invariant (separator-width / treewidth) governs **DP**
  tractability exactly, but the genuine **count** lower bound needs *more* than no-small-separator — it needs the
  algebraic / polynomial-method hardness, which is exactly what the entry-254 socket captures and what Smolensky
  supplies.

⚠️ **No crossing.**  The `ExpanderIncidence` instantiations are proved; the general count obstruction stays the
entry-254 socket.  The refinement (separator-expansion ⊉ count-hardness) is an *honest negative*: it shows the socket
genuinely needs the algebraic content, not just the cut structure.

## What is proved (clean axioms, no `sorry`)

* **`expander_of_pairwise_inter`** (PROVED) — `(∀ g g', g ≠ g' → d ≤ #(supp g ∩ supp g')) → ExpanderIncidence supp d`:
  high pairwise intersection ⇒ every separator `≥ d` (the separator contains the cross-part intersection).
* **`fullSupport_expander`** (PROVED) — the all-variables family `fun _ => univ` satisfies
  `ExpanderIncidence (fun _ => univ) (Fintype.card V)`: no separator smaller than the whole variable set.

## The honest refinement (named)

`fullSupport_expander` is a separator-expander whose count is plausibly tractable (shared support ⇒ no cross-field
mixing).  Hence: **`ExpanderIncidence` is necessary for separator-DP failure but not sufficient for the count lower
bound.**  The right hypothesis for `ExpanderCountObstruction` is a *combinatorial+algebraic* expansion (overlapping
supports of *distinct, non-redundant* gates), not mere no-small-separator.  Isolating that exact hypothesis — and the
lower bound under it — is the open Smolensky-strength core (entry-254 socket / entry-238 `CarryRefinementCrossing`).

## Honest scope

This proves `ExpanderIncidence` for concrete families (high pairwise intersection; full support) and surfaces the honest
negative that separator-expansion alone is not count-hardness.  It does **not** prove the count lower bound on any
family (that is the socket).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0ExpanderFamilies

open PallLean.Paper93.DeepMath.PathB.ACC0ExpanderCountObstruction

variable {V Gate : Type} [Fintype Gate] [DecidableEq Gate] [DecidableEq V]

/-- **High pairwise gate-intersection ⇒ `ExpanderIncidence` (PROVED).**  If every two distinct gates share `≥ d`
variables, then every separator has size `≥ d`: a separator `S` with parts `A`, `B` contains `supp ga ∩ supp gb` for
`ga ∈ A`, `gb ∈ B` (distinct, since `A`, `B` are disjoint), which has size `≥ d`. -/
theorem expander_of_pairwise_inter (supp : Gate → Finset V) (d : ℕ)
    (hpair : ∀ g g', g ≠ g' → d ≤ (supp g ∩ supp g').card) :
    ExpanderIncidence supp d := by
  intro S hsep
  obtain ⟨A, B, _, hdisj, hA, hB, hcross⟩ := hsep
  obtain ⟨ga, hga⟩ := hA
  obtain ⟨gb, hgb⟩ := hB
  have hne : ga ≠ gb := fun h => Finset.disjoint_left.mp hdisj hga (h ▸ hgb)
  calc d ≤ (supp ga ∩ supp gb).card := hpair ga gb hne
    _ ≤ S.card := Finset.card_le_card (hcross ga hga gb hgb)

/-- **The full-support family is maximally expander (PROVED).**  If every gate depends on all `n` variables
(`supp = fun _ => univ`), every separator has size `≥ n = Fintype.card V`: there is no small separator.  Yet (honest
refinement) its mod-`q` fire-count is plausibly tractable — shared support means no genuine cross-field mixing — so
`ExpanderIncidence` alone is not count-hardness. -/
theorem fullSupport_expander [Fintype V] :
    ExpanderIncidence (fun _ : Gate => (Finset.univ : Finset V)) (Fintype.card V) := by
  apply expander_of_pairwise_inter
  intro g g' _
  simp [Finset.card_univ]

/-!
**The honest refinement (named).**  `fullSupport_expander` is a separator-expander whose count is plausibly easy
(shared support ⇒ no cross-field mixing).  So `ExpanderIncidence` is necessary for separator-DP failure but **not
sufficient** for the count lower bound.  The right hypothesis for `ExpanderCountObstruction` is combinatorial+algebraic
expansion of *distinct, non-redundant* gates, not mere no-small-separator; isolating it and proving the bound under it
is the open Smolensky-strength core (entry-254 socket).
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ExpanderFamilies

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExpanderFamilies.expander_of_pairwise_inter
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExpanderFamilies.fullSupport_expander
