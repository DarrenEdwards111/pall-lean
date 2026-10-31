import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverLowerBoundSchema

/-!
# The ACC⁰ frontier: the conditional separation theorem (the exact God-Move target)

`SCOPE_ACC0_OBSERVER_FRONTIER.md` lays out why ACC⁰ is harder than AC⁰[p] (mixed moduli defeat the
single-field low-degree boundary) and what an *enriched-modular observer boundary* would have to do.  This
file states the **exact conditional theorem** that frontier reduces to — the observer schema (§9–11)
specialised to ACC⁰ — with the two genuinely open ingredients as **explicit named hypotheses** (the demotion
pattern: no custom axiom, nothing claimed proved that is not).

> **If** every ACC⁰ circuit has *low* enriched-modular observer boundary (`hbridge`), **and** some NP
> language *forces high* such boundary under every circuit computing it (`hforced`), **then** that language
> is not computed by small ACC⁰ circuits — i.e. `NP ⊄ ACC⁰`.

The implication is the schema; the content is the two hypotheses, **both open**.  `hforced` quantifies over
*every* circuit computing `L` — the all-decompositions content the gap (`equality_decomposition_gap`) shows
cannot come cheaply.  Nothing here asserts either hypothesis.

## What is proved (clean axioms, no `sorry`)

* `acc0_separation_of_boundary` — the conditional separation: `hbridge + hforced + the gap ⇒ every small ACC⁰
  circuit errs on `L``.
* `not_acc0_of_boundary` — the `L ∉ ACC⁰(sizeBound)` packaging.

These are *theorems about the implication*; the hypotheses are the open research targets isolated by the
scope note (the enriched-modular boundary model, and a hard NP language for it).
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverACC0

open PallLean.Paper93.DeepMath.PathB

/-- An abstract ACC⁰ setting: a circuit class with evaluation, size, an `IsACC0` membership predicate, and an
**enriched-modular observer boundary** `boundary` (the measure the scope note calls for — left abstract here;
its concrete definition over mixed moduli is the open modelling target). -/
structure ACC0Setting (Input : Type*) where
  /-- The circuit type. -/
  Circuit : Type
  /-- Evaluation. -/
  computes : Circuit → Input → Bool
  /-- Circuit size. -/
  size : Circuit → ℕ
  /-- Membership in the ACC⁰ class (depth/`MOD`-gate/size constraints). -/
  IsACC0 : Circuit → Prop
  /-- The enriched-modular observer boundary of a circuit. -/
  boundary : Circuit → ℕ

variable {Input : Type*}

/-- **The ACC⁰ conditional separation (the schema, specialised).**  Given:

* `hmono` — the bridge `g` is monotone;
* `hbridge` — *every* ACC⁰ circuit has boundary `≤ g(size)` (ACC⁰ ⇒ low enriched-modular boundary);
* `hforced` — *every* circuit computing `L` has boundary `≥ lb` (`L` forces high boundary);
* `hsep` — the gap `g(sizeBound) < lb`;

then every ACC⁰ circuit of size `≤ sizeBound` **errs** on `L`.  (Pure schema: `lb ≤ boundary ≤ g(size) ≤
g(sizeBound) < lb`.) -/
theorem acc0_separation_of_boundary (S : ACC0Setting Input) (L : Input → Bool)
    (g : ℕ → ℕ) (hmono : Monotone g)
    (hbridge : ∀ C, S.IsACC0 C → S.boundary C ≤ g (S.size C))
    {sizeBound lb : ℕ}
    (hforced : ∀ C, (∀ x, S.computes C x = L x) → lb ≤ S.boundary C)
    (hsep : g sizeBound < lb) :
    ∀ C, S.IsACC0 C → S.size C ≤ sizeBound → ∃ x, S.computes C x ≠ L x := by
  intro C hacc hsize
  by_contra hcon
  push_neg at hcon
  have hchain : lb ≤ g sizeBound :=
    le_trans (hforced C hcon) (le_trans (hbridge C hacc) (hmono hsize))
  exact absurd hchain (Nat.not_le.mpr hsep)

/-- **`NP ⊄ ACC⁰` packaging.**  Under the same hypotheses, there is **no** ACC⁰ circuit of size `≤ sizeBound`
computing `L`: a hard-boundary NP language escapes small ACC⁰.  (`L` is `NP` in the intended instantiation;
that hypothesis is not needed for the implication and is supplied by the model.) -/
theorem not_acc0_of_boundary (S : ACC0Setting Input) (L : Input → Bool)
    (g : ℕ → ℕ) (hmono : Monotone g)
    (hbridge : ∀ C, S.IsACC0 C → S.boundary C ≤ g (S.size C))
    {sizeBound lb : ℕ}
    (hforced : ∀ C, (∀ x, S.computes C x = L x) → lb ≤ S.boundary C)
    (hsep : g sizeBound < lb) :
    ¬ ∃ C, S.IsACC0 C ∧ S.size C ≤ sizeBound ∧ (∀ x, S.computes C x = L x) := by
  rintro ⟨C, hacc, hsize, hcomp⟩
  obtain ⟨x, hx⟩ := acc0_separation_of_boundary S L g hmono hbridge hforced hsep C hacc hsize
  exact hx (hcomp x)

end PallLean.Paper93.DeepMath.PathB.ObserverACC0

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverACC0.acc0_separation_of_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverACC0.not_acc0_of_boundary
