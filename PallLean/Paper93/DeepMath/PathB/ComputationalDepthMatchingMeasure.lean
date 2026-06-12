import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPHPProofSpaceForcing

/-!
# The matching-based measure for graph-PHP (constructed; subadditivity + unsatisfiability proved)

The residual after `ComputationalDepthGraphPHPExpansion.lean` was the **matching-based measure**: the BSW
semantics where assignments are *partial matchings* (each hole holds at most one pigeon), so that a
counterexample places only the relevant pigeons and the unique-neighbour flip applies.  This file **builds
that measure** and proves its two load-bearing properties.

## The construction

* `Matching m n` — partial matchings: assignments `a : (pigeon × hole) → Bool` that are **hole-injective**
  (`IsMatching`: each hole holds at most one pigeon).
* The measure is the generic `SemanticMeasure.measure` instantiated at `α = Matching m n`, with `mSat`
  (literal satisfaction) and `mConstr p` ("pigeon `p` is placed").

## Proved (clean axioms, no `sorry`)

* `m_hcons` — literal-consistency over matchings.
* `m_hunsat` — **unsatisfiability**: if `n < m`, *every* matching leaves a pigeon unplaced (a placed-everywhere
  matching gives an injection `pigeons ↪ holes`, so `m ≤ n`, contradiction).  This is the genuine pigeonhole
  fact, now over the matching semantics.
* `matchingMeasure_resolvent_le` — **subadditivity**: `μ(resolvent) ≤ μ(C) + μ(D)`, obtained *for free* from
  the generic `SemanticMeasure.measure_resolvent_le` (resolution soundness) at `α = Matching m n`.

So the matching-based measure is a real object with the two properties the BSW band argument needs from a
measure (subadditivity, and a globally-unsatisfiable family).

## What remains (named, not faked)

Two expansion-dependent inputs complete the graph-PHP width lower bound on top of this measure:

* **root bound** `μ(⊥) ≥ t` — every set of `< t` pigeons is matchable (Hall / bipartite expansion);
* **flip / width link** — assembled from the three proved cores
  (`ComputationalDepthGraphPHPExpansion.lean`: `pigeonhole_unplaced`, `php_flip_mem_clause`,
  `free_hole_of_unique_neighbor`) *over this matching measure* — the counterexample is now a matching placing
  only `S\{p}`, so a unique-neighbour hole is free (core 3) and the single-variable flip (core 2) pins the
  clause variable.

Both are the bipartite-expansion content of Ben-Sasson–Wigderson graph-PHP — named here, their combinatorial
hearts proved in the companion file.  The measure itself — the piece this file was asked to build — is now
constructed with subadditivity and unsatisfiability proved.
-/

namespace PallLean.Paper93.DeepMath.PathB.PHPProofSpace

open PallLean.Paper93.DeepMath.PathB
open scoped BigOperators

/-- **Hole-injective**: each hole holds at most one pigeon. -/
def IsMatching {m n : ℕ} (a : Fin m × Fin n → Bool) : Prop :=
  ∀ (h : Fin n) (p p' : Fin m), a (p, h) = true → a (p', h) = true → p = p'

/-- A **partial matching** of pigeons into holes. -/
abbrev Matching (m n : ℕ) := {a : Fin m × Fin n → Bool // IsMatching a}

/-- Literal satisfaction over a matching. -/
def mSat {m n : ℕ} (a : Matching m n) (l : PHPLit m n) : Prop := a.val l.1 = l.2

/-- The pigeon constraint: pigeon `p` is placed in some hole. -/
def mConstr {m n : ℕ} (p : Fin m) (a : Matching m n) : Prop := ∃ h, a.val (p, h) = true

/-- **Literal-consistency (proved).** -/
theorem m_hcons {m n : ℕ} (a : Matching m n) (l : PHPLit m n) :
    mSat a l → ¬ mSat a (phpCompl l) := by
  simp only [mSat, phpCompl]
  intro h
  rw [h]
  exact fun hc => by cases hl : l.2 <;> rw [hl] at hc <;> simp at hc

/-- **Unsatisfiability (proved).**  If `n < m`, every matching leaves a pigeon unplaced. -/
theorem m_hunsat {m n : ℕ} (hmn : n < m) (a : Matching m n) : ∃ p, ¬ mConstr p a := by
  by_contra hall
  push_neg at hall
  choose place hplace using hall
  have hinj : Function.Injective place := by
    intro p p' hpp'
    exact a.property (place p) p p' (hplace p) (by rw [hpp']; exact hplace p')
  have hcard := Fintype.card_le_of_injective place hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- **The matching-based measure** (the generic semantic measure at `α = Matching m n`). -/
noncomputable def matchingMeasure {m n : ℕ} (C : ResolutionClause (PHPLit m n)) : ℕ :=
  SemanticMeasure.measure mSat mConstr C

/-- **Subadditivity (proved, free from the generic engine).**  `μ(resolvent C D p) ≤ μ(C) + μ(D)`. -/
theorem matchingMeasure_resolvent_le {m n : ℕ} (hmn : n < m)
    (C D : ResolutionClause (PHPLit m n)) (p : PHPLit m n) :
    matchingMeasure (ResolutionClause.resolvent phpCompl C D p)
      ≤ matchingMeasure C + matchingMeasure D :=
  SemanticMeasure.measure_resolvent_le mSat mConstr phpCompl m_hcons (m_hunsat hmn) C D p

end PallLean.Paper93.DeepMath.PathB.PHPProofSpace

#print axioms PallLean.Paper93.DeepMath.PathB.PHPProofSpace.m_hunsat
#print axioms PallLean.Paper93.DeepMath.PathB.PHPProofSpace.matchingMeasure_resolvent_le
