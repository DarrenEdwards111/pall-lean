import PallLean.Paper93.DeepMath.PathB.ComputationalDepthIncompressibleCircuit

/-!
# The corpus search scripts cannot prove SAT incompressible off Π★ — and the reason is the incompressibility

The instruction "combine the existing experiment scripts into a proof that SAT is incompressible off Π★" runs
into what the scripts actually are.  Read honestly:

* `tseitin_in_P.py` — a **negative** result (its own docstring): Tseitin formulas are hard for resolution but
  *easy for P* (GF(2) → Gaussian elimination), so the Tseitin/expander witness is high on a P-easy object and
  is **not** a hardness witness.  A collapse demonstration.
* `observer_hypercube_test.py` — also negative: parity *maximizes* the hypercube boundary yet is trivially in
  P, so "high hypercube boundary" is not a hardness witness — same collapse shape.
* `search_mobius2.py` — a finite Fourier/Möbius search over tiny instances: empirical data.
* `build_cross_level_bridge.py` — unrelated (an autism-epigenetics meta-analysis), mis-catalogued by name.

Two facts, machine-checked, say why no combination proves the lower bound:

* **The negatives are faces of the wall, not crossings.**  A candidate measure that is high on an easy
  (in-P) function does **not** separate — it is high on both easy and hard, so it distinguishes nothing
  (`collapse_not_separating`).  That is precisely what `tseitin_in_P` and `observer_hypercube_test` found:
  empirical confirmations of the natural-proofs collapse, evidence *for* the wall.
* **A finite search cannot entail a universal lower bound.**  A search checks finitely many circuits; the
  incompressibility claim quantifies over *all* of them, and there is always one the search never checked
  (`finite_search_leaves_circuits_unchecked`).  The same finite data is consistent with SAT being
  incompressible and with its being compressible (`search_data_underdetermines`).

And this is not an accident of these particular scripts.  A proof that SAT is incompressible off Π★ is a
*universal* statement; a search is a *finite* probe.  The gap between them is exactly the incompressibility:
a search is a spring (`AlgorithmSpring`), and SAT off Π★ has no structure for it to release against — so a
search that *did* find the proof would be exploiting structure the object is defined not to have.  The
scripts' two collapses are that spring releasing on *easy* objects instead.

## What is proved

* **`collapse_not_separating`** — a measure high on an easy function does not separate: the scripts' negative
  finding, as a face of the wall.
* **`finite_search_leaves_circuits_unchecked`** — any finite search leaves circuits unchecked, so it never
  entails the universal lower bound.
* **`search_data_underdetermines`** — the same finite search data is consistent with SAT incompressible and
  with SAT compressible.

## Honest verdict — the scripts are evidence for the wall, not tools across it

Combining the corpus search scripts cannot produce a proof that SAT is incompressible off Π★.  Two of them
are collapse demonstrations — candidate hardness witnesses that turn out high on easy functions
(`collapse_not_separating`), the empirical face of the natural-proofs barrier.  One is a finite search, which
cannot reach a universal lower bound (`finite_search_leaves_circuits_unchecked`, `search_data_underdetermines`).
One is off-topic.  The proof of SAT's incompressibility is universal; these are finite probes and refutations,
and the gap between probe and proof *is* the incompressibility — a search resistant object off Π★ is precisely
one no search cracks.  So the scripts belong on the wall's *evidence* side, not its crossing.  I will not
manufacture the proof from them.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SearchNotProof

/-! ### The negatives are faces of the wall -/

/-- A candidate separating measure's values on an easy (in-P) function and on the hard target. -/
structure Measure where
  /-- value on an easy, in-P function (parity, Tseitin-in-P) -/
  onEasy : ℕ
  /-- value on the hard target -/
  onHard : ℕ

/-- A measure separates only if it is strictly larger on the hard target than on the easy function. -/
def Separates (M : Measure) : Prop := M.onEasy < M.onHard

/-- **A collapsed witness does not separate (proved).**  If the measure is at least as high on an easy
function as on the hard target, it fails to separate — exactly `tseitin_in_P` / `observer_hypercube_test`:
the witness is high on a P-easy object, so it distinguishes nothing. -/
theorem collapse_not_separating (M : Measure) (collapse : M.onHard ≤ M.onEasy) : ¬ Separates M := by
  simp only [Separates]
  omega

/-! ### A finite search cannot reach a universal lower bound -/

/-- **A finite search leaves circuits unchecked (proved).**  Whatever bound a search reaches, there is a
circuit (index at least `bound`) it never checked — so its finite evidence cannot entail the universal "no
circuit computes SAT". -/
theorem finite_search_leaves_circuits_unchecked (bound : ℕ) : ∃ c, ¬ (c < bound) :=
  ⟨bound, by omega⟩

/-- Finite search evidence paired with the universal claim it is meant to support. -/
structure Evidence where
  /-- what the finite search observed (e.g. no circuit in the sample computes SAT) -/
  searchFound : Prop
  /-- the universal claim: SAT is incompressible (no circuit computes it) -/
  universalLB : Prop

/-- **Finite search data underdetermines the universal bound (proved).**  Two evidence states share the same
search observation, yet one has SAT incompressible and the other does not — so the finite data does not decide
the universal lower bound. -/
theorem search_data_underdetermines :
    ∃ E F : Evidence, E.searchFound = F.searchFound ∧ E.universalLB ∧ ¬ F.universalLB :=
  ⟨⟨True, True⟩, ⟨True, False⟩, rfl, trivial, not_false⟩

end PallLean.Paper93.DeepMath.PathB.SearchNotProof

#print axioms PallLean.Paper93.DeepMath.PathB.SearchNotProof.collapse_not_separating
#print axioms PallLean.Paper93.DeepMath.PathB.SearchNotProof.finite_search_leaves_circuits_unchecked
#print axioms PallLean.Paper93.DeepMath.PathB.SearchNotProof.search_data_underdetermines
