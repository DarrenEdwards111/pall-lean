import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHardExists

/-!
# The easy-witness search core: a smallness test makes hardness *constructive*

`HardExists` showed hard functions *exist* by counting; the open content of the IKW easy-witness step
is **constructivity** — producing an *explicit* hard function.  This file builds the reduction
skeleton that closes that gap **given the one capability a derandomized `PIT` provides**: a correct
*smallness test* `test : BoolFun n → Bool` deciding whether a truth table has a small circuit (`test f
= true`) or is incompressible (`test f = false`).  With that test in hand, finding a hard function is a
**deterministic search** over the finite truth-table space.

* **`testSurvivors`** — the candidates the test flags as hard: `{f | test f = false}`.
* **`survivors_hard` (proved)** — if the test correctly decides hardness, every survivor is hard.
* **`search_succeeds` (proved)** — the survivor set is nonempty, because a hard function exists by
  counting (`HardExists.exists_hard_function`) and the test flags it.
* **`easy_witness_search` (proved)** — therefore a correct smallness test *constructively* yields a
  hard function: the deterministic search over all truth tables returns a survivor, and it is hard.

**Honest scope.**  The **search is fully proved** — that is the constructive step the easy-witness
method needs, and it is no longer a socket.  What remains socketed, and is named precisely, is the
**test itself**: a correct decision procedure for the hardness (small-circuit) predicate.  That test is
exactly the capability a derandomized `PIT` / an `MCSP`-style oracle supplies, and building it is the
deep `NEXP`-strength IKW content — **not** proved here (indeed, under cryptographic assumptions it is
*not* efficiently constructible, per `NaturalProofsBarrier`).  So constructivity of the hard function
reduces cleanly to the smallness test; nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.EasyWitnessSearch

open PallLean.Paper93.DeepMath.PathB.NaturalProofsBarrier
open PallLean.Paper93.DeepMath.PathB.RestrictedCashout
open PallLean.Paper93.DeepMath.PathB.HardExists

/-- The candidates a smallness test `test` flags as **hard** (incompressible): those with `test f =
false`.  The deterministic search ranges over this finite set. -/
def testSurvivors {n : ℕ} (test : BoolFun n → Bool) : Finset (BoolFun n) :=
  Finset.univ.filter (fun f => test f = false)

/-- **Every survivor is hard (proved).**  If the test correctly decides the hardness predicate
(`test f = false ↔ Hard cheap f`), then anything it flags as incompressible really is hard. -/
theorem survivors_hard {n N : ℕ} (cheap : Fin N → BoolFun n) (test : BoolFun n → Bool)
    (htest : ∀ f, test f = false ↔ Hard cheap f) :
    ∀ f ∈ testSurvivors test, Hard cheap f := by
  intro f hf
  rw [testSurvivors, Finset.mem_filter] at hf
  exact (htest f).mp hf.2

/-- **The search succeeds (proved).**  When the cheap class is small, a hard function exists by
counting, and a correct test flags it — so the survivor set is nonempty and the search finds something. -/
theorem search_succeeds {n N : ℕ} (cheap : Fin N → BoolFun n)
    (hN : 2 * N < Fintype.card (BoolFun n)) (test : BoolFun n → Bool)
    (htest : ∀ f, test f = false ↔ Hard cheap f) :
    (testSurvivors test).Nonempty := by
  obtain ⟨f, hf⟩ := exists_hard_function cheap hN
  refine ⟨f, ?_⟩
  rw [testSurvivors, Finset.mem_filter]
  exact ⟨Finset.mem_univ f, (htest f).mpr hf⟩

/-- **THE EASY-WITNESS SEARCH CORE (proved).**  A correct smallness test `test` *constructively*
yields a hard function: the deterministic search over the finite truth-table space returns a survivor,
and it is hard.  This discharges the constructive step of the easy-witness method; the remaining open
content is entirely the test (the derandomized-`PIT` / `MCSP`-style capability). -/
theorem easy_witness_search {n N : ℕ} (cheap : Fin N → BoolFun n)
    (hN : 2 * N < Fintype.card (BoolFun n)) (test : BoolFun n → Bool)
    (htest : ∀ f, test f = false ↔ Hard cheap f) :
    ∃ f : BoolFun n, test f = false ∧ Hard cheap f := by
  obtain ⟨f, hf⟩ := search_succeeds cheap hN test htest
  have hmem := hf
  rw [testSurvivors, Finset.mem_filter] at hmem
  exact ⟨f, hmem.2, survivors_hard cheap test htest f hf⟩

end PallLean.Paper93.DeepMath.PathB.EasyWitnessSearch

#print axioms PallLean.Paper93.DeepMath.PathB.EasyWitnessSearch.survivors_hard
#print axioms PallLean.Paper93.DeepMath.PathB.EasyWitnessSearch.search_succeeds
#print axioms PallLean.Paper93.DeepMath.PathB.EasyWitnessSearch.easy_witness_search
