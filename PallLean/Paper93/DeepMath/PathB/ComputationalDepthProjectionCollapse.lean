import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ThrSatMachine

/-!
# Why the projection collapses to brute force for general (P/poly) circuits

The cell-count projection compresses `ACC⁰`/`ACC⁰∘THR` because those circuits' values depend only on
the **Hamming weight per support** — so there are `≤ (n+1)^k` cells, and SAT is fast when `k` is small.
General (`P/poly`) circuits have no such structure: to be universal they must read **individual
input bits**, i.e. use singleton-support bottom gates.  This file proves, machine-checked, that in
that regime the projection gives **no speedup at all** — the number of cells is exactly `2^n`, the
brute-force count.

* **`singletonSupports`** — each gate reads one bit;
* **`weightVec_singleton`** — the cell coordinate of gate `j` is just the bit `x j`;
* **`weightVec_singleton_injective`** — so the cell *is* the input (the map is injective);
* **`singleton_cells_eq_two_pow` (proved)** — hence there are exactly `2^n` cells;
* **`singleton_cellSearch_no_speedup` (proved)** — so cell search runs in `2^n` steps: **no speedup.**

**This is the honest reason there is no P/poly projection to build.**  A projection is only a speedup
when the value factors through *few* weight statistics; a universal circuit reads all `n` bits, giving
`2^n` cells and zero gain.  And the deeper impossibility is already formalized elsewhere: a genuine
sub-`2^n` structural projection of *all* `P/poly` circuits would compress a **pseudorandom function**
(which lives in `P/poly`), distinguishing it from random and breaking cryptography — the Razborov–Rudich
natural-proofs barrier (`NaturalProofsBarrier.counting_property_not_constructive`).  So a P/poly
projection is not merely unbuilt; under standard assumptions it **cannot exist**.  Nothing here is
`P ≠ NP`; it is the concrete proof that the fuel the engine needs is not manufacturable.
-/

namespace PallLean.Paper93.DeepMath.PathB.ProjectionCollapse

open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0ThrSatMachine

variable {n : ℕ}

/-- Singleton supports: gate `j` reads exactly input bit `j` — as any universal circuit must. -/
def singletonSupports (n : ℕ) : Fin n → Finset (Fin n) := fun j => {j}

/-- The cell coordinate of a singleton gate is just its input bit. -/
theorem weightVec_singleton (x : Fin n → Bool) (j : Fin n) :
    weightVec (singletonSupports n) x j = if x j then 1 else 0 := by
  simp only [weightVec, singletonSupports, weightOn, Finset.sum_singleton]

/-- **The cell IS the input (proved)**: with singleton supports the cell map is injective, so no two
inputs share a cell — there is nothing to compress. -/
theorem weightVec_singleton_injective :
    Function.Injective (weightVec (singletonSupports n)) := by
  intro x y h
  funext j
  have hj : weightVec (singletonSupports n) x j = weightVec (singletonSupports n) y j := congrFun h j
  rw [weightVec_singleton, weightVec_singleton] at hj
  revert hj; cases x j <;> cases y j <;> simp

/-- **The projection collapses: exactly `2^n` cells (proved)** — the brute-force count. -/
theorem singleton_cells_eq_two_pow (n : ℕ) :
    (Finset.univ.image (weightVec (singletonSupports n))).card = 2 ^ n := by
  rw [Finset.card_image_of_injective _ weightVec_singleton_injective, Finset.card_univ]
  simp [Fintype.card_fun]

/-- **No speedup for bit-reading (general) circuits (proved)**: a cell search over singleton-support
gates runs in `2^n` steps — identical to brute force.  The projection provides zero gain exactly when
the circuit is universal. -/
theorem singleton_cellSearch_no_speedup (C : Depth2SymCircuit n n)
    (h : C.supports = singletonSupports n) : (symCellSearch C).steps = 2 ^ n := by
  show (Finset.univ.image (weightVec C.supports)).card = 2 ^ n
  rw [h]; exact singleton_cells_eq_two_pow n

end PallLean.Paper93.DeepMath.PathB.ProjectionCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.ProjectionCollapse.singleton_cells_eq_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.ProjectionCollapse.singleton_cellSearch_no_speedup
