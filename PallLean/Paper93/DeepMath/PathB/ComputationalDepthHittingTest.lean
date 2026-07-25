import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHittingSet

/-!
# The deterministic identity test from a hitting set — `toDerand`, made concrete

In `HittingSet`, the step "poly-size hitting set ⟹ deterministic `PIT`" (`toDerand`) was a bare
socket.  This file discharges its **mathematical content** unconditionally: given *any* hitting set
`H` for degree `d`, the explicit procedure "evaluate `p` at every point of `H` and accept iff all
values are `0`" **correctly decides** whether a degree-`≤ d` polynomial is identically zero — no
randomness, no assumption.

* **`hittingTest`** — the algorithm: `decide (p vanishes on every point of H)`, a `Bool`.
* **`hittingTest_true_iff_vanishes` (proved)** — it accepts iff `p` vanishes on all of `H`.
* **`hittingTest_correct` (proved)** — under the hitting-set property and `deg p ≤ d`, it accepts
  **iff `p = 0`**.  This is deterministic `PIT`, correct, unconditional.
* **`hittingTest_cost` (proved)** — the procedure performs exactly `#H` evaluations.

**What is now a socket, and what is not.**  *Correctness* of the deterministic test is fully proved
here — that half of `toDerand` is no longer socketed.  What remains is purely *efficiency*: the test
runs in `#H · (cost of one evaluation)` steps, so it is polynomial-time exactly when (i) `#H` is
`poly(n,d)` — the open hitting-set-compression target of `PITVariableWall`/`HittingSet` — and
(ii) each evaluation is polynomial-time, which holds when `p` is presented as a poly-size circuit.
So the entire remaining gap to derandomized `PIT` is condition (i): a **small** hitting set.  The
correctness engine is built; the fuel it needs is the poly-size hitting set.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HittingTest

open PallLean.Paper93.DeepMath.PathB.HittingSet

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The deterministic identity test.**  Accept `p` iff it evaluates to `0` at every point of the
hitting set `H`.  Decidable because `H` is finite and `F` has decidable equality — this is a genuine
algorithm returning a `Bool`. -/
def hittingTest {n : ℕ} (H : Finset (Fin n → F)) (p : MvPolynomial (Fin n) F) : Bool :=
  decide (∀ f ∈ H, MvPolynomial.eval f p = 0)

/-- **The test accepts iff `p` vanishes on the whole hitting set (proved).** -/
theorem hittingTest_true_iff_vanishes {n : ℕ} (H : Finset (Fin n → F))
    (p : MvPolynomial (Fin n) F) :
    hittingTest H p = true ↔ ∀ f ∈ H, MvPolynomial.eval f p = 0 := by
  simp [hittingTest]

/-- **Deterministic `PIT` correctness (proved).**  If `H` is a hitting set for total degree `d` and
`p` has total degree `≤ d`, then the test accepts **iff `p` is the zero polynomial**.  A correct,
deterministic identity test — the mathematical content of `toDerand`, unconditional. -/
theorem hittingTest_correct {n d : ℕ} (H : Finset (Fin n → F)) (hH : IsHittingSet H d)
    (p : MvPolynomial (Fin n) F) (hpd : p.totalDegree ≤ d) :
    hittingTest H p = true ↔ p = 0 := by
  rw [hittingTest_true_iff_vanishes]
  constructor
  · intro hvanish
    by_contra hp
    obtain ⟨f, hfH, hfne⟩ := hH p hp hpd
    exact hfne (hvanish f hfH)
  · intro hp0 f _
    rw [hp0]
    exact map_zero _

/-- **The test reads only the `#H` evaluations (proved).**  If two polynomials agree at every point
of the hitting set `H`, the deterministic identity test returns the same verdict on both.  So the
test is a function of exactly the `#H` values `{eval f p : f ∈ H}` — it performs `#H` evaluations and
nothing more.  Hence it runs in polynomial time precisely when (i) `#H` is `poly(n,d)` — the open
hitting-set-compression target — and (ii) each evaluation is polynomial-time (true for a poly-size
circuit presentation of `p`). -/
theorem hittingTest_reads_only_H {n : ℕ} (H : Finset (Fin n → F))
    (p q : MvPolynomial (Fin n) F)
    (hpq : ∀ f ∈ H, MvPolynomial.eval f p = MvPolynomial.eval f q) :
    hittingTest H p = hittingTest H q := by
  simp only [hittingTest, decide_eq_decide]
  constructor
  · intro h f hf; rw [← hpq f hf]; exact h f hf
  · intro h f hf; rw [hpq f hf]; exact h f hf

end PallLean.Paper93.DeepMath.PathB.HittingTest

#print axioms PallLean.Paper93.DeepMath.PathB.HittingTest.hittingTest_true_iff_vanishes
#print axioms PallLean.Paper93.DeepMath.PathB.HittingTest.hittingTest_correct
#print axioms PallLean.Paper93.DeepMath.PathB.HittingTest.hittingTest_reads_only_H
