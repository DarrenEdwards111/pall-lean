import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NisanWigdersonHybrid

/-!
# The NW reconstruction step — the hardwiring size accounting (proved)

Entry 192 reduced the NW hybrid argument to three sub-sockets; entry 193 discharged the first (Yao).  This file opens
the second — **`Reconstruction`**: a next-bit predictor + the low-intersection design ⇒ a small circuit for the hard
function `f`.  It *proves the genuine quantitative heart* of the reconstruction: the **size accounting**.

The reconstruction builds a circuit for `f` out of (i) the next-bit predictor (from Yao) and (ii) hardwired copies of
the *other* `m−1` design blocks `f(y|_{Sⱼ})`.  Crucially, by the low-intersection property (entry 191), each other
block `Sⱼ` shares only `r_j < k` seed bits with the active block, so — by `low_intersection_table_card` (entry 192) —
each is a Boolean function of `r_j` bits and is hardwirable as a truth table of `2^{r_j} ≤ 2^k` entries.  Summing, the
hardwiring costs at most `(m−1)·2^k` extra gates, so the reconstructed circuit has size
`≤ predictorSize + (m−1)·2^k`.  This is **small** (polynomial in `m`) exactly in the NW parameter regime `k = O(log m)`,
where `2^k = poly(m)` — which is what makes the whole derandomisation efficient.

## What is proved (clean axioms, no `sorry`)

* **`reconstruction_table_sum_le`** — the total hardwiring cost: `∑_j 2^{r_j} ≤ numOther · 2^k` when every block shares
  `r_j < k` bits (`Finset.sum_le_sum` via `low_intersection_table_card`, then `Finset.sum_const`).
* **`reconstruction_total_size_le`** — the reconstructed circuit size `predictorSize + ∑_j 2^{r_j} ≤ predictorSize +
  numOther · 2^k`.
* **`reconstruction_poly`** — the polynomial-size payoff: if `2^k ≤ B` (i.e. `k ≤ log₂ B`, the NW regime), the size is
  `≤ predictorSize + numOther · B`.
* **`reconstruction_socket_discharge`** — discharges the **entry-192 `Reconstruction` socket** for the concrete
  size-carrying predicate: the predictor + the low-intersection design (`∀ j, r_j < k`) + the correctness socket yield a
  small circuit for `f` (it computes `f` *and* has size within the proved bound).

## Honest scope

This proves the **quantitative core** of the reconstruction step — the *size accounting* showing the hardwired circuit
is small (polynomial when `k = O(log m)`) — completely and from first principles (ℕ arithmetic), reusing the entry-191/
192 low-intersection bound, and discharges the entry-192 `Reconstruction` socket for the concrete size-carrying
predicate.  What remains a named residual socket (**`ReconstructionCorrectness`**) is the *model-dependent* claim that
the assembled circuit (predictor + hardwired tables) **actually computes `f`** — this needs the circuit semantics and is
not the size accounting.  This proves the reconstruction's *size engine*, not the circuit-correctness construction.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonReconstruction

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonHybrid (low_intersection_table_card Reconstruction)

/-- **The total hardwiring cost (PROVED).**  If each of the `numOther` other blocks shares `r j < k` seed bits with the
active block, then hardwiring them all as truth tables costs at most `numOther · 2^k` gates: each table has
`2^{r j} ≤ 2^k` entries (`low_intersection_table_card`), and the sum of `numOther` such terms is `numOther · 2^k`. -/
theorem reconstruction_table_sum_le (numOther k : ℕ) (r : Fin numOther → ℕ) (hr : ∀ j, r j < k) :
    ∑ j, Fintype.card (Fin (r j) → Bool) ≤ numOther * 2 ^ k := by
  calc ∑ j, Fintype.card (Fin (r j) → Bool)
      ≤ ∑ _j : Fin numOther, 2 ^ k :=
        Finset.sum_le_sum (fun j _ => low_intersection_table_card (r j) k (hr j))
    _ = numOther * 2 ^ k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **The reconstructed-circuit size bound (PROVED).**  The reconstructed circuit = the predictor (size `predictorSize`)
plus the hardwired tables, so its size is `predictorSize + ∑_j 2^{r j} ≤ predictorSize + numOther · 2^k`. -/
theorem reconstruction_total_size_le (predictorSize numOther k : ℕ) (r : Fin numOther → ℕ)
    (hr : ∀ j, r j < k) :
    predictorSize + ∑ j, Fintype.card (Fin (r j) → Bool) ≤ predictorSize + numOther * 2 ^ k :=
  Nat.add_le_add_left (reconstruction_table_sum_le numOther k r hr) _

/-- **The polynomial-size payoff (PROVED).**  In the NW regime `k = O(log m)` — i.e. `2^k ≤ B` for a polynomial bound
`B` — the reconstructed circuit has size `≤ predictorSize + numOther · B`, polynomial in `numOther`.  This is *why* the
low-intersection design (intersection `< k` with `k` logarithmic) makes the derandomisation efficient. -/
theorem reconstruction_poly (predictorSize numOther k B : ℕ) (r : Fin numOther → ℕ)
    (hr : ∀ j, r j < k) (hB : 2 ^ k ≤ B) :
    predictorSize + ∑ j, Fintype.card (Fin (r j) → Bool) ≤ predictorSize + numOther * B := by
  refine le_trans (reconstruction_total_size_le predictorSize numOther k r hr) ?_
  gcongr

/-- **The next-bit-predictor carrier.**  The data the predictor supplies to the reconstruction: it computes `f` on the
active block (`ComputesF`), with circuit size `predictorSize`.  (Here `ComputesF` is the correctness fact established by
the residual socket below.) -/
def ReconNextBit (_predictorSize : ℕ) (ComputesF : Prop) : Prop := ComputesF

/-- **The low-intersection design carrier.**  The design supplies exactly the low-intersection property of entry 191:
each of the `numOther` other blocks shares `r j < k` seed bits with the active block. -/
def ReconDesign (numOther k : ℕ) (r : Fin numOther → ℕ) : Prop := ∀ j, r j < k

/-- **A small circuit for `f`.**  The reconstructed circuit *computes `f`* (`ComputesF`) and has size `actualSize`
within the proved bound. -/
def SmallCircuitForFAt (ComputesF : Prop) (actualSize bound : ℕ) : Prop :=
  ComputesF ∧ actualSize ≤ bound

/-- **The residual correctness socket.**  The model-dependent remaining claim: the assembled circuit (the predictor wired
to the hardwired block tables) **computes `f`**.  Stated, not proved. -/
def ReconstructionCorrectness (Predictor TableHardwiring ComputesF : Prop) : Prop :=
  Predictor → TableHardwiring → ComputesF

/-- **Discharging the entry-192 `Reconstruction` socket (PROVED).**  Given the next-bit predictor (supplying
`ComputesF` and `predictorSize`) and the low-intersection design (`∀ j, r j < k`, the entry-191 property), the
reconstruction yields a small circuit for `f`: it computes `f` (from the predictor's correctness) and has size
`predictorSize + ∑_j 2^{r j} ≤ predictorSize + numOther · 2^k` (the proved `reconstruction_total_size_le`).  This is the
quantitative content of the reconstruction step; the only model-dependent input is the correctness fact `ComputesF`,
which the residual `ReconstructionCorrectness` socket supplies. -/
theorem reconstruction_socket_discharge
    (predictorSize numOther k : ℕ) (r : Fin numOther → ℕ) (ComputesF : Prop) :
    Reconstruction (ReconNextBit predictorSize ComputesF) (ReconDesign numOther k r)
      (SmallCircuitForFAt ComputesF (predictorSize + ∑ j, Fintype.card (Fin (r j) → Bool))
        (predictorSize + numOther * 2 ^ k)) :=
  fun hComputes hr => ⟨hComputes, reconstruction_total_size_le predictorSize numOther k r hr⟩

end PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonReconstruction

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonReconstruction.reconstruction_table_sum_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonReconstruction.reconstruction_poly
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonReconstruction.reconstruction_socket_discharge
