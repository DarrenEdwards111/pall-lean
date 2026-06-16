import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MiniBTTwoCount

/-!
# The Beigel–Tarui size recurrence — why exact mixed-radix collapse is insufficient, and the probabilistic socket

`…ACC0MiniBTTwoCount` proved the two-count collapse *exactly*, with a single composition step costing
`btComposeSize l r = l·(r+1)+r` gates (a product of the two sizes).  This file does three things:

1. **Formalises the size recurrence and proves the exact blow-up is super-polynomial.**  Folding a gate of fan-in
   `k+1` (each child of size `b`) by iterating the two-count collapse gives `iterSize b k`, and we prove
   `b·(b+1)^k ≤ iterSize b k` — **exponential in the fan-in**.  Since `ACC⁰` gates have polynomial (unbounded) fan-in,
   a *single* layer already blows up exponentially under exact mixed-radix.  This pins down precisely why exact
   composition cannot give a quasipolynomial representation.

2. **States the needed quasipolynomial-compression theorem as a named socket.**  `ApproxSymAndRep` (a concrete
   `ε`-approximate single-count representation of bounded size) and `QuasipolyApproxCompression` (the open replacement
   for exact mixed-radix: every joint representation compresses to an *approximate* single-count one of quasipolynomial
   size).  This is the probabilistic-polynomial content (Razborov–Smolensky / Beigel–Tarui), left open.

3. **Proves the approximation bookkeeping.**  The union bound `error_union_bound` (`s` gates of error `≤ ε` ⇒ total
   `≤ s·ε`) and the calibration `error_choice` (`ε = 1/(10s)` ⇒ total `= 1/10`), so approximate gates compose
   reliably across a bounded-size circuit.

## What is proved (clean axioms, no `sorry`)

* **`btComposeSize_eq`** — the per-step cost equals the proved encoded-layer size of `…ACC0MiniBTTwoCount`.
* **`iterSize`, `iterSize_ge`** — `b·(b+1)^k ≤ iterSize b k`: exact fold of fan-in `k+1` is exponential in `k`.
* **`error_union_bound`**, **`error_choice`** — the union-bound bookkeeping and its `1/(10s)` calibration.

## The open content (socketed honestly)

* **`QuasipolyApproxCompression`** — joint reps compress to quasipolynomial approximate single-count reps (the
  probabilistic collapse; replaces exact mixed-radix).  **Not proved.**
* **`MOD6ProbabilisticApprox`** — the first concrete target: the `MOD₆` count predicate has a quasipolynomial
  approximate `SYM∘AND` representation (the `MOD₆` probabilistic polynomial).  **Not proved.**
* **`probabilistic_route_to_NEXP_not_ACC0`** — *given* a quasipolynomial (approximate) representation surviving
  constant depth, the existing counting + Williams cash-out gives `¬ NEXP ⊆ ACC⁰`
  (re-exporting `…ACC0RankRouteFrontier`).

## Honest scope

The recurrence, its exponential lower bound, and the union-bound bookkeeping are *proved*.  The probabilistic
compression that keeps size quasipolynomial — the genuine Beigel–Tarui / Razborov–Smolensky content — is **not**
proved; it is the named socket.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BTSizeRecurrence

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2
open PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition
open PallLean.Paper93.DeepMath.PathB.ACC0MiniBTTwoCount
open PallLean.Paper93.DeepMath.PathB.ACC0RankRouteFrontier

/-! ## 1. The size recurrence and its exponential blow-up -/

/-- **The per-step two-count collapse cost**: combining a size-`l` accumulator with a size-`r` child costs
`l·(r+1)+r` gates (the mixed-radix encoded layer). -/
def btComposeSize (l r : ℕ) : ℕ := l * (r + 1) + r

/-- **The per-step cost equals the proved encoded-layer size (proved).**  Grounds the recurrence in
`…ACC0MiniBTTwoCount.miniBT_collapse_size`. -/
theorem btComposeSize_eq (t1 t2 : ℕ) :
    btComposeSize t1 t2 = Fintype.card ((Fin t1 × Fin (t2 + 1)) ⊕ Fin t2) :=
  (ACC0MiniBTTwoCount.miniBT_collapse_size t1 t2).symm

/-- **The fan-in fold**: collapsing a gate of fan-in `k+1`, each child of size `b`, by iterating the two-count
collapse `k` times. -/
def iterSize (b : ℕ) : ℕ → ℕ
  | 0 => b
  | k + 1 => btComposeSize (iterSize b k) b

/-- **Exact composition is exponential in the fan-in (proved): `b·(b+1)^k ≤ iterSize b k`.**  A single `ACC⁰` gate of
polynomial fan-in therefore blows up exponentially under exact mixed-radix — the precise reason exact collapse cannot
yield a quasipolynomial representation. -/
theorem iterSize_ge (b k : ℕ) : b * (b + 1) ^ k ≤ iterSize b k := by
  induction k with
  | zero => simp [iterSize]
  | succ k ih =>
      simp only [iterSize, btComposeSize]
      calc b * (b + 1) ^ (k + 1) = (b * (b + 1) ^ k) * (b + 1) := by ring
        _ ≤ iterSize b k * (b + 1) := mul_le_mul_right' ih (b + 1)
        _ ≤ iterSize b k * (b + 1) + b := Nat.le_add_right _ _

/-- **Concrete exponential witness (proved): `2·3^k ≤ iterSize 2 k`.** -/
theorem iterSize_two (k : ℕ) : 2 * 3 ^ k ≤ iterSize 2 k :=
  iterSize_ge 2 k

/-! ## 2. The quasipolynomial-compression socket (the probabilistic replacement) -/

/-- **An `ε`-approximate `SYM∘AND` representation of bounded size**: a single-count symmetric function over a layer of
`sz` gates that disagrees with `F` on at most an `ε`-fraction of inputs. -/
def ApproxSymAndRep {n : ℕ} (F : (Fin n → Bool) → Bool) (sz : ℕ) (ε : ℝ) : Prop :=
  ∃ (supports : Fin sz → Finset (Fin n)) (sym : ℕ → Bool),
    ((Finset.univ.filter (fun x => F x ≠ sym (satCount supports x))).card : ℝ)
      ≤ ε * (Fintype.card (Fin n → Bool) : ℝ)

/-- **The open probabilistic collapse (socket, NOT proved).**  Every joint two-count representation compresses to an
`eps`-approximate single-count representation of quasipolynomial size `qpoly n` — the probabilistic-polynomial
replacement for the exact mixed-radix collapse (whose size, by `iterSize_ge`, is exponential). -/
def QuasipolyApproxCompression (qpoly : ℕ → ℕ) (eps : ℝ) : Prop :=
  ∀ {n : ℕ} (F : (Fin n → Bool) → Bool),
    HasBinarySymRep F → ApproxSymAndRep F (qpoly n) eps

/-- **The first concrete probabilistic-polynomial target (socket, NOT proved).**  The depth-2 `MOD₆∘AND` circuit has a
quasipolynomial approximate `SYM∘AND` representation — the `MOD₆` probabilistic polynomial. -/
def MOD6ProbabilisticApprox (qpoly : ℕ → ℕ) (eps : ℝ) : Prop :=
  ∀ {n : ℕ} (supp : Σ t : ℕ, Fin t → Finset (Fin n)),
    ApproxSymAndRep (fun x => decide (6 ∣ satCount supp.2 x)) (qpoly n) eps

/-! ## 3. The approximation bookkeeping (union bound) -/

/-- **Union bound (proved): `s` gates each of error `≤ ε` accumulate to total error `≤ s·ε`.** -/
theorem error_union_bound {s : ℕ} (errs : Fin s → ℝ) (ε : ℝ) (h : ∀ i, errs i ≤ ε) :
    ∑ i, errs i ≤ (s : ℝ) * ε := by
  calc ∑ i, errs i ≤ ∑ _i : Fin s, ε := Finset.sum_le_sum (fun i _ => h i)
    _ = (s : ℝ) * ε := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Error calibration (proved): choosing `ε = 1/(10s)` makes the total error exactly `1/10`.**  Hence approximate
gates compose reliably across a size-`s` circuit. -/
theorem error_choice (s : ℕ) (hs : 0 < s) :
    (s : ℝ) * (1 / (10 * (s : ℝ))) = 1 / 10 := by
  have hs' : (s : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hs)
  field_simp

/-! ## 4. / 5. The constant-depth cash-out (conditional) -/

/-- **The probabilistic route to `¬ NEXP ⊆ ACC⁰` (proved conditional).**  *Given* a quasipolynomial (approximate)
`SYM∘AND` representation of constant-depth `ACC⁰` (`probabilistic_compression`) — produced by the open
`QuasipolyApproxCompression` / `MOD6ProbabilisticApprox` content rather than the exponential exact collapse — the
existing Route-B counting socket + Williams cash-out yields `¬ NEXPHasACC0Circuits`. -/
theorem probabilistic_route_to_NEXP_not_ACC0
    (RSRep ACC0SatSpeedup NEXPHasACC0Circuits Collapse : Prop)
    (probabilistic_compression : RSRep)
    (counting : RSRep → ACC0SatSpeedup)
    (williams : ACC0SatSpeedup → NEXPHasACC0Circuits → Collapse)
    (hierarchy : ¬ Collapse) :
    ¬ NEXPHasACC0Circuits :=
  composite_route_to_NEXP_not_ACC0 RSRep ACC0SatSpeedup NEXPHasACC0Circuits Collapse
    probabilistic_compression counting williams hierarchy

end PallLean.Paper93.DeepMath.PathB.ACC0BTSizeRecurrence

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BTSizeRecurrence.btComposeSize_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BTSizeRecurrence.iterSize_ge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BTSizeRecurrence.iterSize_two
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BTSizeRecurrence.error_union_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BTSizeRecurrence.error_choice
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BTSizeRecurrence.probabilistic_route_to_NEXP_not_ACC0
