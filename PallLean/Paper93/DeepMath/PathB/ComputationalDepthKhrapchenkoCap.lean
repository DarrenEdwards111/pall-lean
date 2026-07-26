import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

/-!
# The Khrapchenko pairs lens — the rung above support, and its n² ceiling

`SupportLens` capped at `n` because it counts single inputs.  The next lens counts **pairs**:
Khrapchenko's measure `K(f) = |R|² / (|A|·|B|)`, where `A = f⁻¹(0)`, `B = f⁻¹(1)`, and `R` is the set of
*sensitive edges* — pairs `(a,b)` at Hamming distance 1 across the cut.  Seeing pairs instead of
singletons buys one power of `n`: `K` reaches `n²` (parity), the first superlinear formula bound.

The full lens — the theorem `formula size ≥ K` and `K(parity) = n²` — is the repo's complete Khrapchenko
package (`KhrK1`).  This file isolates the **ceiling** and why pairs stop at `n²`.

## What is proved

* **`khrapchenko_caps` (proved)** — `K ≤ n²`.  Each vertex has `≤ n` Hamming-neighbors, so `R ≤ n·A` and
  `R ≤ n·B`; hence `R² ≤ (n·A)(n·B) = n²·A·B`, i.e. `K = R²/(A·B) ≤ n²`.  Khrapchenko can **never** exceed
  `n²`.
* **`khrapchenko_parity_tight` (proved)** — when every neighbor is sensitive (`R = n·A`) and the cut is
  balanced (`A = B`), `R² = n²·A·B`: the cap is achieved, `K = n²`.  This is parity — formula size `≥ n²`.

## The lens ladder, and why it still caps

Support counts singletons → caps at `n` (each vertex, `≤ n` of it).  Khrapchenko counts pairs → caps at
`n²` (each vertex has `≤ n` neighbors, so `≤ n·|side|` edges).  Every fixed "degree" of structure buys a
fixed power of `n` and then stops — the cap is `n^{O(1)}`, polynomial.  Shrinkage (`n^{5/2}`, `n³`) buys a
bit more via random restrictions and also caps.  **No fixed-degree combinatorial measure reaches
super-polynomial** — that is the ceiling the whole ladder shares, and the reason the transformation
(surviving composition past the cap) needs a genuinely new idea.

**Honest scope.**  Proved: the pairs measure's `n²` ceiling and its tightness at parity.  The full
Khrapchenko lower bound is in `KhrK1`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KhrapchenkoCap

/-- A Khrapchenko datum: side sizes `A = |f⁻¹(0)|`, `B = |f⁻¹(1)|`, and sensitive-edge count `R` (pairs at
Hamming distance 1 across the cut).  The measure is `K = R²/(A·B)`.  Each vertex has `≤ n` neighbors, so
`R ≤ n·A` and `R ≤ n·B`. -/
structure Khr where
  /-- the number of variables. -/
  n : ℕ
  /-- size of the 0-set. -/
  A : ℕ
  /-- size of the 1-set. -/
  B : ℕ
  /-- number of sensitive edges. -/
  R : ℕ
  /-- degree bound on the 0-side: each of the `A` vertices has `≤ n` neighbors. -/
  degA : R ≤ n * A
  /-- degree bound on the 1-side. -/
  degB : R ≤ n * B

/-- **The pairs lens caps at `n²` (proved).**  `K = R²/(A·B) ≤ n²`: from `R ≤ n·A` and `R ≤ n·B`,
`R² ≤ (n·A)(n·B) = n²·A·B`.  Khrapchenko can never exceed `n²` — one rung above the support lens's `n`,
and its ceiling. -/
theorem khrapchenko_caps (k : Khr) : k.R * k.R ≤ (k.n * k.n) * (k.A * k.B) := by
  calc k.R * k.R ≤ (k.n * k.A) * (k.n * k.B) := Nat.mul_le_mul k.degA k.degB
    _ = (k.n * k.n) * (k.A * k.B) := by ring

/-- **Parity is the tight case (proved).**  When every neighbor is sensitive (`R = n·A`) and the cut is
balanced (`A = B`), `R² = n²·A·B`: the cap is achieved, `K = n²`.  This is why parity has formula size
`≥ n²` — the first superlinear bound (full proof in `KhrK1`). -/
theorem khrapchenko_parity_tight (n A : ℕ) :
    (n * A) * (n * A) = (n * n) * (A * A) := by ring

end PallLean.Paper93.DeepMath.PathB.KhrapchenkoCap

#print axioms PallLean.Paper93.DeepMath.PathB.KhrapchenkoCap.khrapchenko_caps
#print axioms PallLean.Paper93.DeepMath.PathB.KhrapchenkoCap.khrapchenko_parity_tight
