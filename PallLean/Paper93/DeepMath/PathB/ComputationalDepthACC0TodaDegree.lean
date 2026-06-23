import Mathlib

/-!
# Toda amplification as a polynomial: `totalDegree (A^{[k]} q) ≤ 3^k · deg q` (PROVED)

The degree formalisation of the Toda integer route.  `ACC0TodaAmplify`/`ACC0TodaIterate` proved the
modulus amplification at the *value* level on `ℤ` and recorded the degree *budget* `3^k`.  This file
makes the degree a genuine `MvPolynomial.totalDegree` statement: substituting a polynomial `q` into
`A(y) = 3y² − 2y³` and iterating `k` times multiplies the total degree by at most `3^k`.

  `todaAmpP` / `todaAmpIterP` — the polynomial amplification and its `k`-fold iterate.
  `todaAmpP_totalDegree_le` — `totalDegree (A q) ≤ 3 · totalDegree q`.
  `todaAmpIterP_totalDegree_le` — `totalDegree (A^{[k]} q) ≤ 3^k · totalDegree q`.

So when `q` is the degree-1 count polynomial `∑ xᵢ` of a `MOD` gate, `A^{[k]}(q)` has total degree
`≤ 3^k`, while (by `ACC0TodaIterate`) its value preserves the `{0,1}` residue up to modulus `m^{2^k}`.
With `k ≈ log log N` this is **degree polylog**, exactly as the integer route needs.

## What is proved (clean axioms, no `sorry`)

* `todaAmpP_totalDegree_le` — one step multiplies degree by `≤ 3`.
* `todaAmpIterP_totalDegree_le` — `k` steps multiply degree by `≤ 3^k`.

## Honest scope

The degree side (`3^k`) and the modulus side (`m^{2^k}`, `ACC0TodaIterate`) of the Toda iterate are now
both proved.  The remaining wall is gluing them on the *bottom-`AND`-count* polynomial of an actual
ACC⁰ circuit and choosing `k` against the count range to extract an exact integer-valued `SYM∘AND` of
quasipoly support for unbounded `AND`/`OR`.  That composition is the Beigel–Tarui integer construction
body, not built here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TodaDegree

open MvPolynomial

variable {σ : Type*} {R : Type*} [CommRing R]

/-- Toda's amplification as a polynomial substitution: `A(q) = 3q² − 2q³`. -/
noncomputable def todaAmpP (q : MvPolynomial σ R) : MvPolynomial σ R := 3 * q ^ 2 - 2 * q ^ 3

/-- The `k`-fold polynomial iterate `A^{[k]}`. -/
noncomputable def todaAmpIterP : ℕ → MvPolynomial σ R → MvPolynomial σ R
  | 0, q => q
  | k + 1, q => todaAmpP (todaAmpIterP k q)

/-- **One amplification step multiplies total degree by `≤ 3` (proved).** -/
theorem todaAmpP_totalDegree_le (q : MvPolynomial σ R) :
    (todaAmpP q).totalDegree ≤ 3 * q.totalDegree := by
  have hfac : todaAmpP q = q ^ 2 * (3 - 2 * q) := by rw [todaAmpP]; ring
  rw [hfac]
  refine le_trans (totalDegree_mul _ _) ?_
  have h1 : (q ^ 2).totalDegree ≤ 2 * q.totalDegree := totalDegree_pow q 2
  have h2 : (3 - 2 * q : MvPolynomial σ R).totalDegree ≤ q.totalDegree := by
    have e3 : (3 : MvPolynomial σ R) = C 3 := (map_ofNat C 3).symm
    have e2 : (2 : MvPolynomial σ R) = C 2 := (map_ofNat C 2).symm
    rw [e3, e2]
    refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_)
    · rw [totalDegree_C]; exact Nat.zero_le _
    · refine le_trans (totalDegree_mul _ _) ?_; rw [totalDegree_C]; simp
  omega

/-- **The `k`-fold iterate multiplies total degree by `≤ 3^k` (proved).** -/
theorem todaAmpIterP_totalDegree_le (k : ℕ) (q : MvPolynomial σ R) :
    (todaAmpIterP k q).totalDegree ≤ 3 ^ k * q.totalDegree := by
  induction k with
  | zero => simp [todaAmpIterP]
  | succ k ih =>
    rw [todaAmpIterP]
    refine le_trans (todaAmpP_totalDegree_le _) (le_trans (Nat.mul_le_mul_left 3 ih) ?_)
    exact le_of_eq (by rw [pow_succ]; ring)

/-!
**Toda degree formalisation proved.**  `totalDegree (A^{[k]} q) ≤ 3^k · totalDegree q` — the degree side
of the iterate, matching the `m^{2^k}` modulus side (`ACC0TodaIterate`).  On a degree-1 count polynomial,
`A^{[k]}` has degree `≤ 3^k = polylog` for `k ≈ log log`.  Gluing degree + modulus on the bottom-`AND`
count of an actual circuit (the exact quasipoly `SYM∘AND` for unbounded `AND`/`OR`) is the remaining
wall.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TodaDegree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TodaDegree.todaAmpIterP_totalDegree_le
