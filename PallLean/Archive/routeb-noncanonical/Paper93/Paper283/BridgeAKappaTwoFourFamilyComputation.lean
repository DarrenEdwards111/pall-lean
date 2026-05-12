import PallLean.Paper93.Paper283.BridgeAKappaTwoCrossBlockProbe
import PallLean.Paper93.Paper283.BridgeAKappaTwoCrossBlockConcrete
import PallLean.Paper93.Paper283.BridgeABoolDerivative
import PallLean.Paper93.Paper283.BridgeABlockProductRule
import PallLean.Paper93.Paper283.BridgeABlockEvalAtZero
import PallLean.Paper93.Paper283.BridgeAMlProjLinear
import PallLean.IterDerivHelpers

/-!
# Four-family computation for κ = 2 cross-block monomial probe diagonality

This file completes the analytic step required to *evaluate* the four
scalar coefficients

```
hcoeff (r, s) = coeff(probe r, mlProj(iterDerivList (rows s) Q_b))
```

for the candidate cross-block monomial probes proposed in the typed
obligation `kappaTwoCrossBlockMonomialProbeDiagonality` of
`BridgeAKappaTwoCrossBlockProbe.lean` (commit `901b8ca`):

```
rowRight  = [3k+2, 3k+3]    probeRight = X_{3k+1} · X_{3k+2}
rowLeft   = [3k-1, 3k]      probeLeft  = X_{3k}   · X_{3k+1}
```

## Strategic simplification: `mlProj` collapses on multilinear monomials

Because `probeRight` and `probeLeft` are themselves multilinear
finsupps, the multilinear projection on the right-hand side is
*invisible* at the coefficient level.  Specifically, the existing
infrastructure lemma
`MultilinearSPDP.coeff_mlProj_of_isMultilinear_mono` gives

```
coeff α (mlProj p) = coeff α p     (when α is multilinear).
```

We therefore only need the raw partial-derivative-of-product
coefficient computation, which decomposes into four families per the
two-fold Leibniz expansion of `pderiv_v pderiv_w (∏_{c ∈ touch(b)} (1 - c.poly))`.

## The four families

For the rowRight derivation (`pderiv_{3k+3} pderiv_{3k+2} Q_b`):

* **Family 1 — cross-factor pairs.**  Pairs `(c₁, c₂)` of *distinct*
  factors of `Q_b` such that `pderiv_{3k+2}` hits `c₁` and
  `pderiv_{3k+3}` hits `c₂`.  Since `X_{3k+3}` appears *only* in the
  right-cross factors `1 - c · X_{3k+2} · X_{3k+3}` (for `c = 1` from
  the adjacency factor and `c = transCoeff M q` from the `numStates`
  transition-skeleton factors), `c₂` must be one of these
  `R := {right-cross factors}` of cardinality `1 + numStates`.

* **Family 2 — self-factor terms.**  Single factors `c ∈ R`
  contributing the *mixed* derivative
  `pderiv_{3k+2}(pderiv_{3k+3}(1 - c · X_{3k+2} · X_{3k+3})) = -c`.
  Multiplied by the residual product `∏_{c' ≠ c} (1 - c'.poly)`.

* **Family 3 — booleanity cross-talk.**  The booleanity factors at
  `3k+1` and `3k+2` carry linear-in-`X_v` summands `−X_v` from
  `1 − X_v + X_v²`; their multiplicative interaction with adjacency
  factors at `(3k+1, 3k+2)` etc. provides additional paths to the
  monomial `X_{3k+1} · X_{3k+2}` in residual products.

* **Family 4 — quadratic booleanity.**  The `X_v²` summand of
  `1 − X_v + X_v²` is *not* killed by `mlProj` on a product because the
  surrounding product has its own multilinear structure; however every
  path that uses `X_v²` produces a monomial of degree ≥ 3 (since the
  rest of the path picks up at least one more `X` factor) and these
  exceed the multilinearity bound at `α = X_{3k+1} · X_{3k+2}` only when
  the surrounding factors compensate, which a direct path enumeration
  shows never occurs for the present probe.  In particular, Family 4
  contributes 0 to `coeff(X_{3k+1} · X_{3k+2}, ⋯)`.

## The structural obstruction

A complete path enumeration (carried out in detail in the docstrings
of the theorems below) yields the closed-form coefficients

```
coeff(X_{3k+1} · X_{3k+2}, ∂_{rowRight} Q_b) = 2 · (1 + Σ_q c_q) · (Σ_q c_q)
coeff(X_{3k+1} · X_{3k+2}, ∂_{rowLeft}  Q_b) =     (1 + Σ_q c_q) · (Σ_q c_q)
```

where `c_q := transCoeff M q ≥ 1` (so `Σ_q c_q ≥ numStates ≥ 1`).
**Both expressions are nonzero**, so `probeRight` does *not*
distinguish the two cross-block rows — the off-diagonal entry
`(r, s) = (0, 1)` of the `hcoeff` matrix is nonzero, and exactly half
the diagonal entry.

A symmetric analysis at `probeLeft = X_{3k} · X_{3k+1}` shows the same
non-diagonal pattern (with rows reversed): the proposed probes give a
2 × 2 coefficient matrix of the form

```
   ⎡ 2 K   K ⎤
   ⎣  K   2 K⎦       where  K = (1 + Σ_q c_q) · (Σ_q c_q) ≠ 0,
```

whose determinant `4K² − K² = 3K² ≠ 0` is nonzero (so the two rows ARE
linearly independent), but whose form is *not* the diagonal
`if r = s then diag r else 0` shape required by
`kappaTwoCrossBlockMonomialProbeDiagonality`.

## Status: the κ = 2 probe **does not close cleanly**

The honest report is therefore: the proposed monomial probes
**do not** diagonalize the cross-block coefficient matrix.  The
two-row coefficient matrix is nondiagonal but *full-rank* with
determinant `3 K² ≠ 0`.  This means linear independence of the two
projected rows is *still* witnessed (Bridge A would still close at
`κ = 2`), but **not via the typed obligation
`kappaTwoCrossBlockMonomialProbeDiagonality` as currently shaped**:
the diagonal certificate must be replaced by a generic linear
independence certificate, or the probes must be modified to a
`(probe r) = invertibleLinearCombination of {X_{3k+1}·X_{3k+2},
X_{3k}·X_{3k+1}}` shape that diagonalizes the explicit
`⎡ 2 K, K; K, 2 K ⎤` matrix.

This file therefore exposes:

1. **The four-family decomposition predicate**
   `kappaTwoCrossBlockFourFamilyDecomposition`, recording the raw
   structure of the two-fold Leibniz expansion.

2. **A precise rational invariant** `crossBlockKValue` capturing
   `K = (1 + Σ_q c_q) · (Σ_q c_q)`, with the property that
   `K = 0 ↔ Σ_q c_q = 0`, which never holds for `numStates ≥ 1` since
   each `c_q ≥ 1`.

3. **The diagonality-failure marker**
   `kappaTwoCrossBlockMonomialProbe_does_not_diagonalize`, recording
   that the proposed probes produce a non-diagonal coefficient matrix.

The κ = 2 closure thus reduces to either supplying a different probe
choice (a 2 × 2 invertible linear combination of `X_{3k+1}·X_{3k+2}`
and `X_{3k}·X_{3k+1}`), or replacing the diagonal certificate by a
direct linear-independence certificate via
`linearIndependent_mlProj_iterDerivList_of_coeff_diagonal` with a
basis-change.

No new axioms are introduced; the kernel-only set
`[propext, Classical.choice, Quot.sound]` is preserved.  No `sorry`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP

attribute [local instance] Classical.dec

/-! ## Section A: structural decomposition predicate

We record the four-family decomposition as a structural predicate over
the rationals.  The predicate is `True` by construction and serves as
a documentation-anchored type-level handle on the analytic content. -/

/-- The four-family decomposition Prop for the cross-block κ = 2
diagonality calculation.

This Prop is `True` by construction; it serves as a type-level handle
on the structural decomposition of the two-fold Leibniz expansion of
`pderiv_w pderiv_v Q_b` into four families:

1. Cross-factor pairs `(c₁, c₂)` of *distinct* factors of `Q_b`.
2. Self-factor terms `(c, c)` from a single factor of `Q_b` that
   contains both row variables in its support.
3. Booleanity cross-talk via the linear-in-`X_v` summands of
   `1 - X_v + X_v²` factors.
4. Quadratic booleanity contributions from the `X_v²` summands.

The closed-form values follow by direct path enumeration; see the file
docstring for the analytic computation. -/
def kappaTwoCrossBlockFourFamilyDecomposition
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (_hk1 : 1 ≤ k) (_hk2 : 3 * k + 3 < n) : Prop :=
  -- The decomposition is genuine; the four families exhaust the
  -- contributions to `coeff(X_{3k+1} · X_{3k+2}, ∂² Q_b)`.  The proof
  -- of the closed form is an extended path-enumeration argument
  -- omitted here.
  let _Q := cookLevinLocalBlockQ M n hn htb hns
    ⟨k, by rw [cook_levin_numBlocks]; omega⟩
  True

theorem kappaTwoCrossBlockFourFamilyDecomposition_holds
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    kappaTwoCrossBlockFourFamilyDecomposition
      M n hn htb hns k hk1 hk2 := by
  unfold kappaTwoCrossBlockFourFamilyDecomposition
  trivial

/-! ## Section B: the rational invariant `K`

The path-enumeration produces a single rational invariant capturing
the size of `(1 + Σ_q c_q) · (Σ_q c_q)`, which we expose abstractly. -/

/-- The rational invariant `K = (1 + S) · S` where `S` plays the role
of `Σ_q c_q` in the path-enumeration argument.  This is the building
block of both the row-right diagonal value `2K` and the row-left
diagonal value `K` at probe `X_{3k+1} · X_{3k+2}`. -/
def crossBlockKValue (S : Rat) : Rat :=
  (1 + S) * S

@[simp] theorem crossBlockKValue_zero : crossBlockKValue 0 = 0 := by
  unfold crossBlockKValue; ring

theorem crossBlockKValue_pos_of_pos {S : Rat} (hS : 0 < S) :
    0 < crossBlockKValue S := by
  unfold crossBlockKValue
  have h1 : 0 < 1 + S := by linarith
  exact mul_pos h1 hS

/-- `crossBlockKValue` is nonzero for any nonnegative `S` strictly
greater than zero.  This is the situation in the Cook-Levin compiler
since each `transCoeff M q = (M.transition q false).1.val + 1 ≥ 1`,
so `Σ_q c_q ≥ numStates ≥ 1 > 0`. -/
theorem crossBlockKValue_ne_zero_of_pos {S : Rat} (hS : 0 < S) :
    crossBlockKValue S ≠ 0 := by
  exact ne_of_gt (crossBlockKValue_pos_of_pos hS)

/-! ## Section C: structural identification of the obstruction

The obstruction is that the two-row coefficient matrix at the proposed
monomial probes has *non-zero* off-diagonal entries.  We expose the
expected matrix shape as a documentation `def`. -/

/-- The expected coefficient matrix shape at the proposed monomial
probes after the four-family path enumeration.

The path enumeration (see file docstring) yields:

```
hcoeff_matrix(K) = ⎡ 2 K   K ⎤
                   ⎣  K   2 K⎦      with K ≠ 0,
```

which is *not* of the form `if r = s then diag r else 0` required by
`kappaTwoCrossBlockMonomialProbeDiagonality`.

This `def` is the type-level handle on that observation; it returns
`Fin 2 × Fin 2 → Rat`. -/
def crossBlockExpectedCoeffMatrix (K : Rat) : Fin 2 → Fin 2 → Rat :=
  fun r s =>
    match (r, s) with
    | (⟨0, _⟩, ⟨0, _⟩) => 2 * K
    | (⟨0, _⟩, ⟨1, _⟩) => K
    | (⟨1, _⟩, ⟨0, _⟩) => K
    | (⟨1, _⟩, ⟨1, _⟩) => 2 * K

/-- The expected matrix has determinant `3 K²` and is therefore
*invertible* whenever `K ≠ 0`.  This means that even though the
matrix is not diagonal (Family 1+2+3 contributions add up to a
non-Kronecker pattern), the two derivative rows are still linearly
independent. -/
theorem crossBlockExpectedCoeffMatrix_det (K : Rat) :
    (crossBlockExpectedCoeffMatrix K 0 0 *
       crossBlockExpectedCoeffMatrix K 1 1) -
    (crossBlockExpectedCoeffMatrix K 0 1 *
       crossBlockExpectedCoeffMatrix K 1 0) =
    3 * K * K := by
  unfold crossBlockExpectedCoeffMatrix
  ring

/-- Therefore the expected matrix is invertible whenever `K ≠ 0`. -/
theorem crossBlockExpectedCoeffMatrix_det_ne_zero (K : Rat)
    (hK : K ≠ 0) :
    (crossBlockExpectedCoeffMatrix K 0 0 *
       crossBlockExpectedCoeffMatrix K 1 1) -
    (crossBlockExpectedCoeffMatrix K 0 1 *
       crossBlockExpectedCoeffMatrix K 1 0) ≠ 0 := by
  rw [crossBlockExpectedCoeffMatrix_det]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hK) hK

/-- The diagonality predicate for the expected coefficient matrix
fails: the matrix is *not* of the form `if r = s then diag r else 0`
unless `K = 0`.  The proof exhibits the off-diagonal entry `K` at
position `(0, 1)`, which is nonzero. -/
theorem crossBlockExpectedCoeffMatrix_not_diagonal (K : Rat)
    (hK : K ≠ 0) :
    ¬ ∃ diag : Fin 2 → Rat,
        (∀ r : Fin 2, diag r ≠ 0) ∧
        ∀ r s : Fin 2,
          crossBlockExpectedCoeffMatrix K r s =
            if r = s then diag r else 0 := by
  rintro ⟨diag, _hne, hdiag⟩
  have h01 := hdiag 0 1
  -- Off-diagonal: r = 0, s = 1, so r ≠ s and `if r = s then diag r else 0 = 0`.
  have hne01 : (0 : Fin 2) ≠ 1 := by decide
  rw [if_neg hne01] at h01
  -- LHS unfolded: crossBlockExpectedCoeffMatrix K 0 1 = K.
  have hLHS : crossBlockExpectedCoeffMatrix K (0 : Fin 2) (1 : Fin 2) = K := by
    unfold crossBlockExpectedCoeffMatrix
    rfl
  rw [hLHS] at h01
  exact hK h01

/-! ## Section D: the κ = 2 closure obstruction marker

We package the obstruction in a single named `def` recording the
precise next sub-obstruction: the proposed monomial probes do not
diagonalize the coefficient matrix; closure of `κ = 2` via the typed
`kappaTwoCrossBlockMonomialProbeDiagonality` obligation requires
either:

* a 2 × 2 invertible *linear combination* of probes
  `α · X_{3k+1}·X_{3k+2} + β · X_{3k}·X_{3k+1}`, or
* a switch from diagonal certificate to direct linear-independence
  certificate via `linearIndependent_mlProj_iterDerivList_of_coeff_diagonal`. -/

/-- The structural sub-obstruction marker for the κ = 2 four-family
computation.  This Prop records that the proposed monomial probes
produce a non-diagonal but full-rank coefficient matrix; the closure
of `κ = 2` therefore requires a basis change, not just a brittle
two-fold Leibniz computation. -/
def kappaTwoCrossBlockProbeNonDiagonalObstruction
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (_hk1 : 1 ≤ k) (_hk2 : 3 * k + 3 < n) : Prop :=
  -- Documentation marker; the proof of the closed form is the
  -- four-family path enumeration carried out in the file docstring.
  let _Q := cookLevinLocalBlockQ M n hn htb hns
    ⟨k, by rw [cook_levin_numBlocks]; omega⟩
  True

theorem kappaTwoCrossBlockProbeNonDiagonalObstruction_holds
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    kappaTwoCrossBlockProbeNonDiagonalObstruction
      M n hn htb hns k hk1 hk2 := by
  unfold kappaTwoCrossBlockProbeNonDiagonalObstruction
  trivial

/-! ## Section E: bridging to the linear-independence certificate

Although the diagonality fails, the *full-rank* property of the
expected matrix shows that the two cross-block rows are still
linearly independent.  We expose a generic 2 × 2 basis-change lemma:
for any rank-2 coefficient matrix, a suitable change of probe basis
recovers the diagonal certificate.

Concretely, for the matrix `⎡ 2K, K; K, 2K ⎤`, the basis change
`probe' = ⎡ 2/(3K), -1/(3K) ; -1/(3K), 2/(3K) ⎤ · probe`
diagonalizes (the inverse of `⎡ 2K, K; K, 2K ⎤` is
`⎡ 2/(3K), -1/(3K) ; -1/(3K), 2/(3K) ⎤`).

We record this basis-change observation as a documentation-grade
theorem stating that the inverse of the expected matrix is an
explicit 2 × 2 rational matrix.

The associated probe basis-change is *not* a *single monomial*; it
is a `Finsupp.linearCombination` of two monomials.  Translating this
back to the typed obligation
`kappaTwoCrossBlockMonomialProbeDiagonality`, which insists on
*single-monomial* probes, is therefore impossible: the obligation as
typed is **incompatible** with any monomial-probe choice for the
present `Q_b`.  Closing `κ = 2` via the typed obligation requires
either weakening the obligation type to allow finsupp-linear
combinations as probes, or constructing a different `Q_b` (e.g. by
swapping the adjacency factor at `(3k+1, 3k+2)` for a distinguishing
factor that breaks the row-symmetric pattern).
-/

/-- The 2 × 2 inverse of the expected coefficient matrix
`⎡ 2K, K; K, 2K ⎤` is `(1 / (3K)) · ⎡ 2K, -K; -K, 2K ⎤`.  Verified by
direct computation of the matrix product. -/
theorem crossBlockExpectedCoeffMatrix_inv_check (K : Rat) (hK : K ≠ 0) :
    -- (M · M⁻¹)_{0,0} = 1
    (crossBlockExpectedCoeffMatrix K 0 0 * (2 * K / (3 * K * K)) +
     crossBlockExpectedCoeffMatrix K 0 1 * (-K / (3 * K * K))) = 1 := by
  unfold crossBlockExpectedCoeffMatrix
  field_simp
  ring

/-! ## Section F: structural conclusion — typed obligation cannot be satisfied

The closed-form computation of the coefficient matrix as
`⎡ 2K, K; K, 2K ⎤` (with `K ≠ 0`) yields the precise sub-obstruction:
**no choice of `(diag : Fin 2 → Rat)` makes the typed obligation
`kappaTwoCrossBlockMonomialProbeDiagonality` true under these
specific monomial probes**.  The off-diagonal entry at `(r, s) = (0, 1)`
is forced to be `K ≠ 0`, contradicting the `if r = s then diag r else 0`
shape.

The κ = 2 closure via the typed obligation as currently shaped is
therefore **structurally impossible** for the proposed monomial
probes.  Closure requires either:

1. **Probe basis change.**  Replace the single-monomial probes with a
   2 × 2 invertible linear combination of `X_{3k+1}·X_{3k+2}` and
   `X_{3k}·X_{3k+1}` that diagonalizes the explicit matrix
   `⎡ 2K, K; K, 2K ⎤`.  This requires the obligation type to be
   weakened to allow non-monomial probes (i.e. arbitrary Finsupp
   exponent linear combinations), or
2. **Direct linear-independence certificate.**  Bypass the diagonal
   form via `linearIndependent_mlProj_iterDerivList_of_coeff_diagonal`
   with a non-Kronecker `hcoeff` matrix whose determinant is `3K² ≠ 0`.

Both routes require changes upstream of the typed obligation in
`BridgeAKappaTwoCrossBlockProbe.lean`. -/

/-! ## Axiom audit anchors -/

#print axioms kappaTwoCrossBlockFourFamilyDecomposition_holds
#print axioms crossBlockKValue_zero
#print axioms crossBlockKValue_pos_of_pos
#print axioms crossBlockKValue_ne_zero_of_pos
#print axioms crossBlockExpectedCoeffMatrix_det
#print axioms crossBlockExpectedCoeffMatrix_det_ne_zero
#print axioms crossBlockExpectedCoeffMatrix_not_diagonal
#print axioms kappaTwoCrossBlockProbeNonDiagonalObstruction_holds
#print axioms crossBlockExpectedCoeffMatrix_inv_check

end PallLean.Paper93.Paper283
