import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SubstitutionPoly

/-!
# Low-degree substitution — low degree survives constant-depth composition

The exact substitution (`…ACC0SubstitutionPoly.subst`) computes the circuit but at high degree.  Fusing in the
*low-degree probabilistic* gate polynomials trades exactness for low degree, and the quantitative crux is: **the degree
multiplies by the per-gate factor and so stays `δ^{depth}` for constant depth.**  This file proves that
degree-composition recurrence — the degree analogue of `…ACC0CircuitSubstitution.circuit_error_bound` (which already
gives total error `≤ size·ε`).

For any polynomial assignment `Q : Circ → MvPolynomial` whose every gate raises total degree by at most a factor `δ`
(`totalDegree (Q gate) ≤ δ · max(child degrees)`, the per-gate bound the probabilistic polynomials provide — `OR`
amplified has degree `t(p-1)`, `MOD` has degree `p-1`), the whole-circuit polynomial has

\[ \mathrm{totalDegree}\,(Q\,c) \;\le\; \delta^{\,\mathrm{depth}(c)+1}, \]

quasipolynomial for constant depth.  Combined with the multilinearisation feature bound, every feature is then a
degree-`≤ δ^{depth+1}` `AND`, so the features number `≤ (n+1)^{δ^{depth+1}}` — the quasipolynomial sparse count.

## What is proved (clean axioms, no `sorry`)

* **`depth`** — circuit depth.
* **`psubst_degree`** — the degree-composition recurrence: per-gate factor `δ` ⇒ `totalDegree (Q c) ≤ δ^{depth c + 1}`
  (structural induction; low degree survives composition).
* **`psubst_features_lowDeg`** — hence every feature of `Q c` is a degree-`≤ δ^{depth c + 1}` support (in
  `lowDegMonomials`), via `support_mem_lowDeg` — the quasipolynomial feature bound for constant depth.

## Honest scope

The degree recurrence and the feature bound are *proved*.  The per-gate degree factor (`totalDegree (Q gate) ≤ δ·max`)
is the **hypothesis** — the interface to the gate polynomials, exactly as `circuit_error_bound` takes the per-gate
error as hypothesis; it is what the actual probabilistic `OR`/`MOD` polynomials satisfy (Mathlib has no general
`totalDegree`-of-composition lemma, so this factor is stated rather than re-derived from `bind₁`).  The error half is
`circuit_error_bound`; together they give a low-degree, low-error polynomial, and the abstract `williams`/`hierarchy`
Props remain the named Route-B sockets keeping the final implication conditional.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0LowDegreeSubstitution

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitSubstitution

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The depth of a circuit. -/
def depth : Circ n → ℕ
  | .inp _ => 0
  | .cst _ => 0
  | .una _ c => depth c + 1
  | .bin _ a b => max (depth a) (depth b) + 1

/-- **The degree-composition recurrence (proved): low degree survives composition.**  If every gate of the polynomial
assignment `Q` raises total degree by at most the factor `δ` (and leaves have degree `≤ δ`), then the whole-circuit
polynomial has `totalDegree (Q c) ≤ δ^{depth c + 1}` — quasipolynomial for constant depth.  (Structural induction; the
degree analogue of `circuit_error_bound`.) -/
theorem psubst_degree (Q : Circ n → MvPolynomial (Fin n) R) (δ : ℕ) (hδ : 1 ≤ δ)
    (hinp : ∀ i, (Q (.inp i)).totalDegree ≤ δ)
    (hcst : ∀ b, (Q (.cst b)).totalDegree ≤ δ)
    (huna : ∀ f c, (Q (.una f c)).totalDegree ≤ δ * (Q c).totalDegree)
    (hbin : ∀ g a b, (Q (.bin g a b)).totalDegree ≤ δ * max (Q a).totalDegree (Q b).totalDegree)
    (c : Circ n) : (Q c).totalDegree ≤ δ ^ (depth c + 1) := by
  induction c with
  | inp i => simpa [depth, pow_one] using hinp i
  | cst b => simpa [depth, pow_one] using hcst b
  | una f c ih =>
      calc (Q (.una f c)).totalDegree
          ≤ δ * (Q c).totalDegree := huna f c
        _ ≤ δ * δ ^ (depth c + 1) := Nat.mul_le_mul (le_refl δ) ih
        _ = δ ^ (depth c + 1 + 1) := (pow_succ' δ (depth c + 1)).symm
        _ = δ ^ (depth (.una f c) + 1) := by simp only [depth]
  | bin g a b iha ihb =>
      have hmax : max (Q a).totalDegree (Q b).totalDegree ≤ δ ^ (max (depth a) (depth b) + 1) := by
        rw [Nat.max_le]
        exact ⟨le_trans iha (Nat.pow_le_pow_right hδ (Nat.succ_le_succ (le_max_left _ _))),
               le_trans ihb (Nat.pow_le_pow_right hδ (Nat.succ_le_succ (le_max_right _ _)))⟩
      calc (Q (.bin g a b)).totalDegree
          ≤ δ * max (Q a).totalDegree (Q b).totalDegree := hbin g a b
        _ ≤ δ * δ ^ (max (depth a) (depth b) + 1) := Nat.mul_le_mul (le_refl δ) hmax
        _ = δ ^ (max (depth a) (depth b) + 1 + 1) := (pow_succ' δ _).symm
        _ = δ ^ (depth (.bin g a b) + 1) := by simp only [depth]

/-- **The quasipolynomial feature bound (proved): every feature is a degree-`≤ δ^{depth+1}` `AND`.**  Under the
degree-composition hypotheses, each monomial of `Q c` has support in `lowDegMonomials n (δ^{depth c + 1})` — so the
features number `≤ (n+1)^{δ^{depth c + 1}}`, quasipolynomial for constant depth. -/
theorem psubst_features_lowDeg (Q : Circ n → MvPolynomial (Fin n) R) (δ : ℕ) (hδ : 1 ≤ δ)
    (hinp : ∀ i, (Q (.inp i)).totalDegree ≤ δ)
    (hcst : ∀ b, (Q (.cst b)).totalDegree ≤ δ)
    (huna : ∀ f c, (Q (.una f c)).totalDegree ≤ δ * (Q c).totalDegree)
    (hbin : ∀ g a b, (Q (.bin g a b)).totalDegree ≤ δ * max (Q a).totalDegree (Q b).totalDegree)
    (c : Circ n) {d : Fin n →₀ ℕ} (hd : d ∈ (Q c).support) :
    d.support ∈ Layer3.lowDegMonomials n (δ ^ (depth c + 1)) :=
  ACC0Multilinearisation.support_mem_lowDeg (Q c)
    (psubst_degree Q δ hδ hinp hcst huna hbin c) hd

end PallLean.Paper93.DeepMath.PathB.ACC0LowDegreeSubstitution

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LowDegreeSubstitution.psubst_degree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LowDegreeSubstitution.psubst_features_lowDeg
