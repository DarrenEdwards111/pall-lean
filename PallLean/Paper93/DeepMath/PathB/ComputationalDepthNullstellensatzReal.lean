import Mathlib

/-!
# Genuine Nullstellensatz substrate (real polynomial certificates)

The rung-3 bundle modelled Nullstellensatz as an `abbrev` for polynomial
calculus — which is wrong: Nullstellensatz is a *static* polynomial certificate,
with no derivation tree and no size, whose only resource is *degree*.

This file replaces that placeholder with the real object over `MvPolynomial`:

* a Nullstellensatz certificate is coefficient polynomials `coeff i` with
  `∑ i, coeff i * ax i = 1`;
* its resource is the maximum total degree of the terms;
* the genuine degree accounting `degree ≤ (max coeff degree) + (max axiom degree)`
  is proved from `MvPolynomial.totalDegree_mul`;
* a degree lower bound therefore forces high-degree coefficient polynomials.

Honest scope: this is the real *static-certificate* substrate, with genuine
polynomial semantics — not the abstract resource counter.  It does **not** prove
the Tseitin/PHP Nullstellensatz degree lower bounds (those are the deep
literature results, still cited, not assumed here).  And it does not make cutting
planes or bounded-depth Frege real — those remain abstract placeholders.
-/

namespace PallLean.Paper93.DeepMath.PathB

open scoped BigOperators

variable {ι σ F : Type*} [Fintype ι] [CommRing F] [DecidableEq σ]

/-- A genuine Nullstellensatz certificate refuting the axiom polynomials `ax`:
coefficient polynomials whose combination is the constant `1`.  Static — the
resource is degree, not size. -/
structure NullstellensatzCertificate (ax : ι → MvPolynomial σ F) where
  coeff : ι → MvPolynomial σ F
  isCertificate : (∑ i, coeff i * ax i) = 1

namespace NullstellensatzCertificate

variable {ax : ι → MvPolynomial σ F}

/-- The certificate degree: the maximum total degree among the term polynomials
`coeff i * ax i`. -/
noncomputable def degree (c : NullstellensatzCertificate ax) : ℕ :=
  Finset.univ.sup (fun i => (c.coeff i * ax i).totalDegree)

/-- The maximum total degree among the coefficient polynomials. -/
noncomputable def maxCoeffDegree (c : NullstellensatzCertificate ax) : ℕ :=
  Finset.univ.sup (fun i => (c.coeff i).totalDegree)

/-- The maximum total degree among the axiom polynomials. -/
noncomputable def maxAxiomDegree (ax : ι → MvPolynomial σ F) : ℕ :=
  Finset.univ.sup (fun i => (ax i).totalDegree)

/-- **Genuine degree accounting.**  Each term `coeff i * ax i` has total degree at
most `(coeff degree) + (axiom degree)` (by `totalDegree_mul`), so the whole
certificate's degree is at most the max coefficient degree plus the max axiom
degree. -/
theorem degree_le_maxCoeff_add_maxAxiom (c : NullstellensatzCertificate ax) :
    c.degree ≤ c.maxCoeffDegree + maxAxiomDegree ax := by
  unfold degree maxCoeffDegree maxAxiomDegree
  apply Finset.sup_le
  intro i _
  calc (c.coeff i * ax i).totalDegree
      ≤ (c.coeff i).totalDegree + (ax i).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ (Finset.univ.sup fun j => (c.coeff j).totalDegree) +
          (Finset.univ.sup fun j => (ax j).totalDegree) :=
        Nat.add_le_add
          (Finset.le_sup (f := fun j => (c.coeff j).totalDegree) (Finset.mem_univ i))
          (Finset.le_sup (f := fun j => (ax j).totalDegree) (Finset.mem_univ i))

end NullstellensatzCertificate

/-- A genuine Nullstellensatz degree lower bound: every certificate refuting `ax`
has degree at least `d`. -/
def NullstellensatzDegreeLowerBoundReal (ax : ι → MvPolynomial σ F) (d : ℕ) : Prop :=
  ∀ c : NullstellensatzCertificate ax, d ≤ c.degree

/-- **Genuine consequence.**  A degree lower bound forces high-degree coefficient
polynomials: if every certificate has degree at least `d`, then for any
certificate, its max coefficient degree plus the max axiom degree is at least `d`.
With bounded-degree axioms this means the *coefficients* must carry the degree —
exactly the content of a Nullstellensatz degree lower bound. -/
theorem maxCoeffDegree_ge_of_degreeLowerBound
    {ax : ι → MvPolynomial σ F} {d : ℕ}
    (Hdeg : NullstellensatzDegreeLowerBoundReal ax d)
    (c : NullstellensatzCertificate ax) :
    d ≤ c.maxCoeffDegree + NullstellensatzCertificate.maxAxiomDegree ax :=
  le_trans (Hdeg c) c.degree_le_maxCoeff_add_maxAxiom

/-- Sharpened form with an explicit axiom-degree bound `k`: a degree lower bound
`d` with `k`-bounded axioms forces a certificate coefficient degree of at least
`d - k` (here as `d ≤ maxCoeffDegree + k`). -/
theorem maxCoeffDegree_ge_of_degreeLowerBound_of_axiomBound
    {ax : ι → MvPolynomial σ F} {d k : ℕ}
    (Hdeg : NullstellensatzDegreeLowerBoundReal ax d)
    (hax : NullstellensatzCertificate.maxAxiomDegree ax ≤ k)
    (c : NullstellensatzCertificate ax) :
    d ≤ c.maxCoeffDegree + k :=
  le_trans (maxCoeffDegree_ge_of_degreeLowerBound Hdeg c)
    (Nat.add_le_add_left hax _)

/-! ## Kernel-only axiom trace -/

#print axioms NullstellensatzCertificate.degree_le_maxCoeff_add_maxAxiom
#print axioms maxCoeffDegree_ge_of_degreeLowerBound
#print axioms maxCoeffDegree_ge_of_degreeLowerBound_of_axiomBound

end PallLean.Paper93.DeepMath.PathB
