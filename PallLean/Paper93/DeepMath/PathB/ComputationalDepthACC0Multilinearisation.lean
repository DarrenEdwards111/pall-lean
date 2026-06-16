import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SparsePolyReadoff

/-!
# Multilinearisation — a bounded-degree polynomial on the Boolean cube is a sparse `AND`-feature count

The last gap in the Route-B chain: turning a degree-`≤ D` polynomial (the substituted probabilistic-polynomial
approximant) into the sparse `AND`-feature form that the read-off (`…ACC0SparsePolyReadoff`) consumes.  Over the
Boolean cube this is automatic, for two reasons:

* `x_i^k = x_i` on `{0,1}` (so every monomial collapses to its squarefree support), and
* `∏_{i∈S} x_i = \mathrm{monoAND}_S` (a monomial *is* an `AND` feature).

Hence the Boolean evaluation of any `Q : MvPolynomial (Fin n) R` is a sum over `Q`'s support of
`coeff · (AND feature over the monomial's support)`, each feature of degree `≤ totalDegree Q`, and the **cube sum** is
the closed sparse form `∑_d coeff_d · 2^{n-|supp d|}` — the sub-`2^n` count, with no enumeration of inputs.

## What is proved (clean axioms, no `sorry`)

* **`boolVal`, `boolVal_pow`** — the Boolean value `Bool → R` and the idempotence `boolVal b ^ k = boolVal b` (`k ≥ 1`).
* **`prod_boolVal_eq_andFeature`** — the atom: `∏_{i∈S} boolVal (x i) = [monoAND_S x]` (a monomial is an `AND` feature).
* **`eval_boolean_eq_sparse`** — `eval (boolVal ∘ x) Q = ∑_{d∈Q.support} coeff_d · [monoAND_{supp d} x]`: every
  bounded polynomial evaluates on the cube to a sparse sum of `AND` features (the multilinearisation).
* **`multilinear_cube_sum`** — `∑ₓ eval (boolVal ∘ x) Q = ∑_{d∈Q.support} coeff_d · 2^{n-|supp d|}`: the cube sum is a
  closed sparse count (reusing `monoAND_cube_sum`) — the sub-`2^n` `ACC⁰`-`SAT` count, now for a genuine
  `MvPolynomial`.
* **`support_mem_lowDeg`** — each monomial's support is a degree-`≤ D` feature: `d ∈ Q.support`, `totalDegree Q ≤ D`
  ⇒ `supp d ∈ lowDegMonomials n D` (so the features number `≤ (n+1)^D`).

## Honest scope

This closes the multilinearisation: a bounded-degree polynomial on the cube *is* a sparse low-degree `AND`-feature sum
with a closed sparse cube count.  What remains outside this file is purely the *modelling* link — the circuit
substitution (`…ACC0CircuitSubstitution`) was stated for `Bool`-valued approximants; identifying that approximant with
an actual `MvPolynomial` (so this theorem applies verbatim) is the remaining engineering, and the abstract
`williams`/`hierarchy` inputs stay the named Route-B sockets.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation

open scoped Classical BigOperators
open Finset MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0SparseCounting
open PallLean.Paper93.DeepMath.PathB.Layer3

variable {n : ℕ}

/-- The Boolean value `true ↦ 1`, `false ↦ 0` in a commutative ring. -/
def boolVal {R : Type*} [CommRing R] (b : Bool) : R := if b then 1 else 0

/-- An `AND` feature as a ring element: `[monoAND_S x]`. -/
def andFeature {R : Type*} [CommRing R] (S : Finset (Fin n)) (x : Fin n → Bool) : R :=
  if monoAND S x = true then 1 else 0

/-- **Boolean idempotence (proved): `boolVal b ^ k = boolVal b` for `k ≥ 1`.**  (`x_i^k = x_i` on `{0,1}`.) -/
theorem boolVal_pow {R : Type*} [CommRing R] (b : Bool) {k : ℕ} (hk : 0 < k) :
    (boolVal b : R) ^ k = boolVal b := by
  cases b with
  | false => simp [boolVal, zero_pow hk.ne']
  | true => simp [boolVal]

/-- **A monomial is an `AND` feature (proved): `∏_{i∈S} boolVal (x i) = [monoAND_S x]`.** -/
theorem prod_boolVal_eq_andFeature {R : Type*} [CommRing R] (S : Finset (Fin n))
    (x : Fin n → Bool) :
    (∏ i ∈ S, (boolVal (x i) : R)) = andFeature S x := by
  unfold andFeature
  by_cases h : ∀ i ∈ S, x i = true
  · rw [if_pos (by simp only [monoAND, decide_eq_true_eq]; exact h)]
    exact Finset.prod_eq_one (fun i hi => by simp [boolVal, h i hi])
  · push_neg at h
    obtain ⟨i, hiS, hxi⟩ := h
    rw [if_neg (by simp only [monoAND, decide_eq_true_eq]; exact fun hall => hxi (hall i hiS))]
    refine Finset.prod_eq_zero hiS ?_
    cases hx : x i with
    | true => exact absurd hx hxi
    | false => simp [boolVal]

/-- **The multilinearisation (proved): a bounded polynomial evaluates on the cube to a sparse `AND`-feature sum.**
`eval (boolVal ∘ x) Q = ∑_{d∈Q.support} coeff_d · [monoAND_{supp d} x]`.  Each non-squarefree monomial collapses to its
support feature via `boolVal_pow` and `prod_boolVal_eq_andFeature`. -/
theorem eval_boolean_eq_sparse {R : Type*} [CommRing R] (Q : MvPolynomial (Fin n) R)
    (x : Fin n → Bool) :
    eval (fun i => (boolVal (x i) : R)) Q
      = ∑ d ∈ Q.support, Q.coeff d * andFeature d.support x := by
  rw [eval_eq]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  congr 1
  rw [← prod_boolVal_eq_andFeature d.support x]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  exact boolVal_pow (x i) (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))

/-- **The closed sparse cube count (proved): `∑ₓ eval (boolVal ∘ x) Q = ∑_{d∈Q.support} coeff_d · 2^{n-|supp d|}`.**
The cube sum of a bounded polynomial is a sparse weighted count over its support — the sub-`2^n` `ACC⁰`-`SAT` count for
a genuine `MvPolynomial` (reusing `monoAND_cube_sum`). -/
theorem multilinear_cube_sum {R : Type*} [CommRing R] (Q : MvPolynomial (Fin n) R) :
    (∑ x : Fin n → Bool, eval (fun i => (boolVal (x i) : R)) Q)
      = ∑ d ∈ Q.support, Q.coeff d * (2 : R) ^ (n - d.support.card) := by
  simp_rw [eval_boolean_eq_sparse, andFeature]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [← Finset.mul_sum, monoAND_cube_sum d.support]

/-- **Each monomial's support is a low-degree feature (proved): `d ∈ Q.support`, `totalDegree Q ≤ D ⇒ supp d ∈
lowDegMonomials n D`.**  Hence the multilinearised features number `≤ (n+1)^D` (Beigel–Tarui). -/
theorem support_mem_lowDeg {R : Type*} [CommRing R] (Q : MvPolynomial (Fin n) R) {D : ℕ}
    (hD : Q.totalDegree ≤ D) {d : Fin n →₀ ℕ} (hd : d ∈ Q.support) :
    d.support ∈ lowDegMonomials n D := by
  rw [lowDegMonomials, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨Finset.subset_univ _, ?_⟩
  calc d.support.card
      ≤ d.sum (fun _ e => e) := by
        show d.support.card ≤ ∑ i ∈ d.support, d i
        rw [Finset.card_eq_sum_ones]
        exact Finset.sum_le_sum
          (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
    _ ≤ Q.totalDegree := le_totalDegree hd
    _ ≤ D := hD

end PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation.boolVal_pow
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation.prod_boolVal_eq_andFeature
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation.eval_boolean_eq_sparse
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation.multilinear_cube_sum
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation.support_mem_lowDeg
