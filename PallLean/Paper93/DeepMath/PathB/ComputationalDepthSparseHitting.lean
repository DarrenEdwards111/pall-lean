import PallLean.Paper93.DeepMath.PathB.ComputationalDepthJuntaCovering

/-!
# Toward sparse-polynomial hitting sets: few variables ⟹ few monomials, and the Klivans–Spielman gap

`JuntaHitting`/`JuntaCovering` gave a fully-closed small hitting set for `k`-juntas (few *variables*).
The next class up is **sparse** polynomials — few *monomials*.  This file (a) proves that the junta
class sits inside the sparse class (few variables + bounded degree ⟹ few monomials), and (b) names the
sparse-hitting-set object whose construction is the open Klivans–Spielman target.

* **`support_card_le` (proved)** — a `k`-variable polynomial with all exponents `≤ d` has at most
  `(d+1)ᵏ` monomials.  (Inject each monomial into the bounded exponent grid `Fin k → Fin (d+1)`;
  monomials are determined by their exponent vectors, so the map is injective.)
* **`IsSparse`** — `p` is `s`-sparse iff it has at most `s` monomials.
* **`junta_is_sparse` (proved)** — a `k`-junta `rename e q` with `q`'s exponents `≤ d` is
  `(d+1)ᵏ`-sparse (injective renaming preserves the monomial count).  So bounded-degree juntas *are*
  sparse: the junta hitting set already covers a slice of the sparse class.
* **`SparseHittingFamily`** — the target object: a hitting-set family for `s`-sparse degree-`≤ d`
  polynomials, of size `poly(n,d,s)`.

**Honest scope.**  The proved content is the containment junta ⊆ sparse (few variables ⟹ few
monomials) — real and unconditional.  What is **only defined, not constructed**, is
`SparseHittingFamily`: building one is exactly **Klivans–Spielman sparse `PIT`**, whose engine is an
*isolation* substitution (a Kronecker / prime-modulus map that makes a single monomial survive,
reducing sparse multivariate `PIT` to a univariate test).  That isolation step is the open,
research-level content and is **not** formalized here — it is named as the gap.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SparseHitting

open PallLean.Paper93.DeepMath.PathB.SchwartzZippel

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Few variables + bounded degree ⟹ few monomials (proved).**  A polynomial in `k` variables all of
whose monomials have every exponent `≤ d` has at most `(d+1)ᵏ` monomials: the monomial-to-exponent-
vector map into `Fin k → Fin (d+1)` is injective (a monomial is determined by its exponents). -/
theorem support_card_le {k d : ℕ} (q : MvPolynomial (Fin k) F)
    (hdeg : ∀ m ∈ q.support, ∀ i, m i ≤ d) :
    q.support.card ≤ (d + 1) ^ k := by
  classical
  have hcard : q.support.card ≤ (Finset.univ : Finset (Fin k → Fin (d + 1))).card := by
    apply Finset.card_le_card_of_injOn
      (fun m => (fun i => (⟨min (m i) d, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (d + 1))))
    · intro m _; exact Finset.mem_univ _
    · intro m hm m' hm' h
      apply Finsupp.ext
      intro i
      have hi : min (m i) d = min (m' i) d := by
        have hc := congrFun h i
        simpa [Fin.ext_iff] using hc
      rwa [min_eq_left (hdeg m (Finset.mem_coe.mp hm) i),
        min_eq_left (hdeg m' (Finset.mem_coe.mp hm') i)] at hi
  rwa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hcard

/-- **`p` is `s`-sparse**: it has at most `s` monomials. -/
def IsSparse {n : ℕ} (s : ℕ) (p : MvPolynomial (Fin n) F) : Prop :=
  p.support.card ≤ s

/-- **Bounded-degree `k`-juntas are sparse (proved).**  A `k`-junta `rename e q`, with every exponent
of `q` at most `d`, is `(d+1)ᵏ`-sparse: injective renaming relocates monomials without merging them, so
the monomial count is that of `q`, bounded by `support_card_le`.  Hence the junta hitting set already
covers a slice of the sparse class. -/
theorem junta_is_sparse {k n d : ℕ} (e : Fin k ↪ Fin n) (q : MvPolynomial (Fin k) F)
    (hdeg : ∀ m ∈ q.support, ∀ i, m i ≤ d) :
    IsSparse ((d + 1) ^ k) (MvPolynomial.rename (⇑e) q) := by
  classical
  unfold IsSparse
  rw [MvPolynomial.support_rename_of_injective e.injective,
    Finset.card_image_of_injective _ (Finsupp.mapDomain_injective e.injective)]
  exact support_card_le q hdeg

/-- **The sparse hitting-set target (defined, not constructed).**  A hitting-set family for `s`-sparse
degree-`≤ d` polynomials in `n` variables, of size polynomial in `n, d, s`.  Constructing an instance
is Klivans–Spielman sparse `PIT` — its engine is the *isolation* substitution, the open step. -/
structure SparseHittingFamily (n : ℕ) where
  /-- The hitting set for sparsity bound `s` and degree bound `d`. -/
  H : ℕ → ℕ → Finset (Fin n → F)
  /-- It hits every nonzero `s`-sparse polynomial of total degree `≤ d`. -/
  hits : ∀ s d, ∀ p : MvPolynomial (Fin n) F, p ≠ 0 → IsSparse s p → p.totalDegree ≤ d →
    ∃ f ∈ H s d, MvPolynomial.eval f p ≠ 0
  /-- Polynomial-size constant and exponent. -/
  c : ℕ
  e : ℕ
  /-- The size is `poly(n,d,s)`. -/
  poly : ∀ s d, (H s d).card ≤ c * (n + s + d + 1) ^ e

end PallLean.Paper93.DeepMath.PathB.SparseHitting

#print axioms PallLean.Paper93.DeepMath.PathB.SparseHitting.support_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.SparseHitting.junta_is_sparse
