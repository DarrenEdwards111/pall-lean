import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBeigelTaruiCompose
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBeigelTaruiSymAndFold
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyPoly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BeigelTaruiSparsity

/-!
# Beigel–Tarui, rung 15: the quasipolynomial AND count via the RS low-degree approximation

Rung 12 folded an `AND`/`OR`/`NOT` *formula* to `SYM∘AND` **exactly** — but the exact arithmetisation has degree
`≤ 2^depth` (rung 6), so its AND layer can have `(n+1)^{2^depth}` gates: **exponential**, no size win.  The
Beigel–Tarui / Razborov–Smolensky point is that one should not arithmetise a gate *exactly* — one substitutes the
**low-degree probabilistic approximator** (rungs 2–5, degree `t(p-1)`), whose composition through a depth-`d` circuit
(rung 6's additive/multiplicative bookkeeping) has degree `(t(p-1))^depth = polylog`.  This file proves the payoff of
that degree reduction at the AND-count level:

> a polynomial of total degree `≤ D` has a `SYM∘AND` fold with at most `(n+1)^D` **distinct** AND gates.

The AND layer has one gate per *distinct monomial support* (rung 9's `prod_embed`: the AND of a monomial depends only on
which variables occur, not their exponents), and every monomial support of a degree-`≤D` polynomial has cardinality
`≤ D`, so the distinct ANDs inject into the degree-`≤D` monomials counted by
`ACC0BeigelTaruiSparsity.beigelTarui_monomial_count_le` (`≤ (n+1)^D`).

  `andSupports` — the distinct AND gates of the fold: the image of `P.support` under `Finsupp.support` (one per distinct
        monomial support), the AND layer whose width is the count of interest.
  `card_support_le_totalDegree` — **PROVED**: every monomial support has cardinality `≤ P.totalDegree`.
  `andSupports_subset_lowDeg` — **PROVED**: `totalDegree P ≤ D` ⇒ the distinct ANDs are among the degree-`≤D` monomials.
  `andCount_le_quasipoly` — **PROVED, the main bound**: `totalDegree P ≤ D` ⇒ `#(distinct ANDs) ≤ (n+1)^D`.
  `arithP_andCount_le` — **PROVED**: the *exact* arithmetisation gives `≤ (n+1)^{2^depth}` ANDs — **exponential** (the
        cost of exactness, cf. rung 12).
  `orApprox_andCount_le` — **PROVED**: the RS approximator over `F_p` with `t` subsets gives `≤ (n+1)^{t(p-1)}` ANDs —
        **quasipolynomial** for `t = polylog`; the concrete degree-reduction win.

## Honest scope

This is the **count** consequence of the degree reduction: low degree `D` ⇒ quasipolynomially many distinct ANDs
(`(n+1)^D`).  It is the AND-layer analogue of the repo's monomial-count sparsity `beigelTarui_monomial_count_le`, now
tied to an actual `MvPolynomial`'s support (`andSupports`) and instantiated on both the exact arithmetisation
(exponential — `arithP_andCount_le`) and the RS approximator (quasipolynomial — `orApprox_andCount_le`), exhibiting the
degree-reduction win concretely.  What this does **not** do: build the single low-degree polynomial approximating a whole
depth-`d` `ACC⁰` circuit — rungs 7–8 supply the per-gate substitution error union bound and the averaging existence
*abstractly*; assembling them into one polynomial `Q` with `totalDegree Q ≤ (t(p-1))^depth` (then feeding it here to get
`#ANDs ≤ (n+1)^{(t(p-1))^depth}`) is the remaining Beigel–Tarui content, and the composite-`MOD_m` case remains the
proven two-fields barrier.  Nothing here is the Beigel–Tarui reduction in full, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase

open MvPolynomial
open scoped Classical
open PallLean.Paper93.DeepMath.PathB.Layer3 (lowDegMonomials)
open PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiSparsity (beigelTarui_monomial_count_le)
open PallLean.Paper93.DeepMath.PathB.RazborovSmolensky (orApproxP orApproxP_totalDegree_le)

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **The AND layer of the `SYM∘AND` fold**: one gate per *distinct monomial support*.  By rung 9's `prod_embed` the AND
of a monomial `∏ Xᵢ^{eᵢ}` depends only on its support `{i : eᵢ ≠ 0}`, so the distinct AND gates are the image of the
polynomial's support under `Finsupp.support`.  `#andSupports` is the AND-layer width. -/
def andSupports (P : MvPolynomial (Fin n) R) : Finset (Finset (Fin n)) :=
  P.support.image (fun d => d.support)

/-- **Every monomial support has cardinality `≤ totalDegree` (proved)**: a monomial's number of *distinct* variables is at
most its degree (each occurring variable contributes `≥ 1` to the exponent sum), which is at most the polynomial's total
degree. -/
theorem card_support_le_totalDegree (P : MvPolynomial (Fin n) R) {d : Fin n →₀ ℕ}
    (hd : d ∈ P.support) : d.support.card ≤ P.totalDegree := by
  have h1 : d.support.card ≤ d.sum (fun _ e => e) := by
    simp only [Finsupp.sum]
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
  exact le_trans h1 (le_totalDegree hd)

/-- **The distinct ANDs are low-degree monomials (proved)**: if `totalDegree P ≤ D` then every distinct AND gate is a
monomial support of cardinality `≤ D` — one of the `lowDegMonomials n D`. -/
theorem andSupports_subset_lowDeg {P : MvPolynomial (Fin n) R} {D : ℕ}
    (hD : P.totalDegree ≤ D) : andSupports P ⊆ lowDegMonomials n D := by
  intro s hs
  rw [andSupports, Finset.mem_image] at hs
  obtain ⟨d, hd, rfl⟩ := hs
  rw [lowDegMonomials, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.subset_univ _, le_trans (card_support_le_totalDegree P hd) hD⟩

/-- **The quasipolynomial AND count (proved)**: a total-degree-`≤D` polynomial's `SYM∘AND` fold has at most `(n+1)^D`
distinct AND gates — quasipolynomial in `n` when `D` is polylogarithmic.  This is the AND-layer payoff of the RS degree
reduction: the count of AND gates is controlled by the *degree*, not the size. -/
theorem andCount_le_quasipoly {P : MvPolynomial (Fin n) R} {D : ℕ}
    (hD : P.totalDegree ≤ D) : (andSupports P).card ≤ (n + 1) ^ D :=
  le_trans (Finset.card_le_card (andSupports_subset_lowDeg hD)) (beigelTarui_monomial_count_le n D)

/-- **Exact arithmetisation is exponential (proved)**: the *exact* `arithP` of a formula (rung 6, degree `≤ 2^depth`)
gives an AND layer of at most `(n+1)^{2^depth}` gates — **exponential** in the depth.  This is the cost of exactness that
the RS low-degree substitution is designed to avoid. -/
theorem arithP_andCount_le [Nontrivial R] (f : BForm n) :
    (andSupports (arithP (R := R) f)).card ≤ (n + 1) ^ (2 ^ depth f) :=
  andCount_le_quasipoly (arithP_totalDegree_le_two_pow_depth f)

/-- **The RS approximator is quasipolynomial (proved)**: the Razborov–Smolensky degree-reduced `OR`-approximator over
`F_p` built from `t = subsets.length` subsets (rung 2, degree `≤ t(p-1)`) gives an AND layer of at most `(n+1)^{t(p-1)}`
gates — **quasipolynomial** in `n` for `t = polylog`.  Contrast `arithP_andCount_le`: substituting the low-degree
approximator for the exact gate polynomial turns the exponential AND count into a quasipolynomial one — the degree
reduction, read at the AND-count level. -/
theorem orApprox_andCount_le {p : ℕ} [Fact p.Prime] (subsets : List (Finset (Fin n))) :
    (andSupports (orApproxP (p := p) subsets)).card ≤ (n + 1) ^ (subsets.length * (p - 1)) :=
  andCount_le_quasipoly (orApproxP_totalDegree_le subsets)

end PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase

#print axioms PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase.andCount_le_quasipoly
#print axioms PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase.arithP_andCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase.orApprox_andCount_le
