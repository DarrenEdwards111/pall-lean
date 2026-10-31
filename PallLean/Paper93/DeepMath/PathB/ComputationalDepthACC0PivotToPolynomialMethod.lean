import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3LowDegHolonomy
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3NFrameParityRS
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MODResidualObserver
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCountCharacterization

/-!
# The pivot: from the observer route to the polynomial method, on a single target

The observer / coordinate-merging programme is now proved to be **membership-bounded for `MOD`**: a coordinate's affine
contribution to a linear gate is its membership, so the membership / rank / cell-count / variable-fixing / residual
observers all reduce to the membership cell map, which has a hard-regime ceiling (it collapses *iff* two coordinates
already share a global pattern — false when patterns are injective).  `MOD` gates have no absorbing value, so no
restriction merges them.  The observer route is the wrong tool.

This file performs the pivot and lands the polynomial method **on the very same target** the observer route could not
collapse — the N-frame holonomy parity `fParity univ`.  The polynomial method's lever is *effective dimension* (degree),
not coordinate symmetry:

* **Exact separation (new):** a multivariate polynomial of total degree `< n` cannot, on the Boolean cube, equal the
  holonomy parity `x ↦ ∏ᵢ pmOne(xᵢ)`.  Proof: its cube-evaluation lies in the degree-`≤D` span `V_D`
  (`eval_mem_lowDegSpan`), but the holonomy parity escapes `V_D` (`holonomy_parity_not_lowDegEval`, effective dimension
  `≥ n`).  This is the *dimension* analogue of the observer's swap-invariance — and unlike the observer route it bites
  on `MOD`.
* **Quantitative separation (re-export):** the full Razborov–Smolensky size lower bound `2^{Ω(n^{1/2d})}` for any
  `AC⁰[p]` circuit computing `fParity univ` (`nframe_parity_target_size_lower_bound`).

So the two arcs meet at one target: where the observer route is *bounded* (hard regime, `MOD`), the polynomial method
*separates* (effective-dimension escape + RS size).  That is the content of the pivot.

## What is proved / re-exported (clean axioms, no `sorry`)

* **`lowDegree_poly_ne_holonomy_parity`** (new) — degree `< n` ⇒ the cube-evaluation `≠` the holonomy parity.
* **`holonomy_parity_escapes_lowDegSpan`** — re-export: the holonomy parity `∉ V_D` for `D < n` (effective dim `≥ n`).
* The quantitative `AC⁰[p]` size lower bound `2^{Ω(n^{1/2d})}` on `fParity univ` is
  `…Layer3NFrameParityRS.nframe_parity_target_size_lower_bound` (the RS band-counting; cited, not restated here).
* **`observer_route_no_escape_for_mod`** — re-export: the `MOD`-residual observer cannot merge distinct free
  coordinates in the hard regime (the bound the polynomial method bypasses).

## Honest scope

The polynomial method here is a genuine `PARITY ∉ AC⁰[p]` (`p` odd prime, constant depth) — a real classical theorem,
and the right tool for `MOD_p`.  Composite-modulus `AC⁰[m]` and general `ACC⁰` / `NEXP ⊄ ACC⁰` are **Williams'
algorithmic method**, a different machine, not this `F_p`-polynomial layer (the honest ceiling, per `ACC_ROADMAP.md`).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PivotToPolynomialMethod

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.Layer3LowDegHolonomy
open PallLean.Paper93.DeepMath.PathB.Layer3NFrameParityRS
open PallLean.Paper93.DeepMath.PathB.ACC0RefinedObserverModel
open PallLean.Paper93.DeepMath.PathB.ACC0MODResidualObserver
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountCharacterization

variable {n : ℕ}

/-- **Exact effective-dimension separation (proved).**  A multivariate polynomial of total degree `< n` cannot equal
the holonomy parity `x ↦ ∏ᵢ pmOne(xᵢ)` on the Boolean cube: its evaluation lands in the degree-`≤D` span `V_D`
(`eval_mem_lowDegSpan`), which the holonomy parity escapes (`holonomy_parity_not_lowDegEval`).  This is the polynomial
method's core lever — effective dimension — landing on the observer route's uncollapsible target. -/
theorem lowDegree_poly_ne_holonomy_parity (p : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    {D : ℕ} (hD : D < n) (h : MvPolynomial (Fin n) (ZMod p)) (hdeg : h.totalDegree ≤ D) :
    (fun x : Fin n → Bool => eval (fun i => boolToZMod p (x i)) h)
      ≠ (fun x : Fin n → Bool => ∏ i, pmOne p (x i)) := by
  intro heq
  have hmem := eval_mem_lowDegSpan p D h hdeg
  rw [heq] at hmem
  exact holonomy_parity_not_lowDegEval p hp2 hD hmem

/-- **The holonomy parity escapes the low-degree span (re-export): effective dimension `≥ n`.** -/
theorem holonomy_parity_escapes_lowDegSpan (p : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    {D : ℕ} (hD : D < n) :
    (fun x : Fin n → Bool => ∏ i, pmOne p (x i))
      ∉ Submodule.span (ZMod p)
        (Set.range (fun S : {S // S ∈ lowDegMonomials n D} => squarefreeEvalMonomial p S.1)) :=
  holonomy_parity_not_lowDegEval p hp2 hD

/-- **The observer route's ceiling on the same target (re-export).**  In the hard regime the `MOD`-residual observer
cannot merge distinct free coordinates — the obstruction the polynomial method bypasses via effective dimension. -/
theorem observer_route_no_escape_for_mod {k : ℕ} (ρ : Restriction n)
    (supports : Fin k → Finset (Fin n))
    (hsep : ∀ v w, PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation.SameCell supports v w → v = w)
    (v w : Fin n) (hv : ρ v = none) (hw : ρ w = none) (hne : v ≠ w) :
    residualSignature ρ supports v ≠ residualSignature ρ supports w :=
  residual_no_escape_in_hardRegime ρ supports hsep v w hv hw hne

end PallLean.Paper93.DeepMath.PathB.ACC0PivotToPolynomialMethod

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PivotToPolynomialMethod.lowDegree_poly_ne_holonomy_parity
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PivotToPolynomialMethod.holonomy_parity_escapes_lowDegSpan
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PivotToPolynomialMethod.observer_route_no_escape_for_mod
