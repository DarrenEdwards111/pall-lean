import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3DegreeComposition
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AdditiveCountBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BeigelTaruiSparsity

/-!
# Approximate Beigel–Tarui instantiation — the polylog-degree / quasipoly route

Entry 172 gave the *exact* end-to-end pipeline, whose count `(n+1)^{2^{depth+1}}` is quasipoly only for bounded depth.
This file does step (a): the **approximate** (Razborov–Smolensky probabilistic-polynomial) route, which keeps the degree
*polylog* for all constant-depth circuits, so the monomial count is genuinely quasipolynomial.  It assembles the repo's
existing pieces — the concrete RS approximant `toApprox` (`…Layer3DegreeComposition`, `∨`/`∧` via `genOrApprox`, `MOD_p`
via the Fermat indicator) and its proved degree bound `toApprox_totalDegree_le : deg ≤ ((p−1)·t)^{depth}` — with the
sparse-count machinery (`support_mem_lowDeg` + `beigelTarui_monomial_count_le`) and the quasipoly arithmetic
(`…ACC0AdditiveCountBound.count_quasipoly_of_degree_bound`).

The upgrade over the exact pipeline:
```
  exact:    degree 2^{depth+1},  count (n+1)^{2^{depth+1}}   — quasipoly only for bounded depth
  approx:   degree ((p−1)·t)^{depth} ≤ L^D,  count ≤ (n+1)^{L^D}   — polylog degree, quasipoly count (polylog L, const D)
```

## What is proved (clean axioms, no `sorry`)

* **`toApprox_monomial_count_le`** — the RS approximant has monomial-support count `≤ (n+1)^{((p−1)·t)^{depth}}`
  (degree-governed, via `support_mem_lowDeg` + `beigelTarui_monomial_count_le`).
* **`approx_endToEnd_BT`** — for `(p−1)·t ≤ L` and `depth ≤ D`: the RS approximant has total degree `≤ L^D` *and*
  monomial-support count `≤ (n+1)^{L^D}`.  For a polylog `L` (i.e. `(p−1)·t = polylog`, the RS error parameter) and a
  *constant* `D = depth`, this is **degree polylog and count quasipoly** — the BT-style low-degree sparse bound for all
  constant-depth circuits, not just bounded depth.

## Honest scope

This proves the **degree + quasipoly-count** half of the approximate BT representation, fully, from the proved RS
degree bound — the genuine upgrade from the exact route (entry 172).  The **bounded-error** half is the repo's existing
RS probabilistic machinery: the per-gate error rate `…Layer3.orApprox_error_rate` / `genOrApprox` analysis, the
substitution-error hybrid `…ACC0CircuitSubstitution.circuit_error_bound` (error `≤ size·ε`), and the averaging
`…Layer3.exists_form_few_errors` (a *fixed* low-error approximant exists).  Assembling those into a single per-input
cube-error bound on `toApprox` is the RS *agreement* content (`…Layer3` correlation lemmas, `parity_function_lower_bound`)
— cited here, not re-proved, and *not* faked into this theorem.  This is the prime-`p` (`AC⁰[p]`) route; squarefree
composite `MOD` runs it per prime over `∏ F_p` (entry 171), and prime-power `MOD` is the proven field obstruction (step
(b), the non-field mixed-radix route).  Beigel–Tarui and `NEXP ⊄ ACC⁰` (Williams 2011) are proven classical theorems —
formalisation, not an open problem.  NOT a new separation, NOT `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ApproxBTInstantiation

open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer3 (toApprox toApprox_totalDegree_le)
open PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiSparsity (beigelTarui_monomial_count_le)
open PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation (support_mem_lowDeg)

variable {n : ℕ}

/-- **The RS approximant's monomial count is degree-governed (proved): `≤ (n+1)^{((p−1)·t)^{depth}}`.**  Every
monomial-support of `toApprox p t R C` is a degree-`≤((p−1)·t)^{depth}` feature (`support_mem_lowDeg` +
`toApprox_totalDegree_le`), and there are `≤ (n+1)^{((p−1)·t)^{depth}}` such features
(`beigelTarui_monomial_count_le`). -/
theorem toApprox_monomial_count_le (p t : ℕ) [Fact p.Prime] (ht : 1 ≤ t)
    (R : (k : ℕ) → Fin t → Fin k → ZMod p) (C : BoolCircuitSyntax n) :
    ((toApprox p t R C).support.image (fun d => d.support)).card
      ≤ (n + 1) ^ (((p - 1) * t) ^ C.depth) := by
  refine le_trans (Finset.card_le_card ?_) (beigelTarui_monomial_count_le n (((p - 1) * t) ^ C.depth))
  intro S hS
  rw [Finset.mem_image] at hS
  obtain ⟨d, hd, rfl⟩ := hS
  exact support_mem_lowDeg (toApprox p t R C) (toApprox_totalDegree_le p t ht R C) hd

/-- **Approximate end-to-end BT bound (proved): polylog degree and quasipoly count.**  For `(p−1)·t ≤ L` and
`depth ≤ D`, the RS approximant `toApprox p t R C` has total degree `≤ L^D` and monomial-support count `≤ (n+1)^{L^D}`.
With a polylog RS error parameter `(p−1)·t = polylog` (so `L = polylog`) and *constant* depth `D`, this is **degree
polylog, count quasipolynomial** — the genuine BT-style low-degree sparse bound for every constant-depth circuit,
upgrading the exact route's bounded-depth-only bound. -/
theorem approx_endToEnd_BT (p t : ℕ) [Fact p.Prime] (ht : 1 ≤ t)
    (R : (k : ℕ) → Fin t → Fin k → ZMod p) (C : BoolCircuitSyntax n) (L D : ℕ)
    (hL : 1 ≤ L) (hK : (p - 1) * t ≤ L) (hdepth : C.depth ≤ D) :
    (toApprox p t R C).totalDegree ≤ L ^ D
      ∧ ((toApprox p t R C).support.image (fun d => d.support)).card ≤ (n + 1) ^ (L ^ D) := by
  refine ⟨?_, ?_⟩
  · exact le_trans (toApprox_totalDegree_le p t ht R C)
      (le_trans (Nat.pow_le_pow_left hK _) (Nat.pow_le_pow_right hL hdepth))
  · exact ACC0AdditiveCountBound.count_quasipoly_of_degree_bound n _ ((p - 1) * t) C.depth L D
      hL hK hdepth (toApprox_monomial_count_le p t ht R C)

end PallLean.Paper93.DeepMath.PathB.ACC0ApproxBTInstantiation

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ApproxBTInstantiation.toApprox_monomial_count_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ApproxBTInstantiation.approx_endToEnd_BT
