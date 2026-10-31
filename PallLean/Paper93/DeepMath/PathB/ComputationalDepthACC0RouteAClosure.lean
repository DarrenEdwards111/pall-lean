import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BTDepthCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BTRSConnection
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BTClosureFrontier

/-!
# Step 3 via Route A — the quasipolynomial BT closure, plugged into the Williams chain (proved)

Entry 217 showed the *majority*-amplification route (entries 209–217) yields an exact-but-**exponential** `SYM∘AND`, so
it is **not** the quasipolynomial path.  This file assembles **Route A** — the *direct low-degree* route — into the
BT-closure → `¬ NEXP` chain: an `AC⁰[p]` circuit has a **quasipolynomial** `SYM∘AND` form (entry 203 `btDepthCollapse`),
with the `AccToLowDeg` socket discharged from the proved RS approximation (entry 204), and this quasipolynomial closure
is plugged into the entry-166 `dynamicClosure_to_NEXP_not_ACC0` chain.

Route A vs the majority route.  Williams' fast `ACC⁰`-SAT needs a *quasipolynomial* `SYM∘AND`.  Route A delivers it:
`btQuasipolyCollapse` (203) — a degree-`≤D` representation is a `SYM∘AND` of size `≤ (D+1)·n^D` — composed with
`accToLowDeg_via_rs` (204), which supplies the degree-`((p−1)t)^d` representation from the proved
`acc0_approx_by_lowRankPredictor` (modulo the `SpanApproxToLowDegRep` span bridge, reduced by entries 205/207 to the
count-mod-`p` + amplification residuals).  This is the quasipolynomial terminus the majority route (217) cannot reach.

## What is proved (clean axioms, no `sorry`)

* **`routeA_quasipoly`** — the per-circuit assembly: an `AC⁰[p]` `BoolCircuitSyntax` circuit `C` (every `MOD` modulus
  `p`, size `4·#subcircuits ≤ p^t`, `1 ≤ n`, and the `SpanApproxToLowDegRep` bridge) has
  `∃ m, HasSymAndFormFanIn (C.eval) m (((p−1)t)^{depth}) ∧ m ≤ (((p−1)t)^{depth}+1)·n^{((p−1)t)^{depth}}` — a
  quasipolynomial `SYM∘AND` (entry 203 ∘ entry 204).
* **`RouteAClosure`** / **`routeA_closure_proved`** — the route-A closure as a `Prop` (every `AC⁰[p]` circuit, given its
  span bridge, has a quasipolynomial `SYM∘AND`), proved.
* **`routeA_btClosure_to_NEXP`** — plugs the route-A closure into the entry-166 BT-closure chain: with the Williams
  sockets (`closure → BTQuasi`, `BTQuasi → ACC0Speed`, `williams`, `hierarchy`), `¬ NEXPHasACC0Circuits` follows — the
  BT side discharged via the quasipolynomial Route A.

## Honest scope

This assembles **Route A** (quasipolynomial) into the BT-closure → `¬ NEXP` chain — the genuinely operative path for
Williams' fast-SAT, in contrast to the exponential majority route (217).  The route-A quasipolynomial `SYM∘AND` is
*proved* modulo the `SpanApproxToLowDegRep` span bridge (entry 204's residual, reduced by 205/207 to the count-mod-`p`
multiplicity + the amplification), and the chain's remaining premises (`closure → BTQuasi`, `BTQuasi → ACC0SatSpeedup`,
the Williams meta-theorem, the hierarchy) are the named **Williams-side** sockets — *not* BT content.  This is a second,
independent (`HasSymAndFormFanIn`-based) discharge of the BT-quasipoly closure, parallel to the *toAgree*-based
`DynamicClosesAtBT_AC0p` (entry 179).  This proves the route-A assembly and its chaining, not the span bridge or the
Williams sockets.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RouteAClosure

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0BTDepthCollapse (AccToLowDeg btDepthCollapse)
open PallLean.Paper93.DeepMath.PathB.ACC0BTRSConnection (SpanApproxToLowDegRep accToLowDeg_via_rs)
open PallLean.Paper93.DeepMath.PathB.ACC0SymAndFanIn (HasSymAndFormFanIn)
open scoped Classical

/-- **Route A, per circuit (PROVED).**  An `AC⁰[p]` circuit `C` (every `MOD` modulus `p`, `4·#subcircuits ≤ p^t`,
`1 ≤ n`, and the `SpanApproxToLowDegRep` span bridge) has a **quasipolynomial** `SYM∘AND` form: `∃ m,
HasSymAndFormFanIn (C.eval) m (((p−1)t)^{depth}) ∧ m ≤ (((p−1)t)^{depth}+1)·n^{((p−1)t)^{depth}}` — by `btDepthCollapse`
(entry 203, degree⇒quasipoly) applied to `accToLowDeg_via_rs` (entry 204, the RS degree-`((p−1)t)^{depth}`
representation). -/
theorem routeA_quasipoly {n : ℕ} (C : BoolCircuitSyntax n) (p t : ℕ) [Fact p.Prime]
    (ht : 1 ≤ t) (hn : 1 ≤ n)
    (hmod : ∀ q r cs, (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax n) ∈ subcircuits C → q = p)
    (hsize : 4 * (subcircuits C).toFinset.card ≤ p ^ t)
    (bridge : SpanApproxToLowDegRep C p t) :
    ∃ m, HasSymAndFormFanIn (fun x => C.eval x) m (((p - 1) * t) ^ C.depth)
      ∧ m ≤ (((p - 1) * t) ^ C.depth + 1) * n ^ (((p - 1) * t) ^ C.depth) :=
  btDepthCollapse (fun x => C.eval x) p t C.depth hn (accToLowDeg_via_rs C p t ht hmod hsize bridge)

/-- **The Route-A closure (a `Prop`).**  Every `AC⁰[p]` circuit, given its span bridge (and size/`n` hypotheses), has a
quasipolynomial `SYM∘AND` — the Route-A analogue of `DynamicClosesAtBT`, via `HasSymAndFormFanIn`. -/
def RouteAClosure (p t : ℕ) : Prop :=
  ∀ {n : ℕ} (C : BoolCircuitSyntax n),
    (∀ q r cs, (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax n) ∈ subcircuits C → q = p) →
    4 * (subcircuits C).toFinset.card ≤ p ^ t →
    SpanApproxToLowDegRep C p t →
    1 ≤ n →
    ∃ m, HasSymAndFormFanIn (fun x => C.eval x) m (((p - 1) * t) ^ C.depth)
      ∧ m ≤ (((p - 1) * t) ^ C.depth + 1) * n ^ (((p - 1) * t) ^ C.depth)

/-- **The Route-A closure is PROVED** (modulo the per-circuit span bridge), by `routeA_quasipoly`. -/
theorem routeA_closure_proved (p t : ℕ) [Fact p.Prime] (ht : 1 ≤ t) : RouteAClosure p t :=
  fun C hmod hsize bridge hn => routeA_quasipoly C p t ht hn hmod hsize bridge

/-- **Step 3 via Route A (PROVED): the quasipolynomial BT closure plugged into the Williams chain.**  The *proved*
Route-A closure feeds the entry-166 `dynamicClosure_to_NEXP_not_ACC0`: with the Williams sockets — the closure yields a
BT quasipoly-sparse representation (`closure_to_quasi`), that yields the `ACC⁰`-SAT speedup (`quasi_to_speed`), the
Williams meta-theorem (`williams`), and the nondeterministic hierarchy (`hierarchy : ¬ Collapse`) — `¬ NEXPC` follows.
The BT side is discharged via the *quasipolynomial* Route A; the remaining premises are Williams-side sockets, not BT
content. -/
theorem routeA_btClosure_to_NEXP (p t : ℕ) [Fact p.Prime] (ht : 1 ≤ t)
    {BTQuasi ACC0Speed NEXPC Collapse : Prop}
    (closure_to_quasi : RouteAClosure p t → BTQuasi)
    (quasi_to_speed : BTQuasi → ACC0Speed)
    (williams : ACC0Speed → NEXPC → Collapse)
    (hierarchy : ¬ Collapse) : ¬ NEXPC :=
  ACC0BTClosureFrontier.dynamicClosure_to_NEXP_not_ACC0
    (RouteAClosure p t) BTQuasi ACC0Speed NEXPC Collapse
    (routeA_closure_proved p t ht) closure_to_quasi quasi_to_speed williams hierarchy

end PallLean.Paper93.DeepMath.PathB.ACC0RouteAClosure

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RouteAClosure.routeA_quasipoly
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RouteAClosure.routeA_btClosure_to_NEXP
