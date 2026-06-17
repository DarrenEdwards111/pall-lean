import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3ACC0LowRank
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BTDepthCollapse

/-!
# Connecting `AccToLowDeg` to the existing Razborov–Smolensky approximation (proved)

Entry 203's BT depth-collapse proved the *degree⇒size* half (`btQuasipolyCollapse`: a degree-`≤D` representation
collapses to a quasipolynomial `SYM∘AND`) and left **`AccToLowDeg`** — that a depth-`d` `ACC⁰[p]` circuit actually *has*
a degree-`((p−1)·t)^d` representation — as the Razborov–Smolensky socket.  But the RS approximation is **already proved**
in the repository: `Layer3ACC0LowRank.acc0_approx_by_lowRankPredictor` shows that an `AC⁰[p]` circuit at horizon `t`
(with `p^t ≥ 4·#subcircuits`) has an `F_p`-span approximant of degree **exactly `((p−1)·t)^C.depth`** agreeing with the
circuit on `≥ 3/4` of inputs.  The degree matches `AccToLowDeg`'s `((p−1)·t)^d` *exactly* (`d = C.depth`).

This file makes that connection: it discharges `AccToLowDeg` from the *proved* RS approximation, reducing the original
bare socket to the precise residual **span→`SYM∘AND` representation bridge** (`SpanApproxToLowDegRep`).  The deep analytic
content — the probabilistic polynomial method — is now *supplied by the existing repo proof*, not assumed.

## What is proved (clean axioms, no `sorry`)

* **`SpanApproxToLowDegRep C p t`** — the residual bridge socket: an RS `F_p`-span approximant of `C` (degree
  `((p−1)·t)^C.depth`, `≥ 3/4` agreement) yields an exact Boolean `LowDegRep` of `C.eval` at that degree.
* **`accToLowDeg_via_rs`** — discharges `AccToLowDeg (C.eval) p t C.depth` from the size hypotheses and the bridge, by
  feeding the *proved* `acc0_approx_by_lowRankPredictor` into the bridge.

## Honest scope

This reduces the entry-203 `AccToLowDeg` socket to the **span→`SYM∘AND` bridge**, discharging the
*circuit⇒low-degree-approximant* half from the **already-proved** RS approximation (`acc0_approx_by_lowRankPredictor`,
the genuine probabilistic polynomial method, with degree `((p−1)·t)^C.depth` matching exactly).  What remains is the
**`SpanApproxToLowDegRep`** bridge — turning an `F_p`-linear span approximant (degree `D`, `3/4` agreement) into an
*exact* Boolean symmetric-of-`AND`s representation (`h ∘ saCount`).  This bridge carries the genuine BT
representation content: replacing each monomial with `≤ p−1` copies so the `F_p` value becomes a **count-mod-`p`** of
satisfied `AND`s (a symmetric top), and the amplification from the `3/4`-approximant to the exact circuit.  This file
proves the *reduction* of `AccToLowDeg` to that bridge — the RS degree is no longer assumed but taken from the existing
proof — not the bridge itself.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BTRSConnection

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.Layer3ACC0LowRank (acc0_approx_by_lowRankPredictor)
open PallLean.Paper93.DeepMath.PathB.ACC0BTDepthCollapse (LowDegRep AccToLowDeg)
open scoped Classical

variable {n : ℕ}

/-- **The residual span→`SYM∘AND` bridge socket.**  An RS `F_p`-span approximant of `C` — a function `f` in the span of
the degree-`≤((p−1)·t)^C.depth` squarefree monomials, agreeing with `C` on `≥ 3/4` of inputs — yields an *exact* Boolean
`LowDegRep` of `C.eval` at degree `((p−1)·t)^C.depth`.  This bridge carries the genuine BT representation content
(monomials with `≤ p−1` multiplicity so the value is a count-mod-`p` of satisfied `AND`s; amplification of the
`3/4`-approximant to exact).  Stated, not proved. -/
def SpanApproxToLowDegRep (C : BoolCircuitSyntax n) (p t : ℕ) : Prop :=
  (∃ f : (Fin n → Bool) → ZMod p,
      f ∈ Submodule.span (ZMod p)
          (Set.range (fun S : {S // S ∈ lowDegMonomials n (((p - 1) * t) ^ C.depth)} =>
            squarefreeEvalMonomial p S.1))
        ∧ 3 * 2 ^ n
            ≤ 4 * (Finset.univ.filter
                (fun x : Fin n → Bool => f x = boolToZMod p (C.eval x))).card)
  → LowDegRep (fun x => C.eval x) (((p - 1) * t) ^ C.depth)

/-- **Discharging `AccToLowDeg` from the proved RS approximation (PROVED).**  For an `AC⁰[p]` circuit `C` at horizon `t`
with `p^t ≥ 4·#subcircuits`, the *proved* `acc0_approx_by_lowRankPredictor` supplies the degree-`((p−1)·t)^C.depth`
`F_p`-span approximant (the Razborov–Smolensky probabilistic polynomial method), and the residual bridge
`SpanApproxToLowDegRep` turns it into the `LowDegRep` that entry-203's `AccToLowDeg` requires.  Thus the
*circuit⇒low-degree* half of `AccToLowDeg` is no longer assumed — it is taken from the existing RS proof, with the degree
`((p−1)·t)^C.depth` matching `AccToLowDeg`'s `((p−1)·t)^d` exactly (`d = C.depth`). -/
theorem accToLowDeg_via_rs (C : BoolCircuitSyntax n) (p t : ℕ) [Fact p.Prime] (ht : 1 ≤ t)
    (hmod : ∀ q r cs, (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax n) ∈ subcircuits C → q = p)
    (hsize : 4 * (subcircuits C).toFinset.card ≤ p ^ t)
    (bridge : SpanApproxToLowDegRep C p t) :
    AccToLowDeg (fun x => C.eval x) p t C.depth :=
  bridge (acc0_approx_by_lowRankPredictor p t ht C hmod hsize)

end PallLean.Paper93.DeepMath.PathB.ACC0BTRSConnection

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BTRSConnection.accToLowDeg_via_rs
