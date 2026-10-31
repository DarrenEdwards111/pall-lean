import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CompositeBTCapstone
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CRTGatePolys

/-!
# Integration — the `MOD_p` gate polynomials feed `compositeBT_representation`

This wires the composite-`MOD` gate polynomials (`…ACC0CRTGatePolys.modPGate`) into the composite-BT capstone
(`…ACC0CompositeBTCapstone.compositeBT_representation`).  The key fact: the `MOD_p` gate polynomial `modPGate p` has
total degree `≤ p−1` (proved), so it is a valid degree-`(p−1)` gate polynomial.  Hence a circuit whose unary gates are
`MOD_p` (composed via `aeval`) gets the **quasipolynomial low-degree sparse representation** with `δ = p−1`:

* total degree `≤ (p−1)^{depth+1}`,
* `≤ (n+1)^{(p−1)^{depth+1}}` distinct features,
* the sparse cube count.

For constant depth, `(p−1)^{O(1)}` is `polylog`, so the representation is genuinely quasipolynomial — the composite-`MOD`
algebraic observer feeding the Williams sparse read-off.

## What is proved (clean axioms, no `sorry`)

* **`modP_circuit_representation`** — a `MOD_p`-gate circuit (unary gates `= modPGate p`, binary gates of degree
  `≤ p−1`) has the composite-BT representation with `δ = p−1`, by instantiating `compositeBT_representation` with the
  proved gate degree `modPGate_degree`.

## Honest scope

This is the genuine integration brick: the composite-`MOD` gate polynomials are *valid degree-`δ` gate polynomials* for
the composite-BT pipeline (`δ = p−1`), and a `MOD_p` circuit gets the quasipolynomial representation.  The binary gates
(`AND`/`OR`) are kept as a degree-`≤ p−1` parameter (their polynomials and the `OR` probabilistic-polynomial layer are
proved separately).  The error side is the separate calibrated bound.  This does not assemble a full composite-`ACC⁰`
lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CompositeBTIntegration

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0CRTGatePolys (modPGate modPGate_degree)

/-- **The `MOD_p` gate polynomials feed `compositeBT_representation` (proved).**  A circuit whose unary gates are the
`MOD_p` gate `modPGate p` (degree `≤ p−1`, by `modPGate_degree`) and whose binary gates have degree `≤ p−1`, composed
via `aeval`, has the quasipolynomial low-degree sparse representation with `δ = p−1`. -/
theorem modP_circuit_representation {n : ℕ} (p : ℕ) [Fact p.Prime]
    (Q : ACC0CircuitSubstitution.Circ n → MvPolynomial (Fin n) (ZMod p))
    (gb : (Bool → Bool → Bool) → MvPolynomial (Fin 2) (ZMod p))
    (hinp : ∀ i, (Q (.inp i)).totalDegree ≤ p - 1) (hcst : ∀ b, (Q (.cst b)).totalDegree ≤ p - 1)
    (hgb : ∀ g, (gb g).totalDegree ≤ p - 1)
    (huna_eq : ∀ f c, Q (.una f c) = aeval ![Q c] (modPGate p))
    (hbin_eq : ∀ g a b, Q (.bin g a b) = aeval ![Q a, Q b] (gb g))
    (c : ACC0CircuitSubstitution.Circ n) :
    (Q c).totalDegree ≤ (p - 1) ^ (ACC0LowDegreeSubstitution.depth c + 1)
      ∧ ((Q c).support.image (fun d => d.support)).card
          ≤ (n + 1) ^ ((p - 1) ^ (ACC0LowDegreeSubstitution.depth c + 1))
      ∧ (∑ x : Fin n → Bool,
            eval (fun i => (ACC0Multilinearisation.boolVal (x i) : ZMod p)) (Q c))
          = ∑ d ∈ (Q c).support, (Q c).coeff d * (2 : ZMod p) ^ (n - d.support.card) :=
  ACC0CompositeBTCapstone.compositeBT_representation Q (fun _ => modPGate p) gb (p - 1)
    (by have := (Fact.out : p.Prime).two_le; omega) hinp hcst
    (fun _ => modPGate_degree p) hgb huna_eq hbin_eq c

end PallLean.Paper93.DeepMath.PathB.ACC0CompositeBTIntegration

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeBTIntegration.modP_circuit_representation
