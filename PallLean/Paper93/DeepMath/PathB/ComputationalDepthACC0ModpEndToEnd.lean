import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CompositeBTIntegration
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EndToEndBT
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CRTGatePolys

/-!
# Hard math (SYM∘AND composition count, MOD_p circuits) — unconditional quasipoly count (proved)

The Beigel–Tarui `SYM∘AND` composition count for `MOD_p`-circuits, made **unconditional**.  The corpus already proves the
Boolean composition count end-to-end (`endToEnd_BT`: support-image card `≤ (n+1)^{2^{depth+1}}`) and the *conditional*
`MOD_p` count (`modP_circuit_representation`, which takes the gate polynomials as hypotheses).  This brick discharges those
hypotheses with the concrete substitution `substP` — `una` gates interpreted as the `MOD_p` gate (`modPGate p = 1 − X^{p−1}`,
degree `p−1`, the Toda/Fermat polynomial) and `bin` gates as the bilinear Boolean interpolation (`gbP`, degree `2`).

The result: for any `MOD_p`-circuit `c` of depth `d` (odd prime `p`), the composed polynomial `substP p c` has total degree
`≤ (p−1)^{d+1}` and its monomial support (= the `AND`-terms of the `SYM∘AND` form) has `≤ (n+1)^{(p−1)^{d+1}}` distinct
features — **quasipolynomial for constant depth** — the genuine `SYM∘AND` composition count.

## What is proved (clean axioms, no `sorry`)

* **`substP`** — the `MOD_p`-circuit substitution polynomial (`una → MOD_p gate`, `bin → bilinear Boolean`).
* **`modp_endToEnd`** (PROVED) — `substP p c` has degree `≤ (p−1)^{d+1}` and monomial-support count `≤ (n+1)^{(p−1)^{d+1}}`
  (+ the sparse sum), unconditionally, for odd prime `p`.

## Honest scope

This is the unconditional `SYM∘AND` composition count for `MOD_p`-circuits (the `MOD_p` analogue of `endToEnd_BT`), via the
degree-`p−1` Toda/Fermat `MOD_p` gate.  Composite `MOD_m` (CRT over several primes) and the unconditional `NEXP ⊄ ACC⁰`
(P≠NP-strength) are **not** done here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModpEndToEnd

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitSubstitution (Circ)
open PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation (boolVal)
open PallLean.Paper93.DeepMath.PathB.ACC0CRTGatePolys (modPGate modPGate_degree)
open PallLean.Paper93.DeepMath.PathB.ACC0EndToEndBT (gbP gbP_deg)
open PallLean.Paper93.DeepMath.PathB.ACC0CompositeBTIntegration (modP_circuit_representation)

variable {n : ℕ}

/-- The `MOD_p`-circuit substitution polynomial: `una` gates become the `MOD_p` gate, `bin` gates the bilinear Boolean
interpolation. -/
noncomputable def substP (p : ℕ) : Circ n → MvPolynomial (Fin n) (ZMod p)
  | .inp i => X i
  | .cst b => C (boolVal b)
  | .una _ c => aeval ![substP p c] (modPGate p)
  | .bin g a b => aeval ![substP p a, substP p b] (gbP (R := ZMod p) g)

/-- **The unconditional `SYM∘AND` composition count for `MOD_p`-circuits (PROVED).**  For an odd prime `p` and a `MOD_p`-circuit
`c` of depth `d`, the composed polynomial has total degree `≤ (p−1)^{d+1}` and monomial-support count `≤ (n+1)^{(p−1)^{d+1}}`. -/
theorem modp_endToEnd (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) (c : Circ n) :
    (substP p c).totalDegree ≤ (p - 1) ^ (ACC0LowDegreeSubstitution.depth c + 1)
      ∧ ((substP p c).support.image (fun d => d.support)).card
          ≤ (n + 1) ^ ((p - 1) ^ (ACC0LowDegreeSubstitution.depth c + 1))
      ∧ (∑ x : Fin n → Bool, eval (fun i => (boolVal (x i) : ZMod p)) (substP p c))
          = ∑ d ∈ (substP p c).support, (substP p c).coeff d * (2 : ZMod p) ^ (n - d.support.card) :=
  modP_circuit_representation p (substP p) gbP
    (fun i => le_trans (totalDegree_X i).le (by omega))
    (fun b => by simp [substP, totalDegree_C])
    (fun g => le_trans (gbP_deg g) (by omega))
    (fun _ _ => rfl) (fun _ _ _ => rfl) c

/-!
**MOD_p composition count, proved unconditionally.**  The `SYM∘AND` `AND`-term count for `MOD_p`-circuits is quasipolynomial
(`(n+1)^{(p−1)^{d+1}}`), via the concrete degree-`p−1` Toda/Fermat `MOD_p` gate — the `MOD_p` analogue of `endToEnd_BT`.
Remaining (open, not faked): composite `MOD_m` CRT assembly and the unconditional `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not
`P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModpEndToEnd

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModpEndToEnd.modp_endToEnd
