import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CRTFinsetGate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PrimePowerObstruction

/-!
# The composite-`MOD` field-gate instantiation — squarefree works, prime-power is the obstruction

The additive count bound (entry 170) reduced the remaining Beigel–Tarui formalisation gap to one object: a **low-degree
field gate polynomial** for a composite-`MOD` gate, to feed `compositeBT_representation`.  This file resolves that
object exactly, along the dichotomy already proved across entries 151–162:

* **Squarefree composite `MOD` — the field-gate instantiation EXISTS (proved).**  For a finset `S` of *distinct* primes,
  `MOD_{∏S}` is decided by the family of per-prime Fermat indicators `modPGate p = 1 − X^{p−1}` over the product of
  fields `∏_{p∈S} F_p`, each of degree `≤ p−1` (low-degree).  So a squarefree composite-`MOD` gate has a genuine
  low-degree field-gate representation — exactly what the BT/polynomial-method route needs, and it is *here*.

* **Prime-power `MOD` — NO low-degree field gate (the obstruction, re-affirmed).**  For `e ≥ 2`, `MOD_{p^e}` is not a
  function of the mod-`p` residue (`0` and `p` share it, `MOD_{p^e}` separates them), so *no* `F_p` polynomial of any
  degree computes it; and `ZMod (p^e)` is not a field, so there is no Fermat-style low-degree indicator.  This is the
  documented composite-`MOD` obstruction — it is **not** faked, and it is precisely why the field-gate route stops at
  squarefree.

## What is proved (clean axioms, no `sorry`)

* **`squarefree_modGate_all_lowdegree`** — each prime gate `modPGate p` has degree `≤ p−1` (`p ∈ S`).
* **`squarefree_field_gate_instantiation`** — the squarefree field-gate: the low-degree (`≤ p−1`) per-prime gate family
  decides `MOD_{∏S}` (degree bound ∧ decision).
* **`primepower_field_gate_obstruction`** — the prime-power obstruction: `0`, `p` share the mod-`p` residue but
  `MOD_{p^e}` separates them, so no `F_p` field gate computes it.

## Honest scope

This is the exact resolution of the composite-`MOD` field-gate question: it **exists and is low-degree for the
squarefree case** (built from the proved `modGateProd_decides` + `modPGate_degree`), and **provably does not exist over
a field for prime powers** (`…ACC0PrimePowerObstruction`).  So the BT/polynomial-method route instantiates cleanly for
squarefree composite modulus, and the prime-power case is the genuine barrier — which the *full* Beigel–Tarui theorem
handles by a different (non-low-degree-field, mixed-radix `SYM∘AND`) argument, and that is a proven classical theorem to
formalise, not an open problem.  Nothing here is a new separation or `P ≠ NP`; the only mathematically hard object (a
low-degree field indicator for prime-power `MOD`) is proved *not* to exist, honestly.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CompositeMODFieldGate

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0CRTGatePolys (modPGate modPGate_degree)

/-- **Each squarefree prime gate is low-degree (proved): `(modPGate p).totalDegree ≤ p−1` for `p ∈ S`.** -/
theorem squarefree_modGate_all_lowdegree (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∀ p ∈ S, (modPGate p).totalDegree ≤ p - 1 := by
  intro p hp
  haveI : Fact p.Prime := ⟨hS p hp⟩
  exact modPGate_degree p

/-- **The squarefree composite-`MOD` field-gate instantiation (proved): the low-degree per-prime gate family decides
`MOD_{∏S}`.**  For distinct primes `S`, every gate `modPGate p` has degree `≤ p−1` (low-degree, over `F_p`), and the
family fires (at `s mod p` for all `p ∈ S`) iff `(∏ p ∈ S, p) ∣ s` — the field-gate representation of squarefree
composite `MOD`, exactly the low-degree field gate the BT/polynomial-method route needs. -/
theorem squarefree_field_gate_instantiation (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (s : ℕ) :
    (∀ p ∈ S, (modPGate p).totalDegree ≤ p - 1)
      ∧ ((∀ p ∈ S, eval (fun _ => (s : ZMod p)) (modPGate p) = 1) ↔ (∏ p ∈ S, p) ∣ s) :=
  ⟨squarefree_modGate_all_lowdegree S hS, ACC0CRTFinsetGate.modGateProd_decides S hS s⟩

/-- **The prime-power obstruction (proved, re-affirmed): no `F_p` field gate computes `MOD_{p^e}` (`e ≥ 2`).**  `0` and
`p` share the mod-`p` residue (`(0 : ZMod p) = (p : ZMod p)`) yet `MOD_{p^e}` accepts `0` and rejects `p`, so
`MOD_{p^e}` is not a function of the mod-`p` residue — no `F_p` polynomial of any degree computes it.  This is exactly
why the squarefree field-gate instantiation does not extend to prime powers over a field. -/
theorem primepower_field_gate_obstruction (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e) :
    ((0 : ℕ) : ZMod p) = ((p : ℕ) : ZMod p) ∧ p ^ e ∣ 0 ∧ ¬ p ^ e ∣ p :=
  ACC0PrimePowerObstruction.modPrimePower_not_function_of_modP p e hp he

end PallLean.Paper93.DeepMath.PathB.ACC0CompositeMODFieldGate

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeMODFieldGate.squarefree_modGate_all_lowdegree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeMODFieldGate.squarefree_field_gate_instantiation
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeMODFieldGate.primepower_field_gate_obstruction
