import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Mod6ProbabilisticPolynomial
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CompositeBTTarget

/-!
# Composite-`MOD` gate polynomials — the `MOD₆` local gate polynomial, exact and low-degree

The composite-`MOD` gate polynomials are the one genuinely-open `ACC⁰`-side input to the composite-BT capstone.  This
file builds the first concrete one: the **`MOD₆` local gate polynomial** over the product-residue observer.  `MOD₆` of
a count `s` is decided by the residue pair `(s mod 2, s mod 3)`, and each component is an *exact, low-degree*
polynomial:

* over `F₂`: `mod6GateF2 = 1 + X` — degree `1`, computes `[s ≡ 0 mod 2]`;
* over `F₃`: `mod6GateF3 = 1 - X²` — degree `2`, computes `[s ≡ 0 mod 3]` (Fermat).

The gate fires (both components `= 1`) iff `s = 0` in `F₂ × F₃` iff `6 ∣ s` — exactly `MOD₆`.  These are genuine
`MvPolynomial`s with proved evaluation and degree, the local gate polynomials the composite-BT representation needs.

## What is proved (clean axioms, no `sorry`)

* **`mod6GateF2` / `mod6GateF3`** — the two component gate polynomials.
* **`mod6GateF2_apply` / `mod6GateF3_apply`** — they compute the residue indicators (`1+a`, `1-b²`).
* **`mod6GateF2_degree` (≤ 1) / `mod6GateF3_degree` (≤ 2)** — they are low-degree (valid degree-`δ` gate polys).
* **`mod6Gate_decides`** — the gate fires iff `6 ∣ s`: it computes `MOD₆` of the count `s` exactly.

## Honest scope

The `MOD₆` local gate polynomials are *exact and low-degree*, with evaluation and degree proved — genuine composite-`MOD`
gate polynomials over the product-residue observer.  The remaining work is to (i) generalise to arbitrary composite
modulus via CRT (`ZMod m ≃ ∏ ZMod pᵢ^{eᵢ}`) and (ii) handle the `AND`-layer beneath each `MOD` gate via the
probabilistic `OR` polynomial + amplification (already proved), then feed the result into `compositeBT_representation`.
This builds the `MOD₆` gate polynomial; it does not yet assemble a full composite-`ACC⁰` circuit representation.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CompositeGatePolys

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0Mod6ProbabilisticPolynomial (mod2_indicator mod3_indicator)
open PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT (mod6_decided_by_residue_pair)

/-- The `MOD₂`-component gate polynomial over `F₂`: `1 + X` (degree 1). -/
noncomputable def mod6GateF2 : MvPolynomial (Fin 1) (ZMod 2) := C 1 + X 0

/-- The `MOD₃`-component gate polynomial over `F₃`: `1 - X²` (degree 2, Fermat). -/
noncomputable def mod6GateF3 : MvPolynomial (Fin 1) (ZMod 3) := C 1 - (X 0) ^ 2

/-- **`mod6GateF2` computes the `MOD₂` indicator (proved): `eval a = [a = 0]`.** -/
theorem mod6GateF2_apply (a : ZMod 2) :
    eval (fun _ => a) mod6GateF2 = if a = 0 then 1 else 0 := by
  simp only [mod6GateF2, map_add, eval_C, eval_X]
  exact mod2_indicator a

/-- **`mod6GateF3` computes the `MOD₃` indicator (proved): `eval b = [b = 0]`.** -/
theorem mod6GateF3_apply (b : ZMod 3) :
    eval (fun _ => b) mod6GateF3 = if b = 0 then 1 else 0 := by
  simp only [mod6GateF3, map_sub, map_pow, eval_C, eval_X]
  exact mod3_indicator b

/-- **`mod6GateF2` is degree `≤ 1` (proved).** -/
theorem mod6GateF2_degree : mod6GateF2.totalDegree ≤ 1 := by
  refine le_trans (totalDegree_add _ _) ?_
  simp [totalDegree_C, totalDegree_X]

/-- **`mod6GateF3` is degree `≤ 2` (proved).** -/
theorem mod6GateF3_degree : mod6GateF3.totalDegree ≤ 2 := by
  refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_)
  · simp [totalDegree_C]
  · refine le_trans (totalDegree_pow _ 2) ?_
    simp [totalDegree_X]

/-- **`mod6GateF2` fires iff `a = 0` (proved).** -/
theorem mod6GateF2_eq_one (a : ZMod 2) : eval (fun _ => a) mod6GateF2 = 1 ↔ a = 0 := by
  rw [mod6GateF2_apply]
  constructor
  · intro h; by_contra ha; rw [if_neg ha] at h; exact absurd h (by decide)
  · intro h; rw [if_pos h]

/-- **`mod6GateF3` fires iff `b = 0` (proved).** -/
theorem mod6GateF3_eq_one (b : ZMod 3) : eval (fun _ => b) mod6GateF3 = 1 ↔ b = 0 := by
  rw [mod6GateF3_apply]
  constructor
  · intro h; by_contra hb; rw [if_neg hb] at h; exact absurd h (by decide)
  · intro h; rw [if_pos h]

/-- **The `MOD₆` gate computes `MOD₆` of the count (proved): both components fire iff `6 ∣ s`.**  The product-residue
observer `(s mod 2, s mod 3)` is `(0,0)` iff `6 ∣ s`, so the two exact low-degree gate polynomials together decide
`MOD₆`. -/
theorem mod6Gate_decides (s : ℕ) :
    (eval (fun _ => (s : ZMod 2)) mod6GateF2 = 1 ∧ eval (fun _ => (s : ZMod 3)) mod6GateF3 = 1)
      ↔ 6 ∣ s := by
  rw [mod6GateF2_eq_one, mod6GateF3_eq_one]
  exact (mod6_decided_by_residue_pair s).symm

end PallLean.Paper93.DeepMath.PathB.ACC0CompositeGatePolys

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeGatePolys.mod6GateF2_apply
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeGatePolys.mod6GateF3_apply
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeGatePolys.mod6GateF2_degree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeGatePolys.mod6GateF3_degree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeGatePolys.mod6Gate_decides
