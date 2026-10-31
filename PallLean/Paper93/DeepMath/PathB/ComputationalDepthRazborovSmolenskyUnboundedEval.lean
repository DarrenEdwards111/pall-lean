import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyUnbounded

/-!
# Beigel–Tarui, rung 21: substitution semantics for the unbounded RS approximation

Rung 20 assembled the unbounded fan-in RS-substituted polynomial `uArithApprox subsets f` and bounded its degree
(the genuine fan-in-independent `((#subsets)(p-1))^depth`).  This file supplies its **substitution semantics** — the
evaluation homomorphism and the value-level firing/vanishing of the list-input gate — the foundation the correctness /
error bound (rung 22) is built on.  These are the unbounded analogues of rung 16's `eval_orApproxComp` /
`orApproxVal_fires` / `orApproxVal_allzero` and rung 17's `eval_arithApprox`.

  `linSumNVal` / `orApproxNVal` — the value-level linear form and `OR`-approximator on a **list** of field values.
  `eval_orApproxN` — **PROVED, the gate homomorphism**: `eval φ (orApproxN inputs subsets) = orApproxNVal (inputs.map
        (eval φ)) subsets` — evaluate the sub-inputs, then apply the gadget.
  `orApproxNVal_fires` / `orApproxNVal_allzero` — **PROVED**: the gadget is `1` if some subset has nonzero sub-sum
        (Fermat) and `0` if all subset-sums vanish — for arbitrary field-valued list inputs.
  `uArithApproxVal` — the value-level whole-circuit evaluator (the same recursion on field values).
  `eval_uArithApprox` — **PROVED, the circuit homomorphism**: `eval φ (uArithApprox subsets f) = uArithApproxVal subsets f
        φ` — `uArithApprox` is a genuine substitution, evaluation commuting with the gate composition at every level.

## Honest scope

This is the semantics layer for the unbounded RS substitution: `eval` commutes with the construction, and the list-input
gate fires/vanishes correctly on field values.  It carries no error content by itself — it is the algebraic bridge that
lets the correctness induction (rung 22) discharge each gate with `orApproxNVal_fires`/`orApproxNVal_allzero` under the
clean invariant `uArithApproxVal subsets g (embed∘x) = embed (g.eval x)`, exactly as rung 18 did for the binary case.
What remains after that: the per-gate `2^{n-t}` bound and the correlated-inputs whole-circuit error analysis.  The
composite-`MOD_m` case remains the proven two-fields barrier.  Nothing here is the Beigel–Tarui reduction in full,
`NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

open MvPolynomial
open scoped Classical

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- The value-level RS linear form over a `ℕ`-indexed subset of a list of field values. -/
noncomputable def linSumNVal (vals : List (ZMod p)) (S : Finset ℕ) : ZMod p := ∑ j ∈ S, vals.getD j 0

/-- The value-level RS `OR`-approximator on a list of field values. -/
noncomputable def orApproxNVal (vals : List (ZMod p)) (subsets : List (Finset ℕ)) : ZMod p :=
  1 - (subsets.map (fun S => 1 - (linSumNVal vals S) ^ (p - 1))).prod

/-- **Evaluation commutes with an indexed input (proved)**: `eval φ (inputs.getD j 0) = (inputs.map (eval φ)).getD j 0`. -/
theorem eval_getD (φ : Fin n → ZMod p) (inputs : List (MvPolynomial (Fin n) (ZMod p))) (j : ℕ) :
    (eval φ) (inputs.getD j 0) = (inputs.map (eval φ)).getD j 0 := by
  rcases lt_or_ge j inputs.length with hj | hj
  · rw [List.getD_eq_getElem inputs 0 hj,
      List.getD_eq_getElem (inputs.map (eval φ)) 0 (by rw [List.length_map]; exact hj),
      List.getElem_map]
  · rw [List.getD_eq_default inputs 0 hj,
      List.getD_eq_default (inputs.map (eval φ)) 0 (by rw [List.length_map]; exact hj), map_zero]

/-- **The linear form is a homomorphism (proved)**: `eval φ (linSumN inputs S) = linSumNVal (inputs.map (eval φ)) S`. -/
theorem eval_linSumN (φ : Fin n → ZMod p) (inputs : List (MvPolynomial (Fin n) (ZMod p)))
    (S : Finset ℕ) : (eval φ) (linSumN inputs S) = linSumNVal (inputs.map (eval φ)) S := by
  rw [linSumN, linSumNVal, map_sum]
  exact Finset.sum_congr rfl (fun j _ => eval_getD φ inputs j)

/-- **The gate homomorphism (proved)**: evaluate the sub-inputs, then apply the value-level gadget. -/
theorem eval_orApproxN (φ : Fin n → ZMod p) (inputs : List (MvPolynomial (Fin n) (ZMod p)))
    (subsets : List (Finset ℕ)) :
    (eval φ) (orApproxN inputs subsets) = orApproxNVal (inputs.map (eval φ)) subsets := by
  have hL : (subsets.map
        (fun S => (1 : MvPolynomial (Fin n) (ZMod p)) - (linSumN inputs S) ^ (p - 1))).map (eval φ)
      = subsets.map (fun S => 1 - (linSumNVal (inputs.map (eval φ)) S) ^ (p - 1)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro S _
    simp only [Function.comp_def, map_sub, map_one, map_pow, eval_linSumN]
  rw [orApproxN, orApproxNVal, map_sub, map_one, map_list_prod, hL]

/-- **The gadget fires on a nonzero sub-sum (proved)**: some subset with nonzero value-sum makes the gadget `1` (Fermat).
-/
theorem orApproxNVal_fires (vals : List (ZMod p)) (subsets : List (Finset ℕ)) (S : Finset ℕ)
    (hS : S ∈ subsets) (hne : linSumNVal vals S ≠ 0) : orApproxNVal vals subsets = 1 := by
  simp only [orApproxNVal]
  have hz : (0 : ZMod p) ∈ subsets.map (fun S => 1 - (linSumNVal vals S) ^ (p - 1)) := by
    rw [List.mem_map]
    exact ⟨S, hS, by rw [ZMod.pow_card_sub_one_eq_one hne]; ring⟩
  rw [List.prod_eq_zero hz]; ring

/-- **The gadget vanishes when all sub-sums vanish (proved)**: each factor is `1 - 0^{p-1} = 1`. -/
theorem orApproxNVal_allzero (vals : List (ZMod p)) (subsets : List (Finset ℕ))
    (h : ∀ S ∈ subsets, linSumNVal vals S = 0) : orApproxNVal vals subsets = 0 := by
  simp only [orApproxNVal]
  rw [List.prod_eq_one]
  · ring
  · intro y hy
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hy
    rw [h S hS, zero_pow (by have := (Fact.out : p.Prime).two_le; omega : p - 1 ≠ 0)]; ring

/-- The value-level whole-circuit evaluator: the same recursion on field values. -/
noncomputable def uArithApproxVal (subsets : List (Finset ℕ)) :
    UForm n → (Fin n → ZMod p) → ZMod p
  | .var i, φ => φ i
  | .unot a, φ => 1 - uArithApproxVal subsets a φ
  | .uor l, φ => orApproxNVal (l.map (fun a => uArithApproxVal subsets a φ)) subsets
  | .uand l, φ => 1 - orApproxNVal (l.map (fun a => 1 - uArithApproxVal subsets a φ)) subsets

/-- **The circuit homomorphism (proved)**: evaluating the assembled polynomial equals the value-level recursion — so
`uArithApprox` is a genuine substitution. -/
theorem eval_uArithApprox (subsets : List (Finset ℕ)) (φ : Fin n → ZMod p) :
    ∀ f : UForm n, (eval φ) (uArithApprox (p := p) subsets f) = uArithApproxVal subsets f φ
  | .var i => by simp [uArithApprox, uArithApproxVal]
  | .unot a => by
      rw [uArithApprox, map_sub, map_one, eval_uArithApprox subsets φ a, uArithApproxVal]
  | .uor l => by
      have hL : (l.map (fun a => uArithApprox (p := p) subsets a)).map (eval φ)
          = l.map (fun a => uArithApproxVal subsets a φ) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro a _
        simp only [Function.comp_def]
        exact eval_uArithApprox subsets φ a
      rw [uArithApprox, eval_orApproxN, hL, uArithApproxVal]
  | .uand l => by
      have hL : (l.map (fun a => (1 : MvPolynomial (Fin n) (ZMod p)) - uArithApprox subsets a)).map
            (eval φ)
          = l.map (fun a => 1 - uArithApproxVal subsets a φ) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro a _
        simp only [Function.comp_def, map_sub, map_one]
        rw [eval_uArithApprox subsets φ a]
      rw [uArithApprox, map_sub, map_one, eval_orApproxN, hL, uArithApproxVal]

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.eval_orApproxN
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.eval_uArithApprox
