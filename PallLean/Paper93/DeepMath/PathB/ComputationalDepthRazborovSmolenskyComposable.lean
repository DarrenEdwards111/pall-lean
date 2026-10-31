import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyInstantiate

/-!
# Beigel–Tarui, rung 16: the composable RS `OR`-approximator on polynomial inputs

Rungs 2–8 built the Razborov–Smolensky `OR`-approximator `orApproxP` over the **variables** `Xᵢ`: it approximates an
`OR` whose inputs are the input bits.  To approximate a whole *circuit* one must apply the same gadget with the sub-gates
as inputs — i.e. feed it **arbitrary polynomials** (the sub-circuit approximators), not just `Xᵢ`.  This file builds that
composable primitive:

  `orApproxComp inputs subsets` — the `OR`-approximator `1 - ∏_{S}(1 - (∑_{i∈S} inputsᵢ)^{p-1})` with the linear forms
        taken over an **arbitrary family of input polynomials** `inputs : Fin m → MvPolynomial`.
  `orApproxVal vals subsets` — its value-level counterpart, on a family of field values `vals : Fin m → F_p`.

and proves the three facts a composable gate needs:

  `orApproxComp_totalDegree_le` — **PROVED, the composition degree bound**: if every input has degree `≤ d`, the gate has
        degree `≤ (#subsets)·(p-1)·d` — degrees **multiply** by the gadget's `(#subsets)(p-1)`, so a depth-`h` tower of
        these gates reaches degree `((#subsets)(p-1))^h` (the `polylog` degree of the RS circuit approximation).
  `eval_orApproxComp` — **PROVED, the evaluation homomorphism**: evaluation commutes with composition —
        `eval φ (orApproxComp inputs subsets) = orApproxVal (fun i ↦ eval φ (inputsᵢ)) subsets`, so the gate's value is
        the gadget applied to the *evaluated* sub-inputs (the substitution semantics).
  `orApproxVal_fires` / `orApproxVal_allzero` — **PROVED, value-level correctness**: the gadget is `1` if some subset has
        nonzero input-sum (Fermat) and `0` if all subset-sums vanish — the generalisation of rungs 2/8's
        `orApprox_fires`/`orApprox_allFail` from Boolean-embedded bits to arbitrary field-valued sub-inputs.

Finally `orApproxComp_X_eq` proves `orApproxP` is exactly the variable-input special case (`inputsᵢ = Xᵢ`), so this is a
genuine *generalisation* of rung 2, not a parallel construction.

## Honest scope

This is the composable gate primitive — the `OR`-gadget applied to arbitrary sub-polynomials, with its degree
multiplication, substitution semantics, and field-level firing/vanishing — the piece the variable-only `orApproxP`
lacked.  What remains to assemble the whole-circuit RS-substituted polynomial: (i) the **recursive substitution** over a
formula (`AND` via De Morgan `¬OR(¬·,¬·)`, `NOT` exact, `OR` via this gate), giving one polynomial of degree
`((#subsets)(p-1))^depth`; and (ii) wiring rung 8's per-gate `2^{-t}` error sets through rung 7's `error_card_le` union
bound so the assembled polynomial errs on `≤ #gates·2^{n-t}` inputs.  Those two are the remaining Beigel–Tarui content;
the composite-`MOD_m` case remains the proven two-fields barrier.  Nothing here is the Beigel–Tarui reduction in full,
`NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

open MvPolynomial
open scoped Classical

variable {p : ℕ} [Fact p.Prime] {n m : ℕ}

/-- The linear form `∑_{i∈S} inputsᵢ` over an arbitrary family of input polynomials. -/
noncomputable def linComp (inputs : Fin m → MvPolynomial (Fin n) (ZMod p)) (S : Finset (Fin m)) :
    MvPolynomial (Fin n) (ZMod p) := ∑ i ∈ S, inputs i

/-- The RS gadget `(∑_{i∈S} inputsᵢ)^{p-1}` on arbitrary input polynomials. -/
noncomputable def indComp (inputs : Fin m → MvPolynomial (Fin n) (ZMod p)) (S : Finset (Fin m)) :
    MvPolynomial (Fin n) (ZMod p) := (linComp inputs S) ^ (p - 1)

/-- **The composable `OR`-approximator**: the RS gadget applied to arbitrary input polynomials `inputs`. -/
noncomputable def orApproxComp (inputs : Fin m → MvPolynomial (Fin n) (ZMod p))
    (subsets : List (Finset (Fin m))) : MvPolynomial (Fin n) (ZMod p) :=
  1 - (subsets.map (fun S => 1 - indComp inputs S)).prod

/-- The value-level `OR`-approximator on a family of field values. -/
noncomputable def orApproxVal (vals : Fin m → ZMod p) (subsets : List (Finset (Fin m))) : ZMod p :=
  1 - (subsets.map (fun S => 1 - (∑ i ∈ S, vals i) ^ (p - 1))).prod

/-- **The linear form's degree (proved)**: bounded by the max input degree. -/
theorem linComp_totalDegree_le (inputs : Fin m → MvPolynomial (Fin n) (ZMod p)) (S : Finset (Fin m))
    (d : ℕ) (hd : ∀ i, (inputs i).totalDegree ≤ d) : (linComp inputs S).totalDegree ≤ d :=
  le_trans (totalDegree_finset_sum S _) (Finset.sup_le (fun i _ => hd i))

/-- **The gadget's degree (proved)**: `(∑ inputs)^{p-1}` multiplies the input degree by `p-1`. -/
theorem indComp_totalDegree_le (inputs : Fin m → MvPolynomial (Fin n) (ZMod p)) (S : Finset (Fin m))
    (d : ℕ) (hd : ∀ i, (inputs i).totalDegree ≤ d) : (indComp inputs S).totalDegree ≤ (p - 1) * d := by
  refine le_trans (totalDegree_pow _ _) ?_
  exact Nat.mul_le_mul_left _ (linComp_totalDegree_le inputs S d hd)

/-- **The composition degree bound (proved)**: if every input has degree `≤ d`, the composed `OR`-gate has degree
`≤ (#subsets)·(p-1)·d` — degrees multiply by the gadget factor `(#subsets)(p-1)` per composition level, giving
`((#subsets)(p-1))^depth` over a depth-`depth` tower. -/
theorem orApproxComp_totalDegree_le (inputs : Fin m → MvPolynomial (Fin n) (ZMod p))
    (subsets : List (Finset (Fin m))) (d : ℕ) (hd : ∀ i, (inputs i).totalDegree ≤ d) :
    (orApproxComp inputs subsets).totalDegree ≤ subsets.length * ((p - 1) * d) := by
  refine one_sub_totalDegree_le _ _ ?_
  have hlen : (subsets.map (fun S => (1 : MvPolynomial (Fin n) (ZMod p)) - indComp inputs S)).length
      = subsets.length := List.length_map ..
  rw [← hlen]
  refine listprod_totalDegree_le _ ((p - 1) * d) (fun q hq => ?_)
  obtain ⟨S, _, rfl⟩ := List.mem_map.mp hq
  exact one_sub_totalDegree_le _ _ (indComp_totalDegree_le inputs S d hd)

/-- **The evaluation homomorphism (proved)**: evaluation commutes with the composable gate — the gate's value at `φ` is
the value-level gadget applied to the *evaluated* sub-inputs.  This is the substitution semantics: composing polynomials
then evaluating equals evaluating the sub-inputs then applying the gadget. -/
theorem eval_orApproxComp (φ : Fin n → ZMod p) (inputs : Fin m → MvPolynomial (Fin n) (ZMod p))
    (subsets : List (Finset (Fin m))) :
    (eval φ) (orApproxComp inputs subsets) = orApproxVal (fun i => (eval φ) (inputs i)) subsets := by
  simp only [orApproxComp, orApproxVal, indComp, linComp, map_sub, map_one, map_list_prod,
    List.map_map, map_pow, map_sum, Function.comp_def]

/-- **The gadget fires on a nonzero sub-sum (proved)**: if some subset `S ∈ subsets` has nonzero input-sum, the gadget is
`1` — Fermat makes that subset's factor `1 - 1 = 0`, zeroing the product.  Generalises `orApprox_fires` to field-valued
inputs. -/
theorem orApproxVal_fires (vals : Fin m → ZMod p) (subsets : List (Finset (Fin m)))
    (S : Finset (Fin m)) (hS : S ∈ subsets) (hne : (∑ i ∈ S, vals i) ≠ 0) :
    orApproxVal vals subsets = 1 := by
  simp only [orApproxVal]
  have hz : (0 : ZMod p) ∈ subsets.map (fun S => 1 - (∑ i ∈ S, vals i) ^ (p - 1)) := by
    rw [List.mem_map]
    exact ⟨S, hS, by rw [ZMod.pow_card_sub_one_eq_one hne]; ring⟩
  rw [List.prod_eq_zero hz]; ring

/-- **The gadget vanishes when all sub-sums vanish (proved)**: if every subset has zero input-sum, the gadget is `0`
(each factor is `1 - 0^{p-1} = 1`).  Generalises `orApprox_allFail` to field-valued inputs. -/
theorem orApproxVal_allzero (vals : Fin m → ZMod p) (subsets : List (Finset (Fin m)))
    (h : ∀ S ∈ subsets, (∑ i ∈ S, vals i) = 0) : orApproxVal vals subsets = 0 := by
  simp only [orApproxVal]
  rw [List.prod_eq_one]
  · ring
  · intro y hy
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hy
    rw [h S hS, zero_pow (by have := (Fact.out : p.Prime).two_le; omega : p - 1 ≠ 0)]; ring

/-- **`orApproxP` is the variable-input special case (proved)**: taking `inputsᵢ = Xᵢ` recovers rung 2's variable-only
approximator, so `orApproxComp` genuinely generalises it. -/
theorem orApproxComp_X_eq (subsets : List (Finset (Fin n))) :
    orApproxComp (fun i => X i) subsets = orApproxP (p := p) subsets := by
  simp only [orApproxComp, orApproxP, indComp, indP, linComp, linFormP]

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.orApproxComp_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.eval_orApproxComp
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.orApproxVal_fires
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.orApproxVal_allzero
