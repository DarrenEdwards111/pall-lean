import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCompositeModPoly

/-!
# Composite `MOD_m`: the gate as a genuine `MvPolynomial`, with its degree

Rung 5 (`…CompositeModPoly`) wrote a `MOD_m` gate as `m⁻¹ ∑_{j<m} ∏ᵢ (1 + (ζʲ-1)·[xᵢ])` — a value-level identity.  This
file promotes it to an actual **`MvPolynomial (Fin n) K`** and pins its **total degree**, grounding the char-sum
arithmetisation in the polynomial framework the degree analysis needs.

  `charTerm ζ` — the multilinear polynomial `∏ᵢ (1 + C(ζ-1)·Xᵢ)`.
  `charTerm_totalDegree_le` — **PROVED**: `deg (charTerm ζ) ≤ n` (a product of `n` degree-`≤1` factors).
  `eval_charTerm` — **PROVED**: evaluating at the embedded bits gives the value-level product.
  `modPoly m ζ` — the `MOD_m` gate polynomial `C(m⁻¹) · ∑_{j<m} charTerm (ζʲ)`.
  `modPoly_totalDegree_le` — **PROVED**: `deg (modPoly m ζ) ≤ n`.
  `eval_modPoly` — **PROVED, the grounding**: over a field with a primitive `m`-th root `ζ`, `modPoly m ζ` evaluates to the
        `MOD_m` zero-indicator `[m ∣ count]` on every Boolean input — an actual degree-`≤n` polynomial computing `MOD_m`,
        **valid for composite `m`**.

## Honest scope — the degree the reduction must lower

This makes the single `MOD_m` gate a concrete `MvPolynomial` of total degree `≤ n` computing the gate exactly (composite
`m` included).  Degree `n` is precisely the quantity the Beigel–Tarui / Toda **degree reduction** must bring down to
`polylog` — by low-degree *approximation* of the products through a depth-`d` circuit, so the final `SYM⁺` polynomial has
quasipolynomially many monomials.  That circuit-level degree reduction is the `NEXP`-strength open piece, **not**
established here.  This file supplies the exact degree-`n` polynomial and states, precisely, the degree that must fall.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CompositeMod

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- The multilinear polynomial `∏ᵢ (1 + C(ζ-1)·Xᵢ)` — the arithmetisation of `ζ^{count}`. -/
noncomputable def charTerm (ζ : K) : MvPolynomial (Fin n) K :=
  ∏ i, (1 + C (ζ - 1) * X i)

/-- **`charTerm` has degree `≤ n` (proved)**: a product of `n` degree-`≤1` factors. -/
theorem charTerm_totalDegree_le (ζ : K) : (charTerm (n := n) ζ).totalDegree ≤ n := by
  refine le_trans (totalDegree_finset_prod _ _) ?_
  calc ∑ i : Fin n, (1 + C (ζ - 1) * X i).totalDegree
      ≤ ∑ _i : Fin n, 1 := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
        · simp [totalDegree_one]
        · exact le_trans (totalDegree_mul _ _)
            (by rw [totalDegree_C, zero_add]; exact (totalDegree_X i).le)
    _ = n := by simp

/-- **Evaluation of `charTerm` (proved)**: at the embedded bits it is the value-level product. -/
theorem eval_charTerm (ζ : K) (x : Fin n → Bool) :
    (eval (fun i => (if x i then 1 else 0 : K))) (charTerm ζ)
      = ∏ i, (1 + (ζ - 1) * (if x i then 1 else 0)) := by
  rw [charTerm, map_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp [map_add, map_mul, map_one, eval_C, eval_X]

/-- The `MOD_m` gate polynomial: `C(m⁻¹) · ∑_{j<m} charTerm (ζʲ)`. -/
noncomputable def modPoly (m : ℕ) (ζ : K) : MvPolynomial (Fin n) K :=
  C ((m : K)⁻¹) * ∑ j ∈ Finset.range m, charTerm (ζ ^ j)

/-- **`modPoly` has degree `≤ n` (proved)**. -/
theorem modPoly_totalDegree_le (m : ℕ) (ζ : K) : (modPoly (n := n) m ζ).totalDegree ≤ n := by
  refine le_trans (totalDegree_mul _ _) ?_
  rw [totalDegree_C, zero_add]
  refine le_trans (totalDegree_finset_sum _ _) (Finset.sup_le (fun j _ => ?_))
  exact charTerm_totalDegree_le _

/-- **The grounding (proved)**: over a field with a primitive `m`-th root `ζ`, the degree-`≤n` polynomial `modPoly m ζ`
evaluates to the `MOD_m` zero-indicator `[m ∣ count]` on every Boolean input — an exact polynomial for the gate, valid for
composite `m`. -/
theorem eval_modPoly {m : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ m) (hm : (m : K) ≠ 0)
    (x : Fin n → Bool) :
    (eval (fun i => (if x i then 1 else 0 : K))) (modPoly m ζ)
      = if m ∣ boolCount x then 1 else 0 := by
  rw [modPoly, map_mul, eval_C, map_sum]
  rw [← modZero_charsum_poly hζ hm x]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => eval_charTerm _ x)

end PallLean.Paper93.DeepMath.PathB.CompositeMod

#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.charTerm_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.modPoly_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.eval_modPoly
