import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTwoFields

/-!
# The prime-power flattening fires: `MOD_p∘AND = 1 − (∑AND)^{|F|−1}` on the cube

The depth-3 rung located the composite barrier at the *middle-layer flattening*: turning a `MOD_p∘AND` gate into a
low-degree monomial-`AND` family so the fast-SAT cell count is over the bottom `AND`s.  This file **fires that
arithmetisation** for the prime-power (char-matching) case, extending C15's `charModFn_eq_boolFn` from inputs to `AND`
gates.

Over a finite field `F` of characteristic `p`, an `AND` gate `monoAND S` equals its monomial's cube-evaluation
(`evalMonomial_eq_monoAND`), and the count of accepting `AND`s in `F` is the count mod `p`.  Fermat
(`a^{|F|−1} = [a≠0]`) then gives:

  `charModAndFn_eq_boolFn` — `[#(accepting AND gates) ≡ 0 mod p]  =  boolFn (1 − (∑_j ∏_{i∈S_j} Xᵢ)^{|F|−1})` on the cube.
  `totalDegree_charModAndPoly_le` — that polynomial has total degree `≤ (|F|−1)·D` for `AND` fan-in `≤ D`.
  `nframeComplexity_charModAndFn_le` — hence `NFrameComplexity (MOD_p∘AND) ≤ (|F|−1)·D` (LOW).

So a `MOD_p∘AND` middle gate **flattens** to a degree-`(|F|−1)·D` polynomial — an exact low-degree monomial-`AND`
family on the cube.  This is the genuine Beigel–Tarui/Razborov–Smolensky arithmetisation *firing* for prime-power `MOD`
matched to the field characteristic — the middle-layer flattening the depth-3 rung needed.

## Honest scope — where it forks

The Fermat step needs `[∑ = 0 in F] = [count ≡ 0 mod p]`, i.e. the modulus **matches the characteristic** `p`.  For a
middle modulus `b` coprime to `p`, the count in `F` is `count mod p ≠ count mod b`, and no low-degree `F`-polynomial of
the count captures `MOD_b` (C14/C15/C16) — the flattening fails, and that is exactly the composite fork.  So: prime-power
`MOD` matched to `char` — flattened here (low degree, exact on the cube); composite / coprime middle modulus — the
standing open barrier.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0

open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)

variable {n m : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **An `AND` gate equals its monomial's cube-evaluation (proved)**: `∏_{i∈S} Xᵢ` at the `{0,1}`-point `x` is
`[monoAND S x]`. -/
theorem evalMonomial_eq_monoAND (S : Finset (Fin n)) (x : Fin n → Bool) :
    MvPolynomial.eval (fun i => if x i then (1 : F) else 0) (∏ i ∈ S, X i)
      = if monoAND S x then (1 : F) else 0 := by
  rw [map_prod]
  simp only [MvPolynomial.eval_X]
  by_cases hm : monoAND S x
  · rw [if_pos hm]
    refine Finset.prod_eq_one (fun i hi => ?_)
    unfold monoAND at hm
    rw [if_pos (of_decide_eq_true hm i hi)]
  · rw [if_neg hm]
    unfold monoAND at hm
    rw [decide_eq_true_eq] at hm
    push_neg at hm
    obtain ⟨i, hiS, hix⟩ := hm
    exact Finset.prod_eq_zero hiS (if_neg hix)

/-- The flattened polynomial: `1 − (∑_j ∏_{i∈S_j} Xᵢ)^{|F|−1}` (the Fermat arithmetisation of `MOD_p∘AND`). -/
noncomputable def charModAndPoly (S : Fin m → Finset (Fin n)) : MvPolynomial (Fin n) F :=
  1 - (∑ j, ∏ i ∈ S j, X i) ^ (Fintype.card F - 1)

/-- `MOD_p∘AND` (residue 0) as a Boolean function: `[#(accepting AND gates) ≡ 0 in F]`. -/
noncomputable def charModAndFn (S : Fin m → Finset (Fin n)) : (Fin n → Bool) → F :=
  fun x => if (∑ j, (if monoAND (S j) x then (1 : F) else 0)) = 0 then 1 else 0

/-- **The prime-power flattening fires (proved)**: on the cube, `MOD_p∘AND` equals the degree-`(|F|−1)·D` polynomial
`1 − (∑ AND)^{|F|−1}` — an exact monomial-`AND` family. -/
theorem charModAndFn_eq_boolFn (S : Fin m → Finset (Fin n)) :
    charModAndFn S = boolFn (charModAndPoly S (F := F)) := by
  funext x
  rw [charModAndFn, boolFn, charModAndPoly]
  simp only [map_sub, map_one, map_pow, map_sum]
  rw [Finset.sum_congr rfl (fun j _ => evalMonomial_eq_monoAND (S j) x)]
  by_cases hS : (∑ j, (if monoAND (S j) x then (1 : F) else 0)) = 0
  · rw [if_pos hS, hS, zero_pow (Nat.sub_ne_zero_of_lt Fintype.one_lt_card), sub_zero]
  · rw [if_neg hS, FiniteField.pow_card_sub_one_eq_one _ hS, sub_self]

/-- The flattened polynomial has total degree `≤ (|F|−1)·D` when every `AND` gate has fan-in `≤ D`. -/
theorem totalDegree_charModAndPoly_le (S : Fin m → Finset (Fin n)) {D : ℕ} (hD : ∀ j, (S j).card ≤ D) :
    (charModAndPoly S (F := F)).totalDegree ≤ (Fintype.card F - 1) * D := by
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [MvPolynomial.totalDegree_one]
  refine max_le (Nat.zero_le _) (le_trans (MvPolynomial.totalDegree_pow _ _) ?_)
  refine Nat.mul_le_mul (le_refl _) ?_
  refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) (Finset.sup_le (fun j _ => ?_))
  refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun i _ => (MvPolynomial.totalDegree_X i).le)) ?_
  rw [Finset.sum_const, smul_eq_mul, mul_one]
  exact hD j

/-- **`MOD_p∘AND` has low N-Frame complexity (proved)**: `≤ (|F|−1)·D` — the flattening gives a genuine low-degree
monomial-`AND` object (cube-invariant), the middle-layer content the depth-3 rung needed. -/
theorem nframeComplexity_charModAndFn_le (S : Fin m → Finset (Fin n)) {D : ℕ} (hD : ∀ j, (S j).card ≤ D) :
    NFrameComplexity F (charModAndFn S) ≤ (Fintype.card F - 1) * D := by
  rw [charModAndFn_eq_boolFn]
  exact le_trans (nframeComplexity_boolFn_le _) (totalDegree_charModAndPoly_le S hD)

end PallLean.Paper93.DeepMath.PathB.NFrameACC0

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.charModAndFn_eq_boolFn
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.nframeComplexity_charModAndFn_le
