import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset

/-!
# Discharging `covering` for a restricted AC⁰[p] family (low-degree, indicator points)

The `(A3)` socket (`KakeyaCEWA3`) left `covering : Injective E` open — filling it at *superpolynomial*
dimension is the wall.  This file **discharges it, restricted**: for the genuine low-degree AC⁰[p]
family, evaluated at the Boolean indicator points, `covering` is a *theorem* — because the multilinear
monomials `{χ_T : |T| ≤ d}` are linearly independent on the cube.  That is the Möbius / zeta-triangular
fact: the matrix `[T ⊆ S]` is triangular with unit diagonal, hence invertible.

## What is proved

* **`monoVal_ind`** — the monomial `χ_T` at the indicator point `ind S` equals `[T ⊆ S]`.
* **`zeta_triangular`** — if `∑_{T ⊆ S} c_T = 0` for every `S` with `|S| ≤ d`, then `c_T = 0` for every
  `T` with `|T| ≤ d` (strong induction on `|S|`; the diagonal term is `c_S`, the rest vanish by IH).
* **`covering_discharged`** — the discharge: if the degree-`≤ d` polynomial `∑_T c_T χ_T` vanishes at
  every low-degree indicator point, then all its low-degree coefficients vanish.  This is `Injective`
  of the low-degree evaluation map — i.e. **`covering`, proved**, for this restricted AC⁰[p] family.

## Honest scope — and the exact lesson

This is a *real* discharge of the socket's `covering` hypothesis, axiom-clean.  But note **where** it
succeeds: the low-degree certificate space has dimension `∑_{i≤d} C(n,i)`, which is **polynomial** for
constant `d`.  So `covering` holds — and `separation_from_A3` does **not** fire, because it needs
`covering` at *super*polynomial dimension.  That is the precise lesson: `covering` is dischargeable
exactly in the regime where it yields no separation; discharging it at superpolynomial dimension (for an
NP family) is the circuit lower bound, `cost_super`, the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KakeyaCEWCovering

open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

/-- The Boolean indicator point of a set `S`: coordinate `i` is `true` iff `i ∈ S`. -/
def ind (S : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ S)

/-- The multilinear monomial `χ_T(x) = ∏_{i∈T} x_i`, with `x_i ∈ {0,1} ⊆ F`. -/
def monoVal (T : Finset (Fin n)) (x : Fin n → Bool) : F := ∏ i ∈ T, (if x i then (1 : F) else 0)

/-- **The monomial at an indicator point is the subset indicator (proved).**  `χ_T(ind S) = [T ⊆ S]`. -/
theorem monoVal_ind (T S : Finset (Fin n)) :
    monoVal T (ind S) = if T ⊆ S then (1 : F) else 0 := by
  unfold monoVal ind
  split
  · rename_i hsub
    apply Finset.prod_eq_one
    intro i hi
    simp [hsub hi]
  · rename_i hnsub
    rw [Finset.not_subset] at hnsub
    obtain ⟨i, hiT, hiS⟩ := hnsub
    exact Finset.prod_eq_zero hiT (by simp [hiS])

/-- **Zeta triangularity (proved).**  If every low-degree "downward sum" `∑_{T ⊆ S} c_T` vanishes, so
does every low-degree coefficient.  Strong induction on `|S|`: the diagonal term is `c_S`; the proper
subsets vanish by induction. -/
theorem zeta_triangular (d : ℕ) {c : Finset (Fin n) → F}
    (h : ∀ S : Finset (Fin n), S.card ≤ d → (∑ T ∈ S.powerset, c T) = 0) :
    ∀ T : Finset (Fin n), T.card ≤ d → c T = 0 := by
  intro T
  induction T using Finset.strongInduction with
  | _ S ih =>
    intro hSd
    have hsum := h S hSd
    rw [← Finset.add_sum_erase _ c (Finset.mem_powerset.mpr (Finset.Subset.refl S))] at hsum
    have hrest : (∑ T ∈ S.powerset.erase S, c T) = 0 := by
      apply Finset.sum_eq_zero
      intro T hT
      rw [Finset.mem_erase, Finset.mem_powerset] at hT
      obtain ⟨hne, hsub⟩ := hT
      have hss : T ⊂ S := hsub.ssubset_of_ne hne
      exact ih T hss (le_trans (le_of_lt (Finset.card_lt_card hss)) hSd)
    rw [hrest, add_zero] at hsum
    exact hsum

/-- The polynomial `∑_T c_T χ_T` evaluated at the indicator point `ind S` equals the downward sum
`∑_{T ⊆ S} c_T`. -/
theorem sum_poly_indicator (c : Finset (Fin n) → F) (S : Finset (Fin n)) :
    (∑ T : Finset (Fin n), c T * monoVal T (ind S)) = ∑ T ∈ S.powerset, c T := by
  have step : ∀ T : Finset (Fin n), c T * monoVal T (ind S) = if T ⊆ S then c T else 0 := by
    intro T; rw [monoVal_ind]; split <;> simp
  simp_rw [step]
  rw [← Finset.sum_filter]
  congr 1
  ext T; simp [Finset.mem_powerset]

/-- **`covering` discharged for the restricted low-degree AC⁰[p] family (proved).**  If the degree-`≤ d`
polynomial `∑_T c_T χ_T` vanishes at every low-degree indicator point, then all its low-degree
coefficients vanish — the evaluation map is injective on the low-degree space. -/
theorem covering_discharged (d : ℕ) {c : Finset (Fin n) → F}
    (hvanish : ∀ S : Finset (Fin n), S.card ≤ d →
      (∑ T : Finset (Fin n), c T * monoVal T (ind S)) = 0) :
    ∀ T : Finset (Fin n), T.card ≤ d → c T = 0 := by
  apply zeta_triangular d
  intro S hSd
  rw [← sum_poly_indicator c S]
  exact hvanish S hSd

end PallLean.Paper93.DeepMath.PathB.KakeyaCEWCovering

#print axioms PallLean.Paper93.DeepMath.PathB.KakeyaCEWCovering.covering_discharged
