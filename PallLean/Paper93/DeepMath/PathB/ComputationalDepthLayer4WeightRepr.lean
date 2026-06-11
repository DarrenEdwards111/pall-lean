import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4QarySpan

/-!
# Layer 4 (Route A, piece 3) — assembling the weight character from `MOD_q` indicators

Piece (3) of `SCOPE_LAYER4_3C_DEGREE_REDUCTION.md`: the input that `ζ^{#ones}` (`= qChar ζ univ`) is
low-degree on a large set.  `MOD_q` itself only gives the indicator `[#ones ≡ 0]`; the **full weight
character** decomposes over the `q` residues:
\[
  \zeta^{\#ones} \;=\; \zeta^{\#ones \bmod q} \;=\; \sum_{j<q}\zeta^j\,[\#ones \equiv j \pmod q]
  \qquad(\text{since }\zeta^q=1).
\]
So if each residue indicator `[#ones ≡ j]` has a degree-`Δ` representative `p_j` on a set `A_j`, then
`∑_{j<q} ζ^j · p_j` represents `ζ^{#ones}` on `G = ⋂_j A_j` with degree `≤ Δ`
(`weightChar_repr_of_indicators`).  Chaining with the algebraic dimension collapse
(`qary_every_function_repr`) gives **`qary_reduction_from_indicators`**: *from the `q` indicator
approximants alone, every function on `⋂_j A_j` is degree-`≤(Δ+n/2)`-representable* — i.e. the entire
`(★)` reduction holds once the `q` indicators are low-degree on large sets.

**This is the algebraic assembly of piece (3).**  The sole remaining (genuinely circuit-side) content is
that each residue indicator `[#ones ≡ j]` *is* `AC⁰[p]` and hence *has* such an approximant: `[#ones ≡ j]`
is `MOD_q` of the input padded with `q-j` constant ones, so `MOD_q ∈ AC⁰[p]` makes it `AC⁰[p]`, and the
Layer-3 agreement machinery (base-changed to `F_{p^{q-1}}`) supplies the approximant `p_j` on a
`(1-ε)`-fraction `A_j`.  That circuit construction is **not** done here and **not** faked — it appears as
the explicit hypotheses `(p, A, hpdeg, hp)`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer4

open Finset MvPolynomial

/-- `qChar ζ S x = ζ^{#{i∈S : xᵢ}}` (the partial-support weight, like `weightChar_eq_pow`). -/
theorem qChar_eq_pow (K : Type*) [Field K] (ζ : K) {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    qChar K ζ S x = ζ ^ (S.filter (fun i => x i = true)).card := by
  rw [qChar]
  rw [show (fun i => 1 + (ζ - 1) * (if x i then (1 : K) else 0)) = (fun i => if x i then ζ else 1) from
    funext (fun i => by
      cases x i <;> · first | (show (1 : K) + (ζ - 1) * 0 = 1; ring) | (show (1 : K) + (ζ - 1) * 1 = ζ; ring))]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]

/-- The mod-`q` residue indicator `[#ones ≡ j (mod q)]` as a `K`-valued function. -/
noncomputable def modIndicator (K : Type*) [Field K] (q j : ℕ) {n : ℕ} (x : Fin n → Bool) : K :=
  if (Finset.univ.filter (fun i => x i = true)).card % q = j then 1 else 0

/-- **The weight character as a sum over residue indicators:**
`ζ^{#ones} = ∑_{j<q} ζ^j · [#ones ≡ j (mod q)]` (for `ζ^q = 1`). -/
theorem qChar_univ_eq_sum_indicator (K : Type*) [Field K] {ζ : K} {q : ℕ} (hζ : ζ ^ q = 1) (hq : 0 < q)
    {n : ℕ} (x : Fin n → Bool) :
    qChar K ζ Finset.univ x = ∑ j ∈ Finset.range q, ζ ^ j * modIndicator K q j x := by
  rw [qChar_eq_pow]
  have hmod : (Finset.univ.filter (fun i => x i = true)).card % q < q := Nat.mod_lt _ hq
  simp only [modIndicator, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range q) ((Finset.univ.filter (fun i => x i = true)).card % q)
    (fun j => ζ ^ j), if_pos (Finset.mem_range.mpr hmod)]
  conv_lhs => rw [← Nat.div_add_mod (Finset.univ.filter (fun i => x i = true)).card q]
  rw [pow_add, pow_mul, hζ, one_pow, one_mul]

/-- **Assembling `ζ^{#ones}` from the residue indicators.**  If each `[#ones ≡ j]` (`j < q`) is realised
by a degree-`≤Δ` polynomial `p_j` on `A_j`, then `∑_{j<q} ζ^j · p_j` is a degree-`≤Δ` polynomial realising
`ζ^{#ones} = qChar ζ univ` on `G = ⋂_j A_j`. -/
theorem weightChar_repr_of_indicators (K : Type*) [Field K] {ζ : K} {q : ℕ} (hζ : ζ ^ q = 1)
    (hq : 0 < q) {n : ℕ} (Δ : ℕ) (p : ℕ → MvPolynomial (Fin n) K) (A : ℕ → Finset (Fin n → Bool))
    (hpdeg : ∀ j, (p j).totalDegree ≤ Δ)
    (hp : ∀ j ∈ Finset.range q, ∀ x ∈ A j,
      eval (fun i => boolToField K (x i)) (p j) = modIndicator K q j x) :
    ∃ g : MvPolynomial (Fin n) K, g.totalDegree ≤ Δ ∧
      ∀ x, (∀ j ∈ Finset.range q, x ∈ A j) →
        eval (fun i => boolToField K (x i)) g = qChar K ζ Finset.univ x := by
  refine ⟨∑ j ∈ Finset.range q, C (ζ ^ j) * p j, ?_, ?_⟩
  · refine le_trans (totalDegree_finset_sum _ _) (Finset.sup_le (fun j _ => ?_))
    exact le_trans (totalDegree_mul _ _) (by rw [totalDegree_C, zero_add]; exact hpdeg j)
  · intro x hx
    rw [map_sum, qChar_univ_eq_sum_indicator K hζ hq]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [map_mul, eval_C, hp j hj x (hx j hj)]

/-- **(Piece 3, algebraic assembly) The full `(★)` reduction from the `q` indicator approximants.**  If for
each residue `j < q` the indicator `[#ones ≡ j]` has a degree-`≤Δ` representative `p_j` on `A_j`, then on
`G = ⋂_{j<q} A_j` **every** function agrees with a polynomial of degree `≤ Δ + n/2` — the general-`q`
dimension collapse, now reduced entirely to the (circuit-side) existence of the indicator approximants. -/
theorem qary_reduction_from_indicators (K : Type*) [Field K] {ζ : K} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    {q : ℕ} (hζq : ζ ^ q = 1) (hq : 0 < q) {n : ℕ} (Δ : ℕ) (p : ℕ → MvPolynomial (Fin n) K)
    (A : ℕ → Finset (Fin n → Bool)) (hpdeg : ∀ j, (p j).totalDegree ≤ Δ)
    (hp : ∀ j ∈ Finset.range q, ∀ x ∈ A j,
      eval (fun i => boolToField K (x i)) (p j) = modIndicator K q j x)
    (f : (Fin n → Bool) → K) :
    ∃ h : MvPolynomial (Fin n) K, h.totalDegree ≤ Δ + n / 2 ∧
      ∀ x ∈ (Finset.range q).inf A, eval (fun i => boolToField K (x i)) h = f x := by
  obtain ⟨g, hgdeg, hgeval⟩ := weightChar_repr_of_indicators K hζq hq Δ p A hpdeg hp
  exact qary_every_function_repr K hζ0 hζ1 ((Finset.range q).inf A) Δ g hgdeg
    (fun x hx => hgeval x (fun j hj => (Finset.mem_inf.mp hx) j hj)) f

end PallLean.Paper93.DeepMath.PathB.Layer4

#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.qChar_univ_eq_sum_indicator
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.weightChar_repr_of_indicators
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.qary_reduction_from_indicators
