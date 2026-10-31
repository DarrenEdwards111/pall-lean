import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4QaryReduction

/-!
# Layer 4 (Route A, piece 2) — the `ζ`-character basis and the dimension collapse

This completes the **algebraic** side of the `MOD_q` degree reduction `(★)` (scope §3-C):

* **Spanning (piece 2).**  The `ζ`-characters `{qChar ζ S}` span the cube-function space
  `(Fin n → Bool) → K` (`qSpan_eq_top`).  Unlike the `±1` case, `qChar` is **not** multiplicatively
  closed, so the `pmSpan_eq_top` subalgebra route does *not* transfer.  Instead the **triangular change of
  basis** `qChar ζ S = ∑_{T⊆S} (ζ-1)^{|T|}·e_T` (`qChar_eq_sum_sqfEval`, lower-triangular in `⊆` with
  diagonal `(ζ-1)^{|S|} ≠ 0` since `ζ ≠ 1`) shows each squarefree `e_S ∈ span{qChar}` by strong induction
  on `S` (`sqfEval_mem_qSpan`), so `span{qChar} ⊇ sqfSpan = ⊤`.

* **The dimension collapse.**  Combining the spanning with the halving `qChar_reduction`
  (`ComputationalDepthLayer4QaryReduction`): if the full weight character `qChar ζ univ = ζ^{#ones}` has a
  degree-`Δ` representative on `G`, then **every** function on `G` agrees with a polynomial of degree
  `≤ Δ + n/2` (`qary_every_function_repr`) — the general-`q` analogue of Layer 3's `every_function_repr`.

So the entire algebraic half of `(★)` is now in place over an arbitrary field `K`.  The **only** remaining
input is the genuinely circuit-side piece (3): that `ζ^{#ones}` is low-degree on `G` given
`MOD_q ∈ AC⁰[p]` (via the `q` shifted `MOD_q` indicators) — still open, still not faked.  `qary_every_
function_repr`'s hypothesis `hg` (`g` represents `qChar ζ univ` on `G`) is exactly that input, here an
explicit named hypothesis.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer4

open Finset

/-- **The triangular change of basis.**  `qChar ζ S = ∑_{T⊆S} (ζ-1)^{|T|}·e_T` (expand the product
`∏_{i∈S}(1+(ζ-1)xᵢ)`).  Lower-triangular in `⊆` with diagonal `(ζ-1)^{|S|}`. -/
theorem qChar_eq_sum_sqfEval (K : Type*) [Field K] (ζ : K) {n : ℕ} (S : Finset (Fin n)) :
    qChar K ζ S = ∑ T ∈ S.powerset, (ζ - 1) ^ T.card • sqfEval K T := by
  funext x
  rw [qChar, Finset.prod_one_add, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  rw [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const]
  rfl

/-- The submodule spanned by all `ζ`-characters. -/
noncomputable def qSpan (K : Type*) [Field K] (ζ : K) (n : ℕ) : Submodule K ((Fin n → Bool) → K) :=
  Submodule.span K (Set.range (fun S : Finset (Fin n) => qChar K ζ S))

theorem qChar_mem_qSpan (K : Type*) [Field K] (ζ : K) (n : ℕ) (S : Finset (Fin n)) :
    qChar K ζ S ∈ qSpan K ζ n := Submodule.subset_span ⟨S, rfl⟩

/-- Each squarefree monomial lies in the `ζ`-character span (invert the triangular relation by strong
induction: `(ζ-1)^{|S|}·e_S = qChar ζ S − ∑_{T⊊S}(ζ-1)^{|T|}·e_T`, and `(ζ-1)^{|S|}` is a unit). -/
theorem sqfEval_mem_qSpan (K : Type*) [Field K] {ζ : K} (hζ1 : ζ ≠ 1) (n : ℕ) (S : Finset (Fin n)) :
    sqfEval K S ∈ qSpan K ζ n := by
  have hne : (ζ - 1) ≠ 0 := sub_ne_zero.mpr hζ1
  induction S using Finset.strongInduction with
  | _ S ih =>
    have hsplit : qChar K ζ S
        = (ζ - 1) ^ S.card • sqfEval K S
          + ∑ T ∈ S.powerset.erase S, (ζ - 1) ^ T.card • sqfEval K T := by
      rw [qChar_eq_sum_sqfEval, ← Finset.add_sum_erase _ _ (Finset.mem_powerset.mpr (le_refl S))]
    have hrest : (∑ T ∈ S.powerset.erase S, (ζ - 1) ^ T.card • sqfEval K T) ∈ qSpan K ζ n :=
      Submodule.sum_mem _ (fun T hT => by
        rw [Finset.mem_erase, Finset.mem_powerset] at hT
        exact Submodule.smul_mem _ _ (ih T (Finset.ssubset_iff_subset_ne.mpr ⟨hT.2, hT.1⟩)))
    have hcSeS : (ζ - 1) ^ S.card • sqfEval K S ∈ qSpan K ζ n := by
      have : (ζ - 1) ^ S.card • sqfEval K S
          = qChar K ζ S - ∑ T ∈ S.powerset.erase S, (ζ - 1) ^ T.card • sqfEval K T := by
        rw [hsplit]; abel
      rw [this]; exact Submodule.sub_mem _ (qChar_mem_qSpan K ζ n S) hrest
    have hrw : sqfEval K S = ((ζ - 1) ^ S.card)⁻¹ • ((ζ - 1) ^ S.card • sqfEval K S) := by
      rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hne), one_smul]
    rw [hrw]; exact Submodule.smul_mem _ _ hcSeS

/-- **(Piece 2) The `ζ`-characters span the cube-function space over any field `K`** (for `ζ ≠ 1`) — the
general-`q` analogue of `pmSpan_eq_top`. -/
theorem qSpan_eq_top (K : Type*) [Field K] {ζ : K} (hζ1 : ζ ≠ 1) (n : ℕ) : qSpan K ζ n = ⊤ := by
  rw [eq_top_iff, ← sqfSpan_eq_top K n, sqfSpan, Submodule.span_le]
  rintro _ ⟨S, rfl⟩
  exact sqfEval_mem_qSpan K hζ1 n S

open MvPolynomial in
/-- Uniform per-character representative: every `qChar ζ S` agrees on `G` with a degree-`≤(Δ+n/2)`
polynomial (`qMonomial ζ S` if `|S| ≤ n/2`, else the halving `qChar_reduction`). -/
theorem qChar_repr (K : Type*) [Field K] {ζ : K} (hζ0 : ζ ≠ 0) {n : ℕ}
    (G : Finset (Fin n → Bool)) (Δ : ℕ) (g : MvPolynomial (Fin n) K) (hgdeg : g.totalDegree ≤ Δ)
    (hg : ∀ x ∈ G, eval (fun i => boolToField K (x i)) g = qChar K ζ Finset.univ x)
    (S : Finset (Fin n)) :
    ∃ h : MvPolynomial (Fin n) K, h.totalDegree ≤ Δ + n / 2 ∧
      ∀ x ∈ G, eval (fun i => boolToField K (x i)) h = qChar K ζ S x := by
  by_cases hS : S.card ≤ n / 2
  · exact ⟨qMonomial K ζ S, le_trans (qMonomial_totalDegree_le K ζ S) (by omega),
      fun x _ => qMonomial_eval K ζ S x⟩
  · obtain ⟨h, hdeg, heval⟩ := qChar_reduction K hζ0 G Δ g hgdeg hg S
    exact ⟨h, le_trans hdeg (by omega), heval⟩

open MvPolynomial in
/-- **The `q`-ary dimension collapse** (analogue of `every_function_repr`).  If `g` (degree `Δ`)
represents the full weight character `ζ^{#ones}` on `G` (this is the still-open circuit-side input
`(★)`-piece (3), here an explicit hypothesis), then **every** function on `G` agrees with a polynomial of
degree `≤ Δ + n/2`.  Proof: expand `f = ∑ c_S · qChar ζ S` (`qSpan_eq_top`) and apply `qChar_repr`
termwise (degrees preserved under `+`/`•`). -/
theorem qary_every_function_repr (K : Type*) [Field K] {ζ : K} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) {n : ℕ}
    (G : Finset (Fin n → Bool)) (Δ : ℕ) (g : MvPolynomial (Fin n) K) (hgdeg : g.totalDegree ≤ Δ)
    (hg : ∀ x ∈ G, eval (fun i => boolToField K (x i)) g = qChar K ζ Finset.univ x)
    (f : (Fin n → Bool) → K) :
    ∃ h : MvPolynomial (Fin n) K, h.totalDegree ≤ Δ + n / 2 ∧
      ∀ x ∈ G, eval (fun i => boolToField K (x i)) h = f x := by
  have hf : f ∈ qSpan K ζ n := by rw [qSpan_eq_top K hζ1 n]; exact Submodule.mem_top
  refine Submodule.span_induction (p := fun u _ => ∃ h : MvPolynomial (Fin n) K,
      h.totalDegree ≤ Δ + n / 2 ∧ ∀ x ∈ G, eval (fun i => boolToField K (x i)) h = u x)
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S, rfl⟩; exact qChar_repr K hζ0 G Δ g hgdeg hg S
  · exact ⟨0, by simp, fun x _ => by simp⟩
  · rintro u v _ _ ⟨hu, hud, hue⟩ ⟨hv, hvd, hve⟩
    exact ⟨hu + hv, le_trans (totalDegree_add _ _) (max_le hud hvd),
      fun x hx => by rw [map_add, hue x hx, hve x hx]; rfl⟩
  · rintro c u _ ⟨hu, hud, hue⟩
    exact ⟨c • hu, le_trans (totalDegree_smul_le c hu) hud,
      fun x hx => by rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C, hue x hx, Pi.smul_apply,
        smul_eq_mul]⟩

end PallLean.Paper93.DeepMath.PathB.Layer4

#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.qSpan_eq_top
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.qary_every_function_repr
