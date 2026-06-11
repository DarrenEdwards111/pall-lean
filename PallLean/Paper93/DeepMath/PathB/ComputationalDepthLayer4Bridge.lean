import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4QarySpan

/-!
# Layer 4 (Route A) — the degree→span bridge and the assembled dimension contradiction

This closes the last *algebraic* gap between `qary_every_function_repr` (which gives, for each function on
`G`, a degree-`≤(Δ+n/2)` **polynomial representative**) and `dim_contradiction_general` (whose hypothesis
`hstar` is **span membership** in the low-degree squarefree functions).

* **`eval_mem_lowDegSpan_K`** — the field-general squarefree-reduction bridge (mirror of Layer 3's
  `eval_mem_lowDegSpan`): the evaluation of *any* degree-`≤D` polynomial on the Boolean cube lies in the
  span of the degree-`≤D` squarefree monomial functions (`boolToField^{e+1} = boolToField` collapses each
  monomial `∏ xᵢ^{dᵢ}` to the squarefree `e_{supp d}`, `|supp d| ≤ deg ≤ D`).

* **`qary_hstar_of_repr`** — restricts that to `G`: from "every function on `G` has a degree-`≤D`
  representative" it produces `dim_contradiction_general`'s `hstar` (every function on `↥G` is in the
  span of the low-degree squarefree functions restricted to `G`), via the restriction linear map
  `ρ = funLeft K K Subtype.val` and `Submodule.map_span`.

* **`qary_contradiction`** — the assembled **dimension contradiction over `K`**: for `n = 2m+1`, if the
  weight character `qChar ζ univ = ζ^{#ones}` has a degree-`Δ` representative on `G` (the circuit-side
  input, supplied by `weightChar_repr_of_indicators`), the band-margin window `16Δ² < 2m+3` holds, and
  `|G| ≥ (3/4)·2ⁿ`, then `False`.  Chains `qary_every_function_repr` → `qary_hstar_of_repr` →
  `dim_contradiction_general` (with `(2m+1)/2 = m`, so the degree `Δ + n/2 = m + Δ` matches the
  `lowDegMonomials (2m+1) (m+Δ)` of the dimension count).

This is the general-`q` analogue of `smolensky_contradiction`, with the single hypothesis `hg` (the weight
character is low-degree on `G`) — exactly what the padding + tight-agreement + base-change + intersection
machinery delivers.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer4

open MvPolynomial

/-- `boolToField^{e+1} = boolToField` on `{0,1}` — the `K`-version of the multilinear reduction lever. -/
theorem boolToField_pow_succ (K : Type*) [Field K] (b : Bool) (e : ℕ) :
    (boolToField K b) ^ (e + 1) = boolToField K b := by
  cases b
  · show (0 : K) ^ (e + 1) = 0; exact zero_pow (Nat.succ_ne_zero e)
  · show (1 : K) ^ (e + 1) = 1; exact one_pow _

/-- **The squarefree-reduction spanning bridge over `K`** (mirror of Layer 3's `eval_mem_lowDegSpan`).
On the Boolean cube the evaluation of any degree-`≤D` polynomial lies in the span of the degree-`≤D`
squarefree monomial functions. -/
theorem eval_mem_lowDegSpan_K (K : Type*) [Field K] {n : ℕ} (D : ℕ)
    (h : MvPolynomial (Fin n) K) (hdeg : h.totalDegree ≤ D) :
    (fun x : Fin n → Bool => eval (fun i => boolToField K (x i)) h)
      ∈ Submodule.span K
        (Set.range (fun S : {S // S ∈ Layer3.lowDegMonomials n D} => sqfEval K S.1)) := by
  classical
  have hmono : ∀ (d : Fin n →₀ ℕ) (x : Fin n → Bool),
      (∏ i, (boolToField K (x i)) ^ d i) = ∏ i ∈ d.support, boolToField K (x i) := by
    intro d x
    rw [← Finset.prod_subset (Finset.subset_univ d.support)
      (fun i _ hi => by simp only [Finsupp.mem_support_iff, not_not] at hi; rw [hi, pow_zero])]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    rw [hk, boolToField_pow_succ]
  have hsum : (fun x : Fin n → Bool => eval (fun i => boolToField K (x i)) h)
      = ∑ d ∈ h.support, h.coeff d • sqfEval K d.support := by
    funext x
    rw [eval_eq', Finset.sum_apply]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Pi.smul_apply, smul_eq_mul, hmono d x]; rfl
  rw [hsum]
  refine Submodule.sum_mem _ (fun d hd => Submodule.smul_mem _ _ ?_)
  have hcard : d.support.card ≤ D := by
    refine le_trans ?_ (le_trans (le_totalDegree hd) hdeg)
    rw [Finsupp.sum, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
  have hmem : d.support ∈ Layer3.lowDegMonomials n D := by
    rw [Layer3.lowDegMonomials, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ _, hcard⟩
  exact Submodule.subset_span ⟨⟨d.support, hmem⟩, rfl⟩

/-- **Degree-representative ⇒ `hstar`.**  If every function on `G` has a degree-`≤D` polynomial
representative, then every function on `↥G` lies in the span of the degree-`≤D` squarefree functions
restricted to `G` — exactly `dim_contradiction_general`'s `hstar`.  (Extend `f` to the cube, take its
representative, then restrict via `ρ = funLeft K K Subtype.val`.) -/
theorem qary_hstar_of_repr (K : Type*) [Field K] {n D : ℕ} (G : Finset (Fin n → Bool))
    (hrepr : ∀ f : (Fin n → Bool) → K, ∃ h : MvPolynomial (Fin n) K, h.totalDegree ≤ D ∧
        ∀ x ∈ G, eval (fun i => boolToField K (x i)) h = f x)
    (f : {x // x ∈ G} → K) :
    f ∈ Submodule.span K
      (Set.range (fun S : {S // S ∈ Layer3.lowDegMonomials n D} =>
        fun y : {x // x ∈ G} => sqfEval K S.1 y.1)) := by
  classical
  obtain ⟨h, hdeg, heval⟩ := hrepr (fun x => if hx : x ∈ G then f ⟨x, hx⟩ else 0)
  set ρ : ((Fin n → Bool) → K) →ₗ[K] ({x // x ∈ G} → K) := LinearMap.funLeft K K Subtype.val with hρ
  have hf : f = ρ (fun x => eval (fun i => boolToField K (x i)) h) := by
    funext y
    show f y = eval (fun i => boolToField K ((y : Fin n → Bool) i)) h
    rw [heval (y : Fin n → Bool) y.2, dif_pos y.2]
  rw [hf,
    show (Set.range (fun S : {S // S ∈ Layer3.lowDegMonomials n D} =>
            fun y : {x // x ∈ G} => sqfEval K S.1 y.1))
        = ρ '' Set.range (fun S : {S // S ∈ Layer3.lowDegMonomials n D} => sqfEval K S.1)
      from by rw [← Set.range_comp]; rfl,
    ← Submodule.map_span]
  exact Submodule.mem_map_of_mem (eval_mem_lowDegSpan_K K D h hdeg)

open MvPolynomial in
/-- **The assembled `q`-ary dimension contradiction over `K`** (analogue of `smolensky_contradiction`).
For `n = 2m+1`: if the weight character `qChar ζ univ = ζ^{#ones}` has a degree-`Δ` representative on `G`,
the band-margin window `16Δ² < 2m+3` holds, and `|G| ≥ (3/4)·2ⁿ`, then `False`.  The hypothesis `hg` is
exactly the circuit-side input supplied by `weightChar_repr_of_indicators` (the `MOD_q` indicators). -/
theorem qary_contradiction (K : Type*) [Field K] {ζ : K} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) {m Δ : ℕ}
    (G : Finset (Fin (2 * m + 1) → Bool)) (g : MvPolynomial (Fin (2 * m + 1)) K)
    (hgdeg : g.totalDegree ≤ Δ)
    (hg : ∀ x ∈ G, eval (fun i => boolToField K (x i)) g = qChar K ζ Finset.univ x)
    (hwindow : 16 * Δ ^ 2 < 2 * m + 3) (hGsize : 3 * 2 ^ (2 * m + 1) ≤ 4 * G.card) : False := by
  have hrepr : ∀ f : (Fin (2 * m + 1) → Bool) → K, ∃ h : MvPolynomial (Fin (2 * m + 1)) K,
      h.totalDegree ≤ m + Δ ∧ ∀ x ∈ G, eval (fun i => boolToField K (x i)) h = f x := by
    intro f
    obtain ⟨h, hd, he⟩ := qary_every_function_repr K hζ0 hζ1 G Δ g hgdeg hg f
    exact ⟨h, by omega, he⟩
  exact dim_contradiction_general K G (fun f => qary_hstar_of_repr K G hrepr f) hwindow hGsize

end PallLean.Paper93.DeepMath.PathB.Layer4

#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.eval_mem_lowDegSpan_K
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.qary_hstar_of_repr
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.qary_contradiction
