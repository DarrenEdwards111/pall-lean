import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3DimensionCount
import Mathlib.LinearAlgebra.Pi

/-!
# Layer 4 (foundation) — the field-general dimension half

Bricks (C1) and (C3) of `SCOPE_LAYER4_3C_DEGREE_REDUCTION.md`.  The Layer-3 dimension machinery
(`squarefreeSpan_eq_top`, `dim_bound_on_G`, …) is stated over `ZMod p`; for `MOD_q` the relevant field
is the extension `K = F_{p^{q-1}}`.  Its *content* is field-general, so we re-derive it over an arbitrary
field `K` (mirroring Layer 3 verbatim, `ZMod p ↦ K`, `boolToZMod ↦ boolToField`).  **Layer 3 is not
edited; this only adds the `K`-version.**

* **(C1) `sqfSpan_eq_top`** — the squarefree `{0,1}`-monomials span the whole cube-function space
  `(Fin n → Bool) → K` over any field `K`.  Field-general because it uses only `x²=x` on the cube and the
  point-indicator basis (`Pi.basisFun`).  (Needed by the eventual Route-A proof of the `q`-ary
  degree-reduction `(★)`; not parity-specific.)
* **(C3) `dim_contradiction_general`** — the dimension half restated **conditionally on `(★)`**: the
  Smolensky contradiction follows from
  * `(★)` (`hstar`) — *every function on `G` is a `K`-combination of the low-degree squarefree monomials
    restricted to `G`* — which is **exactly** what the (still open, never faked) `q`-ary degree-reduction
    must establish, here an **explicit named hypothesis**, plus
  * the band margin (`lowDegMonomials_card_band_margin`, reused verbatim — pure `ℕ`) and the agreement
    lower bound `|G| ≥ (3/4)·2ⁿ`.

  So Layer 4's "everything except `(★)`" is in place: when `(★)` is proved over `K = F_{p^{q-1}}`,
  `dim_contradiction_general` closes the `MOD_q` lower bound — exactly as Layer 3 isolated its inputs.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer4

open Finset

/-- `{0,1} ↦ K` (`true ↦ 1`, `false ↦ 0`), the field-general replacement for `boolToZMod`. -/
def boolToField (K : Type*) [CommRing K] (b : Bool) : K := if b then 1 else 0

@[simp] theorem boolToField_true (K : Type*) [CommRing K] : boolToField K true = 1 := rfl
@[simp] theorem boolToField_false (K : Type*) [CommRing K] : boolToField K false = 0 := rfl

/-- The squarefree evaluation monomial `e_S(x) = ∏_{i∈S} x_i` over `K`. -/
noncomputable def sqfEval (K : Type*) [CommRing K] {n : ℕ} (S : Finset (Fin n)) : (Fin n → Bool) → K :=
  fun x => ∏ i ∈ S, boolToField K (x i)

theorem sqfEval_empty (K : Type*) [CommRing K] {n : ℕ} : sqfEval K (∅ : Finset (Fin n)) = 1 := by
  funext x; simp [sqfEval]

/-- `e_S · e_T = e_{S∪T}` on the cube (`x²=x` absorbs the overlap). -/
theorem sqfEval_mul (K : Type*) [CommRing K] {n : ℕ} (S T : Finset (Fin n)) :
    sqfEval K S * sqfEval K T = sqfEval K (S ∪ T) := by
  classical
  funext x
  simp only [sqfEval, Pi.mul_apply]
  have hidem : ∀ i : Fin n, boolToField K (x i) * boolToField K (x i) = boolToField K (x i) := by
    intro i; cases x i <;> simp
  have hPP : (∏ i ∈ S ∩ T, boolToField K (x i)) * (∏ i ∈ S ∩ T, boolToField K (x i))
      = ∏ i ∈ S ∩ T, boolToField K (x i) := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun i _ => hidem i)
  have hsub : S ∩ T ⊆ S ∪ T := Finset.inter_subset_left.trans Finset.subset_union_left
  rw [← Finset.prod_union_inter]
  conv_rhs => rw [← Finset.prod_sdiff hsub]
  conv_lhs => rw [← Finset.prod_sdiff hsub]
  rw [mul_assoc, hPP]

/-- The submodule spanned by all squarefree evaluation monomials over `K`. -/
noncomputable def sqfSpan (K : Type*) [CommRing K] (n : ℕ) : Submodule K ((Fin n → Bool) → K) :=
  Submodule.span K (Set.range (fun S : Finset (Fin n) => sqfEval K S))

theorem sqfEval_mem_sqfSpan (K : Type*) [CommRing K] (n : ℕ) (S : Finset (Fin n)) :
    sqfEval K S ∈ sqfSpan K n := Submodule.subset_span ⟨S, rfl⟩

theorem one_mem_sqfSpan (K : Type*) [CommRing K] (n : ℕ) : (1 : (Fin n → Bool) → K) ∈ sqfSpan K n := by
  rw [← sqfEval_empty K]; exact sqfEval_mem_sqfSpan K n ∅

/-- The span is a subalgebra (`e_S · e_T = e_{S∪T}` is again a generator). -/
theorem mul_mem_sqfSpan (K : Type*) [CommRing K] (n : ℕ) {u v : (Fin n → Bool) → K}
    (hu : u ∈ sqfSpan K n) (hv : v ∈ sqfSpan K n) : u * v ∈ sqfSpan K n := by
  have hclosed : sqfSpan K n * sqfSpan K n ≤ sqfSpan K n := by
    rw [sqfSpan, Submodule.span_mul_span, Submodule.span_le]
    rintro c hc; rw [Set.mem_mul] at hc
    obtain ⟨a, ⟨S, rfl⟩, b, ⟨T, rfl⟩, rfl⟩ := hc
    rw [sqfEval_mul]; exact Submodule.subset_span ⟨S ∪ T, rfl⟩
  exact hclosed (Submodule.mul_mem_mul hu hv)

theorem prod_mem_sqfSpan (K : Type*) [CommRing K] (n : ℕ) {ι : Type*} (s : Finset ι)
    (g : ι → (Fin n → Bool) → K) (hg : ∀ i ∈ s, g i ∈ sqfSpan K n) : (∏ i ∈ s, g i) ∈ sqfSpan K n :=
  Finset.prod_induction g (· ∈ sqfSpan K n) (fun _ _ ha hb => mul_mem_sqfSpan K n ha hb)
    (one_mem_sqfSpan K n) hg

/-- Each indicator factor `x ↦ (yᵢ ? xᵢ : 1-xᵢ)` is in the span. -/
theorem factor_mem_sqfSpan (K : Type*) [CommRing K] (n : ℕ) (y : Fin n → Bool) (i : Fin n) :
    (fun x : Fin n → Bool => if y i then boolToField K (x i) else 1 - boolToField K (x i))
      ∈ sqfSpan K n := by
  by_cases hyi : y i = true
  · have he : (fun x : Fin n → Bool => if y i then boolToField K (x i) else 1 - boolToField K (x i))
        = sqfEval K ({i} : Finset (Fin n)) := by
      funext x; simp [hyi, sqfEval, Finset.prod_singleton]
    rw [he]; exact sqfEval_mem_sqfSpan K n {i}
  · have he : (fun x : Fin n → Bool => if y i then boolToField K (x i) else 1 - boolToField K (x i))
        = 1 - sqfEval K ({i} : Finset (Fin n)) := by
      funext x; simp [hyi, sqfEval, Finset.prod_singleton, Pi.sub_apply, Pi.one_apply]
    rw [he]; exact Submodule.sub_mem _ (one_mem_sqfSpan K n) (sqfEval_mem_sqfSpan K n {i})

/-- The point indicator `Pi.single y 1` is the product of the degree-`≤1` factors. -/
theorem single_eq_prod_factor (K : Type*) [CommRing K] (n : ℕ) (y : Fin n → Bool) :
    (Pi.single y (1 : K) : (Fin n → Bool) → K)
      = ∏ i, (fun x : Fin n → Bool => if y i then boolToField K (x i) else 1 - boolToField K (x i)) := by
  funext x
  rw [Finset.prod_apply, Pi.single_apply]
  have hfac : ∀ i : Fin n, (if y i then boolToField K (x i) else 1 - boolToField K (x i))
        = (if x i = y i then (1 : K) else 0) := by
    intro i; cases y i <;> cases x i <;> simp
  simp_rw [hfac]
  rw [Fintype.prod_boole]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h, if_neg (fun hall => h (funext hall))]

/-- **(C1) The squarefree monomials span the cube-function space over any field `K`.**  The field-general
analogue of Layer-3's `squarefreeSpan_eq_top`. -/
theorem sqfSpan_eq_top (K : Type*) [Field K] (n : ℕ) : sqfSpan K n = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun K (Fin n → Bool)).span_eq, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  rw [Pi.basisFun_apply, single_eq_prod_factor]
  exact prod_mem_sqfSpan K n _ _ (fun i _ => factor_mem_sqfSpan K n y i)

/-- The function space on the agreement set `G` over `K` has dimension `|G|`. -/
theorem finrank_functions_on_G_general (K : Type*) [Field K] {n : ℕ} (G : Finset (Fin n → Bool)) :
    Module.finrank K ({x // x ∈ G} → K) = G.card := by
  rw [Module.finrank_pi, Fintype.card_coe]

/-- **(C3a) The dimension bound, conditional on `(★)`.**  If every function on `G` is a `K`-combination of
the degree-`≤D` squarefree monomials restricted to `G` (the hypothesis `hstar` — what the `q`-ary
degree-reduction must establish), then `|G| ≤ #{deg ≤ D monomials}`. -/
theorem dim_bound_general (K : Type*) [Field K] {n D : ℕ} (G : Finset (Fin n → Bool))
    (hstar : ∀ f : {x // x ∈ G} → K, f ∈ Submodule.span K
      (Set.range (fun S : {S // S ∈ Layer3.lowDegMonomials n D} =>
        fun y : {x // x ∈ G} => sqfEval K S.1 y.1))) :
    G.card ≤ (Layer3.lowDegMonomials n D).card := by
  classical
  set T : Set ({x // x ∈ G} → K) :=
    Set.range (fun S : {S // S ∈ Layer3.lowDegMonomials n D} =>
      fun y : {x // x ∈ G} => sqfEval K S.1 y.1) with hT
  have hspan : Submodule.span K T = ⊤ := by rw [eq_top_iff]; intro v _; exact hstar v
  rw [← finrank_functions_on_G_general K G, ← finrank_top K _, ← hspan]
  refine le_trans (finrank_span_le_card T) ?_
  rw [Set.toFinset_range]
  exact le_trans Finset.card_image_le (by rw [Finset.card_univ, Fintype.card_coe])

/-- **(C3b) The Smolensky dimension contradiction over `K`, conditional on `(★)`.**  For `n = 2m+1` and a
field `K`: if every function on `G` is a low-degree (`≤ m+Δ`) squarefree combination on `G` (`hstar`,
i.e. `(★)`), the band-margin window `16Δ² < 2m+3` holds, and `|G| ≥ (3/4)·2ⁿ`, then `False`.  This is the
field-general analogue of `smolensky_contradiction`, with the genuinely-open `q`-ary degree-reduction
isolated as the explicit hypothesis `hstar` — **never assumed silently, never faked.**  Discharging
`hstar` over `K = F_{p^{q-1}}` (scope §3-C, Route A) is the remaining mathematics. -/
theorem dim_contradiction_general (K : Type*) [Field K] {m Δ : ℕ} (G : Finset (Fin (2 * m + 1) → Bool))
    (hstar : ∀ f : {x // x ∈ G} → K, f ∈ Submodule.span K
      (Set.range (fun S : {S // S ∈ Layer3.lowDegMonomials (2 * m + 1) (m + Δ)} =>
        fun y : {x // x ∈ G} => sqfEval K S.1 y.1)))
    (hwindow : 16 * Δ ^ 2 < 2 * m + 3) (hGsize : 3 * 2 ^ (2 * m + 1) ≤ 4 * G.card) : False := by
  have hdim := dim_bound_general K G hstar
  have hband := Layer3.lowDegMonomials_card_band_margin m Δ hwindow
  omega

end PallLean.Paper93.DeepMath.PathB.Layer4

#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.sqfSpan_eq_top
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.dim_bound_general
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.dim_contradiction_general
