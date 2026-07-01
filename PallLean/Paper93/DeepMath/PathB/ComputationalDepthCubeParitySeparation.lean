import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeGlobalSeparator

/-!
# Step 6 (parity instance): parity is globally robust, so `parity ∉ small ∑∏` (cube-native)

The global separator (`…CubeGlobalSeparator`) reduced "`f ∉ shallow ∑∏`" to discharging `GlobalRobust` — the hard-side
gate.  Here we **discharge it for parity**, firing the criterion on a concrete non-trivial function.  (This is the
classically-easy direction; the composite-`MOD_q` instance stays behind the `F_2`/`F_3` incompatible-field wall.)

The witness family is the **dictator boundaries**: `dictatorB i` hides every coordinate except `i` (fixing them to
`false`).  Then `restrictB (dictatorB i) χ = 1 − 2xᵢ` (`dict i`), and these `n` functions are **linearly independent** —
a clean evaluation argument (all-`false` point + the singletons `eₖ`), needing only `2 ≠ 0`, no Fourier machinery.

  `restrictB_dictatorB_chiFull` — `restrictB (dictatorB i) χ = dict i` where `dict i = fun x => if xᵢ then −1 else 1`.
  `linearIndependent_dict` — the `n` dictator characters are linearly independent (`2 ≠ 0`).
  `dict_mem_globalCubeSpan` — each `dict i` lives in the global span (it is `(−½)·Δᵢ(restrictB (dictatorB i) χ)`).
  **`n_le_globalCubeRank_chiFull`** — `n ≤ globalCubeRank dictatorFamily 1 χ`: parity's global rank grows with `n`.
  **`chiFull_ne_boolFn_sumProd_of_fanin`** — hence `parity ≠ boolFn (∑∏)` whenever `m·2^D < n` — a genuine cube-native
        separation, the global separator *firing*.

## Honest scope

This is a real, restricted separation (`parity ∉ shallow ∑∏` of `< n/2^D` terms), the classically-easy direction, proved
by discharging `GlobalRobust` for parity.  It is **not** `MOD_q ∉ ACC⁰` — that needs the `SYM` top layer and the
composite-`MOD` incompatible-field discharge, the standing wall.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.NFrameACC0 (boolFn)

variable {n : ℕ} {F : Type*} [Field F]

/-- The `i`-th dictator character on the cube: `dict i = fun x => if xᵢ then −1 else 1` ( `= 1 − 2xᵢ` ). -/
def dict (i : Fin n) : (Fin n → Bool) → F := fun x => if x i then (-1 : F) else 1

/-- The dictator boundary: hide every coordinate except `i` (fixing them to `false`). -/
def dictatorB (i : Fin n) : Fin n → Option Bool := fun k => if k = i then none else some false

/-- The family of `n` dictator boundaries. -/
noncomputable def dictatorFamily : Finset (Fin n → Option Bool) :=
  (Finset.univ : Finset (Fin n)).image dictatorB

/-- **Projected parity is a dictator character (proved)**: `restrictB (dictatorB i) χ = dict i`. -/
theorem restrictB_dictatorB_chiFull (i : Fin n) :
    restrictB (dictatorB i) (chiFull : (Fin n → Bool) → F) = dict i := by
  funext x
  simp only [restrictB, chiFull, dict]
  rw [Finset.prod_eq_single i (fun k _ hki => by simp [dictatorB, hki])
        (fun h => absurd (Finset.mem_univ i) h)]
  simp [dictatorB]

/-- **The dictator characters are linearly independent (proved)** — evaluation at the all-`false` point and the
singletons `eₖ` forces all coefficients to `0` (needs `2 ≠ 0`). -/
theorem linearIndependent_dict (h2 : (2 : F) ≠ 0) :
    LinearIndependent F (fun i => dict i : Fin n → (Fin n → Bool) → F) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hx0 : ∑ i, c i = 0 := by
    have hh := congrFun hc (fun _ => false)
    simpa [Finset.sum_apply, Pi.smul_apply, dict, smul_eq_mul] using hh
  intro k
  have hek : ∑ i, c i * (if i = k then (-1 : F) else 1) = 0 := by
    have hh := congrFun hc (fun i => decide (i = k))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, dict,
      decide_eq_true_eq] at hh
    exact hh
  have hBk : ∑ i, c i * (if i = k then (-1 : F) else 1) = (∑ i, c i) - 2 * c k := by
    have hpt : ∀ i, c i * (if i = k then (-1 : F) else 1)
        = c i - (if i = k then 2 * c i else 0) := by
      intro i; by_cases hik : i = k <;> simp [hik] <;> ring
    simp only [hpt]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp
  rw [hBk, hx0, zero_sub, neg_eq_zero, mul_eq_zero] at hek
  exact hek.resolve_left h2

/-- **Each dictator character lives in parity's global span (proved)** — it is `(−½)·Δᵢ(restrictB (dictatorB i) χ)`. -/
theorem dict_mem_globalCubeSpan (h2 : (2 : F) ≠ 0) (i : Fin n) :
    dict i ∈ globalCubeSpan (dictatorFamily) 1 (chiFull : (Fin n → Bool) → F) := by
  have hmemFam : dictatorB i ∈ (dictatorFamily : Finset (Fin n → Option Bool)) :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hgen : cubeDeriv i (restrictB (dictatorB i) chiFull)
      ∈ cubeDerivSpan 1 (restrictB (dictatorB i) (chiFull : (Fin n → Bool) → F)) :=
    Submodule.subset_span ⟨[i], rfl, rfl⟩
  have hle : cubeDerivSpan 1 (restrictB (dictatorB i) (chiFull : (Fin n → Bool) → F))
      ≤ globalCubeSpan dictatorFamily 1 chiFull :=
    Finset.le_sup (f := fun ρ => cubeDerivSpan 1 (restrictB ρ chiFull)) hmemFam
  have hin : cubeDeriv i (restrictB (dictatorB i) chiFull)
      ∈ globalCubeSpan dictatorFamily 1 (chiFull : (Fin n → Bool) → F) := hle hgen
  rw [cubeDeriv_restrictB_chiFull (dictatorB i) (by simp [dictatorB]),
      restrictB_dictatorB_chiFull] at hin
  have heq : ((-2 : F)⁻¹ • ((-2 : F) • dict i) : (Fin n → Bool) → F) = dict i := by
    rw [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr h2), one_smul]
  rw [← heq]
  exact Submodule.smul_mem _ _ hin

/-- **Parity's global rank grows (proved)**: `n ≤ globalCubeRank dictatorFamily 1 χ`. -/
theorem n_le_globalCubeRank_chiFull (h2 : (2 : F) ≠ 0) :
    n ≤ globalCubeRank (dictatorFamily) 1 (chiFull : (Fin n → Bool) → F) := by
  have hLI := linearIndependent_dict (F := F) (n := n) h2
  have hle : Submodule.span F (Set.range (fun i => dict i : Fin n → (Fin n → Bool) → F))
      ≤ globalCubeSpan dictatorFamily 1 chiFull :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr (fun i => dict_mem_globalCubeSpan h2 i))
  have h1 : n = Module.finrank F
      (Submodule.span F (Set.range (fun i => dict i : Fin n → (Fin n → Bool) → F))) := by
    rw [finrank_span_eq_card hLI, Fintype.card_fin]
  simp only [globalCubeRank]
  exact le_trans h1.le (Submodule.finrank_mono hle)

/-- **Parity ∉ small `∑∏` (proved)**: if `∑ⱼ 2^{|Sⱼ|} < n`, then `parity ≠ boolFn (∑∏)` — the global separator firing on
a concrete function. -/
theorem chiFull_ne_boolFn_sumProd_of_lt {m : ℕ} (S : Fin m → Finset (Fin n)) (h2 : (2 : F) ≠ 0)
    (hlt : ∑ j, 2 ^ (S j).card < n) :
    (chiFull : (Fin n → Bool) → F) ≠ boolFn (∑ j, ∏ i ∈ S j, X i) :=
  not_sumProd_of_globalCubeRank_gt S chiFull dictatorFamily
    (lt_of_lt_of_le hlt (n_le_globalCubeRank_chiFull h2))

/-- **Cube-native parity lower bound (proved)**: parity on `n` variables is **not** any shallow `∑∏` of `m` `AND`s of
fan-in `≤ D` whenever `m·2^D < n`. -/
theorem chiFull_ne_boolFn_sumProd_of_fanin {m D : ℕ} (S : Fin m → Finset (Fin n)) (h2 : (2 : F) ≠ 0)
    (hD : ∀ j, (S j).card ≤ D) (hmD : m * 2 ^ D < n) :
    (chiFull : (Fin n → Bool) → F) ≠ boolFn (∑ j, ∏ i ∈ S j, X i) := by
  refine chiFull_ne_boolFn_sumProd_of_lt S h2 (lt_of_le_of_lt ?_ hmD)
  refine le_trans (Finset.sum_le_sum (fun j _ => Nat.pow_le_pow_right (by norm_num) (hD j))) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.n_le_globalCubeRank_chiFull
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.chiFull_ne_boolFn_sumProd_of_fanin
