import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeParitySeparation

/-!
# `MOD_q` instance of `GlobalRobust`: `MOD_q ∉ small ∑∏` — and the sharp `SYM`/`ACC⁰` wall

The parity instance discharged `GlobalRobust` for `χ`.  This file does the **`MOD_q` instance**, and — crucially — draws
the exact line where it stops.

The dictator family `dictatorB i` (hide all but `i`, at `false`) probes only the **weight-0 / weight-1** behaviour of a
symmetric function.  `MOD_q` differs there (`g(0) = [0≡0] = 1`, `g(1) = [1≡0] = 0` for `q ≥ 2`), so — exactly as for
parity — the dictator restrictions of `MOD_q` recover the independent characters `dict i`, forcing
`globalCubeRank ≥ n`:

  `modQFn q` — the cube function `[#(true bits) ≡ 0 mod q]` valued in `F`.
  `restrictB_dictatorB_modQFn` — `restrictB (dictatorB i) (MOD_q) = fun x => if xᵢ then 0 else 1` (weight-0/1 collapse).
  `dict_mem_globalCubeSpan_modQ` — `dict i = −Δᵢ(restrictB (dictatorB i) MOD_q) ∈` the global span.
  **`n_le_globalCubeRank_modQFn`** — `n ≤ globalCubeRank dictatorFamily 1 (MOD_q)`: `GlobalRobust` discharged for `MOD_q`.
  **`modQFn_ne_boolFn_sumProd_of_fanin`** — hence `MOD_q ≠ boolFn(∑∏)` whenever `m·2^D < n`.

## The sharp wall — this is `∑∏`, NOT `ACC⁰`

This proves `MOD_q ∉ small **plain** ∑∏` (depth-2, a sum of monomials) — the classically-easy statement.  It is **not**
`MOD_q ∉ ACC⁰`.  By Beigel–Tarui, `ACC⁰ = SYM∘∑∏`: a **symmetric top gate** over the `∑∏`.  Two things break here, and
they are exactly the standing wall:

1. **The criterion is `∑∏`-only.**  `sumProd_separation_of_globalRobust` bounds a *plain* `∑∏` by `∑ⱼ 2^{|Sⱼ|}` (a
   *linear* combination of the monomial subspaces).  A `SYM` top gate is *not* linear in the `∑∏` features, so the global
   bound does not apply — extending it to `SYM∘∑∏` is open.
2. **The dictator family is weight-0/1-blind.**  It only sees `g(0), g(1)`; a `SYM` gate can reshape the whole weight
   profile, and the composite-`MOD_q` count lives across *all* residues.  Capturing that needs a boundary family that
   resolves the full symmetric spectrum over incompatible prime-power fields — the `F_2`/`F_3` wall (`…CompositeCRT`),
   `P≠NP`-strength per the book1 assessment.

So: `GlobalRobust` for `MOD_q` is discharged (rank `≥ n`), firing the `∑∏` separation; the `SYM`/`ACC⁰` lift is **not**
built and is **not** fakeable.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.NFrameACC0 (boolFn)

variable {n : ℕ} {F : Type*} [Field F]

/-- The number of `true` bits of a cube point. -/
def cubeCount (x : Fin n → Bool) : ℕ := ∑ i, (if x i then 1 else 0)

/-- `MOD_q` as a cube function valued in `F`: `[#(true bits) ≡ 0 mod q]`. -/
def modQFn (q : ℕ) (x : Fin n → Bool) : F := if cubeCount x % q = 0 then 1 else 0

/-- The dictator projection collapses the count to the single visible bit. -/
theorem cubeCount_restrictB_dictatorB (i : Fin n) (x : Fin n → Bool) :
    cubeCount (fun k => (dictatorB i k).getD (x k)) = (if x i then 1 else 0) := by
  rw [cubeCount, Finset.sum_eq_single i]
  · simp [dictatorB]
  · intro k _ hki; simp [dictatorB, hki]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **`MOD_q` under a dictator boundary (proved)**: only the weight-0/1 behaviour survives — `restrictB (dictatorB i)
MOD_q = fun x => if xᵢ then 0 else 1`. -/
theorem restrictB_dictatorB_modQFn {q : ℕ} (hq : 2 ≤ q) (i : Fin n) :
    restrictB (dictatorB i) (modQFn q : (Fin n → Bool) → F) = fun x => if x i then (0 : F) else 1 := by
  funext x
  simp only [restrictB, modQFn, cubeCount_restrictB_dictatorB]
  by_cases hx : x i
  · simp only [if_pos hx, Nat.mod_eq_of_lt (show (1 : ℕ) < q by omega)]
    simp
  · simp only [if_neg hx, Nat.zero_mod]
    simp

/-- The edge derivative of the collapsed `MOD_q` restriction is `−dict i`. -/
theorem cubeDeriv_notX_eq (i : Fin n) :
    cubeDeriv i (fun x => if x i then (0 : F) else 1) = (-1 : F) • dict i := by
  funext x
  simp only [cubeDeriv, dict, Pi.smul_apply, smul_eq_mul, flipBit]
  by_cases hx : x i <;> simp [hx]

/-- **Each dictator character lives in `MOD_q`'s global span (proved)** — `dict i = −Δᵢ(restrictB (dictatorB i) MOD_q)`. -/
theorem dict_mem_globalCubeSpan_modQ {q : ℕ} (hq : 2 ≤ q) (i : Fin n) :
    dict i ∈ globalCubeSpan (dictatorFamily) 1 (modQFn q : (Fin n → Bool) → F) := by
  have hmemFam : dictatorB i ∈ (dictatorFamily : Finset (Fin n → Option Bool)) :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hgen : cubeDeriv i (restrictB (dictatorB i) (modQFn q))
      ∈ cubeDerivSpan 1 (restrictB (dictatorB i) (modQFn q : (Fin n → Bool) → F)) :=
    Submodule.subset_span ⟨[i], rfl, rfl⟩
  have hle : cubeDerivSpan 1 (restrictB (dictatorB i) (modQFn q : (Fin n → Bool) → F))
      ≤ globalCubeSpan dictatorFamily 1 (modQFn q) :=
    Finset.le_sup (f := fun ρ => cubeDerivSpan 1 (restrictB ρ (modQFn q))) hmemFam
  have hin : cubeDeriv i (restrictB (dictatorB i) (modQFn q))
      ∈ globalCubeSpan dictatorFamily 1 (modQFn q : (Fin n → Bool) → F) := hle hgen
  rw [restrictB_dictatorB_modQFn hq, cubeDeriv_notX_eq] at hin
  have heq : ((-1 : F) • ((-1 : F) • dict i) : (Fin n → Bool) → F) = dict i := by
    rw [smul_smul]; simp
  rw [← heq]
  exact Submodule.smul_mem _ _ hin

/-- **`GlobalRobust` discharged for `MOD_q` (proved)**: `n ≤ globalCubeRank dictatorFamily 1 (MOD_q)`. -/
theorem n_le_globalCubeRank_modQFn {q : ℕ} (hq : 2 ≤ q) (h2 : (2 : F) ≠ 0) :
    n ≤ globalCubeRank (dictatorFamily) 1 (modQFn q : (Fin n → Bool) → F) := by
  have hLI := linearIndependent_dict (F := F) (n := n) h2
  have hle : Submodule.span F (Set.range (fun i => dict i : Fin n → (Fin n → Bool) → F))
      ≤ globalCubeSpan dictatorFamily 1 (modQFn q) :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr (fun i => dict_mem_globalCubeSpan_modQ hq i))
  have h1 : n = Module.finrank F
      (Submodule.span F (Set.range (fun i => dict i : Fin n → (Fin n → Bool) → F))) := by
    rw [finrank_span_eq_card hLI, Fintype.card_fin]
  simp only [globalCubeRank]
  exact le_trans h1.le (Submodule.finrank_mono hle)

/-- **`MOD_q ∉ small plain `∑∏` (proved)**: for `q ≥ 2` and `2 ≠ 0` in `F`, the cube function `MOD_q` is not any shallow
`∑∏` of `m` `AND`s of fan-in `≤ D` whenever `m·2^D < n`.  (This is the `∑∏` separation, **not** `ACC⁰`; see file header.) -/
theorem modQFn_ne_boolFn_sumProd_of_fanin {q m D : ℕ} (S : Fin m → Finset (Fin n))
    (hq : 2 ≤ q) (h2 : (2 : F) ≠ 0) (hD : ∀ j, (S j).card ≤ D) (hmD : m * 2 ^ D < n) :
    (modQFn q : (Fin n → Bool) → F) ≠ boolFn (∑ j, ∏ i ∈ S j, X i) := by
  refine not_sumProd_of_globalCubeRank_gt S (modQFn q) dictatorFamily
    (lt_of_lt_of_le ?_ (n_le_globalCubeRank_modQFn hq h2))
  refine lt_of_le_of_lt ?_ hmD
  refine le_trans (Finset.sum_le_sum (fun j _ => Nat.pow_le_pow_right (by norm_num) (hD j))) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.n_le_globalCubeRank_modQFn
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.modQFn_ne_boolFn_sumProd_of_fanin
