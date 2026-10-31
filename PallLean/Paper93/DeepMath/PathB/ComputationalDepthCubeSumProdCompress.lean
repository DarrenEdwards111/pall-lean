import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeAdmissibleBoundary

/-!
# Step 4: shallow `∑∏` / BT forms are boundary-compressible (small cube-derivative rank)

The admissible-boundary rung classified the two *extreme* witnesses (`∏Xᵢ` fragile, parity robust).  This file does the
**easy side in general**: a shallow `∑∏` (sum of `m` bounded-fan-in `AND` gates) has cube-derivative rank bounded by
`∑ⱼ 2^{|Sⱼ|} ≤ m·2^D` — **independent of the number of variables `n`**.  This is the cube-native analog of the Part C
product upper bound `spdpRank_prod_le_card`: easy shallow forms are compressible.

Two ingredients:

* **Locality** — a monomial `∏_{i∈S} Xᵢ` depends only on the `S`-coordinates, so all its cube-derivatives live in the
  pullback subspace `range (embS S)` of dimension `2^{|S|}`:
    `boolFn_monoAND_mem_range`, `cubeDeriv_mem_range_embS`, `cubeDerivList_mem_range_embS`,
    `cubeDerivRank_boolFn_monoAND_le` — `cubeDerivRank κ (boolFn ∏_{i∈S} Xᵢ) ≤ 2^{|S|}`.
* **Subadditivity** — cube-rank is subadditive (derivatives are linear):
    `cubeDerivRank_add_le`, `cubeDerivRank_sum_le`.

Combining (with `boolFn_sum`):
    `cubeDerivRank_boolFn_sumProd_le` — `cubeDerivRank κ (boolFn ∑ⱼ ∏_{i∈Sⱼ} Xᵢ) ≤ ∑ⱼ 2^{|Sⱼ|}`.
    `cubeDerivRank_boolFn_sumProd_le_fanin` — `≤ m·2^D` under fan-in `≤ D`.

Since `restrictB` is linear and preserves the pullback subspace, the same bound holds through **any** boundary:
    `boundaryCubeRank_boolFn_sumProd_le` — `boundaryCubeRank ρ κ (boolFn ∑∏) ≤ ∑ⱼ 2^{|Sⱼ|}`.

So shallow `∑∏` is compressible both raw and through every observer cut — the "easy = boundary-compressible" half of the
cube-Godmove picture (HAL step 4), complementing the parity/`MOD` robustness (`≥ 1` under every cut).

## Honest scope

This is a genuine upper bound (the compressibility side), the cube-native `spdpRank_prod_le_card`.  It is **not** the
separation: the hard-side robustness lower bound for a full `MOD_q`/composite family across a boundary *family* (HAL
steps 5–6, the global dual separator) is not here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.NFrameACC0 (boolFn)

variable {n : ℕ} {F : Type*} [Field F]

/-! ### Subadditivity of cube-derivative rank -/

theorem cubeDeriv_add (i : Fin n) (f g : (Fin n → Bool) → F) :
    cubeDeriv i (f + g) = cubeDeriv i f + cubeDeriv i g := by
  funext x; simp only [cubeDeriv, Pi.add_apply]; ring

theorem cubeDerivList_add (L : List (Fin n)) (f g : (Fin n → Bool) → F) :
    cubeDerivList L (f + g) = cubeDerivList L f + cubeDerivList L g := by
  induction L generalizing f g with
  | nil => rfl
  | cons i L' ih =>
    show cubeDerivList L' (cubeDeriv i (f + g))
        = cubeDerivList L' (cubeDeriv i f) + cubeDerivList L' (cubeDeriv i g)
    rw [cubeDeriv_add, ih]

theorem cubeDerivRank_add_le (κ : ℕ) (f g : (Fin n → Bool) → F) :
    cubeDerivRank κ (f + g) ≤ cubeDerivRank κ f + cubeDerivRank κ g := by
  have hle : cubeDerivSpan κ (f + g) ≤ cubeDerivSpan κ f ⊔ cubeDerivSpan κ g := by
    rw [cubeDerivSpan, Submodule.span_le]
    rintro h ⟨L, hlen, rfl⟩
    rw [cubeDerivList_add]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.subset_span ⟨L, hlen, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨L, hlen, rfl⟩))
  have hkey := Submodule.finrank_sup_add_finrank_inf_eq (cubeDerivSpan κ f) (cubeDerivSpan κ g)
  have hmono := Submodule.finrank_mono hle
  simp only [cubeDerivRank]
  omega

theorem cubeDerivRank_sum_le {ι : Type*} (s : Finset ι) (f : ι → (Fin n → Bool) → F) {κ : ℕ} :
    cubeDerivRank κ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, cubeDerivRank κ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [cubeDerivRank_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (cubeDerivRank_add_le _ _ _) (Nat.add_le_add_left ih _)

/-! ### Locality: the pullback subspace of an `S`-local function -/

/-- The pullback of functions on the `S`-subcube into the full cube (functions depending only on `S`-coordinates). -/
noncomputable def embS (S : Finset (Fin n)) : ((↥S → Bool) → F) →ₗ[F] ((Fin n → Bool) → F) where
  toFun h := fun x => h (fun i => x i.val)
  map_add' h1 h2 := by funext x; simp
  map_smul' c h := by funext x; simp

theorem embS_apply (S : Finset (Fin n)) (h : (↥S → Bool) → F) (x : Fin n → Bool) :
    embS S h x = h (fun i => x i.val) := rfl

/-- A monomial's cube-function lies in the `S`-pullback subspace. -/
theorem boolFn_monoAND_mem_range (S : Finset (Fin n)) :
    boolFn (∏ i ∈ S, X i : MvPolynomial (Fin n) F) ∈ LinearMap.range (embS S (F := F)) := by
  refine ⟨fun y => ∏ i : ↥S, (if y i then (1 : F) else 0), ?_⟩
  funext x
  simp only [embS_apply, boolFn, map_prod, MvPolynomial.eval_X]
  exact Finset.prod_coe_sort S (fun i => if x i then (1 : F) else 0)

/-- The `S`-pullback subspace is closed under cube derivatives. -/
theorem cubeDeriv_mem_range_embS (S : Finset (Fin n)) (j : Fin n) (g : (Fin n → Bool) → F)
    (hg : g ∈ LinearMap.range (embS S (F := F))) :
    cubeDeriv j g ∈ LinearMap.range (embS S (F := F)) := by
  obtain ⟨h, rfl⟩ := hg
  by_cases hj : j ∈ S
  · refine ⟨fun y => h (fun i => if i = ⟨j, hj⟩ then !(y i) else y i) - h y, ?_⟩
    funext x
    have harg : (fun i : ↥S => if i = ⟨j, hj⟩ then !(x i.val) else x i.val)
        = (fun i : ↥S => (flipBit j x) i.val) := by
      funext i
      simp only [flipBit]
      by_cases hij : i = ⟨j, hj⟩
      · subst hij; simp
      · have hne : (i : Fin n) ≠ j := fun hv => hij (Subtype.ext hv)
        rw [if_neg hij, if_neg hne]
    simp only [embS_apply, cubeDeriv]
    rw [harg]
  · refine ⟨0, ?_⟩
    funext x
    have hr : (fun i : ↥S => (flipBit j x) i.val) = (fun i : ↥S => x i.val) := by
      funext i
      simp only [flipBit]
      have hne : (i : Fin n) ≠ j := fun hv => hj (hv ▸ i.2)
      rw [if_neg hne]
    simp only [embS_apply, cubeDeriv, Pi.zero_apply]
    rw [hr, sub_self]

/-- Iterated cube derivatives stay in the `S`-pullback subspace. -/
theorem cubeDerivList_mem_range_embS (S : Finset (Fin n)) (L : List (Fin n))
    (g : (Fin n → Bool) → F) (hg : g ∈ LinearMap.range (embS S (F := F))) :
    cubeDerivList L g ∈ LinearMap.range (embS S (F := F)) := by
  induction L generalizing g with
  | nil => exact hg
  | cons i L' ih =>
    exact ih (cubeDeriv i g) (cubeDeriv_mem_range_embS S i g hg)

/-- **Locality bound (proved)**: a monomial `∏_{i∈S} Xᵢ` has cube-derivative rank `≤ 2^{|S|}` — its derivatives live in
the `S`-local pullback subspace, dimension `2^{|S|}`, independent of `n`. -/
theorem cubeDerivRank_boolFn_monoAND_le (S : Finset (Fin n)) {κ : ℕ} :
    cubeDerivRank κ (boolFn (∏ i ∈ S, X i : MvPolynomial (Fin n) F)) ≤ 2 ^ S.card := by
  have hle : cubeDerivSpan κ (boolFn (∏ i ∈ S, X i : MvPolynomial (Fin n) F))
      ≤ LinearMap.range (embS S (F := F)) := by
    rw [cubeDerivSpan, Submodule.span_le]
    rintro g ⟨L, hlen, rfl⟩
    exact cubeDerivList_mem_range_embS S L _ (boolFn_monoAND_mem_range S)
  refine le_trans (Submodule.finrank_mono hle) ?_
  refine le_trans (LinearMap.finrank_range_le (embS S (F := F))) ?_
  rw [Module.finrank_pi]
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

/-! ### Compressibility of shallow `∑∏` -/

/-- `boolFn` is additive (a `∑` of cube-functions). -/
theorem boolFn_sum {m : ℕ} (p : Fin m → MvPolynomial (Fin n) F) :
    boolFn (∑ j, p j) = ∑ j, boolFn (p j) := by
  funext x
  rw [boolFn, map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => rfl)

/-- **Compressibility of shallow `∑∏` (proved)**: `cubeDerivRank κ (boolFn ∑ⱼ ∏_{i∈Sⱼ} Xᵢ) ≤ ∑ⱼ 2^{|Sⱼ|}`. -/
theorem cubeDerivRank_boolFn_sumProd_le {m : ℕ} (S : Fin m → Finset (Fin n)) {κ : ℕ} :
    cubeDerivRank κ (boolFn (∑ j, ∏ i ∈ S j, X i : MvPolynomial (Fin n) F))
      ≤ ∑ j, 2 ^ (S j).card := by
  rw [boolFn_sum]
  refine le_trans (cubeDerivRank_sum_le _ _) ?_
  exact Finset.sum_le_sum (fun j _ => cubeDerivRank_boolFn_monoAND_le (S j))

/-- **Compressibility under fan-in `≤ D` (proved)**: shallow `∑∏` of `m` `AND`s of fan-in `≤ D` has cube-derivative rank
`≤ m·2^D` — independent of `n`. -/
theorem cubeDerivRank_boolFn_sumProd_le_fanin {m D : ℕ} (S : Fin m → Finset (Fin n))
    (hD : ∀ j, (S j).card ≤ D) {κ : ℕ} :
    cubeDerivRank κ (boolFn (∑ j, ∏ i ∈ S j, X i : MvPolynomial (Fin n) F)) ≤ m * 2 ^ D := by
  refine le_trans (cubeDerivRank_boolFn_sumProd_le S) ?_
  refine le_trans (Finset.sum_le_sum (fun j _ => Nat.pow_le_pow_right (by norm_num) (hD j))) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-! ### The bound holds through any admissible boundary -/

/-- `restrictB` is additive over a `∑` (the projection is linear). -/
theorem restrictB_sum (ρ : Fin n → Option Bool) {m : ℕ} (p : Fin m → (Fin n → Bool) → F) :
    restrictB ρ (∑ j, p j) = ∑ j, restrictB ρ (p j) := by
  funext x
  simp only [restrictB, Finset.sum_apply]

/-- The `S`-pullback subspace is preserved by every boundary projection. -/
theorem restrictB_mem_range_embS (S : Finset (Fin n)) (ρ : Fin n → Option Bool)
    (v : (Fin n → Bool) → F) (hv : v ∈ LinearMap.range (embS S (F := F))) :
    restrictB ρ v ∈ LinearMap.range (embS S (F := F)) := by
  obtain ⟨h, rfl⟩ := hv
  refine ⟨fun y => h (fun i => (ρ i.val).getD (y i)), ?_⟩
  funext x
  simp only [embS_apply, restrictB]

/-- **Boundary locality bound (proved)**: through *any* boundary `ρ`, a monomial keeps `boundaryCubeRank ρ κ (boolFn
∏_{i∈S} Xᵢ) ≤ 2^{|S|}`. -/
theorem boundaryCubeRank_boolFn_monoAND_le (ρ : Fin n → Option Bool) (S : Finset (Fin n)) {κ : ℕ} :
    boundaryCubeRank ρ κ (boolFn (∏ i ∈ S, X i : MvPolynomial (Fin n) F)) ≤ 2 ^ S.card := by
  rw [boundaryCubeRank]
  have hmem : restrictB ρ (boolFn (∏ i ∈ S, X i : MvPolynomial (Fin n) F))
      ∈ LinearMap.range (embS S (F := F)) :=
    restrictB_mem_range_embS S ρ _ (boolFn_monoAND_mem_range S)
  have hle : cubeDerivSpan κ (restrictB ρ (boolFn (∏ i ∈ S, X i : MvPolynomial (Fin n) F)))
      ≤ LinearMap.range (embS S (F := F)) := by
    rw [cubeDerivSpan, Submodule.span_le]
    rintro g ⟨L, hlen, rfl⟩
    exact cubeDerivList_mem_range_embS S L _ hmem
  refine le_trans (Submodule.finrank_mono hle) ?_
  refine le_trans (LinearMap.finrank_range_le (embS S (F := F))) ?_
  rw [Module.finrank_pi, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

/-- **Boundary compressibility of shallow `∑∏` (proved)**: through *any* boundary, `boundaryCubeRank ρ κ (boolFn ∑∏) ≤
∑ⱼ 2^{|Sⱼ|}` — easy shallow forms compress under every observer cut, complementing the parity/`MOD` robustness. -/
theorem boundaryCubeRank_boolFn_sumProd_le (ρ : Fin n → Option Bool) {m : ℕ}
    (S : Fin m → Finset (Fin n)) {κ : ℕ} :
    boundaryCubeRank ρ κ (boolFn (∑ j, ∏ i ∈ S j, X i : MvPolynomial (Fin n) F))
      ≤ ∑ j, 2 ^ (S j).card := by
  rw [boundaryCubeRank, boolFn_sum, restrictB_sum]
  refine le_trans (cubeDerivRank_sum_le _ _) ?_
  exact Finset.sum_le_sum (fun j _ => boundaryCubeRank_boolFn_monoAND_le ρ (S j))

end PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.cubeDerivRank_boolFn_monoAND_le
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.cubeDerivRank_boolFn_sumProd_le_fanin
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.boundaryCubeRank_boolFn_sumProd_le
