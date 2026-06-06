import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukSubfunctionMultiplicative

/-!
# Toward `n²/log n`: the leaf-dependency (factoring) lemma and the base rungs

The two failed routes (per-block alphabet, `SkeletonNoGo`) showed the gap is real.  The **correct**
mechanism is that a residual depends on the `S`-variables *only through the `S`-leaves*: with `k`
such leaves the residual is (a fixed gate-composition of) a function of `k` inputs, and — crucially —
gate-chains collapse because `Bool → Bool` is finite (`|Bool → Bool| = 4`).  That collapse is exactly
what the subtree-count missed.

This file establishes the *rigorous* heart of that mechanism and the **base rungs** of the real
`s_i ≤ 4^{leavesIn(S)}` induction:

* `litCount_zero_const` — a literal-free formula computes a constant.
* `leavesIn_one_factors` — if `F` has a single `S`-leaf (reading `i0`), every restriction
  `restrict S α F` depends on its argument **only through coordinate `i0`** (uniformly in `α`).
* `card_blockResiduals_le_two_of_leavesIn_zero` — `leavesIn S F = 0 ⇒ s_i ≤ 2`.
* `card_blockResiduals_le_four_of_leavesIn_one` — `leavesIn S F = 1 ⇒ s_i ≤ 4 = 4¹`
  (the residuals inject into `Bool → Bool`; this is the tight base case, e.g. `(x∧y)∨(¬x∧z)` hits `4`).

## The remaining core (FLAGGED, not faked)

The inductive step `leavesIn S F = k ⇒ s_i ≤ 4^k` is **not** established here.  The naive multiplicative
recursion (`SubfunctionMultiplicative`) loses a factor `2` per `S`-free sibling and so blows up on
gate-chains; closing it needs the **gate-collapse** accounting (contract maximal degree-2 spine paths,
each collapsing to one of the `4` functions `Bool → Bool`).  Formalising that contraction is the open
work.  The headline bound stays `N²/log²N`; reaching `N²/log N` is **not** claimed.
-/

namespace PallLean.Paper93.DeepMath.PathB

open BFormula

variable {n : ℕ}

/-- A literal-free formula computes a constant (its value is independent of the input). -/
theorem litCount_zero_const : ∀ (F : BFormula n), BFormula.litCount F = 0 →
    ∀ x y, BFormula.eval F x = BFormula.eval F y
  | BFormula.lit _ _, h, _, _ => by simp [BFormula.litCount] at h
  | BFormula.cst _, _, _, _ => rfl
  | BFormula.un u t, h, x, y => by
      simp only [BFormula.litCount] at h
      simp only [BFormula.eval, litCount_zero_const t h x y]
  | BFormula.bin g a b, h, x, y => by
      simp only [BFormula.litCount] at h
      simp only [BFormula.eval, litCount_zero_const a (by omega) x y,
        litCount_zero_const b (by omega) x y]

/-- **Single-leaf factoring.**  If `F` reads `S`-variables through exactly one leaf (reading `i0`),
then for every outside assignment `α` the restriction `restrict S α F` depends on its argument only
through coordinate `i0` — uniformly in `α` (the coordinate is structural, not `α`-dependent). -/
theorem leavesIn_one_factors {S : Finset (Fin n)} :
    ∀ (F : BFormula n), BFormula.leavesIn S F = 1 →
      ∃ i0, ∀ (α x y : Fin n → Bool), x i0 = y i0 →
        BFormula.eval (BFormula.restrict S α F) x = BFormula.eval (BFormula.restrict S α F) y
  | BFormula.lit i b, h => by
      by_cases hi : i ∈ S
      · exact ⟨i, fun α x y hxy => by simp [BFormula.restrict, if_pos hi, BFormula.eval, hxy]⟩
      · simp [BFormula.leavesIn, if_neg hi] at h
  | BFormula.cst c, h => by simp [BFormula.leavesIn] at h
  | BFormula.un u t, h => by
      simp only [BFormula.leavesIn] at h
      obtain ⟨i0, hi0⟩ := leavesIn_one_factors t h
      exact ⟨i0, fun α x y hxy => by
        simp only [BFormula.restrict, BFormula.eval]; rw [hi0 α x y hxy]⟩
  | BFormula.bin g a b, h => by
      simp only [BFormula.leavesIn] at h
      rcases (show BFormula.leavesIn S a = 1 ∧ BFormula.leavesIn S b = 0 ∨
                   BFormula.leavesIn S a = 0 ∧ BFormula.leavesIn S b = 1 from by omega) with
        ⟨ha, hb⟩ | ⟨ha, hb⟩
      · obtain ⟨i0, hi0⟩ := leavesIn_one_factors a ha
        refine ⟨i0, fun α x y hxy => ?_⟩
        have hbc : ∀ x y, BFormula.eval (BFormula.restrict S α b) x
            = BFormula.eval (BFormula.restrict S α b) y := by
          apply litCount_zero_const; rw [BFormula.litCount_restrict]; exact hb
        simp only [BFormula.restrict, BFormula.eval]
        rw [hi0 α x y hxy, hbc x y]
      · obtain ⟨i0, hi0⟩ := leavesIn_one_factors b hb
        refine ⟨i0, fun α x y hxy => ?_⟩
        have hac : ∀ x y, BFormula.eval (BFormula.restrict S α a) x
            = BFormula.eval (BFormula.restrict S α a) y := by
          apply litCount_zero_const; rw [BFormula.litCount_restrict]; exact ha
        simp only [BFormula.restrict, BFormula.eval]
        rw [hi0 α x y hxy, hac x y]

/-- Every residual on `S` factors as `restrict`, so a single-leaf block makes each residual depend on
its argument only through `i0`. -/
private theorem residual_factors {S : Finset (Fin n)} {F : BFormula n} {i0 : Fin n}
    (hi0 : ∀ (α x y : Fin n → Bool), x i0 = y i0 →
      BFormula.eval (BFormula.restrict S α F) x = BFormula.eval (BFormula.restrict S α F) y) :
    ∀ φ ∈ blockResiduals S F, ∀ x y, x i0 = y i0 → φ x = φ y := by
  classical
  intro φ hφ x y hxy
  simp only [blockResiduals, Finset.mem_image, Finset.mem_univ, true_and] at hφ
  obtain ⟨α, rfl⟩ := hφ
  have hx := BFormula.eval_restrict S α F x
  have hy := BFormula.eval_restrict S α F y
  show BFormula.eval F (fun i => if i ∈ S then x i else α i)
     = BFormula.eval F (fun i => if i ∈ S then y i else α i)
  rw [← hx, ← hy]; exact hi0 α x y hxy

/-- **Base rung (`leavesIn = 0`).**  A block with no leaves yields at most two residuals (constants). -/
theorem card_blockResiduals_le_two_of_leavesIn_zero {S : Finset (Fin n)} {F : BFormula n}
    (h : BFormula.leavesIn S F = 0) : (blockResiduals S F).card ≤ 2 := by
  classical
  have hconst : ∀ φ ∈ blockResiduals S F, ∀ x y, φ x = φ y := by
    intro φ hφ x y
    simp only [blockResiduals, Finset.mem_image, Finset.mem_univ, true_and] at hφ
    obtain ⟨α, rfl⟩ := hφ
    show BFormula.eval F (fun i => if i ∈ S then x i else α i)
       = BFormula.eval F (fun i => if i ∈ S then y i else α i)
    rw [← BFormula.eval_restrict S α F x, ← BFormula.eval_restrict S α F y]
    exact litCount_zero_const _ (by rw [BFormula.litCount_restrict]; exact h) x y
  have hinj : Set.InjOn (fun φ : (Fin n → Bool) → Bool => φ (fun _ => false))
      (blockResiduals S F : Set _) := by
    intro φ hφ ψ hψ hpq
    simp only [Finset.mem_coe] at hφ hψ
    funext x
    rw [hconst φ hφ x (fun _ => false), hconst ψ hψ x (fun _ => false)]; exact hpq
  calc (blockResiduals S F).card
      = ((blockResiduals S F).image (fun φ => φ (fun _ => false))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset Bool).card := Finset.card_le_card (Finset.subset_univ _)
    _ = 2 := by decide

/-- **Base rung (`leavesIn = 1`).**  A block read through a single leaf yields at most four residuals
(functions of one bit) — the tight base case of `s_i ≤ 4^{leavesIn}`. -/
theorem card_blockResiduals_le_four_of_leavesIn_one {S : Finset (Fin n)} {F : BFormula n}
    (h : BFormula.leavesIn S F = 1) : (blockResiduals S F).card ≤ 4 := by
  classical
  obtain ⟨i0, hi0⟩ := leavesIn_one_factors F h
  have hfac := residual_factors hi0
  have hinj : Set.InjOn (fun φ : (Fin n → Bool) → Bool => (fun v => φ (fun _ => v)))
      (blockResiduals S F : Set _) := by
    intro φ hφ ψ hψ hpq
    simp only [Finset.mem_coe] at hφ hψ
    funext x
    have hφx : φ x = φ (fun _ => x i0) := hfac φ hφ x (fun _ => x i0) (by simp)
    have hψx : ψ x = ψ (fun _ => x i0) := hfac ψ hψ x (fun _ => x i0) (by simp)
    rw [hφx, hψx]
    exact congrFun hpq (x i0)
  calc (blockResiduals S F).card
      = ((blockResiduals S F).image (fun φ => fun v => φ (fun _ => v))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Bool → Bool)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = 4 := by decide

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.leavesIn_one_factors
#print axioms PallLean.Paper93.DeepMath.PathB.card_blockResiduals_le_four_of_leavesIn_one
