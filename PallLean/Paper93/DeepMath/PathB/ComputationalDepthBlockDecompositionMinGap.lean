import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverBlockDecompositionMin

/-!
# The address-block restriction is necessary: a decomposition gap for `hardF`

`ComputationalDepthObserverBlockDecompositionMin` proves the *positive* min-realized bound: over the `m`
address-block decompositions of `hardF`, the minimum formula-observer boundary is `≥ 2^b − 1`
(super-logarithmic).  Its honest-scope note says the class is restricted — a decider could pick a decomposition
*outside* the address blocks.  This file turns that caveat into a theorem, exactly as
`equality_decomposition_gap` does for the fixed-cut EQUALITY collapse.

**The single-variable cut is cheap (for every function).**  `formulaBlockBoundary_singleton_le`: reading one
variable produces at most `4` residuals (a residual on `{v}` is determined by the two values of `F` with `v`
set to `false`/`true`), so its observer boundary is `≤ 2` — for *any* `B₂` formula `F`, not just `hardF`.

**Hence the min over all subsets collapses.**  `hardF_decomposition_gap`: for `b ≥ 2` there is a single-variable
decomposition with boundary `≤ 2`, while *every* address block has boundary `≥ 3` (indeed `≥ 2^b − 1`).  So the
minimum boundary over **all** decompositions is `≤ 2`, not super-logarithmic — the super-log min-realized bound
is a genuine property of the *address-block class*, and the restriction to it is essential and quantitatively
tight (`≤ 2` outside the class vs `≥ 2^b − 1` inside).

## Honest scope

A machine-checked *necessity/tightness* companion to the address-block min-realized rung.  It sharpens — does not
weaken — the positive result: it shows precisely why the min is taken over the structured class rather than all
decompositions (the latter collapses, just as for EQUALITY).  It proves no separation and no new lower bound.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinGap

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NecHard
open PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk
open scoped BigOperators

/-! ## The single-variable cut is cheap for every formula -/

/-- A residual of `F` on a singleton `{v}` depends only on `x v`, so there are at most `4` of them: the map
`α ↦ residual_α` factors through `(F|_{v=false}, F|_{v=true}) ∈ Bool × Bool`. -/
theorem blockResiduals_singleton_card_le {n : ℕ} (v : Fin n) (F : BFormula n) :
    (blockResiduals ({v} : Finset (Fin n)) F).card ≤ 4 := by
  classical
  have key : ∀ α : Fin n → Bool,
      (fun x : Fin n → Bool =>
          BFormula.eval F (fun i => if i ∈ ({v} : Finset (Fin n)) then x i else α i))
        = (fun x : Fin n → Bool =>
            if x v then BFormula.eval F (Function.update α v true)
            else BFormula.eval F (Function.update α v false)) := by
    intro α
    funext x
    have harg : (fun i => if i ∈ ({v} : Finset (Fin n)) then x i else α i)
        = Function.update α v (x v) := by
      funext i
      by_cases hiv : i = v
      · subst hiv; simp [Function.update_self]
      · simp [Finset.mem_singleton, hiv, Function.update_of_ne hiv]
    rw [harg]
    cases x v <;> simp
  have hsub : blockResiduals ({v} : Finset (Fin n)) F ⊆
      (Finset.univ : Finset (Bool × Bool)).image
        (fun p => (fun x : Fin n → Bool => if x v then p.2 else p.1)) := by
    intro g hg
    simp only [blockResiduals, Finset.mem_image, Finset.mem_univ, true_and] at hg
    obtain ⟨α, rfl⟩ := hg
    rw [key α]
    exact Finset.mem_image.mpr
      ⟨(BFormula.eval F (Function.update α v false), BFormula.eval F (Function.update α v true)),
        Finset.mem_univ _, rfl⟩
  calc (blockResiduals ({v} : Finset (Fin n)) F).card
      ≤ ((Finset.univ : Finset (Bool × Bool)).image
          (fun p => (fun x : Fin n → Bool => if x v then p.2 else p.1))).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Bool × Bool)).card := Finset.card_image_le
    _ = 4 := by decide

/-- **The single-variable decomposition is cheap.**  For any `B₂` formula `F` and any variable `v`, the formula
observer's boundary on `{v}` is `≤ 2`. -/
theorem formulaBlockBoundary_singleton_le {n : ℕ} (v : Fin n) (F : BFormula n) :
    formulaBlockBoundary {v} F ≤ 2 := by
  unfold formulaBlockBoundary
  calc Nat.log 2 ((blockResiduals ({v} : Finset (Fin n)) F).card)
      ≤ Nat.log 2 (2 ^ 2) :=
        Nat.log_mono_right (le_trans (blockResiduals_singleton_card_le v F) (by norm_num))
    _ = 2 := Nat.log_pow (by norm_num) 2

/-! ## The decomposition gap for `hardF` -/

variable {b m : ℕ}

/-- **Decomposition gap for `hardF`.**  For `b ≥ 2`: some single-variable decomposition has boundary `≤ 2`,
while *every* address block has boundary `≥ 3` (`≥ 2^b − 1`).  Hence the minimum boundary over *all*
decompositions collapses to `≤ 2` — the super-logarithmic min-realized bound genuinely requires the
address-block class, and the restriction is quantitatively tight.  (The `hardF` analogue of
`equality_decomposition_gap`.) -/
theorem hardF_decomposition_gap (hb : 2 ≤ b) (hm : 0 < m)
    (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = hardF x) :
    (∃ v : Fin (nn b m), formulaBlockBoundary {v} F ≤ 2)
      ∧ (∀ k : Fin m, 3 ≤ formulaBlockBoundary (blockS k) F) := by
  have hpos : 0 < nn b m := by
    unfold nn
    have hD : 0 < Dsize b := by rw [dsize_eq]; positivity
    omega
  refine ⟨⟨⟨0, hpos⟩, formulaBlockBoundary_singleton_le _ F⟩, fun k => ?_⟩
  have hbb := hardF_blockBoundary_ge k F hF
  have hd : Dsize b = 2 ^ b := dsize_eq
  have h4 : 4 ≤ 2 ^ b := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  omega

end PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinGap

#print axioms PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinGap.formulaBlockBoundary_singleton_le
#print axioms PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinGap.hardF_decomposition_gap
