import PallLean.Paper93.DeepMath.PathB.ComputationalDepthModPoly
import Mathlib

/-!
# Probabilistic low-degree approximation of OR (PROVED core) — Razborov–Smolensky

`OR` is **not** exactly a low-degree polynomial over `𝔽_p`, but it has a low-degree *probabilistic* approximation
(Razborov–Smolensky): for random subsets `S₁,…,S_t`, the polynomial `1 - ∏ⱼ (1 - Lⱼ^(p-1))` (where
`Lⱼ = Σ_{i∈Sⱼ} xᵢ`) has degree `t(p-1)` and agrees with `OR(x)` with probability `≥ 1 - 2⁻ᵗ`.

The combinatorial **heart** is the halving lemma:

  `card_linForm_zero_le` — for a nonzero `x`, *at most half* of the `2ⁿ` subsets `S` give a zero linear form
        `Σ_{i∈S} xᵢ`.  Proved by the fixed-point-free involution `S ↦ S △ {i₀}` (toggle a coordinate where
        `x i₀ ≠ 0`), which injects the zero-set into the nonzero-set.

This is exactly why a single random linear form distinguishes `x ≠ 0` from `x = 0` with probability `≥ ½`, the
engine of the approximation.  The full `t`-fold amplification / union bound and the polynomial degree bound build
on this; the `MOD_q ∉ AC⁰[p]` lower bound that uses the approximation remains the genuine target.
-/

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.SymAnd (indicator_zero_eq)

namespace PallLean.Paper93.DeepMath.PathB.OrApprox

variable {n : ℕ} {p : ℕ}

/-- A linear form: the sum of a subset `S` of the coordinates of `x`, over `ℤ/pℤ`. -/
def linForm (x : Fin n → ZMod p) (S : Finset (Fin n)) : ZMod p := ∑ i ∈ S, x i

/-- Toggle membership of `i₀` in `S` (i.e. `S △ {i₀}`). -/
def toggle (i₀ : Fin n) (S : Finset (Fin n)) : Finset (Fin n) :=
  if i₀ ∈ S then S.erase i₀ else insert i₀ S

/-- Toggling the same coordinate twice is the identity: the toggle is an involution. -/
theorem toggle_involutive (i₀ : Fin n) : Function.Involutive (toggle i₀ (n := n)) := by
  intro S
  unfold toggle
  by_cases h : i₀ ∈ S
  · rw [if_pos h, if_neg (Finset.notMem_erase _ _), Finset.insert_erase h]
  · rw [if_neg h, if_pos (Finset.mem_insert_self _ _), Finset.erase_insert h]

/-- If `x i₀ ≠ 0`, toggling `i₀` sends a zero linear form to a nonzero one (the sum changes by `± x i₀`). -/
theorem linForm_toggle_ne (x : Fin n → ZMod p) (i₀ : Fin n) (S : Finset (Fin n))
    (hi₀ : x i₀ ≠ 0) (hS : linForm x S = 0) : linForm x (toggle i₀ S) ≠ 0 := by
  by_cases h : i₀ ∈ S
  · rw [toggle, if_pos h]
    have key : linForm x S = x i₀ + linForm x (S.erase i₀) := by
      rw [linForm, linForm, ← Finset.sum_insert (Finset.notMem_erase i₀ S), Finset.insert_erase h]
    intro hzero
    rw [hzero, add_zero, hS] at key
    exact hi₀ key.symm
  · rw [toggle, if_neg h, linForm, Finset.sum_insert h, ← linForm, hS, add_zero]
    exact hi₀

/-- **The halving lemma (combinatorial heart of Razborov–Smolensky).**  For a nonzero `x`, at most half of the
`2ⁿ` subsets give a zero linear form: `2 · #{S : Σ_{i∈S} xᵢ = 0} ≤ 2ⁿ`.  Hence a uniformly random subset gives a
nonzero form with probability `≥ ½`.  Proof: the fixed-point-free involution `toggle i₀` (for `x i₀ ≠ 0`) injects
the zero-set into the nonzero-set. -/
theorem card_linForm_zero_le [Fact p.Prime] (x : Fin n → ZMod p) (hx : x ≠ 0) :
    2 * (Finset.univ.filter (fun S => linForm x S = 0)).card ≤ 2 ^ n := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  rw [Pi.zero_apply] at hi₀
  have hmaps : Set.MapsTo (toggle i₀)
      (Finset.univ.filter (fun S => linForm x S = 0) : Set (Finset (Fin n)))
      (Finset.univ.filter (fun S => linForm x S ≠ 0)) := by
    intro S hS
    rw [Finset.mem_coe, Finset.mem_filter] at hS
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, linForm_toggle_ne x i₀ S hi₀ hS.2⟩
  have hinj : Set.InjOn (toggle i₀)
      (Finset.univ.filter (fun S => linForm x S = 0)) :=
    (toggle_involutive i₀).injective.injOn
  have hcard := Finset.card_le_card_of_injOn (toggle i₀) hmaps hinj
  have hsum : (Finset.univ.filter (fun S => linForm x S = 0)).card
      + (Finset.univ.filter (fun S => linForm x S ≠ 0)).card = 2 ^ n := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Fintype.card_finset, Fintype.card_fin]
  omega

/-- The `0/1`-power identity over `𝔽_p`: `y^(p-1) = [y ≠ 0]` (`0` if `y = 0`, else `1`), from Fermat. -/
theorem pow_card_sub_one [Fact p.Prime] (y : ZMod p) : y ^ (p - 1) = if y = 0 then 0 else 1 := by
  have h := indicator_zero_eq y
  rw [ZMod.card] at h
  have hy : y ^ (p - 1) = 1 - (if y = 0 then (1 : ZMod p) else 0) := by rw [h]; ring
  rw [hy]; by_cases hc : y = 0 <;> simp [hc]

/-- The **single random-form approximator** of `OR`: `L_S^(p-1)` where `L_S = Σ_{i∈S} Xᵢ`.  Degree `p-1`. -/
noncomputable def orApprox1 (p : ℕ) (S : Finset (Fin n)) : MvPolynomial (Fin n) (ZMod p) :=
  (∑ i ∈ S, X i) ^ (p - 1)

/-- The single-form approximator, on a Boolean input, equals `[L_S ≠ 0]` (`0` if the form vanishes, else `1`). -/
theorem orApprox1_eval [Fact p.Prime] (x : Fin n → Bool) (S : Finset (Fin n)) :
    eval (fun i => ((x i).toNat : ZMod p)) (orApprox1 p S)
      = if linForm (fun i => ((x i).toNat : ZMod p)) S = 0 then 0 else 1 := by
  rw [orApprox1, map_pow, map_sum]
  simp only [eval_X]
  rw [← linForm, pow_card_sub_one]

/-- A Boolean input with a true coordinate is a nonzero `𝔽_p`-vector. -/
theorem boolVec_ne_zero [Fact p.Prime] (x : Fin n → Bool) (hx : ∃ i, x i = true) :
    (fun i => ((x i).toNat : ZMod p)) ≠ 0 := by
  obtain ⟨i₀, hi₀⟩ := hx
  refine Function.ne_iff.mpr ⟨i₀, ?_⟩
  simp only [Pi.zero_apply, hi₀, Bool.toNat_true, Nat.cast_one]
  exact one_ne_zero

/-- **Probabilistic approximation of `OR` (single form).**  When `OR(x) = true` (some input is true), the
single-form approximator `L_S^(p-1)` *disagrees* with `OR` (i.e. evaluates to `0` rather than `1`) for at most
half of the subsets `S`.  Equivalently, a uniformly random `S` makes `L_S^(p-1) = 1 = OR(x)` with probability
`≥ ½`.  (On `OR(x) = false` the approximator is identically `0 = OR(x)`.)  This is the halving lemma applied to
the Boolean vector. -/
theorem orApprox1_disagree_count [Fact p.Prime] (x : Fin n → Bool) (hx : ∃ i, x i = true) :
    2 * (Finset.univ.filter (fun S =>
      eval (fun i => ((x i).toNat : ZMod p)) (orApprox1 p S) = 0)).card ≤ 2 ^ n := by
  classical
  have hb := boolVec_ne_zero (p := p) x hx
  have hfilter : (Finset.univ.filter (fun S =>
        eval (fun i => ((x i).toNat : ZMod p)) (orApprox1 p S) = 0))
      = Finset.univ.filter (fun S => linForm (fun i => ((x i).toNat : ZMod p)) S = 0) := by
    apply Finset.filter_congr
    intro S _
    rw [orApprox1_eval]
    by_cases h : linForm (fun i => ((x i).toNat : ZMod p)) S = 0 <;> simp [h]
  rw [hfilter]
  exact card_linForm_zero_le _ hb

end PallLean.Paper93.DeepMath.PathB.OrApprox

#print axioms PallLean.Paper93.DeepMath.PathB.OrApprox.toggle_involutive
#print axioms PallLean.Paper93.DeepMath.PathB.OrApprox.card_linForm_zero_le
#print axioms PallLean.Paper93.DeepMath.PathB.OrApprox.orApprox1_eval
#print axioms PallLean.Paper93.DeepMath.PathB.OrApprox.orApprox1_disagree_count
