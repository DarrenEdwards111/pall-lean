import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMajorityAlgebraicImmunity

/-!
# Optimality: the matching upper bound `AI(f) ≤ ⌈n/2⌉` for every Boolean function

The lower bound `AI(Maj_{2t-1}) ≥ t` (in `…MajorityAlgebraicImmunity`) shows Majority's immunity grows.  Here we
prove the matching **upper bound**: *every* Boolean function on `n` variables has algebraic immunity `≤ ⌈n/2⌉`.
Together they give `AI(Maj_n) = ⌈n/2⌉` — Majority is **optimal**.

The argument is a dimension / pigeonhole count, not the Möbius inversion:

* The space of ANF degree‑`< d+1` functions has `#{S : |S| ≤ d}` coefficients; annihilating `f` imposes
  `#supp(f)` linear constraints.  If `#{S : |S| ≤ d} > #supp(f)`, a nonzero degree‑`≤ d` annihilator exists
  (more unknowns than equations — pigeonhole on the evaluation map).
* For `d = ⌈n/2⌉`, `#{S : |S| ≤ ⌈n/2⌉} > 2^{n-1}` (complement symmetry on subset sizes), and one of
  `supp(f)`, `supp(¬f)` has `≤ 2^{n-1}` points.  So a degree‑`≤ ⌈n/2⌉` annihilator of `f` or of `¬f` exists.

## Proved (clean axioms, no `sorry`)

* `exists_low_degree_annihilator` — **the pigeonhole core**: if `#supp(f) < #{S : |S| ≤ d}`, there is a nonzero
  `g` of ANF degree `≤ d` (`anf g` vanishes on `|S| > d`) with `g` vanishing on `supp(f)` (a degree‑`≤ d`
  annihilator).  Proved by `Fintype.exists_ne_map_eq_of_card_lt` on the coefficient→evaluation map, lifted via
  `cmask` and the `F₂` involution `anf_involutive`.
* `card_small_subsets_gt` — `#{S : |S| ≤ ⌈n/2⌉} > 2^{n-1}` (complement symmetry `S ↦ Sᶜ` + inclusion–exclusion).
* `algebraic_immunity_le_ceil` — **`AI(f) ≤ ⌈n/2⌉`**: every `f` has a nonzero ANF degree‑`≤ ⌈n/2⌉` function
  annihilating `f` or `¬f`.  Combined with the lower bound, `AI(Maj_{2t-1}) = t = ⌈n/2⌉` — optimal.
-/

namespace PallLean.Paper93.DeepMath.PathB.MajorityAIUpper

open Finset
open PallLean.Paper93.DeepMath.PathB.MajorityAI

variable {n : ℕ}

/-- Lift a coefficient function on small sets (`|S| ≤ d`) to all sets, padding by `0`. -/
def cmask {d : ℕ} (c : {S : Finset (Fin n) // S.card ≤ d} → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  if h : S.card ≤ d then c ⟨S, h⟩ else 0

/-- The subset‑sum transform is additive. -/
theorem anf_sub (a b : Finset (Fin n) → ZMod 2) (S : Finset (Fin n)) :
    anf (a - b) S = anf a S - anf b S := by
  simp only [anf, Pi.sub_apply, Finset.sum_sub_distrib]

/-- **The pigeonhole core (proved).**  If `f`'s support is smaller than the number of small sets
(`#supp(f) < #{S : |S| ≤ d}`), there is a nonzero degree‑`≤ d` annihilator of `f`: a nonzero `g` whose ANF
coefficients vanish above size `d` and which vanishes on `supp(f)`. -/
theorem exists_low_degree_annihilator (f : Finset (Fin n) → ZMod 2) (d : ℕ)
    (hcard : (univ.filter (fun T : Finset (Fin n) => f T = 1)).card
           < (univ.filter (fun S : Finset (Fin n) => S.card ≤ d)).card) :
    ∃ g : Finset (Fin n) → ZMod 2,
      g ≠ 0 ∧ (∀ S : Finset (Fin n), d < S.card → anf g S = 0) ∧ (∀ T, f T = 1 → g T = 0) := by
  classical
  -- the coefficient → evaluation‑on‑support map
  let Φ : ({S : Finset (Fin n) // S.card ≤ d} → ZMod 2) →
      ({T : Finset (Fin n) // f T = 1} → ZMod 2) := fun c T => anf (cmask c) T.val
  have hlt : Fintype.card ({T : Finset (Fin n) // f T = 1} → ZMod 2)
           < Fintype.card ({S : Finset (Fin n) // S.card ≤ d} → ZMod 2) := by
    simp only [Fintype.card_fun, ZMod.card]
    apply Nat.pow_lt_pow_right (by norm_num)
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact hcard
  obtain ⟨c₁, c₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt Φ hlt
  refine ⟨anf (cmask c₁) - anf (cmask c₂), ?_, ?_, ?_⟩
  · -- nonzero: differs from 0 at the witnessing coefficient
    obtain ⟨S₀, hS₀⟩ := Function.ne_iff.mp hne
    intro hg
    apply hS₀
    have key : cmask c₁ S₀.val - cmask c₂ S₀.val = 0 := by
      have hval : anf (anf (cmask c₁) - anf (cmask c₂)) S₀.val
          = cmask c₁ S₀.val - cmask c₂ S₀.val := by
        rw [anf_sub, anf_involutive, anf_involutive]
      rw [hg] at hval
      rw [show anf (0 : Finset (Fin n) → ZMod 2) S₀.val = 0 from by simp [anf]] at hval
      exact hval.symm
    rw [cmask, dif_pos S₀.2, cmask, dif_pos S₀.2, Subtype.coe_eta] at key
    exact sub_eq_zero.mp key
  · -- ANF degree ≤ d : coefficients above size d vanish
    intro S hS
    have hval : anf (anf (cmask c₁) - anf (cmask c₂)) S = cmask c₁ S - cmask c₂ S := by
      rw [anf_sub, anf_involutive, anf_involutive]
    rw [hval]
    have hnle : ¬ S.card ≤ d := by omega
    simp only [cmask, dif_neg hnle, sub_zero]
  · -- vanishes on supp(f)
    intro T hT
    show anf (cmask c₁) T - anf (cmask c₂) T = 0
    have h := congrFun heq ⟨T, hT⟩
    simp only [Φ] at h
    rw [h, sub_self]

/-- **More than half the subsets are small (proved).**  `#{S : |S| ≤ ⌈n/2⌉} > 2^{n-1}`, by the complement
symmetry `S ↦ Sᶜ` (which matches small sets with large sets) and inclusion–exclusion: the small and large
families cover everything and overlap, so each exceeds half. -/
theorem card_small_subsets_gt (hn : 1 ≤ n) :
    2 ^ (n - 1) < (univ.filter (fun S : Finset (Fin n) => S.card ≤ (n + 1) / 2)).card := by
  classical
  set d := (n + 1) / 2 with hd
  set A := univ.filter (fun S : Finset (Fin n) => S.card ≤ d) with hA
  set B := univ.filter (fun S : Finset (Fin n) => n - d ≤ S.card) with hB
  have hAB : A.card = B.card := by
    apply Finset.card_nbij' (fun S => Sᶜ) (fun S => Sᶜ)
    · intro S hS
      simp only [hA, hB, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      have hc : Sᶜ.card = n - S.card := by rw [Finset.card_compl, Fintype.card_fin]
      have hsn : S.card ≤ n := card_finset_fin_le S
      rw [hc]; omega
    · intro S hS
      simp only [hA, hB, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      have hc : Sᶜ.card = n - S.card := by rw [Finset.card_compl, Fintype.card_fin]
      have hsn : S.card ≤ n := card_finset_fin_le S
      rw [hc]; omega
    · intro S _; simp [compl_compl]
    · intro S _; simp [compl_compl]
  have hunion : A ∪ B = univ := by
    rw [Finset.eq_univ_iff_forall]
    intro S
    simp only [hA, hB, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    have hsn : S.card ≤ n := card_finset_fin_le S
    omega
  have hinter : (A ∩ B).Nonempty := by
    obtain ⟨S, _, hScard⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin n))) (n := n - d)
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    refine ⟨S, ?_⟩
    simp only [hA, hB, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hScard]; omega
  have huniv : (univ : Finset (Finset (Fin n))).card = 2 ^ n := by
    rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  have hcombine : A.card + B.card = (univ : Finset (Finset (Fin n))).card + (A ∩ B).card := by
    rw [← hunion]; exact (Finset.card_union_add_card_inter A B).symm
  have hpos : 0 < (A ∩ B).card := Finset.card_pos.mpr hinter
  have h2 : 2 * 2 ^ (n - 1) = 2 ^ n := by rw [← pow_succ']; congr 1; omega
  rw [huniv] at hcombine
  omega

/-- **`AI(f) ≤ ⌈n/2⌉` (proved).**  Every Boolean function `f` on `n ≥ 1` variables has a nonzero ANF
degree‑`≤ ⌈n/2⌉` function annihilating `f` or `¬f`.  Whichever of `supp(f)`, `supp(¬f)` has `≤ 2^{n-1}` points is
smaller than `#{S : |S| ≤ ⌈n/2⌉}`, so `exists_low_degree_annihilator` applies. -/
theorem algebraic_immunity_le_ceil (f : Finset (Fin n) → ZMod 2) (hn : 1 ≤ n) :
    ∃ g : Finset (Fin n) → ZMod 2, g ≠ 0 ∧ (∀ S : Finset (Fin n), (n + 1) / 2 < S.card → anf g S = 0) ∧
      ((∀ T, f T = 1 → g T = 0) ∨ (∀ T, f T = 0 → g T = 0)) := by
  classical
  have hsmall : 2 ^ (n - 1) < (univ.filter (fun S : Finset (Fin n) => S.card ≤ (n + 1) / 2)).card :=
    card_small_subsets_gt hn
  have hfeq : (univ.filter (fun T : Finset (Fin n) => f T = 0))
            = (univ.filter (fun T : Finset (Fin n) => ¬ f T = 1)) := by
    apply Finset.filter_congr
    intro T _
    have h : ∀ x : ZMod 2, (x = 0) ↔ (¬ x = 1) := by decide
    exact h (f T)
  have hpart : (univ.filter (fun T : Finset (Fin n) => f T = 1)).card
             + (univ.filter (fun T : Finset (Fin n) => f T = 0)).card = 2 ^ n := by
    rw [hfeq, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_finset,
        Fintype.card_fin]
  have h2 : 2 * 2 ^ (n - 1) = 2 ^ n := by rw [← pow_succ']; congr 1; omega
  by_cases hf : (univ.filter (fun T : Finset (Fin n) => f T = 1)).card ≤ 2 ^ (n - 1)
  · obtain ⟨g, hg0, hgd, hgann⟩ := exists_low_degree_annihilator f ((n + 1) / 2) (by omega)
    exact ⟨g, hg0, hgd, Or.inl hgann⟩
  · push_neg at hf
    have hcard0 : (univ.filter (fun T : Finset (Fin n) => (1 : ZMod 2) - f T = 1)).card
                < (univ.filter (fun S : Finset (Fin n) => S.card ≤ (n + 1) / 2)).card := by
      have hset : (univ.filter (fun T : Finset (Fin n) => (1 : ZMod 2) - f T = 1))
                = (univ.filter (fun T : Finset (Fin n) => f T = 0)) := by
        apply Finset.filter_congr
        intro T _
        have h : ∀ x : ZMod 2, ((1 - x = 1) ↔ (x = 0)) := by decide
        exact h (f T)
      rw [hset]
      omega
    obtain ⟨g, hg0, hgd, hgann⟩ := exists_low_degree_annihilator (fun T => 1 - f T) ((n + 1) / 2) hcard0
    refine ⟨g, hg0, hgd, Or.inr ?_⟩
    intro T hT0
    apply hgann
    show (1 : ZMod 2) - f T = 1
    rw [hT0, sub_zero]

/-- **`AI(Maj_{2t-1}) = t = ⌈n/2⌉` — optimality (proved).**  For `n = 2t-1`, packaging the two bounds:
*(lower)* no nonzero ANF degree‑`< t` function annihilates `Maj` or `¬Maj`; *(upper)* a nonzero ANF degree‑`≤ t`
function annihilates `Maj` or `¬Maj`.  Hence the minimal annihilator degree is exactly `t = ⌈n/2⌉`: Majority has
the **optimal** algebraic immunity. -/
theorem majority_AI_optimal {t : ℕ} (ht : 1 ≤ t) (hn : n = 2 * t - 1) :
    (∀ g : Finset (Fin n) → ZMod 2, g ≠ 0 → DegreeLt g t →
        (∃ T, g T * Maj t T ≠ 0) ∧ (∃ T, g T * negMaj t T ≠ 0))
    ∧ (∃ g : Finset (Fin n) → ZMod 2, g ≠ 0 ∧ (∀ S : Finset (Fin n), t < S.card → anf g S = 0) ∧
        ((∀ T, Maj t T = 1 → g T = 0) ∨ (∀ T, Maj t T = 0 → g T = 0))) := by
  have hn1 : 1 ≤ n := by omega
  have hceil : (n + 1) / 2 = t := by omega
  refine ⟨fun g hg hdeg => majority_algebraic_immunity_two_sided (by omega) g hg hdeg, ?_⟩
  obtain ⟨g, hg0, hgd, hgann⟩ := algebraic_immunity_le_ceil (Maj t) hn1
  rw [hceil] at hgd
  exact ⟨g, hg0, hgd, hgann⟩

end PallLean.Paper93.DeepMath.PathB.MajorityAIUpper

#print axioms PallLean.Paper93.DeepMath.PathB.MajorityAIUpper.algebraic_immunity_le_ceil
#print axioms PallLean.Paper93.DeepMath.PathB.MajorityAIUpper.majority_AI_optimal
