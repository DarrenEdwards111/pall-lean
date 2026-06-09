import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityWidthAwareBlockCleanSeq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvBlockREL2
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundBlockCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3NonEmptyGates
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3GateCount

/-!
# Block-DT model, route-2 step [171e]: the m-free general-`d` block bound on a gate-count-bounded schedule

The capstone of the m-free depth-`d` arc: all four invariants threaded (alternation `AltO`, bottom
width `BottomWidth`, well-formedness `BottomClean`, gate count `(bottomGates C).length ≤ M`), the
two-threshold survivor [171b] discharged inline, the gate count held by `collapseRoundBlock_count_le`
[171d].  The whole m-free depth-`d` block lower bound now reduces to **two pure schedule inequalities**
with no tower dependence:

* `hgap` — `7·s(i+1) < s i · p` (the star gap), and
* `huni` — `2M · (r')^{s(i+1)}/(1-r') < 1/2` (the uniform union bound; `card ≤ 2M` by
  `bottomGatesG_card_le`).

* `parity_not_altO_block_seq_count_findep` — a depth-`(d+2)` alternating, width-`≤ w`, `BottomClean`
  tower of `≤ M` bottom gates does not compute parity, given only the two schedule inequalities.

This is the complete m-free depth-`d` AC⁰ lower bound modulo a concrete schedule + instance ([171f]):
no clause-count `m`, no `canonicalDT ↔ canonicalDTree` bridge, all constants tracked.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The m-free general-`d` block parity bound on a gate-count-bounded schedule.**  Reduces to the two
pure schedule inequalities `hgap` (star gap) and `huni` (uniform union bound). -/
theorem parity_not_altO_block_seq_count_findep {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : 3 * p ≤ 1)
    (s : ℕ → ℕ) (w F d M : ℕ) [NeZero w]
    (hmono : ∀ i, s (i + 1) ≤ s i) (hsw : ∀ i, s (i + 1) ≤ w) (hpos : ∀ i, i ≤ d → 2 ≤ s (i + 1))
    (hF : n < F) (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool) (hC₀ : AltO (d + 2) C₀)
    (hbw₀ : BottomWidth w C₀) (hcl₀ : BottomClean C₀) (hcnt₀ : (bottomGates C₀).length ≤ M)
    (hτ₀ : s 0 ≤ SwitchingCounting.stars τ₀)
    (hgap : ∀ i, i ≤ d → 7 * (s (i + 1) : ℚ) < (s i : ℚ) * p)
    (huni : ∀ i, i ≤ d → (2 * (M : ℚ))
        * (((2 * p / (1 - p)) * (4 * w + 1)) ^ s (i + 1)
            / (1 - (2 * p / (1 - p)) * (4 * w + 1))) < 1 / 2) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  have h1p : (0 : ℚ) < 1 - p := by linarith
  have hr0 : (0 : ℚ) ≤ (2 * p / (1 - p)) * (4 * w + 1) :=
    mul_nonneg (div_nonneg (by linarith) (by linarith)) (by positivity)
  refine recursive_tower_not_parity_surv_seq_block
    (fun i C => (if i ≤ d then AltO (d + 2 - i) C else True) ∧ BottomWidth w C ∧ BottomClean C
      ∧ (bottomGates C).length ≤ M)
    s C₀ τ₀ ?_ hτ₀ ?_ d w F ?_
  · -- Valid 0 C₀
    refine ⟨?_, hbw₀, hcl₀, hcnt₀⟩
    simp only [Nat.zero_le, if_true, Nat.sub_zero]; exact hC₀
  · -- oracle
    intro i C τ hV hsurvτ
    obtain ⟨hP, hbw, hcl, hcnt⟩ := hV
    by_cases hid : i < d
    · simp only [] at hP; rw [if_pos (le_of_lt hid)] at hP
      have hgeom0 : (0 : ℚ) ≤ ((2 * p / (1 - p)) * (4 * w + 1)) ^ s (i + 1)
          / (1 - (2 * p / (1 - p)) * (4 * w + 1)) :=
        div_nonneg (pow_nonneg hr0 _) (by linarith)
      have hcardle : ((bottomGatesG C).card : ℚ) ≤ 2 * (M : ℚ) := by
        have h1 : ((bottomGatesG C).card : ℚ) ≤ 2 * ((bottomGates C).length : ℚ) := by
          exact_mod_cast bottomGatesG_card_le C
        have h2 : ((bottomGates C).length : ℚ) ≤ (M : ℚ) := by exact_mod_cast hcnt
        linarith
      have hunion : ((bottomGatesG C).card : ℚ)
          * (((2 * p / (1 - p)) * (4 * w + 1)) ^ s (i + 1)
              / (1 - (2 * p / (1 - p)) * (4 * w + 1))) < 1 / 2 :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcardle hgeom0) (huni i (le_of_lt hid))
      obtain ⟨ρ, hext, hge, hltF, hshallow⟩ :=
        hsurv_block_REL2_round hp0 hp1 hp3 (hpos i (le_of_lt hid)) hF C τ hbw hcl hr'
          (lt_of_lt_of_le (hgap i (le_of_lt hid)) (mul_le_mul_of_nonneg_right (by exact_mod_cast hsurvτ) hp0))
          hunion
      refine ⟨collapseRoundBlock w F ρ C, ρ, hext, hge,
        collapseRoundBlock_EquivOn w F hltF C, ?_, ?_, ?_, ?_⟩
      · show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) (collapseRoundBlock w F ρ C) else True)
        rw [if_pos (show i + 1 ≤ d from hid)]
        have hk : d + 2 - i = (d - 1 - i) + 3 := by omega
        rw [hk] at hP
        have hred := collapseRoundBlock_AltO w F ρ hP
        have hk2 : d + 2 - (i + 1) = (d - 1 - i) + 2 := by omega
        rw [hk2]; exact hred
      · exact BottomWidth_mono (hsw i) (collapseRoundBlock_BottomWidth w F ρ hshallow)
      · exact collapseRoundBlock_BottomClean w F ρ hcl.2
      · exact le_trans (collapseRoundBlock_count_le w F ρ (AltO_NonEmptyGates hP)) hcnt
    · refine ⟨C, τ, fun _ _ h => h, le_trans (hmono i) hsurvτ, fun _ _ => rfl, ?_, hbw, hcl, hcnt⟩
      show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) C else True)
      rw [if_neg (by omega : ¬ i + 1 ≤ d)]; trivial
  · -- terminal
    intro Cd σ hVd _hextσ hsurvσ
    obtain ⟨hPd, hbwd, hcld, hcntd⟩ := hVd
    simp only [] at hPd
    rw [if_pos (le_refl d), show d + 2 - d = 2 from by omega] at hPd
    obtain ⟨D, rfl⟩ := AltO_two_dnf hPd
    have hgeom0 : (0 : ℚ) ≤ ((2 * p / (1 - p)) * (4 * w + 1)) ^ s (d + 1)
        / (1 - (2 * p / (1 - p)) * (4 * w + 1)) :=
      div_nonneg (pow_nonneg hr0 _) (by linarith)
    have hcardle : ((bottomGatesG (dnf D)).card : ℚ) ≤ 2 * (M : ℚ) := by
      have h1 : ((bottomGatesG (dnf D)).card : ℚ) ≤ 2 * ((bottomGates (dnf D)).length : ℚ) := by
        exact_mod_cast bottomGatesG_card_le (dnf D)
      have h2 : ((bottomGates (dnf D)).length : ℚ) ≤ (M : ℚ) := by exact_mod_cast hcntd
      linarith
    have hunion : ((bottomGatesG (dnf D)).card : ℚ)
        * (((2 * p / (1 - p)) * (4 * w + 1)) ^ s (d + 1)
            / (1 - (2 * p / (1 - p)) * (4 * w + 1))) < 1 / 2 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcardle hgeom0) (huni d (le_refl d))
    obtain ⟨ρ, hext, hge, hltF, hshallow⟩ :=
      hsurv_block_REL2_round hp0 hp1 hp3 (hpos d (le_refl d)) hF (dnf D) σ hbwd hcld hr'
        (lt_of_lt_of_le (hgap d (le_refl d)) (mul_le_mul_of_nonneg_right (by exact_mod_cast hsurvσ) hp0))
        hunion
    refine ⟨ρ, D, hext, rfl, hltF, ?_⟩
    have hsh := (hshallow D (by rw [show bottomGates (dnf D) = [D] from rfl]; simp)).1
    exact lt_of_lt_of_le hsh hge

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_block_seq_count_findep
