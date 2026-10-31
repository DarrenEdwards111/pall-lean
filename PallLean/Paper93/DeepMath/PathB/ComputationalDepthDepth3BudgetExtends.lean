import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DescentExtends
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ShellDecomp
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3GeomTail

/-!
# Tight switching, step 80: the subcube-relative tight switching budget (branch `razborov-recoverRho-wip`)

The relative analogue of `tight_switching_budget_uncond`: geometrically summing the relative descent bound (step
79) over depth-shells gives the deep-gate mass *relative to the box*,

  `∑_{σ ∈ extBox τ, s ≤ (canonicalDT cs F σ).depth} pweight ≤ (CAP^s/(1-CAP)) · box`,

where `CAP = (2p/(1-p))·2wm` and `box = ((1-p)/2)^(n - stars τ)`.  This is the missing tight (box-factor) bound
that makes the union-bound atom `h2_rel_clean` (step 74) hold for the binary `canonicalDT`.

* `sum_filter_ge_eq_sum_shells_on` — the shell decomposition over an arbitrary base `Finset`.
* `tight_switching_budget_extends_uncond` — the subcube-relative tight switching budget.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Shell decomposition over an arbitrary base `Finset` (the `univ` version is `sum_filter_ge_eq_sum_shells`). -/
theorem sum_filter_ge_eq_sum_shells_on {α : Type*} [DecidableEq α] (S : Finset α)
    (g : α → ℕ) (f : α → ℚ) (s N : ℕ) (hN : ∀ a ∈ S, g a ≤ N) :
    ∑ a ∈ S.filter (fun a => s ≤ g a), f a
      = ∑ K ∈ Finset.Icc s N, ∑ a ∈ S.filter (fun a => g a = K), f a := by
  have hbiU : S.filter (fun a => s ≤ g a)
      = (Finset.Icc s N).biUnion (fun K => S.filter (fun a => g a = K)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_Icc]
    constructor
    · rintro ⟨haS, hsg⟩; exact ⟨g a, ⟨hsg, hN a haS⟩, haS, rfl⟩
    · rintro ⟨K, ⟨hsK, _⟩, haS, hgK⟩; exact ⟨haS, by omega⟩
  rw [hbiU, Finset.sum_biUnion]
  intro K1 _ K2 _ hne
  refine Finset.disjoint_left.mpr (fun a hK1a hK2a => hne ?_)
  exact (Finset.mem_filter.mp hK1a).2.symm.trans (Finset.mem_filter.mp hK2a).2

/-- **The subcube-relative tight switching budget.**  The deep-gate mass over `extBox τ` is bounded by the
geometric tail times the box mass. -/
theorem tight_switching_budget_extends_uncond {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] {cs : List (Clause n)} (τ : Fin n → Option Bool)
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) (hm : cs.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1) :
    (∑ σ ∈ (extBox τ).filter (fun σ => s ≤ (canonicalDT cs F σ).depth), pweight p σ)
      ≤ ((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
          / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)))
        * ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ) := by
  classical
  set r : ℚ := (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) with hr
  have h1p : (0 : ℚ) < 1 - p := by linarith
  have hr0 : 0 ≤ r := by rw [hr]; exact mul_nonneg (div_nonneg (by linarith) (le_of_lt h1p)) (by positivity)
  have hbox0 : (0 : ℚ) ≤ ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ) :=
    pow_nonneg (by linarith) _
  rw [sum_filter_ge_eq_sum_shells_on (extBox τ)
    (fun σ => (canonicalDT cs F σ).depth) (pweight p) s F
    (fun σ _ => canonicalDT_depth_le cs F σ)]
  calc ∑ K ∈ Finset.Icc s F,
          ∑ σ ∈ (extBox τ).filter (fun σ => (canonicalDT cs F σ).depth = K), pweight p σ
      ≤ ∑ K ∈ Finset.Icc s F, r ^ K * ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ) := by
        apply Finset.sum_le_sum
        intro K _
        have hshell := descent_switching_le_tight_extends_uncond (p := p) hp0 hp3
          (w := w) (F := F) (s := K) (m := m) (cs := cs)
          (Bad := (extBox τ).filter (fun σ => (canonicalDT cs F σ).depth = K)) τ hw hm
          (fun ρ hρ => mem_extBox.mp (Finset.mem_filter.mp hρ).1)
          (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
        have hcast : (((2 * w * m) ^ K : ℕ) : ℚ) = (2 * (w : ℚ) * (m : ℚ)) ^ K := by
          push_cast; ring
        rw [hcast, ← mul_pow, ← hr] at hshell
        exact hshell
      _ = (∑ K ∈ Finset.Icc s F, r ^ K) * ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ) := by
        rw [← Finset.sum_mul]
      _ ≤ r ^ s / (1 - r) * ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ) :=
        mul_le_mul_of_nonneg_right (geom_shell_tail_le hr0 hr1 s F) hbox0

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.tight_switching_budget_extends_uncond
