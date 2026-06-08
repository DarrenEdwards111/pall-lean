import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightCollapseRound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightParity

/-!
# Tight switching, step 15: a tight `F`-independent parity refutation for a single DNF (branch `razborov-recoverRho-wip`)

The depth-2 capstone of the tight route, assembling bricks 50/52/54.  `tight_collapse_round` (step 12)
produced a restriction with `stars ρ ≤ F` (an *upper* bound) collapsing every gate shallow.  For the parity
contradiction `shallow_canonicalDT_not_parity` (step 14) we also need a survivor **lower** bound
`s ≤ stars ρ`, so that `depth < s ≤ stars ρ` lands in the regime where `canonicalDT` shallowness refutes
parity.

We fold that lower bound in as a *third* bad event.  The union bound now carries

```
  1 = ∑_ρ pweight  ≤  ∑_{stars ρ < s} pweight  +  ∑_{F < stars ρ} pweight  +  ∑_{g} ∑_{ρ : depth_g ρ ≥ s} pweight
                   ≤  (low star tail)          +  (high star tail)         +  #gates · r^s/(1-r),
```

so if the three terms total `< 1` some `ρ` has `s ≤ stars ρ ≤ F` **and** every gate shallow.  Both star
tails are `F`-independent at the tight `p ≈ 1/(4w)` (Markov via `stars_tail_le`/`stars_tail_ge`), as is the
deep cap — so the whole threshold is `F`-independent (`tight_round_budget_satisfiable`, step 13, witnesses a
satisfying point in the `s ≤ k < n` regime).

Feeding the resulting `ρ` (with `G = {D}`) into `shallow_canonicalDT_not_parity` then gives, for a single
bottom DNF `D`: a `σ`-consistent input on which `D` disagrees with parity — a genuine, non-vacuous,
`F`-independent parity refutation, over the *tight tree all the way through*.

* `exists_survivor_shallow` — the three-event union bound: `∃ ρ, s ≤ stars ρ ∧ stars ρ ≤ F ∧ ∀ g ∈ G,
  (canonicalDT g F ρ).depth < s`.
* `tight_dnf_not_parity` — a single shallow-collapsing DNF disagrees with parity somewhere on the subcube.

## Honest scope

The two star tails are left as explicit sums in the union-bound hypothesis (discharged by the Markov bounds
of `stars_tail_le`/`stars_tail_ge` for chosen `t`), and the per-gate hypotheses are the alive/leaf/position
conditions — the empty-skip wall (brick 49) — carried explicitly.  `tight_dnf_not_parity` is the *single
DNF* case; the full depth-3 `OR`/`AND` circuit still needs the `Reduces`/tower spine threaded over the
`canonicalDT` collapse (the other remaining wire).  We flag that, not paper over it.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The three-event union bound (survivor band + shallowness).**  If the low star tail, the high star
tail and the `F`-independent deep cap total `< 1`, some restriction has `s ≤ stars ρ ≤ F` and makes every
gate's single-literal canonical tree shallow. -/
theorem exists_survivor_shallow {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s : ℕ} [NeZero w] (G : Finset (List (Clause n)))
    (hnf : ∀ g ∈ G, ∀ ρ : Restriction n, ∀ U ∈ g,
      SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ g ∈ G, ∀ ρ : Restriction n,
      SwitchingCounting.anyTermSat g (deepestEnd g F ρ) = false)
    (hpos : ∀ g ∈ G, ∀ ρ : Restriction n, ∀ q ∈ deepestFullSeq g F ρ, q.1 < w)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ)) < 1)
    (hsmall :
        (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
            pweight p ρ)
          + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F < SwitchingCounting.stars ρ),
              pweight p ρ)
          + (G.card : ℚ)
              * (((2 * p / (1 - p)) * (2 * (w : ℚ))) ^ s
                  / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ)))) < 1) :
    ∃ ρ : Restriction n, s ≤ SwitchingCounting.stars ρ ∧ SwitchingCounting.stars ρ ≤ F ∧
      ∀ g ∈ G, (canonicalDT g F ρ).depth < s := by
  classical
  set cap : ℚ := ((2 * p / (1 - p)) * (2 * (w : ℚ))) ^ s
    / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ))) with hcap
  have hpw_nonneg : ∀ ρ : Restriction n, 0 ≤ pweight p ρ :=
    fun ρ => pweight_nonneg hp0 (by linarith) ρ
  by_contra hcon
  push_neg at hcon
  -- the three-way disjunction every `ρ` falls into.
  have hcase : ∀ ρ : Restriction n,
      SwitchingCounting.stars ρ < s ∨ F < SwitchingCounting.stars ρ
        ∨ ∃ g ∈ G, s ≤ (canonicalDT g F ρ).depth := by
    intro ρ
    by_cases h1 : SwitchingCounting.stars ρ < s
    · exact Or.inl h1
    · by_cases h2 : F < SwitchingCounting.stars ρ
      · exact Or.inr (Or.inl h2)
      · obtain ⟨g, hg, hgρ⟩ := hcon ρ (Nat.le_of_not_lt h1) (Nat.le_of_not_lt h2)
        exact Or.inr (Or.inr ⟨g, hg, hgρ⟩)
  have key : (1 : ℚ) ≤
      (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
          pweight p ρ)
        + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F < SwitchingCounting.stars ρ),
            pweight p ρ)
        + (G.card : ℚ) * cap := by
    calc (1 : ℚ) = ∑ ρ : Restriction n, pweight p ρ := (pweight_sum_eq_one p).symm
      _ ≤ ∑ ρ : Restriction n,
            ((if SwitchingCounting.stars ρ < s then pweight p ρ else 0)
              + (if F < SwitchingCounting.stars ρ then pweight p ρ else 0)
              + ∑ g ∈ G, (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0)) := by
          apply Finset.sum_le_sum
          intro ρ _
          have hlo_nn : (0 : ℚ) ≤ (if SwitchingCounting.stars ρ < s then pweight p ρ else 0) := by
            split <;> first | exact hpw_nonneg ρ | exact le_refl 0
          have hhi_nn : (0 : ℚ) ≤ (if F < SwitchingCounting.stars ρ then pweight p ρ else 0) := by
            split <;> first | exact hpw_nonneg ρ | exact le_refl 0
          have hsum_nn : (0 : ℚ) ≤
              ∑ g ∈ G, (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0) :=
            Finset.sum_nonneg
              (fun g' _ => by split <;> first | exact hpw_nonneg ρ | exact le_refl 0)
          rcases hcase ρ with hlo | hhi | ⟨g, hg, hgρ⟩
          · rw [if_pos hlo]; linarith
          · rw [if_pos hhi]; linarith
          · have hnn : ∀ g' ∈ G,
                (0 : ℚ) ≤ (if s ≤ (canonicalDT g' F ρ).depth then pweight p ρ else 0) :=
              fun g' _ => by split <;> first | exact hpw_nonneg ρ | exact le_refl 0
            have hsingle := Finset.single_le_sum hnn hg
            rw [if_pos hgρ] at hsingle
            linarith
      _ = (∑ ρ : Restriction n, (if SwitchingCounting.stars ρ < s then pweight p ρ else 0))
            + (∑ ρ : Restriction n, (if F < SwitchingCounting.stars ρ then pweight p ρ else 0))
            + ∑ ρ : Restriction n,
                ∑ g ∈ G, (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
              pweight p ρ)
            + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F < SwitchingCounting.stars ρ),
                pweight p ρ)
            + ∑ g ∈ G, ∑ ρ : Restriction n,
                (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0) := by
          rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_comm]
      _ ≤ (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
              pweight p ρ)
            + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F < SwitchingCounting.stars ρ),
                pweight p ρ)
            + (G.card : ℚ) * cap := by
          have hgate : ∑ g ∈ G, ∑ ρ : Restriction n,
              (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0) ≤ (G.card : ℚ) * cap := by
            calc ∑ g ∈ G, ∑ ρ : Restriction n,
                    (if s ≤ (canonicalDT g F ρ).depth then pweight p ρ else 0)
                ≤ ∑ _g ∈ G, cap := by
                  apply Finset.sum_le_sum
                  intro g hg
                  rw [← Finset.sum_filter]
                  exact tight_switching_budget hp0 hp3 (cs := g)
                    (hnf g hg) (hleaf g hg) (hpos g hg) hr1
              _ = (G.card : ℚ) * cap := by rw [Finset.sum_const, nsmul_eq_mul]
          linarith
  linarith

/-- **A tight `F`-independent parity refutation for a single DNF.**  Under the alive/leaf/position
hypotheses, the tight regime `r < 1`, and the three-event union bound (with `#gates = 1`), a single bottom
DNF `D` disagrees with parity at some `σ`-consistent input — the depth-2 capstone of the tight route, over
the single-literal tree throughout. -/
theorem tight_dnf_not_parity {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s : ℕ} [NeZero w] (D : List (Clause n))
    (hnf : ∀ ρ : Restriction n, ∀ U ∈ D, SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ ρ : Restriction n, SwitchingCounting.anyTermSat D (deepestEnd D F ρ) = false)
    (hpos : ∀ ρ : Restriction n, ∀ q ∈ deepestFullSeq D F ρ, q.1 < w)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ)) < 1)
    (hsmall :
        (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
            pweight p ρ)
          + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F < SwitchingCounting.stars ρ),
              pweight p ρ)
          + (((2 * p / (1 - p)) * (2 * (w : ℚ))) ^ s
              / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ)))) < 1) :
    ∃ (ρ : Restriction n) (x : Fin n → Bool),
      DTree.agreeRestriction ρ x ∧ DTree.dnfValue D x ≠ DTree.parity x := by
  classical
  obtain ⟨ρ, hge, hle, hshallow⟩ :=
    exists_survivor_shallow hp0 hp3 ({D} : Finset (List (Clause n)))
      (fun g hg ρ U hU => by rw [Finset.mem_singleton] at hg; subst hg; exact hnf ρ U hU)
      (fun g hg ρ => by rw [Finset.mem_singleton] at hg; subst hg; exact hleaf ρ)
      (fun g hg ρ q hq => by rw [Finset.mem_singleton] at hg; subst hg; exact hpos ρ q hq)
      hr1
      (by rw [Finset.card_singleton, Nat.cast_one, one_mul]; exact hsmall)
  have hsh : (canonicalDT D F ρ).depth < SwitchingCounting.stars ρ :=
    lt_of_lt_of_le (hshallow D (Finset.mem_singleton.mpr rfl)) hge
  obtain ⟨x, hx, hne⟩ := shallow_canonicalDT_not_parity D F ρ hle hsh
  exact ⟨ρ, x, hx, hne⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_survivor_shallow
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.tight_dnf_not_parity
