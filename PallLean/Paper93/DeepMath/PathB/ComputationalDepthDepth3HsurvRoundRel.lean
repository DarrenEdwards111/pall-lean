import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SurvivorExtendsRel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvRound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HcfFromGap

/-!
# Tight switching, step 82: the per-round relative survivor from gap ∧ union bound (branch `razborov-recoverRho-wip`)

The final wire.  The per-round survivor `hsurv` of the width-aware capstone (step 59) is discharged from the
*box-free* per-round conditions, via the relative survivor budget (step 81):

* the **Chernoff gap** `(stars τ)·p > 7·s` (step 71) bounds the low-star tail;
* the **box-free union bound** `card · CAP^s/(1-CAP) < 1/2` (step 74) bounds the deep-gate term;

together they discharge the relative `hsmall` `(low-star) + card·(cap·box) < box` (`hsmall_of_chernoff` step 61
+ `hcf_of_split` step 67), and `exists_survivor_shallow_extends_REL` (step 81) at `G = bottomGatesG C` yields a
survivor `ρ` shallowing every bottom gate in both polarities — `Shallows F ρ s C`.  No box, no `exp`, no
consistency/nodup invariant.

* `hsurv_REL_round` — one round's survivor (`Shallows`) from the gap and the box-free union bound.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **One round's relative survivor.**  Given the bottom width, a clause-count bound, the rate, the Chernoff
gap `(stars τ)·p > 7·s`, and the box-free union bound `card·CAP^s/(1-CAP) < 1/2`, there is a survivor `ρ`
shallowing every bottom gate of `C` below `s` in both polarities. -/
theorem hsurv_REL_round {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] (hs : 2 ≤ s) (hF : n ≤ F)
    (C : Layered n) (τ : Fin n → Option Bool) (hbw : BottomWidth w C)
    (hmc : ∀ cs ∈ bottomGates C, cs.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hgap : 7 * (s : ℚ) < (SwitchingCounting.stars τ : ℚ) * p)
    (hh2 : ((bottomGatesG C).card : ℚ)
        * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
            / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)))) < 1 / 2) :
    ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧
      SwitchingCounting.stars ρ ≤ F ∧ Shallows F ρ s C := by
  have hp_lt : p < 1 := by linarith
  have hsq : (1 : ℚ) < (s : ℚ) := by exact_mod_cast (by omega : 1 < s)
  set t : ℚ := 1 - 1 / (s : ℚ) with ht
  have h1s : 1 / (s : ℚ) < 1 := by rw [div_lt_one (by positivity)]; exact hsq
  have ht0 : 0 < t := by rw [ht]; linarith
  have h0s : (0 : ℚ) ≤ 1 / (s : ℚ) := by positivity
  have ht1 : t ≤ 1 := by rw [ht]; linarith
  set cap : ℚ := ((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
    / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) with hcapd
  set box : ℚ := ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ) with hboxd
  have hbox0 : 0 < box := by rw [hboxd]; exact pow_pos (by linarith) _
  -- the box-free union bound, scaled to box
  have hh2box : ((bottomGatesG C).card : ℚ) * (cap * box) < box / 2 := by
    rw [show ((bottomGatesG C).card : ℚ) * (cap * box)
          = (((bottomGatesG C).card : ℚ) * cap) * box by ring,
        show box / 2 = (1 / 2) * box by ring]
    exact mul_lt_mul_of_pos_right hh2 hbox0
  -- the relative survivor budget hsmall
  have hsmall : (∑ σ ∈ (extBox τ).filter (fun σ => SwitchingCounting.stars σ < s), pweight p σ)
      + ((bottomGatesG C).card : ℚ) * (cap * box) < box :=
    hsmall_of_chernoff ht0 ht1 hp0 hp1 (by omega) τ (((bottomGatesG C).card : ℚ) * (cap * box))
      (hcf_of_split hp_lt ((bottomGatesG C).card : ℚ) (cap * box)
        (h1_of_gap hp0 hp1 (SwitchingCounting.stars τ) s (by omega) hgap) hh2box)
  -- apply the relative survivor lemma at G = bottomGatesG C
  obtain ⟨ρ, hext, hge, hle, hsh⟩ :=
    exists_survivor_shallow_extends_REL hp0 hp3 hF τ (bottomGatesG C)
      (by intro g hg T hT
          rcases mem_bottomGatesG.mp hg with h | ⟨cs, hcs, rfl⟩
          · exact hbw g h T hT
          · rw [negDNF, List.mem_map] at hT
            obtain ⟨S, hS, rfl⟩ := hT
            simpa using hbw cs hcs S hS)
      (by intro g hg
          rcases mem_bottomGatesG.mp hg with h | ⟨cs, hcs, rfl⟩
          · exact hmc g h
          · rw [negDNF, List.length_map]; exact hmc cs hcs)
      hr1 hsmall
  refine ⟨ρ, hext, hge, hle, ?_⟩
  intro cs hcs
  exact ⟨hsh cs (mem_bottomGatesG.mpr (Or.inl hcs)),
    hsh (negDNF cs) (mem_bottomGatesG.mpr (Or.inr ⟨cs, hcs, rfl⟩))⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.hsurv_REL_round
