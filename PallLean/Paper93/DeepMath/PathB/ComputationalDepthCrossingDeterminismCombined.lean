import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingExtract

/-!
# The combined per-cycle step: extraction fused with the sync invariant

The determinism is a *combined* induction — extraction and the sync invariant advance together, because
a cycle's shared right-excursion length is only valid once the two computations are `RightSynced`.
This file proves the fused inductive step, `cycle_advance`, composing the whole tower in one cycle:

1. **Extract the exit** (`exists_first_exit` on comp 1): the first-return time `d`, with head `> b`
   before it.
2. **Comp 2 exits at the same `d`** (`run_local_right`): the right-excursion runs both in lockstep, so
   `(run d a₂).hd = (run d a₁).hd ≤ b`, and their right tapes agree at the exit.
3. **Extract both re-entries** (`exists_first_entry` on the two exit configs): first re-entry times
   `ℓ₁, ℓ₂`.
4. **Freeze the right tapes** (`entry_frozen_and_head`): each re-enters at head `b+1` with its right
   tape frozen to the (equal) exit right tape.

So from `RightSynced` at a crossing, `cycle_advance` produces the *next* entry configs with **heads
`b+1` and equal right tapes** — three of the four `RightSynced` conjuncts, extracted from mere
crossing existence.  The fourth, the entry-state equality, is exactly what the crossing sequence
supplies; it is *not* producible here (two different left parts may enter in different states — that
they don't is the fooling hypothesis).

## What still remains (NOT here)

The full determinism theorem iterates `cycle_advance`, adding the entry-state equality from the
assumed-equal crossing sequences at each cycle to upgrade "heads + right tape" to full `RightSynced`,
and tracking the recursive `k`-th entry configs.  That recursive-config induction — plus the
palindrome fooling that furnishes the state equalities, and the `crossing_info_capacity` counting — is
the remaining work.  This file does **not** claim the determinism theorem or the `Ω(n²)` bound.

Ceiling unchanged: even finished, an unconditional *restricted* bound (`crossingCount ≤ time` caps the
technique at polynomial; one-tape P `=` P), not `SAT ∉ P`.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- **The fused per-cycle step.**  From `RightSynced` entry configs, given that comp 1 exits and each
computation eventually re-enters from any left configuration, the next entry configs have head `b+1`
and equal tapes right of `b`.  (The remaining entry-state equality is the crossing-sequence datum.) -/
theorem cycle_advance (M : Machine) (b : ℕ) (a₁ a₂ : Cfg M)
    (hsync : RightSynced M b a₁ a₂)
    (hexit : ∃ t, (run M t a₁).hd ≤ b)
    (hre1 : ∀ e, (run M e a₁).hd ≤ b → ∃ t, b < (run M (e + t) a₁).hd)
    (hre2 : ∀ e, (run M e a₂).hd ≤ b → ∃ t, b < (run M (e + t) a₂).hd) :
    ∃ d ℓ₁ ℓ₂,
      (run M (d + ℓ₁) a₁).hd = b + 1 ∧ (run M (d + ℓ₂) a₂).hd = b + 1 ∧
        (∀ p, b < p →
          (run M (d + ℓ₁) a₁).tp.getD p false = (run M (d + ℓ₂) a₂).tp.getD p false) := by
  obtain ⟨hhd1, hhd2, hst, hagree⟩ := hsync
  -- 1. extract the exit d of comp 1
  obtain ⟨d, hright, hexitd⟩ := exists_first_exit M b a₁ hexit
  -- 2. comp 2 exits at the same d, with equal right tape
  have hhd : a₁.hd = a₂.hd := by rw [hhd1, hhd2]
  obtain ⟨_, hd_hd, hd_tp⟩ := run_local_right M b a₁ a₂ d hst hhd hagree hright
  have hexit2d : (run M d a₂).hd ≤ b := by rw [← hd_hd]; exact hexitd
  -- 3. extract both re-entries
  obtain ⟨t1, hre1t⟩ := hre1 d hexitd
  obtain ⟨t2, hre2t⟩ := hre2 d hexit2d
  have hex1 : ∃ t, b < (run M t (run M d a₁)).hd :=
    ⟨t1, by rw [← run_add M d t1 a₁]; exact hre1t⟩
  have hex2 : ∃ t, b < (run M t (run M d a₂)).hd :=
    ⟨t2, by rw [← run_add M d t2 a₂]; exact hre2t⟩
  obtain ⟨ℓ₁, hbef1, hcr1⟩ := exists_first_entry M b (run M d a₁) hex1
  obtain ⟨ℓ₂, hbef2, hcr2⟩ := exists_first_entry M b (run M d a₂) hex2
  -- 4. freeze each right tape through the left excursion; re-enter at b+1
  obtain ⟨hh1, hfroz1⟩ := entry_frozen_and_head M b (run M d a₁) ℓ₁ hexitd hbef1 hcr1
  obtain ⟨hh2, hfroz2⟩ := entry_frozen_and_head M b (run M d a₂) ℓ₂ hexit2d hbef2 hcr2
  refine ⟨d, ℓ₁, ℓ₂, ?_, ?_, ?_⟩
  · rw [run_add M d ℓ₁ a₁]; exact hh1
  · rw [run_add M d ℓ₂ a₂]; exact hh2
  · intro p hp
    rw [run_add M d ℓ₁ a₁, run_add M d ℓ₂ a₂, hfroz1 p hp, hfroz2 p hp]
    exact hd_tp p hp

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
