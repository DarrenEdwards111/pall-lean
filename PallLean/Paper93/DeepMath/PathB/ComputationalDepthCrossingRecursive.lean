import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingExtract

/-!
# The recursive-config determinism induction

This file defines the concrete `k`-th entry config (via `Nat.find` crossing times) and iterates the
fused cycle step into the determinism theorem: two computations that are `RightSynced` at their first
crossing and have equal crossing-sequence states stay `RightSynced` at every crossing.

* `firstExitTime` / `firstEntryTime` — the first time the head drops to `≤ b` / rises to `> b`.
* `firstExitTime_spec` / `firstEntryTime_spec` — the before/at data of those first crossings.
* `firstExit_eq` — `RightSynced` computations exit at the **same** time (their right-excursions run in
  lockstep), so their cycles stay aligned.
* `nextEntry` — the next entry config: run to the first exit, then to the first re-entry.
* `nextEntry_synced` — **the pair advance**: `RightSynced` + crossing existence + equal next entry
  states ⇒ `RightSynced` at the next entry.
* `determinism_recursive` — **the determinism.**  Iterating `nextEntry_synced`: with equal
  crossing-sequence states along the way, `RightSynced` propagates to the `k`-th entry.

## What still remains (NOT here)

The palindrome fooling supplies the equal crossing-sequence states hypothesis (distinct middle-halves
would otherwise force distinct states), and `crossing_info_capacity` turns the resulting `2^Ω(n)`
distinct sequences into the `Ω(n²)` bound.  That fooling/counting is the remaining work; this file
provides the determinism it rests on but does **not** claim the `Ω(n²)` bound.

Ceiling unchanged: even the finished bound is an unconditional *restricted* result (`crossingCount ≤
time` caps the technique at polynomial; one-tape P `=` P), not `SAT ∉ P`.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

attribute [local instance] Classical.propDecidable

/-- First time the head drops to `≤ b` (junk `0` if it never does). -/
noncomputable def firstExitTime (M : Machine) (b : ℕ) (c : Cfg M) : ℕ :=
  if h : ∃ t, (run M t c).hd ≤ b then Nat.find h else 0

/-- First time the head rises to `> b` (junk `0` if it never does). -/
noncomputable def firstEntryTime (M : Machine) (b : ℕ) (c : Cfg M) : ℕ :=
  if h : ∃ t, b < (run M t c).hd then Nat.find h else 0

theorem firstExitTime_spec (M : Machine) (b : ℕ) (c : Cfg M) (h : ∃ t, (run M t c).hd ≤ b) :
    (∀ j, j < firstExitTime M b c → b < (run M j c).hd) ∧ (run M (firstExitTime M b c) c).hd ≤ b := by
  rw [firstExitTime, dif_pos h]
  exact ⟨fun j hj => by have := Nat.find_min h hj; omega, Nat.find_spec h⟩

theorem firstEntryTime_spec (M : Machine) (b : ℕ) (c : Cfg M) (h : ∃ t, b < (run M t c).hd) :
    (∀ j, j < firstEntryTime M b c → (run M j c).hd ≤ b) ∧ b < (run M (firstEntryTime M b c) c).hd := by
  rw [firstEntryTime, dif_pos h]
  exact ⟨fun j hj => by have := Nat.find_min h hj; omega, Nat.find_spec h⟩

/-- **Aligned exits.**  `RightSynced` computations exit at the same first time (right-excursion
lockstep), and comp 2 exits too. -/
theorem firstExit_eq (M : Machine) (b : ℕ) (a₁ a₂ : Cfg M) (hsync : RightSynced M b a₁ a₂)
    (hexit : ∃ t, (run M t a₁).hd ≤ b) :
    (∃ t, (run M t a₂).hd ≤ b) ∧ firstExitTime M b a₁ = firstExitTime M b a₂ := by
  obtain ⟨hhd1, hhd2, hst, hagree⟩ := hsync
  obtain ⟨hbefore1, hexit1⟩ := firstExitTime_spec M b a₁ hexit
  have hhd : a₁.hd = a₂.hd := by rw [hhd1, hhd2]
  have hheadeq : ∀ t, t ≤ firstExitTime M b a₁ → (run M t a₁).hd = (run M t a₂).hd := by
    intro t ht
    obtain ⟨_, h, _⟩ := run_local_right M b a₁ a₂ t hst hhd hagree (fun j hj => hbefore1 j (by omega))
    exact h
  have hexit2d : (run M (firstExitTime M b a₁) a₂).hd ≤ b := by
    rw [← hheadeq (firstExitTime M b a₁) (le_refl _)]; exact hexit1
  have hex2 : ∃ t, (run M t a₂).hd ≤ b := ⟨firstExitTime M b a₁, hexit2d⟩
  refine ⟨hex2, ?_⟩
  obtain ⟨hbefore2, hexit2⟩ := firstExitTime_spec M b a₂ hex2
  have hle : firstExitTime M b a₂ ≤ firstExitTime M b a₁ := by
    rw [firstExitTime, dif_pos hex2]; exact Nat.find_le hexit2d
  have hge : firstExitTime M b a₁ ≤ firstExitTime M b a₂ := by
    by_contra hlt
    push_neg at hlt
    have : b < (run M (firstExitTime M b a₂) a₂).hd := by
      rw [← hheadeq (firstExitTime M b a₂) (le_of_lt hlt)]; exact hbefore1 _ hlt
    omega
  omega

/-- The next entry config: run to the first exit, then to the first re-entry. -/
noncomputable def nextEntry (M : Machine) (b : ℕ) (a : Cfg M) : Cfg M :=
  run M (firstEntryTime M b (run M (firstExitTime M b a) a)) (run M (firstExitTime M b a) a)

/-- **The pair advance.**  `RightSynced` entry configs, with comp 1 exiting, both re-entering, and
equal next entry states, are `RightSynced` at the next entry. -/
theorem nextEntry_synced (M : Machine) (b : ℕ) (a₁ a₂ : Cfg M)
    (hsync : RightSynced M b a₁ a₂)
    (hexit : ∃ t, (run M t a₁).hd ≤ b)
    (hre1 : ∃ t, b < (run M t (run M (firstExitTime M b a₁) a₁)).hd)
    (hre2 : ∃ t, b < (run M t (run M (firstExitTime M b a₂) a₂)).hd)
    (hstate : (nextEntry M b a₁).st = (nextEntry M b a₂).st) :
    RightSynced M b (nextEntry M b a₁) (nextEntry M b a₂) := by
  obtain ⟨hhd1, hhd2, hst, hagree⟩ := hsync
  obtain ⟨_, hd_eq⟩ := firstExit_eq M b a₁ a₂ ⟨hhd1, hhd2, hst, hagree⟩ hexit
  obtain ⟨hbefore1, hexit1⟩ := firstExitTime_spec M b a₁ hexit
  have hhd : a₁.hd = a₂.hd := by rw [hhd1, hhd2]
  obtain ⟨_, hd_hd, hd_tp⟩ := run_local_right M b a₁ a₂ (firstExitTime M b a₁) hst hhd hagree hbefore1
  have hexit2d : (run M (firstExitTime M b a₁) a₂).hd ≤ b := by rw [← hd_hd]; exact hexit1
  have hre2' : ∃ t, b < (run M t (run M (firstExitTime M b a₁) a₂)).hd := by rw [hd_eq]; exact hre2
  obtain ⟨hbef1, hcr1⟩ := firstEntryTime_spec M b (run M (firstExitTime M b a₁) a₁) hre1
  obtain ⟨hbef2, hcr2⟩ := firstEntryTime_spec M b (run M (firstExitTime M b a₁) a₂) hre2'
  obtain ⟨hh1, hfroz1⟩ := entry_frozen_and_head M b (run M (firstExitTime M b a₁) a₁)
    (firstEntryTime M b (run M (firstExitTime M b a₁) a₁)) hexit1 hbef1 hcr1
  obtain ⟨hh2, hfroz2⟩ := entry_frozen_and_head M b (run M (firstExitTime M b a₁) a₂)
    (firstEntryTime M b (run M (firstExitTime M b a₁) a₂)) hexit2d hbef2 hcr2
  have hne1 : nextEntry M b a₁ =
      run M (firstEntryTime M b (run M (firstExitTime M b a₁) a₁)) (run M (firstExitTime M b a₁) a₁) := rfl
  have hne2 : nextEntry M b a₂ =
      run M (firstEntryTime M b (run M (firstExitTime M b a₁) a₂)) (run M (firstExitTime M b a₁) a₂) := by
    rw [nextEntry, ← hd_eq]
  refine ⟨?_, ?_, hstate, ?_⟩
  · rw [hne1]; exact hh1
  · rw [hne2]; exact hh2
  · intro p hp
    rw [hne1, hne2, hfroz1 p hp, hfroz2 p hp]
    exact hd_tp p hp

/-- **The determinism, iterated.**  Two computations `RightSynced` at their first crossing that keep
crossing (exit/re-enter at each of the first `k` entries) and have equal crossing-sequence states
(equal control state at each of the first `k` re-entries) are `RightSynced` at the `k`-th entry. -/
theorem determinism_recursive (M : Machine) (b : ℕ) (a₁ a₂ : Cfg M) (k : ℕ)
    (hsync0 : RightSynced M b a₁ a₂)
    (hexit : ∀ j, j < k → ∃ t, (run M t ((nextEntry M b)^[j] a₁)).hd ≤ b)
    (hre1 : ∀ j, j < k →
      ∃ t, b < (run M t (run M (firstExitTime M b ((nextEntry M b)^[j] a₁)) ((nextEntry M b)^[j] a₁))).hd)
    (hre2 : ∀ j, j < k →
      ∃ t, b < (run M t (run M (firstExitTime M b ((nextEntry M b)^[j] a₂)) ((nextEntry M b)^[j] a₂))).hd)
    (hstates : ∀ j, j < k → ((nextEntry M b)^[j + 1] a₁).st = ((nextEntry M b)^[j + 1] a₂).st) :
    RightSynced M b ((nextEntry M b)^[k] a₁) ((nextEntry M b)^[k] a₂) := by
  revert hexit hre1 hre2 hstates
  induction k with
  | zero => intro _ _ _ _; simpa using hsync0
  | succ k ih =>
    intro hexit hre1 hre2 hstates
    have ihs := ih (fun j hj => hexit j (by omega)) (fun j hj => hre1 j (by omega))
      (fun j hj => hre2 j (by omega)) (fun j hj => hstates j (by omega))
    have hst_k := hstates k (by omega)
    simp only [Function.iterate_succ_apply'] at hst_k ⊢
    exact nextEntry_synced M b ((nextEntry M b)^[k] a₁) ((nextEntry M b)^[k] a₂) ihs
      (hexit k (by omega)) (hre1 k (by omega)) (hre2 k (by omega)) hst_k

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
