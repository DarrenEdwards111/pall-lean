import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingEnergy

/-!
# Falsification attempt: can crossing energy stay low on a slow computation?

Last step made `crossingEnergy` a *sound* observer invariant, reducing the route to `InvHard` — a
superlinear (indeed superpolynomial) crossing-energy bound on every SAT decider.  Falsify-first: try
to break that by keeping crossing energy **low while time is high**.  If some slow machine has small
crossing energy, `InvHard` is false and the route dies.

## The floor that blocks it (proved)

The falsification fails: crossing energy cannot sink below the **space** the computation uses.

* `one_le_crossingCount_of_reached` — if the head starts at `0` and reaches a position past boundary
  `b` by time `T`, then `b` is crossed at least once (the first step whose head exceeds `b` crosses
  it — a discrete intermediate-value argument).
* `crossingEnergy_ge_reached` — if the head reaches position `P` (with `P ≤ S`), then
  `crossingEnergy ≥ P`.  Every boundary below `P` is crossed at least once, contributing `≥ 1` each.

Combined with the existing `sumCrossings_le_crossingEnergy` (`crossingEnergy ≥ Σ_b crossingCount(b)`),
crossing energy is at least both the space used and the total crossing count.

## The decisive time-tie (analysis — NOT formalized here)

The space floor alone does not finish the falsification: a poly-space, exp-time decider could still
hope for small crossing energy.  It cannot, for a separate reason.  A halting single-tape machine can
idle at a fixed cell for at most `2|State|` consecutive steps before some `(state, cell-content)`
pair repeats — a configuration repeat, i.e. a non-halting loop.  Hence

  `T ≤ O(|State|) · (Σ_b crossingCount(b) + space)`,

so `crossingEnergy ≥ Σ_b crossingCount(b) ≥ Ω(T / |State|)`.  Crossing energy is therefore `Ω(time)`:
it **cannot** be kept low while time is high.  On any superpolynomial-time (SAT-hard) family crossing
energy is superpolynomial — the falsification **fails**.

The no-long-stay lemma this uses (a halting machine idles boundedly per cell) is *not* formalized
here; only the space floor is.  So the `Ω(time)` conclusion is argued, not machine-checked.

## The sting

The same tie is bad news for the *leverage* one hoped a novelty measure would give.  Because
`crossingEnergy = Ω(time)` (up to the `|State|` factor) and `crossingEnergy ≤ S·T²`, crossing energy
is polynomially equivalent to time.  So `InvHard(crossingEnergy)` holds **iff** SAT needs
superpolynomial time — it is the separation with *no structural discount* over a direct time lower
bound.  This matches the file-documented ceiling: the crossing-sequence technique tops out at
`Ω(n log n)` one-tape time (crossing-for-space tradeoff), and pushing crossing energy superpolynomial
on SAT is, like every sound-and-hard invariant, exactly the separation.

Verdict: the candidate **survives** falsification (crossing energy is forced high, not low), but the
survival mechanism — crossing energy being time in disguise — removes the hoped-for leverage.  No
lower bound and no `InvHard` is proved.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

variable {M : Machine}

/-- **A reached boundary is crossed.**  If the head starts at `≤ b` and its position exceeds `b` by
time `t₀ ≤ T`, then boundary `b` is crossed at least once in `[0,T)`: the first step whose head
exceeds `b` has its predecessor at `≤ b`, so that step crosses `b`. -/
theorem one_le_crossingCount_of_reached (c : Cfg M) (b t₀ T : ℕ)
    (hstart : headAt M c 0 ≤ b) (ht₀ : t₀ ≤ T) (hreach : b < headAt M c t₀) :
    1 ≤ crossingCount M c b T := by
  classical
  have hex : ∃ t, b < headAt M c t := ⟨t₀, hreach⟩
  have hfind : b < headAt M c (Nat.find hex) := Nat.find_spec hex
  have ht1_le : Nat.find hex ≤ t₀ := Nat.find_le hreach
  have ht1_pos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0] at hfind; omega
    · exact hpos
  have hprev : headAt M c (Nat.find hex - 1) ≤ b := by
    by_contra hc
    push_neg at hc
    have := Nat.find_le (h := hex) hc
    omega
  have hcross : crossesAt M c b (Nat.find hex - 1) := by
    refine Or.inl ⟨hprev, ?_⟩
    have h1 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [h1]; exact hfind
  have hmem : (Nat.find hex - 1) ∈ crossingTimes M c b T := by
    unfold crossingTimes
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hcross⟩
  unfold crossingCount
  exact Finset.card_pos.mpr ⟨Nat.find hex - 1, hmem⟩

/-- **Space floor.**  If the head starts at `0` and reaches position `P ≤ S` by time `T`, then
`crossingEnergy ≥ P`.  Each of the `P` boundaries below the reached position is crossed at least
once, contributing at least `1²` to the energy. -/
theorem crossingEnergy_ge_reached (c : Cfg M) (P t₀ S T : ℕ)
    (hstart0 : headAt M c 0 = 0) (ht₀ : t₀ ≤ T) (hreach : headAt M c t₀ = P) (hPS : P ≤ S) :
    P ≤ crossingEnergy M c S T := by
  unfold crossingEnergy
  have hsum1 : (∑ _b ∈ Finset.range P, (1 : ℕ)) = P := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  calc P = ∑ _b ∈ Finset.range P, (1 : ℕ) := hsum1.symm
    _ ≤ ∑ b ∈ Finset.range P, (crossingCount M c b T) ^ 2 := by
        apply Finset.sum_le_sum
        intro b hb
        have hbP : b < P := Finset.mem_range.mp hb
        have h1 : 1 ≤ crossingCount M c b T :=
          one_le_crossingCount_of_reached c b t₀ T (by rw [hstart0]; exact Nat.zero_le b) ht₀
            (by rw [hreach]; exact hbP)
        exact le_trans h1 (Nat.le_self_pow (by norm_num) _)
    _ ≤ ∑ b ∈ Finset.range S, (crossingCount M c b T) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          rw [Finset.mem_range] at hx ⊢
          omega
        · intro i _ _
          exact Nat.zero_le _

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
