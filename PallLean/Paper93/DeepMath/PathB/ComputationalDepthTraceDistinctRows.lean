import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceMeasureSchema

/-!
# Why distinct-configuration count is time-sensitive (unlike rank)

The falsification of tableau rank turned on `rank ≤ space`.  This file records the structural
reason the *next* candidate — the number of distinct configurations visited — is not killed the
same way: it directly **upper-bounds time**.

A deterministic run cannot repeat a full configuration before it halts (a repeat would make it
loop forever, `no_config_repeat`), so the configurations at times `0..T` are pairwise distinct and
`T + 1 ≤ #distinct configurations` (`time_le_configs`).  A configuration is `(state, head, tape)`,
so `#distinct configs ≤ |State| · #distinct heads · #distinct tapes` (`visitedConfigs_card_le_product`).
Hence

> `time + 1 ≤ |State| · #headPositions · distinctTapes`   (`time_le`).

`|State|` is a machine constant and `distinctTapes` is exactly the trace's distinct-row count.  So
a machine whose head stays in a polynomial range with polynomially many distinct tape snapshots
runs in polynomial time — the property rank lacks.  Concretely, the polynomial-*space* brute-force
SAT decider that killed rank (it has `traceRank ≤ space = poly`) must, by this bound, have
*exponentially many* distinct tape snapshots — so distinct-row count is **not** collapsed on it.

This does **not** prove distinct-row count is SAT-hard: the head can range over superpolynomially
many positions, so polynomial distinct tapes need not force polynomial time in general.  Whether a
SAT decider can achieve polynomial distinct-row count (necessarily with superpolynomial head range)
is the open robustness question — this file only shows the candidate survives the space kill.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceDistinctRows

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema

attribute [local instance] Classical.propDecidable

variable {M : Machine}

/-! ## Periodicity of a repeating run -/

/-- If the config at time `i + p` equals the config at time `i`, the run is `p`-periodic from `i`. -/
theorem run_shift (c : Cfg M) {i p : ℕ} (h : run M (i + p) c = run M i c) (b : ℕ) :
    run M (i + p + b) c = run M (i + b) c := by
  rw [run_add M (i + p) b c, h, ← run_add M i b c]

/-- The `p`-periodic run reduces the time index modulo `p` (from base `i`). -/
theorem run_mod (c : Cfg M) {i p : ℕ} (hp : 0 < p) (h : run M (i + p) c = run M i c) :
    ∀ s, run M (i + s) c = run M (i + s % p) c := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    rcases lt_or_ge s p with hs | hs
    · rw [Nat.mod_eq_of_lt hs]
    · have key : run M (i + s) c = run M (i + (s - p)) c := by
        have hb := run_shift c h (s - p)
        rw [show i + s = i + p + (s - p) from by omega]; exact hb
      have hmod : s % p = (s - p) % p := by
        conv_lhs => rw [← Nat.sub_add_cancel hs]
        rw [Nat.add_mod_right]
      rw [key, ih (s - p) (by omega), hmod]

/-! ## No configuration repeats before halting -/

/-- **A deterministic halting run does not repeat a configuration.**  If two times `i, j ≤ T` give
the same configuration, then `i = j`: otherwise the run would be periodic and never reach its halt
at `T`. -/
theorem no_config_repeat (c : Cfg M) {T : ℕ}
    (hhalt : M.halt (run M T c).st = true)
    (hpre : ∀ k, k < T → M.halt (run M k c).st = false)
    {i j : ℕ} (hi : i ≤ T) (hj : j ≤ T) (heq : run M i c = run M j c) : i = j := by
  have core : ∀ a b, a < T → b ≤ T → a < b → run M a c = run M b c → False := by
    intro a b ha _ hab heq
    have hp : 0 < b - a := by omega
    have hper : run M (a + (b - a)) c = run M a c := by
      rw [show a + (b - a) = b from by omega]; exact heq.symm
    have hTa : run M T c = run M (a + (T - a) % (b - a)) c := by
      conv_lhs => rw [show T = a + (T - a) from by omega]
      exact run_mod c hp hper (T - a)
    have hlt2 : a + (T - a) % (b - a) < T := by
      have := Nat.mod_lt (T - a) hp; omega
    rw [hTa, hpre _ hlt2] at hhalt
    simp at hhalt
  rcases lt_trichotomy i j with hlt | he | hgt
  · exact (core i j (by omega) hj hlt heq).elim
  · exact he
  · exact (core j i (by omega) hi hgt heq.symm).elim

/-! ## Time is bounded by configuration diversity -/

/-- The configurations visited in `[0, T]`. -/
noncomputable def visitedConfigs (c : Cfg M) (T : ℕ) : Finset (Cfg M) :=
  (Finset.range (T + 1)).image (fun t => run M t c)

/-- **Time is bounded by the number of distinct configurations.**  The `T + 1` configurations at
times `0..T` are pairwise distinct, so there are exactly `T + 1` of them. -/
theorem time_le_configs (c : Cfg M) {T : ℕ}
    (hhalt : M.halt (run M T c).st = true)
    (hpre : ∀ k, k < T → M.halt (run M k c).st = false) :
    T + 1 ≤ (visitedConfigs c T).card := by
  have hInj : Set.InjOn (fun t => run M t c) ↑(Finset.range (T + 1)) := by
    intro a ha b hb hab
    rw [Finset.coe_range, Set.mem_Iio] at ha hb
    exact no_config_repeat c hhalt hpre (by omega) (by omega) hab
  have hcard : (visitedConfigs c T).card = T + 1 := by
    rw [visitedConfigs, Finset.card_image_of_injOn hInj, Finset.card_range]
  omega

/-- **A configuration is `(state, head, tape)`, so the number of distinct configurations is at most
the state count times the distinct heads times the distinct tapes.** -/
theorem visitedConfigs_card_le_product (c : Cfg M) (T : ℕ) :
    (visitedConfigs c T).card
      ≤ Fintype.card M.State
        * ((visitedConfigs c T).image (fun d => d.hd)).card
        * ((visitedConfigs c T).image (fun d => d.tp)).card := by
  set F := visitedConfigs c T with hF
  have hinj : Set.InjOn (fun d : Cfg M => (d.st, d.hd, d.tp)) ↑F := by
    intro a _ b _ hab
    obtain ⟨as, ah, at'⟩ := a
    obtain ⟨bs, bh, bt⟩ := b
    simp only [Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl, rfl⟩ := hab
    rfl
  have hsub : F.image (fun d : Cfg M => (d.st, d.hd, d.tp))
      ⊆ (Finset.univ : Finset M.State) ×ˢ (F.image (fun d => d.hd))
          ×ˢ (F.image (fun d => d.tp)) := by
    intro p hp
    simp only [Finset.mem_image] at hp
    obtain ⟨d, hd, rfl⟩ := hp
    simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_image, true_and]
    exact ⟨⟨d, hd, rfl⟩, ⟨d, hd, rfl⟩⟩
  calc F.card
      = (F.image (fun d : Cfg M => (d.st, d.hd, d.tp))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((Finset.univ : Finset M.State) ×ˢ (F.image (fun d => d.hd))
          ×ˢ (F.image (fun d => d.tp))).card := Finset.card_le_card hsub
    _ = Fintype.card M.State * ((F.image (fun d => d.hd)).card
          * (F.image (fun d => d.tp)).card) := by
        rw [Finset.card_product, Finset.card_product, Finset.card_univ]
    _ = Fintype.card M.State * (F.image (fun d => d.hd)).card
          * (F.image (fun d => d.tp)).card := by ring

/-- **THE STRUCTURAL BOUND.**  For a deterministic halting run, time is bounded by the product of
the machine's state count, the number of distinct head positions, and the number of distinct tape
snapshots (the trace's distinct-row count):

`time + 1 ≤ |State| · #headPositions · distinctTapes`.

So polynomially many distinct tapes plus a polynomial head range forces polynomial time — the
time-sensitivity rank lacks. -/
theorem time_le (c : Cfg M) {T : ℕ}
    (hhalt : M.halt (run M T c).st = true)
    (hpre : ∀ k, k < T → M.halt (run M k c).st = false) :
    T + 1 ≤ Fintype.card M.State
      * ((visitedConfigs c T).image (fun d => d.hd)).card
      * ((visitedConfigs c T).image (fun d => d.tp)).card :=
  le_trans (time_le_configs c hhalt hpre) (visitedConfigs_card_le_product c T)

end PallLean.Paper93.DeepMath.PathB.TraceDistinctRows
