import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverInvariantBridge

/-!
# The abstract-invariant no-go: every ∃-invariant route is the separation, verbatim

**Step 4 of the separation phase** (prove-or-refute the isolated inequality (S) before building
infrastructure).  The verdict, fully formal: the invariant-bridge framework
(`InvSound`/`InvHard`, `ObserverInvariantBridge`) carries **zero content at the abstract level**.
All three existential route forms are *equivalent* to the separation itself:

1. `invariant_route_iff_sep` — `(∃ Inv, InvSound ∧ InvHard) ↔ ¬ PolyCollapse SATV`.
   Hardness is cheap (`invHard_diag`: the machine-blind diagonal invariant `(n+1)^n` is
   "hard" for every decider), and soundness is *vacuous* under separation
   (`invSound_of_sep`: it quantifies only over poly SAT-deciders, of which there are then
   none).  Given hardness, soundness **is** the separation (`invSound_iff_sep`) — the
   circularity of (S) made exact.

2. `timeBounded_route_iff_sep` — the same for HAL's finer, non-vacuous calibration
   `InvTimeBounded` (`Inv ≤ poly(time)` over *all* deciders, poly or not).  Witness:
   `minTimeInv`, the minimal uniform correct-halting time per input length.  It is
   time-bounded by construction (`minTimeInv_timeBounded`, unconditionally) and its hardness
   is verbatim "every SAT decider needs superpolynomial time" (`minTimeInv_hard_iff_sep`).

3. `genSound_route_iff_sep` — the same even for the *SAT-free* generic soundness
   `InvGenSound` (`Inv` poly on **every** poly-time machine, no correctness hypothesis) —
   the only formulation whose soundness half is not conditioned on SAT-deciders and hence
   not vacuously creditable.  It is genuinely falsifiable (`diag_not_genSound`), yet
   `minTimeInv` satisfies it unconditionally (`minTimeInv_genSound`: on a poly-clock halting
   machine, the halt time *is* poly), so the ∃-form still collapses to the separation.

**What survives.**  No abstract factorization of `¬ PolyCollapse` through an invariant pair
decomposes the problem: exhibiting *any* `Inv` with (sound, hard) — in any of the three
senses — is exactly as hard as the separation, because time itself (`minTimeInv`) trivializes
the soundness axis and pushes all content into hardness = the separation.  Content can enter
only through a **concrete** invariant (e.g. a rank of a specific algebraic object) for which
`InvGenSound` is a real transfer theorem and `InvHard` is attacked by algebra rather than
diagonalization.  For such a concrete `Inv`, `InvGenSound` demands: every poly-time machine
has a poly invariant — and this is where language-containing extractions die (a poly-time
machine computing a high-rank language, e.g. `MOD_q`, refutes generic soundness for any
invariant dominating the language rank; that concrete kill is the next brick).

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SeparationNoGo

open Classical
open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge
open PallLean.Paper93.DeepMath.PathB.ComposableMachine (Machine Decides decideOut HaltsBy run
  init run_stable)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-! ## Hardness is cheap: the machine-blind diagonal invariant -/

/-- The diagonal growth function `(n+1)^n` is not polynomially bounded: from
`(n+1)^n ≤ c·(n+1)^k` at `n := c+k+1`, cancelling `(n+1)^k` forces `n+1 ≤ c`. -/
theorem diag_not_polyBounded : ¬ PolyBounded (fun n => (n + 1) ^ n) := by
  rintro ⟨c, k, h⟩
  have hn := h (c + k + 1)
  simp only [] at hn
  have hpos : (0 : ℕ) < (c + k + 1 + 1) ^ k := pow_pos (by omega) k
  have hsplit : (c + k + 1 + 1) ^ (c + k + 1) = (c + k + 1 + 1) ^ k * (c + k + 1 + 1) ^ (c + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hself : c + k + 1 + 1 ≤ (c + k + 1 + 1) ^ (c + 1) :=
    Nat.le_self_pow (by omega) _
  have h2 : (c + k + 1 + 1) ^ k * (c + k + 1 + 1) ≤ (c + k + 1 + 1) ^ k * c := by
    calc (c + k + 1 + 1) ^ k * (c + k + 1 + 1)
        ≤ (c + k + 1 + 1) ^ k * (c + k + 1 + 1) ^ (c + 1) := Nat.mul_le_mul_left _ hself
      _ = (c + k + 1 + 1) ^ (c + k + 1) := hsplit.symm
      _ ≤ c * (c + k + 1 + 1) ^ k := hn
      _ = (c + k + 1 + 1) ^ k * c := Nat.mul_comm _ _
  have h3 : c + k + 1 + 1 ≤ c := Nat.le_of_mul_le_mul_left h2 hpos
  omega

/-- **Hardness is cheap.**  The machine-blind diagonal invariant `Inv M n := (n+1)^n` is
`InvHard` for every verifier: it never consults the machine, so "every decider has a
superpolynomial invariant" holds vacuously of it.  `InvHard` alone therefore carries no
information about SAT. -/
theorem invHard_diag (SATV : NPObs) : InvHard SATV (fun _ n => (n + 1) ^ n) :=
  fun _M _T _hD => diag_not_polyBounded

/-! ## Soundness is vacuous under separation -/

/-- **Soundness is free once the theorem is true.**  `InvSound` quantifies only over
polynomial-time SAT-deciders; under `¬ PolyCollapse` there are none, so *every* invariant
is sound.  Proving `InvSound` for a hard invariant can therefore never be easier than the
separation itself. -/
theorem invSound_of_sep (SATV : NPObs) (Inv : Invariant) (hsep : ¬ PolyCollapse SATV) :
    InvSound SATV Inv := fun M T hT hD => absurd ⟨M, T, hT, hD⟩ hsep

/-- **The circularity of (S), exact.**  Given hardness, the soundness hypothesis is
*equivalent* to the separation — it is not an independently attackable inequality. -/
theorem invSound_iff_sep (SATV : NPObs) (Inv : Invariant) (hHard : InvHard SATV Inv) :
    InvSound SATV Inv ↔ ¬ PolyCollapse SATV :=
  ⟨fun hS => invariant_bridge SATV Inv hS hHard, invSound_of_sep SATV Inv⟩

/-- **No-go I.**  The ∃-invariant route in the `InvSound` form is verbatim the separation:
forward is the (proved) bridge; backward, the diagonal invariant is hard for free and sound
vacuously. -/
theorem invariant_route_iff_sep (SATV : NPObs) :
    (∃ Inv : Invariant, InvSound SATV Inv ∧ InvHard SATV Inv) ↔ ¬ PolyCollapse SATV := by
  constructor
  · rintro ⟨Inv, hS, hH⟩
    exact invariant_bridge SATV Inv hS hH
  · intro hsep
    exact ⟨fun _ n => (n + 1) ^ n, invSound_of_sep SATV _ hsep, invHard_diag SATV⟩

/-! ## The minimal-time invariant

The witness that kills the finer forms: `minTimeInv SATV M n` is the least single time `t`
at which `M` has halted *and* answered `acceptBool SATV` correctly on **every** input of
length `n` (and `0` if no such time exists).  It is "time itself" as an invariant. -/

/-- `M` has, by time `t`, uniformly halted-and-correctly-decided the verifier's boundary
language on all inputs of length `n`. -/
def SolvedAt (SATV : NPObs) (M : Machine) (n t : ℕ) : Prop :=
  ∀ x : List Bool, x.length = n → HaltsBy M x t ∧ decideOut M x t = acceptBool SATV x

/-- Solvedness is upward-closed in time: a halted config is stable (`run_stable`), so both
the halt flag and the decision persist. -/
theorem solvedAt_mono (SATV : NPObs) (M : Machine) {n t t' : ℕ} (hle : t ≤ t')
    (h : SolvedAt SATV M n t) : SolvedAt SATV M n t' := by
  intro x hx
  obtain ⟨hh, hc⟩ := h x hx
  have hs := run_stable M x hle hh
  refine ⟨?_, ?_⟩
  · show M.halt (run M t' (init M x)).st = true
    rw [hs]
    exact hh
  · show M.accept (run M t' (init M x)).st = acceptBool SATV x
    rw [hs]
    exact hc

/-- A solved length stays solved at *any* time by which the machine halts on that length —
in particular at earlier halting times: whichever of the two times is later, the config
there equals the halted config at the earlier one. -/
theorem solvedAt_of_halts (SATV : NPObs) (M : Machine) {n t T : ℕ}
    (h : SolvedAt SATV M n t) (hH : ∀ x : List Bool, x.length = n → HaltsBy M x T) :
    SolvedAt SATV M n T := by
  rcases le_total t T with hle | hle
  · exact solvedAt_mono SATV M hle h
  · intro x hx
    obtain ⟨hh, hc⟩ := h x hx
    have hs := run_stable M x hle (hH x hx)
    have hc' : M.accept (run M t (init M x)).st = acceptBool SATV x := hc
    rw [hs] at hc'
    exact ⟨hH x hx, hc'⟩

/-- **The minimal-time invariant**: the least uniform correct-halting time per length
(`0` where none exists). -/
noncomputable def minTimeInv (SATV : NPObs) : Invariant := fun M n =>
  if h : ∃ t, SolvedAt SATV M n t then Nat.find h else 0

/-- A decider's minimal-time invariant is bounded by its clock. -/
theorem minTimeInv_le (SATV : NPObs) {M : Machine} {T : ℕ → ℕ}
    (hD : Decides M (acceptBool SATV) T) (n : ℕ) : minTimeInv SATV M n ≤ T n := by
  have hsolved : SolvedAt SATV M n (T n) := by
    intro x hx
    obtain ⟨hh, hc⟩ := hD x
    rw [hx] at hh hc
    exact ⟨hh, hc⟩
  show (if h : ∃ t, SolvedAt SATV M n t then Nat.find h else 0) ≤ T n
  rw [dif_pos ⟨T n, hsolved⟩]
  exact Nat.find_le hsolved

/-- `minTimeInv` satisfies HAL's finer calibration `InvTimeBounded` **unconditionally**:
for every decider, `Inv M n ≤ T n ≤ 1·(T n + n + 1)^1`. -/
theorem minTimeInv_timeBounded (SATV : NPObs) : InvTimeBounded SATV (minTimeInv SATV) := by
  intro M T hD
  refine ⟨1, 1, fun n => ?_⟩
  have h1 := minTimeInv_le SATV hD n
  have h2 : (T n + n + 1) ^ 1 = T n + n + 1 := pow_one _
  omega

/-- Any clock dominating the minimal-time invariant is itself a valid decision clock: the
minimal witness solves the length, and solvedness propagates up to the new clock. -/
theorem decides_of_minTimeInv_le (SATV : NPObs) {M : Machine} {T T' : ℕ → ℕ}
    (hD : Decides M (acceptBool SATV) T) (hle : ∀ n, minTimeInv SATV M n ≤ T' n) :
    Decides M (acceptBool SATV) T' := by
  intro x
  set n := x.length with hn
  have hsolved : SolvedAt SATV M n (T n) := by
    intro x' hx'
    obtain ⟨hh, hc⟩ := hD x'
    rw [hx'] at hh hc
    exact ⟨hh, hc⟩
  have hex : ∃ t, SolvedAt SATV M n t := ⟨T n, hsolved⟩
  have hval : minTimeInv SATV M n = Nat.find hex := by
    show (if h : ∃ t, SolvedAt SATV M n t then Nat.find h else 0) = Nat.find hex
    rw [dif_pos hex]
  have hfle : Nat.find hex ≤ T' n := by
    rw [← hval]
    exact hle n
  have hup : SolvedAt SATV M n (T' n) := solvedAt_mono SATV M hfle (Nat.find_spec hex)
  exact hup x hn.symm

/-- **`minTimeInv`'s hardness is verbatim the separation**: "every SAT decider has a
superpolynomially growing minimal correct-halting time" ⟺ "SAT has no poly decider".
Forward: a poly decider's clock dominates its invariant.  Backward: a poly bound on the
invariant is itself a valid poly clock (`decides_of_minTimeInv_le`). -/
theorem minTimeInv_hard_iff_sep (SATV : NPObs) :
    InvHard SATV (minTimeInv SATV) ↔ ¬ PolyCollapse SATV := by
  constructor
  · intro hH hcol
    obtain ⟨M, T, hT, hD⟩ := hcol
    exact hH M T hD (polyBounded_of_le (minTimeInv_le SATV hD) hT)
  · intro hsep M T hD hPB
    obtain ⟨c, k, hb⟩ := hPB
    exact hsep ⟨M, fun n => c * (n + 1) ^ k, ⟨c, k, fun n => Nat.le_refl _⟩,
      decides_of_minTimeInv_le SATV hD hb⟩

/-- **No-go II.**  Even HAL's finer route form — `Inv ≤ poly(time)` over *all* deciders,
which is not vacuous under separation — is verbatim the separation: `minTimeInv` is
time-bounded unconditionally, and its hardness is the separation. -/
theorem timeBounded_route_iff_sep (SATV : NPObs) :
    (∃ Inv : Invariant, InvTimeBounded SATV Inv ∧ InvHard SATV Inv) ↔ ¬ PolyCollapse SATV := by
  constructor
  · rintro ⟨Inv, hTB, hH⟩
    exact invariant_bridge SATV Inv (invSound_of_timeBounded SATV Inv hTB) hH
  · intro hsep
    exact ⟨minTimeInv SATV, minTimeInv_timeBounded SATV,
      (minTimeInv_hard_iff_sep SATV).mpr hsep⟩

/-! ## The honest residue: SAT-free generic soundness — and its collapse too -/

/-- A machine is polynomial-time if some polynomially bounded clock halts it on every
input.  No correctness hypothesis — this predicate never mentions SAT. -/
def PolyTime (M : Machine) : Prop :=
  ∃ T : ℕ → ℕ, PolyBounded T ∧ ∀ x, HaltsBy M x (T x.length)

/-- **Generic soundness** — the only non-circular calibration: the invariant is
polynomially bounded on *every* polynomial-time machine, whatever it computes. -/
def InvGenSound (Inv : Invariant) : Prop := ∀ M, PolyTime M → PolyBounded (Inv M)

/-- Generic soundness implies the SAT-conditioned soundness (a poly SAT-decider is in
particular a poly-time machine). -/
theorem invSound_of_genSound (SATV : NPObs) (Inv : Invariant) (h : InvGenSound Inv) :
    InvSound SATV Inv :=
  fun M T hT hD => h M ⟨T, hT, fun x => (hD x).1⟩

/-- Poly-time machines exist (the constant machine). -/
theorem polyTime_exists : ∃ M, PolyTime M := by
  obtain ⟨M, T, hT, hD⟩ := PLang_const true
  exact ⟨M, T, hT, fun x => (hD x).1⟩

/-- Generic soundness is genuinely falsifiable — the diagonal hard invariant fails it.
Under `InvGenSound` the free-hardness trick of No-go I is unavailable. -/
theorem diag_not_genSound : ¬ InvGenSound (fun _ n => (n + 1) ^ n) := by
  intro h
  obtain ⟨M, hM⟩ := polyTime_exists
  exact diag_not_polyBounded (h M hM)

/-- **Yet `minTimeInv` is generically sound, unconditionally**: on any machine with a poly
halting clock `T`, whenever a length is solvable at all, `T n` is itself a solving time
(`solvedAt_of_halts`), so the minimal one is `≤ T n`; unsolvable lengths contribute `0`. -/
theorem minTimeInv_genSound (SATV : NPObs) : InvGenSound (minTimeInv SATV) := by
  intro M hM
  obtain ⟨T, hT, hH⟩ := hM
  refine polyBounded_of_le (fun n => ?_) hT
  show (if h : ∃ t, SolvedAt SATV M n t then Nat.find h else 0) ≤ T n
  by_cases hex : ∃ t, SolvedAt SATV M n t
  · rw [dif_pos hex]
    refine Nat.find_le (solvedAt_of_halts SATV M (Nat.find_spec hex) fun x hx => ?_)
    have hhx := hH x
    rw [hx] at hhx
    exact hhx
  · rw [dif_neg hex]
    exact Nat.zero_le _

/-- **No-go III (the full collapse).**  Even the SAT-free route form — generic soundness
plus hardness — is verbatim the separation.  Time itself trivializes the soundness axis in
every formulation; all content lives in hardness, and hardness of `minTimeInv` *is* the
separation.  An invariant route acquires content only when `Inv` is a concrete measure
whose generic soundness is a real transfer theorem and whose hardness has a non-diagonal
proof. -/
theorem genSound_route_iff_sep (SATV : NPObs) :
    (∃ Inv : Invariant, InvGenSound Inv ∧ InvHard SATV Inv) ↔ ¬ PolyCollapse SATV := by
  constructor
  · rintro ⟨Inv, hG, hH⟩
    exact invariant_bridge SATV Inv (invSound_of_genSound SATV Inv hG) hH
  · intro hsep
    exact ⟨minTimeInv SATV, minTimeInv_genSound SATV,
      (minTimeInv_hard_iff_sep SATV).mpr hsep⟩

end PallLean.Paper93.DeepMath.PathB.SeparationNoGo
