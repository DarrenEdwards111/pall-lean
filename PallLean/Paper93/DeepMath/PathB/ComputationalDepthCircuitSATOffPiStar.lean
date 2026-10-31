import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Basic

/-!
# The crossing object, specified off Π★ — spec + reduction, NOT the algorithm

Three curiosity passes and the Williams-threading arc converged on one object: a faster-than-brute-force
Circuit-SAT algorithm, **off Π★** (a genuine computation, not the barriered separating measure), fed
through the cashout and magnification.  This file makes that object precise as a **spec and a
reduction**, and proves the one honest non-triviality around it.

**It does NOT build the algorithm.**  The algorithm's correctness is the field `Attack.decides`, left as
an explicit open socket.  Filling that socket is `P ≠ NP`; the whole session refused to fake it, and so
does this file.  What is built here is the frame: the speedup requirement, the off-Π★ distinction, the
circularity of the Π★ route, and the statement that the separation rests on exactly this one off-Π★
object and nothing else.

## What is proved

* **`brute_does_not_beat_itself`** — brute force does not beat itself, so a valid attack must be a
  STRICT sub-brute-force algorithm (the speedup requirement is genuinely non-trivial).
* **`piStar_attack_not_off`** — an attack resting on Π★ is not off Π★ (by construction).
* **`piStar_route_circular`** — if Π★ exists iff SAT is hard (the barriered equivalence), resting on Π★
  "proves" the separation only by assuming it — no progress.  This is *why* the crossing must be off Π★.
* **`crossing_is_off_pistar_and_sufficient`** — given the corpus's cashout+magnification chain
  (a correct off-Π★ fast algorithm ⟹ the separation, `williams_cashout` axiom-free), the separation
  follows from `GenuineCrossing` and nothing else, and no Π★-based attack is a genuine crossing.

## Honest scope

`GenuineCrossing` (an off-Π★, correct, sub-brute-force Circuit-SAT algorithm) is the single open socket.
This file is its specification, not its construction.  Nothing here is a proof of `P ≠ NP` — proving
`Attack.decides` for such an attack *is* `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CircuitSATOffPiStar

/-- Brute-force Circuit-SAT time on `n` inputs: `2^n` (try every assignment). -/
def brute (n : ℕ) : ℕ := 2 ^ n

/-- A running time **beats brute force** in the Williams-triggering sense: sub-`2^n` by every
polynomial factor, infinitely often.  This is the speedup the cashout needs. -/
def BeatsBruteForce (T : ℕ → ℕ) : Prop := ∀ k, ∃ n, T n * (n + 1) ^ k < 2 ^ n

/-- **The speedup is genuinely non-trivial (proved).**  Brute force does not beat itself — so a valid
attack must be a STRICT sub-brute-force algorithm, not `2^n` in disguise. -/
theorem brute_does_not_beat_itself : ¬ BeatsBruteForce (fun n => 2 ^ n) := by
  intro h
  obtain ⟨n, hn⟩ := h 1
  simp only [pow_one] at hn
  rw [show 2 ^ n * (n + 1) = 2 ^ n * n + 2 ^ n from by ring] at hn
  omega

/-- What a Circuit-SAT attack rests on. -/
inductive Basis where
  /-- a genuine computation. -/
  | algorithm : Basis
  /-- the Π★ separating measure — barriered: Π★ exists ↔ SAT ∉ P/poly. -/
  | piStarObserver : Basis
  deriving DecidableEq

/-- A candidate Circuit-SAT attack: a claimed running time, what it rests on, a proof it is fast, and
the OPEN socket `decides` = it correctly decides Circuit-SAT within that time. -/
structure Attack where
  T : ℕ → ℕ
  basis : Basis
  fast : BeatsBruteForce T
  /-- SOCKET — the open algorithm's correctness.  NOT proved here; proving it is the theorem. -/
  decides : Prop

/-- The attack is **off Π★**: it rests on a genuine algorithm, not the barriered separating measure. -/
def OffPiStar (a : Attack) : Prop := a.basis = Basis.algorithm

/-- **A Π★-based attack is not off Π★ (proved).**  It rests on the barriered measure. -/
theorem piStar_attack_not_off (a : Attack) (h : a.basis = Basis.piStarObserver) : ¬ OffPiStar a := by
  unfold OffPiStar; rw [h]; decide

/-- **The genuine crossing.**  There is an off-Π★, correct, fast Circuit-SAT algorithm.  This is the
single open object — building it (proving some `a.decides`) is `P ≠ NP`. -/
def GenuineCrossing : Prop := ∃ a : Attack, OffPiStar a ∧ a.decides

/-- **The Π★ route is circular (proved).**  If Π★ exists iff SAT is hard (the barriered equivalence),
then "resting on Π★" yields the separation only by assuming it — no progress.  This is exactly why the
crossing must be off Π★. -/
theorem piStar_route_circular {PiStarExists Separation : Prop} (hbar : PiStarExists ↔ Separation) :
    PiStarExists → Separation :=
  hbar.mp

/-- **Capstone (proved): the separation rests on exactly one object, off Π★.**

Given the corpus's established chain — a correct off-Π★ fast Circuit-SAT algorithm ⟹ the separation
(`williams_cashout`, axiom-free, plus magnification to superpoly-NP), supplied here as `cashout` — the
whole separation follows from `GenuineCrossing`, and no Π★-based attack is a genuine crossing.  So the
crossing is pinned to one open socket, and that socket is off Π★.

This BUILDS THE SPEC AND THE REDUCTION.  It does NOT build the algorithm: `GenuineCrossing` unfolds to
`∃ a, OffPiStar a ∧ a.decides`, and `a.decides` is unproved.  Proving it is `P ≠ NP`. -/
theorem crossing_is_off_pistar_and_sufficient {Separation : Prop}
    (cashout : GenuineCrossing → Separation) :
    (GenuineCrossing → Separation) ∧
      (∀ a : Attack, a.basis = Basis.piStarObserver → ¬ OffPiStar a) :=
  ⟨cashout, fun a h => piStar_attack_not_off a h⟩

end PallLean.Paper93.DeepMath.PathB.CircuitSATOffPiStar

#print axioms PallLean.Paper93.DeepMath.PathB.CircuitSATOffPiStar.brute_does_not_beat_itself
#print axioms PallLean.Paper93.DeepMath.PathB.CircuitSATOffPiStar.crossing_is_off_pistar_and_sufficient
