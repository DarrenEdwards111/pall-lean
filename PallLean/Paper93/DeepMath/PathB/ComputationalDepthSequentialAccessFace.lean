import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Basic

/-!
# A face of the wall: sequential vs random access — the seek penalty is the traversal factor

The cassette result is real and unconditional: a single-tape Turing machine serving `n` far-apart
requests pays `Ω(n²)` (Hennie, via crossing sequences) — no `cost_super`, a genuine proved separation.
This file applies the honest decomposition that says where it lands relative to `P vs NP`.

The tape's `n²` factors as **crossings × traversal-cost**: information must cross a cut, the head is the
only channel, so each of the crossings re-traverses the tape.  Moving to a circuit (random access)
replaces the single channel with *wires* — unbounded fan-out — so the circuit pays `crossings` **alone**
(all wires active simultaneously); the `× traversal` factor vanishes.  That is exactly why the tape's
compounding does not transfer.

So the tape supplies, unconditionally, the **traversal factor** — and that factor is *polynomial*
(`= n`, from locality).  The real wall is whether SAT forces **superpolynomially many crossings** on a
circuit — a circuit-size lower bound.  This file proves:

* the tape's unconditional compounding is polynomially bounded (`n²`) — a restricted/poly lower bound;
* the traversal factor can never lift a polynomial crossing-count to superpolynomial;
* the wall — `SuperpolyCrossings`, a superpolynomial crossing/size bound — is provably not reached by
  anything polynomial, so it is a genuinely separate, open condition (`cost_super` in crossing
  coordinates).

## Honest scope

This does not prove SAT forces superpolynomial crossings — that is `cost_super = P ≠ NP`.  It pins the
cassette precisely: the unconditional part is the (polynomial) traversal factor from locality; the
crossing-count factor is the wall, and the tape does not supply it.  Connects to the corpus's
crossing-capacity (Nečiporuk, capped `n²/log n`) and communication-complexity work.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SequentialAccessFace

/-- The cost a single-tape (sequential) channel pays: `crossings` re-traversals, each of size
`traversal`. -/
def tapeCost (crossings traversal : ℕ) : ℕ := crossings * traversal

/-- The cost a circuit (random access) pays: `crossings` alone — all wires active at once, no
per-crossing traversal. -/
def circuitCost (crossings : ℕ) : ℕ := crossings

/-- **The seek penalty is exactly the traversal factor (proved).**  Tape cost = circuit cost × the
per-crossing traversal cost; random access erases the second factor. -/
theorem seek_penalty_is_traversal_factor (crossings traversal : ℕ) :
    tapeCost crossings traversal = circuitCost crossings * traversal := rfl

/-- Polynomial boundedness (mirrors the corpus `PolyBounded`). -/
def PolyBounded (f : ℕ → ℕ) : Prop := ∃ c d, ∀ n, f n ≤ c * (n + 1) ^ d

/-- A **superpolynomial** crossing-count: the circuit crossing/size measure is not polynomially
bounded.  This is the circuit-size lower bound — `cost_super` in crossing coordinates. -/
def SuperpolyCrossings (cost : ℕ → ℕ) : Prop := ¬ PolyBounded cost

/-! ## The tape's unconditional compounding is polynomial -/

/-- `n·n ≤ (n+1)²`. -/
theorem tape_cost_is_polynomial (n : ℕ) : tapeCost n n ≤ (n + 1) ^ 2 := by
  unfold tapeCost
  calc n * n ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n)
    _ = (n + 1) ^ 2 := by ring

/-- **The cassette's compounding is polynomially bounded (proved).**  The unconditional single-tape
`n²` is a *polynomial* lower bound — capped like every restricted lower bound, `n²` not superpoly. -/
theorem tape_cost_polyBounded : PolyBounded (fun n => tapeCost n n) :=
  ⟨1, 2, fun n => by rw [one_mul]; exact tape_cost_is_polynomial n⟩

/-! ## The traversal factor cannot reach the wall -/

/-- **The traversal factor cannot manufacture the gap (proved).**  Multiplying a polynomially-bounded
crossing-count by the tape's per-crossing traversal factor `(n+1)` stays polynomial.  So the tape's
unconditional compounding (the `× traversal` factor from locality) can never lift a polynomial
crossing-count to superpolynomial. -/
theorem traversal_cannot_cross {cost : ℕ → ℕ} (h : PolyBounded cost) :
    PolyBounded (fun n => cost n * (n + 1)) := by
  obtain ⟨c, d, hcost⟩ := h
  refine ⟨c, d + 1, fun n => ?_⟩
  calc cost n * (n + 1) ≤ (c * (n + 1) ^ d) * (n + 1) := Nat.mul_le_mul (hcost n) (le_refl (n + 1))
    _ = c * (n + 1) ^ (d + 1) := by ring

/-- **Capstone (proved): the cassette is polynomially below the wall.**

The tape's unconditional compounding is polynomial (`tape_cost_polyBounded`), and anything polynomial
is *not* `SuperpolyCrossings` — so the cassette's real, unconditional `n²` sits provably below the wall.
The wall is `SuperpolyCrossings`: a superpolynomial crossing count on a circuit, which is exactly a
circuit-size lower bound.  Moving tape → circuit strips the (polynomial) traversal factor
(`traversal_cannot_cross` shows that factor can't help), leaving the crossing count alone — and that
count being superpolynomial for SAT is `cost_super`, undischarged.  "Does SAT force sequential access on
a circuit?" = "does SAT force superpolynomial crossings?" = the wall. -/
theorem cassette_polynomially_below_wall :
    PolyBounded (fun n => tapeCost n n) ∧
      (∀ cost, PolyBounded cost → ¬ SuperpolyCrossings cost) :=
  ⟨tape_cost_polyBounded, fun _ h hsp => hsp h⟩

end PallLean.Paper93.DeepMath.PathB.SequentialAccessFace

#print axioms PallLean.Paper93.DeepMath.PathB.SequentialAccessFace.tape_cost_polyBounded
#print axioms PallLean.Paper93.DeepMath.PathB.SequentialAccessFace.traversal_cannot_cross
#print axioms PallLean.Paper93.DeepMath.PathB.SequentialAccessFace.cassette_polynomially_below_wall
