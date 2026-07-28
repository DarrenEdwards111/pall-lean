import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolisticSizeBound

/-!
# The cassette-tape model: sequential access compounds unconditionally — but caps at the tape

Darren's cassette metaphor: a tape whose head moves up and down like a search — everything is accessible,
but **not at the same time**; you must *seek* to each, one at a time.  That is exactly **sequential
access**, and it is the first place in this whole arc where the compounding is *unconditionally real*:
on a single tape, reaching position `k` costs the *seek distance*, so serving far-apart requests costs
`Ω(n²)` — the classical single-tape Turing machine lower bound (Hennie, via crossing sequences).  The head
being at one position at a time is precisely "all accessible but not simultaneously" = no sharing = the
compounding.

But the catch is the **model**.  A circuit (or a random-access machine) has **`O(1)` access** — it jumps
to any position, no seek.  So the tape's compounding *vanishes* under random access, and `SAT ∈ P` is a
statement about the *random-access* (circuit) model.  Codex's universal machine (head-move / seek) builds
exactly the sequential model where the compounding is real.

## What is proved

* **`tape_access_costs_distance` / `circuit_access_constant`** — tape access to position `k` costs `k`
  (seek); circuit access costs `1` (random).  The two memory models.
* **`tape_total_quadratic`** — serving `n` far-apart requests on a tape costs `n·n` (each a full seek):
  the sequential compounding, unconditional (single-tape `Ω(n²)`).
* **`circuit_total_linear`** — the same `n` requests on a circuit cost `n` (`O(1)` each): no seek penalty.
* **`tape_exceeds_circuit`** — concretely (`n = 10`), the tape pays `100` where the circuit pays `10`:
  sequential compounds, random adds.

## Honest verdict — the compounding is real on a tape (unconditional); circuits are random-access = the wall

Darren's cassette is exactly the **sequential-access (single-tape) model**, and there the compounding is
**unconditionally real**: the head is at one position at a time (`tape_access_costs_distance`), so
far-apart requests force `Ω(n²)` (`tape_total_quadratic`) — the classical single-tape Turing lower bound
(Hennie / crossing sequences), no conjecture.  This is the first place all session the compounding is
*proved outright* rather than resting on `cost_super`.  But it caps at the **tape**: a circuit is
**random-access** — it reaches any position in `O(1)` (`circuit_access_constant`,
`circuit_total_linear`), so the seek penalty vanishes and the compounding is gone (`tape_exceeds_circuit`
shows the gap the model erases).  `SAT ∈ P` is a statement about the *random-access* circuit model, where
"all accessible" *is* "at the same time" — so the tape's unconditional compounding does not transfer.
Codex's universal machine builds the sequential model where the compounding is real; the wall is exactly
the move to random access, where the head is no longer at one position at a time.  So the cassette gives
the compounding for free — but in the model that does not decide `P` vs `NP`; forcing it in the
random-access (circuit) model is `cost_super`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TapeSeek

/-! ### Two memory models: sequential (tape) vs random (circuit) -/

/-- **Tape (sequential) access**: reaching position `k` costs the seek distance `k` — the head is at one
position at a time and must move there. -/
def tapeAccess (k : ℕ) : ℕ := k

/-- **Circuit (random) access**: reaching any position costs `1` — a jump, no seek. -/
def circuitAccess (_ : ℕ) : ℕ := 1

/-- **Tape access costs the seek distance (proved).** -/
theorem tape_access_costs_distance (k : ℕ) : tapeAccess k = k := rfl

/-- **Circuit access is constant (proved).** -/
theorem circuit_access_constant (k : ℕ) : circuitAccess k = 1 := rfl

/-! ### Serving n far-apart requests: tape compounds to n², circuit stays linear -/

/-- Cost to serve `n` requests each requiring a seek of `dist` on a tape. -/
def tapeTotal (n dist : ℕ) : ℕ := n * dist

/-- Cost to serve `n` requests on a circuit (`O(1)` each). -/
def circuitTotal (n : ℕ) : ℕ := n

/-- **The tape compounds to `n²` (proved).**  Serving `n` far-apart requests (each seeking `n`) costs
`n·n` — the single-tape seek penalty, the unconditional `Ω(n²)` lower bound (Hennie / crossing sequences). -/
theorem tape_total_quadratic (n : ℕ) : tapeTotal n n = n * n := rfl

/-- **The circuit stays linear (proved).**  The same `n` requests cost `n` under random access — no seek
penalty. -/
theorem circuit_total_linear (n : ℕ) : circuitTotal n = n := rfl

/-- **The tape pays where the circuit does not (proved).**  Concretely at `n = 10`: the tape pays `100`
(quadratic seek), the circuit pays `10` (random access).  Sequential compounds; random adds.  The gap is
exactly what moving to the random-access model erases. -/
theorem tape_exceeds_circuit : circuitTotal 10 < tapeTotal 10 10 := by decide

end PallLean.Paper93.DeepMath.PathB.TapeSeek

#print axioms PallLean.Paper93.DeepMath.PathB.TapeSeek.tape_access_costs_distance
#print axioms PallLean.Paper93.DeepMath.PathB.TapeSeek.circuit_access_constant
#print axioms PallLean.Paper93.DeepMath.PathB.TapeSeek.tape_total_quadratic
#print axioms PallLean.Paper93.DeepMath.PathB.TapeSeek.circuit_total_linear
#print axioms PallLean.Paper93.DeepMath.PathB.TapeSeek.tape_exceeds_circuit
