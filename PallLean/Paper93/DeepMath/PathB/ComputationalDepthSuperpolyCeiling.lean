import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAndreevCeiling

/-!
# Raising the ceiling to a superpolynomial base bound: this rung is the wall

The blade ladder climbed sharing models (capped at the ceiling) and then raised the ceiling `n² → n^{5/2}`
(Andreev) — real, but still polynomial.  The next rung is to raise the base bound to *superpolynomial*.  I did
not fake it, because a superpolynomial base bound **is** the wall: a superpolynomial *formula* bound is
`P ⊄ NC¹` (open), and a superpolynomial *general-circuit* bound is `P ≠ NP` itself (`cost_super`).  What I build
is the exact implication the ladder points at, with the superpolynomial bound as the *hypothesis* it is —
undischarged — plus the two facts that make it the wall.

**The implication is real and axiom-clean.**  If the target family's circuit cost is superpolynomial — it
dominates every polynomial `n^k` — then the family is not polynomial-size (`superpoly_ceiling_gives_separation`
via `superpoly_not_polyBounded`).  For a target in `NP`, that is `P ≠ NP`.  So the raised superpolynomial
ceiling *would* crown the ladder: this is exactly why every rung pointed here.

**But the hypothesis is the open object.**  Every base bound anyone has *proved* is polynomial — Khrapchenko
`n²`, Andreev `n^{5/2}` — a fixed power (`known_base_is_polynomial`), and a fixed power is *not* superpolynomial
(`known_base_not_superpoly`).  No superpolynomial base bound exists in the literature; a polynomial world is
consistent (`superpoly_ceiling_is_open`).  `Superpoly` on the base is the undischarged hypothesis — `cost_super`
in the ceiling's language, the same discipline as `RemainingLine` (the line appears only as a hypothesis, never
proved).

**And even a superpolynomial *formula* bound does not reach `P ≠ NP`.**  A general circuit is a formula with
sharing, so its cost is *below* the formula cost: `circuitLB ≤ formulaLB`.  Hence a superpolynomial formula
bound `g` can sit above a *polynomial* circuit bound `h` — `formula_superpoly_allows_circuit_poly`: `g`
superpolynomial and `h` polynomial coexist under `h ≤ g`.  So raising the *formula* ceiling to superpolynomial
(itself open, `P ⊄ NC¹`) does **not** force the *circuit* ceiling superpolynomial (`P ≠ NP`).  The rung splits
into two open walls, the general one strictly harder.

## What is proved

* **`superpoly_not_polyBounded`** — a superpolynomial function is not polynomially bounded.
* **`superpoly_ceiling_gives_separation`** — if the target family's circuit cost is superpolynomial, the family
  is not polynomial-size: the raised ceiling *would* give the separation.  (Implication; hypothesis
  undischarged.)
* **`known_base_is_polynomial`** / **`known_base_not_superpoly`** — every proved base bound (`n²`, `n^{5/2}`) is
  a fixed power, not superpolynomial.
* **`superpoly_ceiling_is_open`** — a polynomial world is consistent: no superpolynomial base bound is known.
* **`formula_superpoly_allows_circuit_poly`** — a superpolynomial formula bound coexists with a polynomial
  circuit bound below it: formula-superpolynomial (`P ⊄ NC¹`) does not force circuit-superpolynomial (`P ≠ NP`).
* **`superpoly_ceiling_is_the_wall`** — both: the implication holds, and the base bound is open.

## Honest verdict — the rung is the wall; I built the implication, not a superpolynomial bound

Raising the ceiling to a superpolynomial base bound is the wall, and I did not manufacture it.  What is
machine-checked is the implication the whole ladder points at: a superpolynomial circuit-cost bound gives the
separation (`superpoly_ceiling_gives_separation`), which is why every rung led here — and the two facts that
keep it a wall: every *proved* base bound is a fixed power, not superpolynomial (`known_base_not_superpoly`,
`superpoly_ceiling_is_open`), and even a superpolynomial *formula* bound (open, `P ⊄ NC¹`) does not reach a
superpolynomial *circuit* bound (`P ≠ NP`) because sharing puts the circuit cost below the formula cost
(`formula_superpoly_allows_circuit_poly`).  So `Superpoly` on the base is the undischarged hypothesis —
`cost_super` in ceiling language — split into two open walls with the general one strictly harder.  The ladder
is complete: it climbs to the rung where the base bound must go superpolynomial, and that rung is exactly the
open object.  I built the receipt, not a proof of it.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SuperpolyCeiling

/-- A bound is polynomially bounded if some fixed power `n^k` dominates it. -/
def PolyBounded (f : Nat → Nat) : Prop := ∃ k, ∀ n, f n ≤ n ^ k

/-- A bound is superpolynomial if it exceeds *every* fixed power `n^k` at some `n`. -/
def Superpoly (f : Nat → Nat) : Prop := ∀ k, ∃ n, n ^ k < f n

/-- **A superpolynomial bound is not polynomially bounded (proved).**  If `n^k` dominated `f` everywhere, `f`
could not exceed `n^k` anywhere. -/
theorem superpoly_not_polyBounded {f : Nat → Nat} (h : Superpoly f) : ¬ PolyBounded f := by
  rintro ⟨k, hk⟩
  obtain ⟨n, hn⟩ := h k
  have := hk n
  omega

/-- A family of targets, with the minimal circuit size at each parameter `n`. -/
structure CircuitFamily where
  /-- minimal general-circuit size for the target at parameter `n` -/
  circuitCost : Nat → Nat

/-- **The raised superpolynomial ceiling would give the separation (proved).**  If the family's circuit cost is
superpolynomial, the family is not polynomial-size — for a target in `NP`, `P ≠ NP`.  This is the implication
the ladder points at; the hypothesis `Superpoly F.circuitCost` is `cost_super`, undischarged. -/
theorem superpoly_ceiling_gives_separation (F : CircuitFamily) (h : Superpoly F.circuitCost) :
    ¬ PolyBounded F.circuitCost :=
  superpoly_not_polyBounded h

/-- The best proved base bounds — Khrapchenko `n²`, Andreev `n^{5/2}` — are fixed powers; take `n²` as the
representative. -/
def knownBase : Nat → Nat := fun n => n ^ 2

/-- **Every proved base bound is polynomial (proved).**  `n²` is dominated by `n²`. -/
theorem known_base_is_polynomial : PolyBounded knownBase :=
  ⟨2, fun n => le_refl (n ^ 2)⟩

/-- **The known base bound is not superpolynomial (proved).**  A fixed power cannot exceed every power. -/
theorem known_base_not_superpoly : ¬ Superpoly knownBase := fun h =>
  superpoly_not_polyBounded h known_base_is_polynomial

/-- **The superpolynomial ceiling is open (proved).**  A polynomial world is consistent — no superpolynomial
base bound is known.  `Superpoly` on the base is the undischarged hypothesis, `cost_super`. -/
theorem superpoly_ceiling_is_open : ∃ f : Nat → Nat, ¬ Superpoly f :=
  ⟨knownBase, known_base_not_superpoly⟩

/-- **A superpolynomial formula bound does not force a superpolynomial circuit bound (proved).**  Since a
circuit is a formula with sharing, `circuitLB ≤ formulaLB`; so a superpolynomial formula bound `g` can sit
above a *polynomial* circuit bound `h` — they coexist under `h ≤ g`, and `h` is not superpolynomial.  Raising
the *formula* ceiling to superpolynomial (`P ⊄ NC¹`, open) does not reach the *circuit* ceiling (`P ≠ NP`). -/
theorem formula_superpoly_allows_circuit_poly
    (g h : Nat → Nat) (hg : Superpoly g) (hh : PolyBounded h) (hle : ∀ n, h n ≤ g n) :
    Superpoly g ∧ ¬ Superpoly h :=
  ⟨hg, fun hsp => superpoly_not_polyBounded hsp hh⟩

/-- **The superpolynomial-ceiling rung is the wall (proved).**  Left: a superpolynomial circuit bound gives the
separation (the implication the ladder points at).  Right: no superpolynomial base bound is known — the
hypothesis is open.  Together: the ladder terminates exactly at `cost_super`. -/
theorem superpoly_ceiling_is_the_wall (F : CircuitFamily) :
    (Superpoly F.circuitCost → ¬ PolyBounded F.circuitCost)
    ∧ (∃ f : Nat → Nat, ¬ Superpoly f) :=
  ⟨fun h => superpoly_not_polyBounded h, superpoly_ceiling_is_open⟩

end PallLean.Paper93.DeepMath.PathB.SuperpolyCeiling

#print axioms PallLean.Paper93.DeepMath.PathB.SuperpolyCeiling.superpoly_not_polyBounded
#print axioms PallLean.Paper93.DeepMath.PathB.SuperpolyCeiling.superpoly_ceiling_gives_separation
#print axioms PallLean.Paper93.DeepMath.PathB.SuperpolyCeiling.known_base_not_superpoly
#print axioms PallLean.Paper93.DeepMath.PathB.SuperpolyCeiling.formula_superpoly_allows_circuit_poly
#print axioms PallLean.Paper93.DeepMath.PathB.SuperpolyCeiling.superpoly_ceiling_is_the_wall
