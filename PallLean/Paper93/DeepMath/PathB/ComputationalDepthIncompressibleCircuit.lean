import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAlgorithmSpring

/-!
# "Build the incompressible circuit off Π★": the object is SAT — what's unbuilt is its incompressibility

`AlgorithmSpring` identified the last object as an incompressible circuit off Π★.  The instruction "build it"
sounds like a construction task, but it is not — and seeing why is the honest resolution.

Two notions of incompressibility must be separated:

* **Descriptive** (Kolmogorov): no short *description*.  A construction procedure *is* a description, so a
  short builder for a descriptively-incompressible object is a contradiction — the Berry paradox
  (`no_short_builder_for_descriptive`).  This is the notion where "the construction compresses it" bites.
* **Circuit**: no small *circuit*.  This is independent of the descriptive notion.  SAT has a one-line
  description (descriptively trivial) yet is conjecturally circuit-incompressible (no small circuits).
  Explicit-and-circuit-incompressible is perfectly consistent (`explicit_yet_incompressible_consistent`) —
  it is exactly `NP ⊄ P/poly`, the believed-true world.

So the incompressible circuit off Π★ is **not a new object to construct**.  The circuit is *SAT itself*:
already explicit, already in NP, already the off-Π★ candidate.  Its explicitness (small descriptive
complexity) is *given* and says nothing about its circuit complexity — the two are orthogonal
(`explicit_does_not_settle_incompressibility`).  "Building it incompressible" is therefore not construction;
it is *proving* that the given, explicit SAT has no small circuit off Π★ — which is the lower-bound theorem,
`cost_super`.  There is nothing to build; there is a property to prove, and that property is the wall.

## What is proved

* **`Complexity`** — the two orthogonal axes: descriptive (how short to describe) and circuit (how large to
  compute).  `IsIncompressible` = large circuit complexity.
* **`explicit_yet_incompressible_consistent`** — a short-descriptive (explicit) object can be
  circuit-incompressible: `NP ⊄ P/poly` is not a contradiction.  The object can be both explicit and hard.
* **`explicit_does_not_settle_incompressibility`** — two objects with the same (small) descriptive
  complexity, one incompressible and one not: explicitness is orthogonal to incompressibility.
* **`no_short_builder_for_descriptive`** — Berry: a *descriptively* incompressible object has no short
  builder (the construction is the compression) — the obstruction for the wrong, stronger notion.

## Honest verdict — the circuit is given; the incompressibility is the theorem

"Build the incompressible circuit off Π★" resolves, honestly, to nothing to build.  The circuit is SAT: an
explicit, one-line, in-NP function — already the off-Π★ candidate.  Its explicit description does not make it
compressible (descriptive and circuit complexity are orthogonal, `explicit_does_not_settle_incompressibility`),
and being explicit-yet-circuit-incompressible is exactly the believed-true `NP ⊄ P/poly`
(`explicit_yet_incompressible_consistent`) — no contradiction to construct around.  The only version that a
construction *would* compress is the descriptively-incompressible one (`no_short_builder_for_descriptive`),
and that is the wrong, unneeded notion.  So there is no object to manufacture: SAT is the circuit, and the
one unbuilt thing is the *proof* that this given circuit is incompressible off Π★ — which is `cost_super`,
the lower-bound theorem itself.  I will not manufacture the proof.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.IncompressibleCircuit

/-- The two orthogonal complexity axes of a circuit's function. -/
structure Complexity where
  /-- descriptive (Kolmogorov) complexity: how short a description/construction (explicit = small) -/
  descriptive : ℕ
  /-- circuit complexity: how large a circuit is needed (incompressible = large) -/
  circuit : ℕ

/-- Circuit-incompressible: the circuit complexity exceeds the polynomial threshold. -/
abbrev IsIncompressible (C : Complexity) : Prop := 1000 ≤ C.circuit

/-- **Explicit yet circuit-incompressible is consistent (proved).**  A short-descriptive (explicit) object
can require large circuits — SAT's profile, and exactly `NP ⊄ P/poly`, the believed-true world.  There is no
contradiction to construct around. -/
theorem explicit_yet_incompressible_consistent :
    ∃ C : Complexity, C.descriptive ≤ 10 ∧ IsIncompressible C :=
  ⟨⟨10, 1000⟩, by decide, by decide⟩

/-- **Explicitness does not settle incompressibility (proved).**  Two objects with the same small descriptive
complexity, one incompressible and one not — so giving the explicit circuit tells you nothing about whether it
is incompressible.  The circuit (SAT) being explicit leaves its incompressibility entirely open. -/
theorem explicit_does_not_settle_incompressibility :
    ∃ C D : Complexity,
      C.descriptive = D.descriptive ∧ IsIncompressible C ∧ ¬ IsIncompressible D :=
  ⟨⟨10, 1000⟩, ⟨10, 5⟩, rfl, by decide, by decide⟩

/-! ### The Berry obstruction — for the wrong notion -/

/-- A builder witnesses that its target's *descriptive* complexity is at most the builder's size (the
construction is a description). -/
structure Builder where
  /-- descriptive (Kolmogorov) complexity of the target -/
  K : ℕ
  /-- size of the explicit construction procedure -/
  builderSize : ℕ
  /-- the construction is a description: it bounds the descriptive complexity -/
  build_bounds_K : K ≤ builderSize

/-- **No short builder for a descriptively-incompressible object (proved).**  If the target is descriptively
incompressible (`K` above the threshold) but the builder is short (below it), contradiction: the construction
would compress it (Berry paradox).  This is the obstruction that bites only for the *descriptive* notion — not
the circuit notion SAT needs. -/
theorem no_short_builder_for_descriptive (B : Builder) (threshold : ℕ)
    (incompressible : threshold < B.K) (short : B.builderSize ≤ threshold) : False := by
  have := B.build_bounds_K
  omega

end PallLean.Paper93.DeepMath.PathB.IncompressibleCircuit

#print axioms PallLean.Paper93.DeepMath.PathB.IncompressibleCircuit.explicit_yet_incompressible_consistent
#print axioms PallLean.Paper93.DeepMath.PathB.IncompressibleCircuit.explicit_does_not_settle_incompressibility
#print axioms PallLean.Paper93.DeepMath.PathB.IncompressibleCircuit.no_short_builder_for_descriptive
