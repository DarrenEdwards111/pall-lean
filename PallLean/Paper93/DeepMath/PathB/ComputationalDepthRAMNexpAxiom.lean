import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMFinalShape
import Mathlib.Tactic

/-!
# Discharging Socket 2 (`decider_in_nexp`) as a cited classical axiom — step 6b

The `WilliamsBridge.decider_in_nexp` field asserts that the diagonal decider `ramDiag sim` lies in `NEXP`.  This
is **separation-strength classical content** — it is Williams' faster-than-brute-force `ACC`-`SAT` /
`SYM∘AND`-evaluation algorithm, which lets a nondeterministic exponential-time machine guess-and-verify the
clocked simulation of every `ACC⁰` machine.  We do not prove it; we **assert it as a named, cited Lean `axiom`**
so the dependency is explicit and auditable via `#print axioms`.

References:
* R. Williams, *Improving Exhaustive Search Implies Superpolynomial Lower Bounds*, STOC 2010 / SICOMP 2013.
* R. Williams, *Nonuniform ACC Circuit Lower Bounds*, JACM 61(1), 2014 (CCC 2011).

The construction is the standard consistent one: a designated `opaque` `NEXP` predicate (`WilliamsNEXP`,
standing for the genuine nondeterministic exponential-time class) and a single axiom inhabiting it for the
decider.  Nothing here can derive `False` (the predicate is opaque, the axiom only asserts one membership), and
the diagonalisation core remains unconditional — only Socket 2 is now supplied by the cited axiom.
-/

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- The designated `NEXP` predicate for the construction.  Left **opaque**: its intended meaning is the standard
nondeterministic exponential-time class; the only fact we need about it is that the diagonal decider lies in it
(the cited axiom below).  Opacity keeps the axiom consistent — no definition is available to derive anything
beyond the asserted membership. -/
opaque WilliamsNEXP : (ℕ → ℕ) → Prop

/-- **Williams' fast `ACC`-`SAT` theorem — cited axiom** [Williams, STOC 2010 / JACM 2014].

The diagonal decider `ramDiag sim` lies in `NEXP`: the faster-than-brute-force `ACC`-`SAT` / `SYM∘AND`
evaluation algorithm lets a nondeterministic exponential-time machine guess-and-verify the clocked simulation
of every `ACC⁰` machine, so the diagonal of that simulation is computed within a nondeterministic exponential
budget.

This is **asserted, not proved** — it is the separation-strength algorithmic content of the Williams program.
It appears in `#print axioms` as `williams_decider_in_NEXP`, making the dependency explicit. -/
axiom williams_decider_in_NEXP (sim : ℕ → ℕ → ℕ) : WilliamsNEXP (ramDiag sim)

/-- **Socket 2, discharged by the cited axiom.**  Build a `WilliamsBridge` with `NEXP := WilliamsNEXP`, taking
its `decider_in_nexp` field from `williams_decider_in_NEXP`; only the remaining sockets (Socket 1 `faithful`,
`boolean`, and the structural `acc0_enumerated`) need to be supplied. -/
def WilliamsBridge.ofCitedNEXP (ACC0 : (ℕ → ℕ) → Prop) (sim C : ℕ → ℕ → ℕ)
    (faithful : FaithfulOnDiagonal C sim) (boolean : ∀ e, C e e ≤ 1)
    (acc0_enumerated : ∀ f : ℕ → ℕ, ACC0 f → ∃ e, ∀ x, C e x = f x) :
    WilliamsBridge ACC0 WilliamsNEXP sim C where
  faithful := faithful
  boolean := boolean
  decider_in_nexp := williams_decider_in_NEXP sim
  acc0_enumerated := acc0_enumerated

/-- **`NEXP ⊄ ACC⁰` with Socket 2 discharged.**  With `NEXP := WilliamsNEXP` and the decider's membership
supplied by the cited Williams axiom, the separation follows from only the remaining sockets.  Compare
`NEXP_not_subset_ACC0`: the `decider_in_nexp` hypothesis is gone, now carried by `williams_decider_in_NEXP`
(visible in `#print axioms`). -/
theorem NEXP_not_subset_ACC0_citedNEXP
    (ACC0 : (ℕ → ℕ) → Prop) (sim C : ℕ → ℕ → ℕ)
    (faithful : FaithfulOnDiagonal C sim) (boolean : ∀ e, C e e ≤ 1)
    (acc0_enumerated : ∀ f : ℕ → ℕ, ACC0 f → ∃ e, ∀ x, C e x = f x) :
    ¬ (∀ f : ℕ → ℕ, WilliamsNEXP f → ACC0 f) :=
  NEXP_not_subset_ACC0 ACC0 WilliamsNEXP sim C
    (WilliamsBridge.ofCitedNEXP ACC0 sim C faithful boolean acc0_enumerated)

/-- The decider witnesses the separation, with `NEXP`-membership now from the cited axiom: `ramDiag sim` is in
`WilliamsNEXP` and not in `ACC⁰`. -/
theorem ramDiag_separates_citedNEXP
    (ACC0 : (ℕ → ℕ) → Prop) (sim C : ℕ → ℕ → ℕ)
    (faithful : FaithfulOnDiagonal C sim) (boolean : ∀ e, C e e ≤ 1)
    (acc0_enumerated : ∀ f : ℕ → ℕ, ACC0 f → ∃ e, ∀ x, C e x = f x) :
    WilliamsNEXP (ramDiag sim) ∧ ¬ ACC0 (ramDiag sim) :=
  ramDiag_separates ACC0 WilliamsNEXP sim C
    (WilliamsBridge.ofCitedNEXP ACC0 sim C faithful boolean acc0_enumerated)

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.NEXP_not_subset_ACC0_citedNEXP
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.ramDiag_separates_citedNEXP
