import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCircuitUpgrade

/-!
# N-Frame: the exact conditional `P vs NP` theorem of the boundary route

The circuit upgrade aimed the boundary model at `P/poly`.  This file states and proves the **exact conditional theorem**
the route now supports — no jump claimed, every ingredient named:

  `PolyCBudget F` / `SuperPolyCBudget F` — a function family has polynomially bounded / super-polynomial circuit energy.
  `superPoly_iff_not_poly` — **PROVED**: super-polynomial = not polynomially bounded (the two readings agree exactly).
  `no_polytime_decider_of_superpoly` — **PROVED, the conditional bridge**: *if* every polynomial-time decider of the
        family yields polynomial circuit energy (`simulation` — the classical `P ⊆ P/poly` tabling, a **named
        hypothesis**), and the family has super-polynomial circuit energy, *then* no polynomial-time decider exists.
        Instantiated at `F = SAT`: **superpoly `cbudget` for SAT ⇒ P ≠ NP**.
  `polyCBudget_of_polytime_decider` — **PROVED, the converse direction**: a polynomial-time decider forces polynomial
        circuit energy (so `P = NP ⇒ SAT has polynomial cbudget`, under the same named simulation).
  `NFrameCircuitLowerBoundTarget` — the remaining target, marked in one definition: `SuperPolyCBudget SAT`, i.e.
        `∀ k, ∃ n, nᵏ + k < cbudget (SAT n)` — the open circuit lower-bound problem, and nothing else.

## Honest scope — what is proved, what is named, what is open

* **Proved here**: the bridge and its converse, over an abstract machine type `M` with abstract `PolyTime`/`decidesSAT`
  predicates and an arbitrary target family `F` — the route's logic is complete and hypothesis-explicit.
* **Named, not proved**: `simulation` — that a polynomial-time decider of `F` yields polynomially bounded `cbudget (F n)`.
  This is the classical `P ⊆ P/poly` (Cook–Levin tableau simulation): true, standard, and *formalizable in principle*
  against a concrete machine model (cf. the repo's RAM-machine bricks), but a substantial separate project.  It is a
  hypothesis of the bridge, in the repo's named-socket discipline — never silently assumed.
* **Open (the target)**: `SuperPolyCBudget SAT`.  By the identity and upgrade files this is exactly the super-polynomial
  circuit lower-bound problem.  Nothing in this repo proves it; the best known explicit bounds are linear.

So the N-Frame boundary route is now maximally sharp: a proved conditional `P ≠ NP` theorem whose sole missing premise is
the single, precisely-stated open target.  Nothing here is an unconditional `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The family `F` has **polynomially bounded circuit energy**: some exponent `k` bounds `cbudget (F n)` by `nᵏ + k`. -/
def PolyCBudget (F : ∀ n : ℕ, (Fin n → Bool) → Bool) : Prop :=
  ∃ k, ∀ n, cbudget (F n) ≤ n ^ k + k

/-- The family `F` has **super-polynomial circuit energy**: every polynomial bound is exceeded somewhere. -/
def SuperPolyCBudget (F : ∀ n : ℕ, (Fin n → Bool) → Bool) : Prop :=
  ∀ k, ∃ n, n ^ k + k < cbudget (F n)

/-- **The two readings agree exactly (proved)**: super-polynomial circuit energy is precisely the failure of every
polynomial bound. -/
theorem superPoly_iff_not_poly (F : ∀ n : ℕ, (Fin n → Bool) → Bool) :
    SuperPolyCBudget F ↔ ¬ PolyCBudget F := by
  unfold SuperPolyCBudget PolyCBudget
  push_neg
  rfl

/-- **The conditional bridge (proved).**  Over an abstract machine type `M`: if every polynomial-time decider of the
family yields polynomially bounded circuit energy (`simulation` — the classical `P ⊆ P/poly` tabling, a named
hypothesis), and the family's circuit energy is super-polynomial, then no polynomial-time decider exists.  Instantiated
at `F = SAT`: **super-polynomial `cbudget` for SAT ⇒ P ≠ NP**. -/
theorem no_polytime_decider_of_superpoly {M : Type*}
    (PolyTime decides : M → Prop) (F : ∀ n : ℕ, (Fin n → Bool) → Bool)
    (simulation : ∀ m, PolyTime m → decides m → PolyCBudget F)
    (hard : SuperPolyCBudget F) :
    ¬ ∃ m, PolyTime m ∧ decides m := by
  rintro ⟨m, hpt, hdec⟩
  exact (superPoly_iff_not_poly F).mp hard (simulation m hpt hdec)

/-- **The converse direction (proved).**  A polynomial-time decider forces polynomial circuit energy — so under the same
named simulation, `P = NP ⇒ SAT has polynomial cbudget`. -/
theorem polyCBudget_of_polytime_decider {M : Type*}
    (PolyTime decides : M → Prop) (F : ∀ n : ℕ, (Fin n → Bool) → Bool)
    (simulation : ∀ m, PolyTime m → decides m → PolyCBudget F)
    (hdec : ∃ m, PolyTime m ∧ decides m) :
    PolyCBudget F := by
  obtain ⟨m, hpt, hd⟩ := hdec
  exact simulation m hpt hd

/-- **THE REMAINING TARGET, marked.**  For the SAT family, this single statement — `∀ k, ∃ n, nᵏ + k < cbudget (SAT n)` —
is the missing premise of the conditional bridge: the open super-polynomial circuit lower-bound problem.  Everything else
in the route is proved. -/
def NFrameCircuitLowerBoundTarget (F : ∀ n : ℕ, (Fin n → Bool) → Bool) : Prop :=
  SuperPolyCBudget F

/-- The target is literally the bridge's missing premise (proved, definitional). -/
theorem target_closes_bridge {M : Type*}
    (PolyTime decides : M → Prop) (F : ∀ n : ℕ, (Fin n → Bool) → Bool)
    (simulation : ∀ m, PolyTime m → decides m → PolyCBudget F)
    (target : NFrameCircuitLowerBoundTarget F) :
    ¬ ∃ m, PolyTime m ∧ decides m :=
  no_polytime_decider_of_superpoly PolyTime decides F simulation target

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.superPoly_iff_not_poly
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.no_polytime_decider_of_superpoly
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.polyCBudget_of_polytime_decider
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.target_closes_bridge
