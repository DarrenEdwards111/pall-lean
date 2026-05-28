import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionWidthSize

/-!
# Medium-clause descent: the combinatorial skeleton of the BSW connector

**STATUS: A REAL, COMPLETABLE PIECE OF THE CONNECTOR — not the whole connector.**

The Ben-Sasson–Wigderson width lower bound runs through a complexity measure `μ`
on clauses (e.g. "minimum number of axioms semantically implying the clause").
Its decisive combinatorial step is: along any refutation, `μ` climbs from small
(axioms) to large (the empty clause), and *subadditivity under resolution forces
a clause of medium `μ`*.  That medium clause is then shown to be wide via
expansion (the link to the expander kernel).

This file proves that decisive descent step, abstractly over any subadditive
measure:

  `exists_medium_measure` — if `μ` is subadditive on resolvents, axioms have
  `μ ≤ a`, and the root has `μ ≥ t` with `a < 2t`, then the derivation contains a
  clause `C'` with `t ≤ μ C' < 2t`.

What is **not** here (the genuine hard core, deliberately not faked):
* the Tseitin-specific measure `μ` and the proof that `μ(⊥) = n` (global parity);
* the expansion → width link (a medium-`μ` clause is wide), i.e. *supplying*
  `ResolutionWidthLowerBound` by connecting this to the expander kernel;
* the linear→exponential size amplification (random restrictions);
* tree-like → DAG-like.

So this is one real rung of the connector — the descent skeleton — proved
honestly, with the crux (the measure's Tseitin properties + the expansion link)
left as named open work.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace ResolutionDerivation

variable {Lit : Type*} [DecidableEq Lit]
variable {compl : Lit → Lit}
variable {Axiom : ResolutionClause Lit → Prop}

/-- **BSW medium-clause descent (proved).**  For any measure `μ` that is
subadditive under resolution, with axiom measures bounded by `a`, a derivation
whose root has measure at least `t` (where `a < 2t`) contains a clause of
*medium* measure: `t ≤ μ C' < 2t`.  This is the step that, with the right `μ`,
forces a wide clause to appear in every refutation. -/
theorem exists_medium_measure
    {a t : Nat}
    (μ : ResolutionClause Lit → Nat)
    (hsub : ∀ {C D : ResolutionClause Lit} (p : Lit),
        μ (ResolutionClause.resolvent compl C D p) ≤ μ C + μ D)
    (hax : ∀ {C : ResolutionClause Lit}, Axiom C → μ C ≤ a)
    (ht : a < 2 * t)
    {Target : ResolutionClause Lit}
    (Der : ResolutionDerivation compl Axiom Target) :
    t ≤ μ Target →
      ∃ C' : ResolutionClause Lit,
        t ≤ μ C' ∧ μ C' < 2 * t ∧
          Nonempty (ResolutionDerivation compl Axiom C') := by
  induction Der with
  | ax h =>
      intro hroot
      exact ⟨_, hroot, lt_of_le_of_lt (hax h) ht, ⟨ResolutionDerivation.ax h⟩⟩
  | @resolve C Dp L R p ihL ihR =>
      intro hroot
      by_cases hlt : μ (ResolutionClause.resolvent compl C Dp p) < 2 * t
      · exact ⟨_, hroot, hlt, ⟨ResolutionDerivation.resolve L R p⟩⟩
      · push_neg at hlt
        have hsum : 2 * t ≤ μ C + μ Dp := le_trans hlt (hsub p)
        rcases Nat.lt_or_ge (μ C) t with hC | hC
        · exact ihR (by omega)
        · exact ihL hC

/-- Convenience restatement: with axioms of measure `≤ a` and the empty/target
clause of measure `≥ 2 * a + 1` (so `a < 2 t` holds for `t = a + 1`), every
refutation contains a clause of measure in `[a+1, 2a+1]`.  This is the shape used
downstream: the medium clause sits strictly above the axiom level. -/
theorem exists_medium_measure_above_axioms
    {a : Nat}
    (μ : ResolutionClause Lit → Nat)
    (hsub : ∀ {C D : ResolutionClause Lit} (p : Lit),
        μ (ResolutionClause.resolvent compl C D p) ≤ μ C + μ D)
    (hax : ∀ {C : ResolutionClause Lit}, Axiom C → μ C ≤ a)
    {Target : ResolutionClause Lit}
    (Der : ResolutionDerivation compl Axiom Target)
    (hroot : a + 1 ≤ μ Target) :
    ∃ C' : ResolutionClause Lit,
      a + 1 ≤ μ C' ∧ μ C' < 2 * (a + 1) ∧
        Nonempty (ResolutionDerivation compl Axiom C') :=
  exists_medium_measure μ hsub hax (by omega) Der hroot

end ResolutionDerivation

/-! ## Kernel-only axiom trace -/

#print axioms ResolutionDerivation.exists_medium_measure
#print axioms ResolutionDerivation.exists_medium_measure_above_axioms

end PallLean.Paper93.DeepMath.PathB
