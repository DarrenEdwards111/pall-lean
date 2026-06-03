import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTRefutation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivationTseitin

/-!
# Composing the chain with the expander-Tseitin width lower bound

The gate-2 chain produces, from a refuting decision tree of depth `D`, an `LDeriv` resolution
refutation **all of whose clauses have width `≤ D`** (`DTRef.dtRef_to_ldderiv`).  The
expander-Tseitin **width lower bound** (`LDeriv.ldn_width_lower_bound`) says every refutation of the
Tseitin axioms contains a clause of width `≥ c·t`.  Composing the two is the lower-bound contradiction
in its cleanest form: a refuting tree over the Tseitin axioms cannot be shallow.

* `depth_ge_expander_width` — any `LDeriv` refutation of the Tseitin axioms whose clauses all have
  width `≤ Dwidth` forces `c·t ≤ Dwidth`.  (Direct: the wide clause from `ldn_width_lower_bound` is
  one of those clauses.)
* `dtRef_refuting_depth_ge` — **the capstone**: a clause-labelled refutation tree (`DTRef`) over the
  expander-Tseitin axioms has `c·t ≤ T.depth`.  Its width-`≤ depth` `LDeriv` (from
  `dtRef_to_ldderiv`) meets the width lower bound.

**The parameter regime.**  `c` is the expansion constant and `t` the BSW window; `c·t` is the width
lower bound the refutation must meet, so any refuting tree has depth `≥ c·t`.  Combined with the
collapse (`depth3_collapse_*`: a good restriction makes the canonical tree *shallow*), the regime is
the squeeze — if the switching parameters force depth `< c·t` for a good restriction, the circuit
cannot have refuted the axioms with that depth, i.e. it must have been large.  The concrete numeric
choice of `(c, t)` against the switching parameters (the binomial-ratio regime) is the remaining
analytic input to the application; the *qualitative* squeeze — shallow-by-collapse vs.
deep-by-width — is proved here.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]
  [Nonempty Edge]

/-- **A narrow refutation meets the width lower bound.**  Any `LDeriv` refutation of the
expander-Tseitin axioms whose clauses all have width `≤ Dwidth` forces `c·t ≤ Dwidth`. -/
theorem depth_ge_expander_width (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (Axiom : ResolutionClause (TLit Edge) → Prop)
    (haxiom : ∀ C, Axiom C → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht2 : 2 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V)
    {L : List (ResolutionClause (TLit Edge))} (hLD : LDeriv tcompl Axiom L)
    (hmt : (∅ : ResolutionClause (TLit Edge)) ∈ L)
    {Dwidth : ℕ} (hwidth : ∀ C ∈ L, ResolutionClause.width C ≤ Dwidth) :
    c * t ≤ Dwidth := by
  obtain ⟨C, hCL, hC⟩ :=
    LDeriv.ldn_width_lower_bound G charge hunsat Axiom haxiom hc hexp ht2 hcard hLD hmt
  exact le_trans hC (hwidth C hCL)

/-- **The capstone: a refuting decision tree over expander Tseitin is deep.**  A clause-labelled
refutation tree `T` over the Tseitin axioms `Ax` has `c·t ≤ T.depth`.  Its `LDeriv` refutation
(`dtRef_to_ldderiv`) has all clause widths `≤ T.depth`, so it meets the width lower bound. -/
theorem dtRef_refuting_depth_ge (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (Ax : List (ResolutionClause (TLit Edge)))
    (hAxiom : ∀ C, C ∈ Ax → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht2 : 2 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V)
    (T : DTRef (TLit Edge)) (hlab : DTRef.Labeled (· ∈ Ax) T)
    (href : DTRef.Refutes tcompl T (∅ : ResolutionClause (TLit Edge))) :
    c * t ≤ T.depth := by
  obtain ⟨hLD, hmt, _, hw⟩ := DTRef.dtRef_to_ldderiv T hlab href
  exact depth_ge_expander_width G charge hunsat (· ∈ Ax) hAxiom hc hexp ht2 hcard hLD hmt hw

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.depth_ge_expander_width
#print axioms PallLean.Paper93.DeepMath.PathB.dtRef_refuting_depth_ge
