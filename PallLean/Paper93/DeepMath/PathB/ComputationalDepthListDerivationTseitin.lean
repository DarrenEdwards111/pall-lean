import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivationWidth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivationSizeWidthFinal
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinRootBound

/-!
# Size–width tradeoff for expander Tseitin (list model)

Coupling the BSW upper recursion (`size_width_recursion`) with the width **lower**
bound in the list model (`ldn_width_lower_bound`, the medium-clause argument
instantiated at the semantic measure) gives the size–width lower bound for
expander Tseitin:

If the axioms have a refutation `L` whose fat-clause count satisfies the BSW
invariant `(n-d)^b · #fat < n^b`, then `c·t ≤ w₀ + d + b` — equivalently, no
refutation can have a small fat count while the width budget `w₀ + d + b` stays
below the expander lower bound `c·t`.  The exponential size lower bound is the
arithmetic corollary (`d ≈ √(n ln S)`).
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace LDeriv

open PallLean.Paper93.DeepMath.PathB.TseitinResolution
open scoped BigOperators

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]
  [Nonempty Edge]

/-- **Width lower bound in the list model.**  Any list-derivation refutation of
Tseitin axioms (each implied by a single vertex constraint) on an expander
contains a clause of width `≥ c·t`. -/
theorem ldn_width_lower_bound (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (Axiom : ResolutionClause (TLit Edge) → Prop)
    (haxiom : ∀ C, Axiom C → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht2 : 2 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V)
    {L : List (ResolutionClause (TLit Edge))} (D : LDeriv tcompl Axiom L)
    (hmt : (∅ : ResolutionClause (TLit Edge)) ∈ L) :
    ∃ C ∈ L, c * t ≤ ResolutionClause.width C := by
  refine D.exists_wide_clause (SemanticMeasure.measure TSat (TConstr G charge)) (a := 1)
    (t := t) (W := c * t)
    (fun {C E} p => SemanticMeasure.measure_resolvent_le TSat (TConstr G charge) tcompl
      tsat_tcompl hunsat C E p)
    (fun {C C'} h => SemanticMeasure.measure_mono TSat (TConstr G charge) hunsat h)
    (fun {C} hC => ?_)
    (by omega)
    (fun {C} hlo hhi => width_ge_of_medium G charge hunsat hexp (by omega) hcard hlo hhi)
    ⟨∅, hmt, ?_⟩
  · obtain ⟨v, hv⟩ := haxiom C hC
    calc SemanticMeasure.measure TSat (TConstr G charge) C
        ≤ ({v} : Finset V).card :=
          SemanticMeasure.measure_le_of_implies TSat (TConstr G charge) hv
      _ = 1 := Finset.card_singleton v
  · exact TseitinRootBound.root_bound G charge hunsat hc hexp hcard

/-- **Size–width lower bound for expander Tseitin (list model).**  A refutation `L`
of Tseitin axioms `Ax` (each Tseitin-implied, widths `≤ w₀`) cannot simultaneously
have a fat count meeting the BSW invariant `(n-d)^b · #fat < n^b` and a width
budget `w₀ + d + b` below the expander lower bound `c·t`. -/
theorem tseitin_size_width (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (Ax : List (ResolutionClause (TLit Edge)))
    (hAxiom : ∀ C, C ∈ Ax → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht2 : 2 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V) {w₀ : ℕ} (hw0 : ∀ C ∈ Ax, ResolutionClause.width C ≤ w₀)
    {d b : ℕ} (hd : 0 < d) {L : List (ResolutionClause (TLit Edge))}
    (hLD : LDeriv tcompl (· ∈ Ax) L) (hmt : (∅ : ResolutionClause (TLit Edge)) ∈ L)
    (hsize : (Fintype.card (TLit Edge) - d) ^ b * (fatSet d L).card
        < Fintype.card (TLit Edge) ^ b)
    (hsmall : w₀ + d + b < c * t) :
    False := by
  obtain ⟨L', hLD', hmt', hw'⟩ :=
    size_width_recursion d hd (varsOf L).card Ax L b w₀ (le_refl _) hLD hmt hw0 hsize
  obtain ⟨C, hC, hwide⟩ :=
    ldn_width_lower_bound G charge hunsat (· ∈ Ax) hAxiom hc hexp ht2 hcard hLD' hmt'
  have := hw' C hC
  omega

end LDeriv

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.ldn_width_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.tseitin_size_width
