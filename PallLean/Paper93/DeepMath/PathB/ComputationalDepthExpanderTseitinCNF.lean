import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinExpSize
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinUnsat

/-!
# The canonical Tseitin CNF and its exponential size lower bound (concretization)

We replace the abstract axiom predicate `Axiom`/`haxiom` of the resolution size
lower bound by the **explicit Tseitin CNF**.  For a vertex `v` with incident edge
set `incident v`, the parity constraint `⊕_{e ∋ v} x_e = charge_v` is encoded by one
clause per *wrong-parity pattern* `α` on the incident edges:

  `tseitinClause v α = { (e, α_e + 1) : e ∈ incident v }`,

falsified exactly by the assignment agreeing with `α` on `incident v`.  Including
`tseitinClause v α` for every `α` with `parity_v(α) ≠ charge_v` gives a CNF whose
clauses are each implied by the single constraint at `v` (`tseitinCNF_implies`) and
have width `= deg(v)` (`tseitinCNF_width_le`).

Combined with the concrete unsatisfiability (`tseitin_unsat`, odd charge) and the
capstone `resolution_exp_size`, this yields a lower bound on the resolution
refutation size of an **explicit CNF family** (`tseitinCNF_exp_size`): no abstract
axiom hypotheses remain, only the graph, its expansion, the odd charge, and the
degree bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.TseitinResolution

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.SemanticMeasure
open scoped BigOperators

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- The edges incident to a vertex. -/
def incident (G : TseitinGraph V Edge) (v : V) : Finset Edge :=
  Finset.univ.filter (fun e => v ∈ G.endpoints e)

/-- The canonical clause ruling out the wrong-parity pattern `α` at vertex `v`:
the literals `(e, α_e + 1)` over edges incident to `v`.  It is falsified exactly by
assignments agreeing with `α` on `incident v`. -/
def tseitinClause (G : TseitinGraph V Edge) (v : V) (α : Edge → ZMod 2) :
    ResolutionClause (TLit Edge) :=
  (incident G v).image (fun e => (e, α e + 1))

/-- The canonical Tseitin CNF: one clause per vertex and wrong-parity pattern. -/
def TseitinCNF (G : TseitinGraph V Edge) (charge : V → ZMod 2) :
    ResolutionClause (TLit Edge) → Prop :=
  fun C => ∃ v α, parity G α v ≠ charge v ∧ C = tseitinClause G v α

/-- **Each canonical clause is implied by its vertex constraint.**  If `α` has the
wrong parity at `v`, then any assignment satisfying the constraint `parity_v = charge_v`
must differ from `α` on some incident edge — i.e. it satisfies `tseitinClause v α`. -/
theorem implies_tseitinClause (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (v : V) (α : Edge → ZMod 2) (hwrong : parity G α v ≠ charge v) :
    Implies TSat (TConstr G charge) {v} (tseitinClause G v α) := by
  intro a ha
  have hcv : parity G a v = charge v := ha v (Finset.mem_singleton_self v)
  by_contra hns
  have hae : ∀ e, v ∈ G.endpoints e → a e = α e := by
    intro e he
    by_contra hne
    have hflip : a e = α e + 1 := by
      rcases (by decide : ∀ x y : ZMod 2, x = y ∨ x = y + 1) (a e) (α e) with h | h
      · exact absurd h hne
      · exact h
    exact hns ⟨(e, α e + 1),
      Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩, rfl⟩, hflip⟩
  have hpeq : parity G a v = parity G α v := by
    unfold parity
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases he : v ∈ G.endpoints e
    · rw [hae e he]
    · simp [TseitinGraph.constraint, he]
  rw [hcv] at hpeq
  exact hwrong hpeq.symm

/-- The first coordinate makes `e ↦ (e, α e + 1)` injective. -/
theorem tseitinClause_width (G : TseitinGraph V Edge) (v : V) (α : Edge → ZMod 2) :
    (tseitinClause G v α).width = (incident G v).card := by
  unfold tseitinClause ResolutionClause.width
  exact Finset.card_image_of_injective _ (fun e₁ e₂ h => congrArg Prod.fst h)

/-- **`haxiom` for the canonical CNF.**  Every clause is implied by a single
constraint. -/
theorem tseitinCNF_implies (G : TseitinGraph V Edge) (charge : V → ZMod 2) :
    ∀ C, TseitinCNF G charge C → ∃ v, Implies TSat (TConstr G charge) {v} C := by
  rintro C ⟨v, α, hwrong, rfl⟩
  exact ⟨v, implies_tseitinClause G charge v α hwrong⟩

/-- **`hw₀` for the canonical CNF.**  Every clause has width `≤ w₀`, where `w₀`
bounds the degrees. -/
theorem tseitinCNF_width_le (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    {w₀ : ℕ} (hdeg : ∀ v, (incident G v).card ≤ w₀) :
    ∀ C, TseitinCNF G charge C → C.width ≤ w₀ := by
  rintro C ⟨v, α, _, rfl⟩
  rw [tseitinClause_width]
  exact hdeg v

/-- **Exponential resolution size for the explicit Tseitin CNF.**  On a graph with
expansion `c`, odd total charge, degrees `≤ w₀`, and `w₀ < c·t` with `4t ≤ |V|`,
every resolution refutation of the canonical Tseitin CNF has size `> 2^{c·t-w₀-1}`.
No abstract axiom hypotheses remain. -/
theorem tseitinCNF_exp_size (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hodd : ∑ v : V, charge v = 1) {c t w₀ : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c)
    (ht1 : 1 ≤ t) (hcard : 4 * t ≤ Fintype.card V) (hdeg : ∀ v, (incident G v).card ≤ w₀)
    (hgap : w₀ < c * t)
    (Der : ResolutionDerivation tcompl (TseitinCNF G charge) (∅ : ResolutionClause (TLit Edge))) :
    2 ^ (c * t - w₀ - 1) < ResolutionDerivation.size Der :=
  TseitinRootBound.resolution_exp_size G charge (tseitin_unsat G charge hodd)
    (TseitinCNF G charge) (tseitinCNF_implies G charge) hc hexp ht1 hcard
    (tseitinCNF_width_le G charge hdeg) hgap Der

end PallLean.Paper93.DeepMath.PathB.TseitinResolution

#print axioms PallLean.Paper93.DeepMath.PathB.TseitinResolution.implies_tseitinClause
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinResolution.tseitinCNF_exp_size
