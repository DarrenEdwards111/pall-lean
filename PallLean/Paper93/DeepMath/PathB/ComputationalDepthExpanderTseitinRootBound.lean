import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinResolutionWidth
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Expander-Tseitin resolution width (3): the root bound `μ(⊥) ≥ t`

The last brick of the resolution-width lower bound.  An unsatisfiable subsystem
of the Tseitin constraints must be large: by expansion, a small set `S`
(`2|S| ≤ |V|`) has linearly independent constraint rows (no nonempty subset has a
vanishing F₂ combination), so the parity system is solvable for *any* charge —
`S` is satisfiable.  Hence every unsatisfiable set has `2|S| > |V|`, giving
`μ(⊥) > |V|/2 ≥ t` whenever `4t ≤ |V|`.

The linear-algebra linchpin (`mulVec_surjective_of_indep_rows`) is generic:
a matrix with linearly independent rows has surjective `mulVec` (full row rank).
-/

namespace PallLean.Paper93.DeepMath.PathB.TseitinRootBound

open PallLean.Paper93.DeepMath.PathB
open scoped BigOperators

/-- **Linear-algebra linchpin.**  Over a field, a matrix with linearly independent
rows has surjective `mulVec`: the system `M *ᵥ x = b` is solvable for every `b`. -/
theorem mulVec_surjective_of_indep_rows {m n K : Type*} [Field K]
    [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n K) (h : LinearIndependent K M.row) :
    Function.Surjective M.mulVec := by
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    show M.rank = Module.finrank K (m → K)
    rw [h.rank_matrix, Module.finrank_pi]
  intro b
  obtain ⟨a, ha⟩ := LinearMap.range_eq_top.mp htop b
  exact ⟨a, by rw [← Matrix.mulVecLin_apply]; exact ha⟩

open TseitinResolution SemanticMeasure

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- The constraint matrix of a vertex set `S`: row `v` is the constraint vector of
`v` (its edge-incidence indicator). -/
def cMat (G : TseitinGraph V Edge) (S : Finset V) : Matrix ↥S Edge (ZMod 2) :=
  fun v e => G.constraint v.1 e

/-- **Expansion ⇒ independent constraint rows.**  For `S` with `2|S| ≤ |V|`, the
constraint vectors `{constraint v : v ∈ S}` are linearly independent over `F₂`:
any nonzero F₂-combination is `combination T` for a nonempty `T ⊆ S`, which is
nonzero by expansion. -/
theorem indep_rows (G : TseitinGraph V Edge) {c : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c)
    (S : Finset V) (hsmall : 2 * S.card ≤ Fintype.card V) :
    LinearIndependent (ZMod 2) (cMat G S).row := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push_neg at hne
  obtain ⟨v₀, hv₀⟩ := hne
  set T : Finset V := (Finset.univ.filter (fun v : ↥S => g v = 1)).image Subtype.val with hT
  have hgite : ∀ (b x : ZMod 2), b * x = if b = 1 then x else 0 := by decide
  have hclaim : G.combination T = ∑ v : ↥S, g v • (cMat G S).row v := by
    funext e
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hrhs : ∀ v : ↥S, g v * (cMat G S).row v e
        = if g v = 1 then G.constraint v.1 e else 0 := by
      intro v; rw [hgite]; rfl
    rw [Finset.sum_congr rfl (fun v _ => hrhs v), ← Finset.sum_filter]
    rw [TseitinGraph.combination, hT,
      Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
  have hzero : G.combination T = 0 := by rw [hclaim, hg]
  have hTsub : T ⊆ S := by
    rw [hT]; intro w hw
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw
    exact v.2
  have hTpos : 1 ≤ T.card := by
    rw [hT, Finset.card_image_of_injective _ Subtype.val_injective]
    exact Finset.card_pos.mpr ⟨v₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) (g v₀) hv₀⟩⟩
  have hThalf : 2 * T.card ≤ Fintype.card V :=
    le_trans (by have := Finset.card_le_card hTsub; omega) hsmall
  obtain ⟨e, he⟩ := G.exists_combination_ne_zero_of_expansion hc hexp T hTpos hThalf
  exact he (by rw [hzero]; rfl)

/-- **Small constraint sets are satisfiable.**  For `2|S| ≤ |V|`, the parity
system `{parity_v = charge_v : v ∈ S}` has a solution (the rows are independent,
so `mulVec` is surjective). -/
theorem exists_sat (G : TseitinGraph V Edge) (charge : V → ZMod 2) {c : ℕ}
    (hc : 1 ≤ c) (hexp : G.HasExpansion c) (S : Finset V) (hsmall : 2 * S.card ≤ Fintype.card V) :
    ∃ a, ∀ v ∈ S, TConstr G charge v a := by
  obtain ⟨a, ha⟩ :=
    mulVec_surjective_of_indep_rows (cMat G S) (indep_rows G hc hexp S hsmall) (fun v => charge v.1)
  exact ⟨a, fun v hv => congrFun ha ⟨v, hv⟩⟩

/-- A small constraint set is not unsatisfiable (does not imply the empty clause). -/
theorem not_implies_empty_of_small (G : TseitinGraph V Edge) (charge : V → ZMod 2) {c : ℕ}
    (hc : 1 ≤ c) (hexp : G.HasExpansion c) (S : Finset V) (hsmall : 2 * S.card ≤ Fintype.card V) :
    ¬ SemanticMeasure.Implies TSat (TConstr G charge) S (∅ : ResolutionClause (TLit Edge)) := by
  obtain ⟨a, ha⟩ := exists_sat G charge hc hexp S hsmall
  intro himp
  obtain ⟨l, hl, _⟩ := himp a (fun v hv => ha v hv)
  simp at hl

/-- **Root bound (3): `μ(⊥) ≥ t`.**  Every unsatisfiable constraint set is large
(`2|S| > |V|`), so the measure of the empty clause exceeds `|V|/2 ≥ t` whenever
`4t ≤ |V|`.  This is the last input to the resolution-width lower bound. -/
theorem root_bound (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (hcard : 4 * t ≤ Fintype.card V) :
    t ≤ SemanticMeasure.measure TSat (TConstr G charge) (∅ : ResolutionClause (TLit Edge)) := by
  obtain ⟨S, hSimp, hScard⟩ :=
    SemanticMeasure.exists_implies_measure TSat (TConstr G charge) hunsat ∅
  by_contra hlt
  push_neg at hlt
  exact not_implies_empty_of_small G charge hc hexp S (by rw [hScard]; omega) hSimp

/-- **Unconditional expander-Tseitin resolution-width lower bound.**  No carried
hypothesis: on an expander (`c ≥ 1`), for an odd/globally-unsatisfiable charge and
`4t ≤ |V|`, every resolution refutation of the Tseitin axioms has width `≥ c·t`. -/
theorem resolution_width_lower_bound (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (Axiom : ResolutionClause (TLit Edge) → Prop)
    (haxiom : ∀ C, Axiom C → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht1 : 1 ≤ t) (hcard : 4 * t ≤ Fintype.card V)
    (Der : ResolutionDerivation tcompl Axiom (∅ : ResolutionClause (TLit Edge))) :
    c * t ≤ ResolutionDerivation.proofWidth Der :=
  TseitinResolution.resolution_width_lower_bound G charge hunsat Axiom haxiom hexp ht1 hcard
    (root_bound G charge hunsat hc hexp hcard) Der

end PallLean.Paper93.DeepMath.PathB.TseitinRootBound

#print axioms PallLean.Paper93.DeepMath.PathB.TseitinRootBound.mulVec_surjective_of_indep_rows
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinRootBound.root_bound
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinRootBound.resolution_width_lower_bound
