import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinSizeWidth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinRootBound

/-!
# Exponential resolution size lower bound for expander-Tseitin (capstone)

Combining the tree-like Ben-Sasson–Wigderson size–width bound
(`tree_width_le`: `proofWidth ≤ w₀ + ⌈log₂ size⌉`) with the unconditional
resolution-width lower bound (`proofWidth ≥ c·t`) yields the **exponential size
lower bound**:

  `c·t ≤ w₀ + ⌈log₂ size⌉`,  equivalently  `size > 2^{c·t - w₀ - 1}`.

For Tseitin on a good expander the width bound is `c·t = Ω(n)` while initial
clauses have bounded width `w₀`, so every (tree-like, weakening-)resolution
refutation has size `2^{Ω(n)}` — the BSW capstone.
-/

namespace PallLean.Paper93.DeepMath.PathB.TseitinRootBound

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TseitinResolution
open PallLean.Paper93.DeepMath.PathB.TseitinRestriction

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- **Weakening-resolution width lower bound** for expander-Tseitin: the same
`c·t` bound as for ordinary resolution, now for the weakening system (via the
weakening-augmented BSW descent `WDerivation.proofWidth_ge_of_medium_wide`, whose
extra input is measure monotonicity `measure_mono`). -/
theorem wderivation_width_lower_bound (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (Axiom : ResolutionClause (TLit Edge) → Prop)
    (haxiom : ∀ C, Axiom C → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht1 : 1 ≤ t) (hcard : 4 * t ≤ Fintype.card V)
    (W : WDerivation tcompl Axiom (∅ : ResolutionClause (TLit Edge))) :
    c * t ≤ WDerivation.proofWidth W := by
  refine WDerivation.proofWidth_ge_of_medium_wide
    (μ := SemanticMeasure.measure TSat (TConstr G charge)) (a := 1) (t := t) (W := c * t)
    (fun {C D} p => SemanticMeasure.measure_resolvent_le TSat (TConstr G charge) tcompl
      tsat_tcompl hunsat C D p)
    (fun {C C'} hsub => SemanticMeasure.measure_mono TSat (TConstr G charge) hunsat hsub)
    (fun {C} hC => ?_)
    (by omega)
    (fun {C} hlo hhi => width_ge_of_medium G charge hunsat hexp ht1 hcard hlo hhi)
    W (root_bound G charge hunsat hc hexp hcard)
  obtain ⟨v, hv⟩ := haxiom C hC
  calc SemanticMeasure.measure TSat (TConstr G charge) C
      ≤ ({v} : Finset V).card :=
        SemanticMeasure.measure_le_of_implies TSat (TConstr G charge) hv
    _ = 1 := Finset.card_singleton v

/-- **Exponential resolution size lower bound (size–width form).**  Every
(weakening-)resolution refutation `Der` of the Tseitin axioms (initial width `≤ w₀`)
on an expander satisfies `c·t ≤ w₀ + ⌈log₂ size⌉`. -/
theorem resolution_size_width (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (Axiom : ResolutionClause (TLit Edge) → Prop)
    (haxiom : ∀ C, Axiom C → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C)
    {c t w₀ : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht1 : 1 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V) (hw₀ : ∀ C, Axiom C → C.width ≤ w₀)
    (Der : ResolutionDerivation tcompl Axiom (∅ : ResolutionClause (TLit Edge))) :
    c * t ≤ w₀ + Nat.clog 2 (ResolutionDerivation.size Der) := by
  obtain ⟨W', hW'⟩ := tree_width_le hw₀ (WDerivation.ofResolution Der)
  have hwlb := wderivation_width_lower_bound G charge hunsat Axiom haxiom hc hexp ht1 hcard W'
  rw [WDerivation.ofResolution_size] at hW'
  omega

/-- **Exponential resolution size lower bound (explicit form).**  When the width
bound exceeds the initial width (`w₀ < c·t`), the refutation size is exponential:
`2^{c·t - w₀ - 1} < size`. -/
theorem resolution_exp_size (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (Axiom : ResolutionClause (TLit Edge) → Prop)
    (haxiom : ∀ C, Axiom C → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C)
    {c t w₀ : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht1 : 1 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V) (hw₀ : ∀ C, Axiom C → C.width ≤ w₀)
    (hgap : w₀ < c * t)
    (Der : ResolutionDerivation tcompl Axiom (∅ : ResolutionClause (TLit Edge))) :
    2 ^ (c * t - w₀ - 1) < ResolutionDerivation.size Der := by
  have hsw := resolution_size_width G charge hunsat Axiom haxiom hc hexp ht1 hcard hw₀ Der
  have hclog : c * t - w₀ ≤ Nat.clog 2 (ResolutionDerivation.size Der) := by omega
  by_contra hle
  push_neg at hle
  have : Nat.clog 2 (ResolutionDerivation.size Der) ≤ c * t - w₀ - 1 :=
    (Nat.le_pow_iff_clog_le (by norm_num : (1 : ℕ) < 2)).mp hle
  omega

end PallLean.Paper93.DeepMath.PathB.TseitinRootBound

#print axioms PallLean.Paper93.DeepMath.PathB.TseitinRootBound.resolution_size_width
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinRootBound.resolution_exp_size
