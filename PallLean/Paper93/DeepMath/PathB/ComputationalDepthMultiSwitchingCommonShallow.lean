import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwitchingWitnessLabel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictionCardinality

/-!
# Common residual-shallowness event for multi-switching

A joint evaluator is not enough for iteration.  The required object is a bounded-depth common
trunk whose reached leaf carries a residual restriction under which every gate has small canonical
decision-tree depth.  This file defines that exact certificate, its fixed-shell bad event, and the
proportional contraction statement that a genuine multi-switching count must prove.
-/

namespace PallLean.Paper93.DeepMath.PathB.MultiSwitching

open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting

/-- Restriction-to-restriction extension, kept separate from assignment extension. -/
def RestrictionExtends {n : ℕ} (σ τ : Restriction n) : Prop :=
  ∀ v b, σ v = some b → τ v = some b

/-- A real common switching certificate.  Its leaves are residual restrictions, not merely vectors
of gate values.  Every reached restriction extends the root, agrees with the followed assignment,
and makes every residual canonical gate tree shallow. -/
def CommonShallowAt {n G : ℕ} (gates : Fin G → List (Clause n))
    (fuel : ℕ) (σ : Restriction n) (trunkDepth residualDepth : ℕ) : Prop :=
  ∃ trunk : CommonTree n (Restriction n),
    CommonTree.depth trunk ≤ trunkDepth ∧
    ∀ x : Fin n → Bool, Rung4Restriction.Extends σ x →
      RestrictionExtends σ (CommonTree.run trunk x) ∧
      Rung4Restriction.Extends (CommonTree.run trunk x) x ∧
      ∀ g, (canonicalDT (gates g) fuel (CommonTree.run trunk x)).depth ≤ residualDepth

/-- Increasing either allowed common-trunk depth or residual depth preserves a certificate. -/
theorem CommonShallowAt.mono {n G : ℕ} {gates : Fin G → List (Clause n)}
    {fuel : ℕ} {σ : Restriction n} {d s d' s' : ℕ}
    (h : CommonShallowAt gates fuel σ d s) (hd : d ≤ d') (hs : s ≤ s') :
    CommonShallowAt gates fuel σ d' s' := by
  obtain ⟨trunk, hdepth, hleaf⟩ := h
  refine ⟨trunk, hdepth.trans hd, ?_⟩
  intro x hx
  obtain ⟨hroot, hext, hshallow⟩ := hleaf x hx
  exact ⟨hroot, hext, fun g => (hshallow g).trans hs⟩

/-- Restrictions on the exact `K`-live shell that do not admit the requested common-shallow
certificate. -/
noncomputable def commonShallowBad {n G : ℕ} (gates : Fin G → List (Clause n))
    (fuel K trunkDepth residualDepth : ℕ) : Finset (Restriction n) := by
  classical
  exact Finset.univ.filter fun σ =>
    stars σ = K ∧ ¬CommonShallowAt gates fuel σ trunkDepth residualDepth

theorem mem_commonShallowBad {n G : ℕ} {gates : Fin G → List (Clause n)}
    {fuel K d s : ℕ} {σ : Restriction n} :
    σ ∈ commonShallowBad gates fuel K d s ↔
      stars σ = K ∧ ¬CommonShallowAt gates fuel σ d s := by
  classical
  simp [commonShallowBad]

/-- Allowing a deeper trunk or deeper residual gates can only shrink the bad event. -/
theorem commonShallowBad_mono {n G : ℕ} {gates : Fin G → List (Clause n)}
    {fuel K d s d' s' : ℕ} (hd : d ≤ d') (hs : s ≤ s') :
    commonShallowBad gates fuel K d' s' ⊆ commonShallowBad gates fuel K d s := by
  intro σ hσ
  rw [mem_commonShallowBad] at hσ ⊢
  refine ⟨hσ.1, ?_⟩
  intro hsmall
  exact hσ.2 (hsmall.mono hd hs)

/-- Exact proportional exceptional-mass target.  `savingNum/savingDen` is the desired number of
exponent bits saved per live variable; multiplying avoids probability/rational coercions. -/
def CommonShallowShellContraction {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel residualDepth : ℕ)
    (trunkDepth : ℕ → ℕ) (savingNum savingDen : ℕ) : Prop :=
  ∀ K,
    (commonShallowBad gates fuel K (trunkDepth K) residualDepth).card *
        2 ^ ((savingNum * K) / savingDen) ≤
      (Finset.univ.filter fun σ : Restriction n => stars σ = K).card

/-- The target explicitly implies the corresponding unnormalized bad-shell cardinality bound. -/
theorem commonShallowBad_card_le_of_contraction {n G : ℕ}
    {gates : Fin G → List (Clause n)} {fuel residualDepth : ℕ}
    {trunkDepth : ℕ → ℕ} {savingNum savingDen K : ℕ}
    (h : CommonShallowShellContraction gates fuel residualDepth trunkDepth
      savingNum savingDen) :
    (commonShallowBad gates fuel K (trunkDepth K) residualDepth).card *
        2 ^ ((savingNum * K) / savingDen) ≤
      (Finset.univ.filter fun σ : Restriction n => stars σ = K).card :=
  h K

end PallLean.Paper93.DeepMath.PathB.MultiSwitching

#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonShallowAt.mono
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_mono
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_card_le_of_contraction
