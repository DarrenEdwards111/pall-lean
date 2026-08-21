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

/-- `CSD_s`: the common-shallow-depth event at residual threshold `s`.

The extra argument `d` is the permitted depth of the shared trunk.  Keeping it explicit is
essential: an iteration lemma must pay for the common trunk separately from the residual gate
depth. -/
abbrev CSD_s {n G : ℕ} (gates : Fin G → List (Clause n))
    (fuel : ℕ) (σ : Restriction n) (d s : ℕ) : Prop :=
  CommonShallowAt gates fuel σ d s

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

/-- The exceptional event really is a subset of the fixed live-variable shell. -/
theorem commonShallowBad_subset_shell {n G : ℕ} {gates : Fin G → List (Clause n)}
    {fuel K d s : ℕ} :
    commonShallowBad gates fuel K d s ⊆
      Finset.univ.filter fun σ : Restriction n => stars σ = K := by
  intro σ hσ
  rw [mem_commonShallowBad] at hσ
  simp [hσ.1]

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

/-- With zero claimed saving the shell inequality is unconditional.  Thus every genuinely useful
iteration theorem must prove a *positive* exponent saving; it cannot come merely from the event
definition. -/
theorem commonShallowShellContraction_zero {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel residualDepth : ℕ)
    (trunkDepth : ℕ → ℕ) (savingDen : ℕ) :
    CommonShallowShellContraction gates fuel residualDepth trunkDepth 0 savingDen := by
  intro K
  simpa using Finset.card_le_card
    (commonShallowBad_subset_shell (gates := gates) (fuel := fuel)
      (K := K) (d := trunkDepth K) (s := residualDepth))

/-- A genuine exact-path encoder lands automatically in the shorter star shell.

This is the quantitative interface between the semantic failure event and the corrected common
bad-path reconstruction.  Unlike `commonBadPath_count`, callers do not assume that encoded
endpoints lie in an arbitrary `Short`: exact path length proves that the endpoint has `K-d` stars.
The remaining semantic content is therefore precisely the construction, from every failure of
`CSD_s`, of an extending assignment with an exact `d`-coordinate common path whose finite label
determines `pathVars`. -/
theorem commonShallowBad_card_le_of_exact_path_encoder
    {n G w d m fuel K residualDepth : ℕ} {gates : Fin G → List (Clause n)}
    (assignment : Restriction n → (Fin n → Bool))
    (label : Restriction n → CommonBadPathLabel w d G m)
    (hext : ∀ ρ ∈ commonShallowBad gates fuel K d residualDepth,
      Rung4Restriction.Extends ρ (assignment ρ))
    (hexact : ∀ ρ ∈ commonShallowBad gates fuel K d residualDepth,
      (CommonTree.pathVars ρ (canonicalFamilyTree gates fuel ρ) (assignment ρ)).card = d)
    (hvars : ∀ ρ ∈ commonShallowBad gates fuel K d residualDepth,
      ∀ σ ∈ commonShallowBad gates fuel K d residualDepth, label ρ = label σ →
        CommonTree.pathVars ρ (canonicalFamilyTree gates fuel ρ) (assignment ρ) =
          CommonTree.pathVars σ (canonicalFamilyTree gates fuel σ) (assignment σ)) :
    (commonShallowBad gates fuel K d residualDepth).card ≤
      (Finset.univ.filter fun τ : Restriction n => stars τ = K - d).card *
        (((d + 1) * 2 ^ d) * w ^ d * ((d + 1) ^ G * ((d + 1) ^ m) ^ G)) := by
  apply commonBadPath_count_of_pathVars
    (tree := fun ρ => canonicalFamilyTree gates fuel ρ)
    (assignment := assignment) (label := label)
  · exact hext
  · intro ρ hρ
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [CommonTree.stars_pathEndpoint ρ _ (assignment ρ) (hext ρ hρ),
      (mem_commonShallowBad.mp hρ).1, hexact ρ hρ]
  · exact hvars

/-- Prefix-path counting interface for genuinely long bad paths.

Unlike `commonShallowBad_card_le_of_exact_path_encoder`, this theorem does not require the *entire*
canonical-family path to have length exactly `d`.  It takes the first `d` fresh queries of any path
of length at least `d`, lands in the exact `(K-d)` shell, and discharges root injectivity from equality
of the prefix-variable sets.  The remaining encoder obligation is now correctly prefix-local. -/
theorem commonShallowBad_card_le_of_prefix_encoder
    {n G w d m fuel K residualDepth : ℕ} {gates : Fin G → List (Clause n)}
    (assignment : Restriction n → (Fin n → Bool))
    (label : Restriction n → SparseCommonBadPathLabel w d G m)
    (hext : ∀ ρ ∈ commonShallowBad gates fuel K d residualDepth,
      Rung4Restriction.Extends ρ (assignment ρ))
    (hlong : ∀ ρ ∈ commonShallowBad gates fuel K d residualDepth,
      d ≤ (CommonTree.trace
        (CommonTree.readOnce ρ (canonicalFamilyTree gates fuel ρ))
          (assignment ρ)).length)
    (hvars : ∀ ρ ∈ commonShallowBad gates fuel K d residualDepth,
      ∀ σ ∈ commonShallowBad gates fuel K d residualDepth, label ρ = label σ →
        CommonTree.prefixVars ρ (canonicalFamilyTree gates fuel ρ) d (assignment ρ) =
          CommonTree.prefixVars σ (canonicalFamilyTree gates fuel σ) d (assignment σ)) :
    (commonShallowBad gates fuel K d residualDepth).card ≤
      (Finset.univ.filter fun τ : Restriction n => stars τ = K - d).card *
        (((d + 1) * 2 ^ d) * (w + 1) ^ d * (G * m + 1) ^ d) := by
  classical
  apply card_bad_le_label_card
    (fun ρ => CommonTree.prefixEndpoint ρ
      (canonicalFamilyTree gates fuel ρ) d (assignment ρ)) label
  · exact le_of_eq (card_sparseCommonBadPathLabel w d G m)
  · intro ρ hρ
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [CommonTree.stars_prefixEndpoint ρ _ d (assignment ρ) (hext ρ hρ),
      (mem_commonShallowBad.mp hρ).1,
      CommonTree.prefixVars_card_eq_of_le_trace ρ _ d (assignment ρ)
        (hext ρ hρ) (hlong ρ hρ)]
  · intro ρ hρ σ hσ hE hlabel
    exact CommonTree.prefixEndpoint_inj_of_prefixVars_eq
      (hext ρ hρ) (hext σ hσ) hE (hvars ρ hρ σ hσ hlabel)

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
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_subset_shell
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_mono
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowShellContraction_zero
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_card_le_of_exact_path_encoder
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_card_le_of_prefix_encoder
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_card_le_of_contraction
