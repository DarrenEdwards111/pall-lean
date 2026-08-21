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

/-- The restriction stored at a canonical prefix leaf preserves every value fixed at the root. -/
theorem prefixEndpoint_restrictionExtends {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget : ℕ) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    RestrictionExtends σ (CommonTree.run (CommonTree.prefixEndpoints σ t budget) x) := by
  rw [CommonTree.run_prefixEndpoints]
  intro v b hv
  simp only [fixOn]
  split
  · next hmem => simpa [hext v b hv]
  · exact hv

/-- The canonical prefix trunk is a `CommonShallowAt` certificate as soon as all of its reached
restrictions have the requested residual gate-depth bound. -/
theorem commonShallowAt_of_prefix_residual {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (trunkDepth residualDepth : ℕ)
    (hresidual : ∀ x : Fin n → Bool, Rung4Restriction.Extends σ x → ∀ g,
      (canonicalDT (gates g) fuel
        (CommonTree.run (CommonTree.prefixEndpoints σ
          (canonicalFamilyTree gates fuel σ) trunkDepth) x)).depth ≤ residualDepth) :
    CommonShallowAt gates fuel σ trunkDepth residualDepth := by
  refine ⟨CommonTree.prefixEndpoints σ (canonicalFamilyTree gates fuel σ) trunkDepth,
    CommonTree.depth_prefixEndpoints_le σ _ trunkDepth, ?_⟩
  intro x hx
  exact ⟨prefixEndpoint_restrictionExtends σ _ trunkDepth x hx,
    CommonTree.run_prefixEndpoints_extends σ _ trunkDepth x hx,
    hresidual x hx⟩

/-- Failure of common shallowness is witnessed at the canonical prefix trunk by an extending
assignment and a gate whose residual canonical tree is still too deep. -/
theorem exists_deep_prefix_residual_of_not_commonShallowAt {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (trunkDepth residualDepth : ℕ)
    (hbad : ¬CommonShallowAt gates fuel σ trunkDepth residualDepth) :
    ∃ x : Fin n → Bool, Rung4Restriction.Extends σ x ∧ ∃ g,
      residualDepth < (canonicalDT (gates g) fuel
        (CommonTree.run (CommonTree.prefixEndpoints σ
          (canonicalFamilyTree gates fuel σ) trunkDepth) x)).depth := by
  classical
  by_contra hnone
  apply hbad
  apply commonShallowAt_of_prefix_residual gates fuel σ trunkDepth residualDepth
  intro x hx g
  apply Nat.le_of_not_lt
  intro hdeep
  exact hnone ⟨x, hx, g, hdeep⟩

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

/-- Canonical choice of the extending assignment witnessing a deep residual at the prefix trunk for
each bad root.  Outside the bad event its value is irrelevant. -/
noncomputable def commonShallowBadAssignment {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel K trunkDepth residualDepth : ℕ)
    (σ : Restriction n) : Fin n → Bool := by
  classical
  if hσ : σ ∈ commonShallowBad gates fuel K trunkDepth residualDepth then
    exact Classical.choose (exists_deep_prefix_residual_of_not_commonShallowAt
      gates fuel σ trunkDepth residualDepth (mem_commonShallowBad.mp hσ).2)
  else
    exact fun v => (σ v).getD false

/-- On a bad root, the canonical chosen assignment both extends the root and leaves some gate
deeper than the residual threshold at the canonical prefix endpoint. -/
theorem commonShallowBadAssignment_spec {n G : ℕ}
    {gates : Fin G → List (Clause n)} {fuel K trunkDepth residualDepth : ℕ}
    {σ : Restriction n} (hσ : σ ∈ commonShallowBad gates fuel K trunkDepth residualDepth) :
    Rung4Restriction.Extends σ
        (commonShallowBadAssignment gates fuel K trunkDepth residualDepth σ) ∧
      ∃ g, residualDepth < (canonicalDT (gates g) fuel
        (CommonTree.run (CommonTree.prefixEndpoints σ
          (canonicalFamilyTree gates fuel σ) trunkDepth)
            (commonShallowBadAssignment gates fuel K trunkDepth residualDepth σ))).depth := by
  classical
  rw [commonShallowBadAssignment, dif_pos hσ]
  exact Classical.choose_spec (exists_deep_prefix_residual_of_not_commonShallowAt
    gates fuel σ trunkDepth residualDepth (mem_commonShallowBad.mp hσ).2)

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

/-- Concrete sparse prefix count for genuinely long bad paths.  The first `d` fresh tagged
witnesses are used as the selected set, so no unproved correspondence between two prefix orders is
needed. -/
theorem commonShallowBad_card_le_of_sparse_prefix
    {n G w d m fuel K residualDepth : ℕ} {gates : Fin G → List (Clause n)}
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hgate : ∀ g, (gates g).length ≤ m)
    (assignment : Restriction n → (Fin n → Bool))
    (hext : ∀ ρ ∈ commonShallowBad gates fuel K d residualDepth,
      Rung4Restriction.Extends ρ (assignment ρ))
    (hlong : ∀ ρ ∈ commonShallowBad gates fuel K d residualDepth,
      d ≤ (CommonTree.trace
        (CommonTree.readOnce ρ (canonicalFamilyTree gates fuel ρ))
          (assignment ρ)).length) :
    (commonShallowBad gates fuel K d residualDepth).card ≤
      (Finset.univ.filter fun τ : Restriction n => stars τ = K - d).card *
        (((d + 1) * 2 ^ d) * (w + 1) ^ d * (G * m + 1) ^ d) := by
  apply sparseCanonicalCommonLongPath_count gates hnd hw hgate fuel assignment hext hlong
  intro ρ hρ
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [stars_freshTaggedPrefixEndpoint gates fuel ρ (assignment ρ) d (hext ρ hρ),
    (mem_commonShallowBad.mp hρ).1,
    freshTaggedPrefixVars_card_eq_of_le_trace gates fuel ρ (assignment ρ) d
      (hext ρ hρ) (hlong ρ hρ)]

/-- The concrete sparse prefix count with the semantic witness assignment chosen directly from
failure of `CommonShallowAt`.  The sole remaining semantic premise is that this canonical witness
actually traverses at least `d` fresh common queries. -/
theorem commonShallowBad_card_le_of_semantic_sparse_prefix
    {n G w d m fuel K residualDepth : ℕ} {gates : Fin G → List (Clause n)}
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hgate : ∀ g, (gates g).length ≤ m)
    (hlong : ∀ ρ ∈ commonShallowBad gates fuel K d residualDepth,
      d ≤ (CommonTree.trace
        (CommonTree.readOnce ρ (canonicalFamilyTree gates fuel ρ))
          (commonShallowBadAssignment gates fuel K d residualDepth ρ)).length) :
    (commonShallowBad gates fuel K d residualDepth).card ≤
      (Finset.univ.filter fun τ : Restriction n => stars τ = K - d).card *
        (((d + 1) * 2 ^ d) * (w + 1) ^ d * (G * m + 1) ^ d) := by
  apply commonShallowBad_card_le_of_sparse_prefix hnd hw hgate
    (commonShallowBadAssignment gates fuel K d residualDepth)
  · intro ρ hρ
    exact (commonShallowBadAssignment_spec hρ).1
  · exact hlong

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
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowAt_of_prefix_residual
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_deep_prefix_residual_of_not_commonShallowAt
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBadAssignment_spec
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_subset_shell
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_mono
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowShellContraction_zero
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_card_le_of_exact_path_encoder
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_card_le_of_prefix_encoder
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_card_le_of_sparse_prefix
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_card_le_of_semantic_sparse_prefix
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_card_le_of_contraction
