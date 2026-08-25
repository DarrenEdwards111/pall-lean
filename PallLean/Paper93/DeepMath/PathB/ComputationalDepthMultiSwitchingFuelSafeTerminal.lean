import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwitchingCommonShallow
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SatRecovery
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingProcessedUnsat
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingBinomialRegime
import Mathlib.Data.Fintype.BigOperators

/-!
# Fuel-safe terminal states for canonical DNF executions

The residual-fuel counterexample shows that a path may stop solely because recursive fuel reaches
zero.  This file isolates the sufficient repair for one gate: if the initial fuel is at least the
number of live variables, following the canonical execution reaches a semantic terminal state
(a satisfied term or no active term), rather than a fuel-exhausted artificial leaf.  Rebuilding the
canonical tree at that restriction therefore has depth zero for every fuel.
-/

namespace PallLean.Paper93.DeepMath.PathB.MultiSwitching

open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting

/-- Restriction reached by following the canonical binary DNF execution under `x`. -/
def canonicalEnd {n : ℕ} (cs : List (Clause n)) :
    ℕ → Restriction n → (Fin n → Bool) → Restriction n
  | 0, σ, _ => σ
  | fuel + 1, σ, x =>
      if anyTermSat cs σ then σ
      else match activeTerm cs σ with
        | none => σ
        | some T => match (freeLits σ T).head? with
          | none => σ
          | some ell => canonicalEnd cs fuel (fixVar σ (litVar ell) (x (litVar ell))) x

/-- A semantic canonical terminal: either a term is already satisfied or no active term remains. -/
def CanonicalTerminal {n : ℕ} (cs : List (Clause n)) (σ : Restriction n) : Prop :=
  anyTermSat cs σ = true ∨ activeTerm cs σ = none

/-- Fixing an inserted coordinate in one step agrees with fixing it first and then fixing the
remaining selected set. -/
theorem fixOn_insert_eq_fixOn_fixVar {n : ℕ} (σ : Restriction n) (v : Fin n)
    (S : Finset (Fin n)) (x : Fin n → Bool) :
    fixOn σ (insert v S) x = fixOn (fixVar σ v (x v)) S x := by
  funext j
  by_cases hjv : j = v
  · subst j
    by_cases hvS : v ∈ S <;> simp [fixOn, fixVar, hvS]
  · by_cases hjS : j ∈ S <;> simp [fixOn, fixVar, hjv, hjS]

/-- A free root query decomposes the normalized path endpoint into the followed child endpoint. -/
theorem CommonTree.pathEndpoint_query_of_free {n : ℕ} {α : Type}
    (σ : Restriction n) (i : Fin n) (lo hi : CommonTree n α) (x : Fin n → Bool)
    (hfree : σ i = none) :
    CommonTree.pathEndpoint σ (.query i lo hi) x =
      if x i then CommonTree.pathEndpoint (fixVar σ i true) hi x
      else CommonTree.pathEndpoint (fixVar σ i false) lo x := by
  by_cases hx : x i
  · simp [CommonTree.pathEndpoint, CommonTree.pathVars, CommonTree.readOnce,
      CommonTree.queryVars, hfree, hx, fixOn_insert_eq_fixOn_fixVar]
  · simp [CommonTree.pathEndpoint, CommonTree.pathVars, CommonTree.readOnce,
      CommonTree.queryVars, hfree, hx, fixOn_insert_eq_fixOn_fixVar]

/-- A leaf path endpoint is the unchanged root restriction. -/
@[simp] theorem CommonTree.pathEndpoint_leaf {n : ℕ} {α : Type}
    (σ : Restriction n) (a : α) (x : Fin n → Bool) :
    CommonTree.pathEndpoint σ (.leaf a) x = σ := by
  funext j
  simp [CommonTree.pathEndpoint, CommonTree.pathVars, CommonTree.readOnce,
    CommonTree.queryVars, fixOn]

/-- Once the budget covers the whole normalized trace, the prefix endpoint is the full path
endpoint. -/
theorem CommonTree.prefixEndpoint_eq_pathEndpoint_of_trace_length_le
    {n : ℕ} {α : Type} (σ : Restriction n) (t : CommonTree n α)
    (budget : ℕ) (x : Fin n → Bool)
    (hle : (CommonTree.trace (CommonTree.readOnce σ t) x).length ≤ budget) :
    CommonTree.prefixEndpoint σ t budget x = CommonTree.pathEndpoint σ t x := by
  rw [CommonTree.prefixEndpoint_eq_fixOn]
  unfold CommonTree.prefixVars CommonTree.pathEndpoint CommonTree.pathVars
  rw [CommonTree.queryVars_prefixEndpoints]
  have hquery : (CommonTree.queryVars (CommonTree.readOnce σ t) x).length ≤ budget := by
    rwa [← CommonTree.trace_length_eq_queryVars_length]
  rw [(List.take_eq_self_iff _).mpr hquery]

/-- Following the canonical execution preserves consistency with the followed assignment. -/
theorem canonicalEnd_extends {n : ℕ} (cs : List (Clause n)) :
    ∀ (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool),
      Rung4Restriction.Extends σ x → Rung4Restriction.Extends (canonicalEnd cs fuel σ x) x := by
  intro fuel
  induction fuel with
  | zero => intro σ x hext; exact hext
  | succ fuel ih =>
      intro σ x hext
      by_cases hany : anyTermSat cs σ = true
      · simp [canonicalEnd, hany, hext]
      · cases hact : activeTerm cs σ with
        | none => simp [canonicalEnd, hany, hact, hext]
        | some T =>
            cases hhead : (freeLits σ T).head? with
            | none => simp [canonicalEnd, hany, hact, hhead, hext]
            | some ell =>
                simpa [canonicalEnd, hany, hact, hhead] using
                  ih (fixVar σ (litVar ell) (x (litVar ell))) x
                    (extends_fixVar hext rfl)

/-- The operational canonical endpoint is exactly the normalized common-tree path endpoint of the
same canonical gate tree. -/
theorem canonicalEnd_eq_pathEndpoint {n : ℕ} (cs : List (Clause n)) :
    ∀ (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool),
      canonicalEnd cs fuel σ x =
        CommonTree.pathEndpoint σ (CommonTree.ofBool (canonicalDT cs fuel σ)) x := by
  intro fuel
  induction fuel with
  | zero =>
      intro σ x
      rw [canonicalEnd, canonicalDT]
      split <;> rfl
  | succ fuel ih =>
      intro σ x
      by_cases hany : anyTermSat cs σ = true
      · simp [canonicalEnd, canonicalDT, hany, CommonTree.ofBool]
      · cases hact : activeTerm cs σ with
        | none => simp [canonicalEnd, canonicalDT, hany, hact, CommonTree.ofBool]
        | some T =>
            obtain ⟨ell, hhead, hfree⟩ := activeTerm_first_free hact
            rw [canonicalEnd, canonicalDT]
            simp only [hany, Bool.false_eq_true, if_false, hact, hhead, CommonTree.ofBool]
            rw [CommonTree.pathEndpoint_query_of_free σ (litVar ell) _ _ x hfree]
            by_cases hx : x (litVar ell)
            · simp [hx, ih]
            · simp [hx, ih]

/-- Ample fuel prevents an artificial fuel-exhaustion leaf: the reached restriction is
semantically terminal. -/
theorem canonicalEnd_terminal_of_stars_le_fuel {n : ℕ} (cs : List (Clause n)) :
    ∀ (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool),
      stars σ ≤ fuel → CanonicalTerminal cs (canonicalEnd cs fuel σ x) := by
  intro fuel
  induction fuel with
  | zero =>
      intro σ x hstars
      have hzero : stars σ = 0 := Nat.eq_zero_of_le_zero hstars
      by_cases hany : anyTermSat cs σ = true
      · exact Or.inl hany
      · right
        cases hact : activeTerm cs σ with
        | none => exact hact
        | some T =>
            obtain ⟨ell, _, hfree⟩ := activeTerm_first_free hact
            have hmem : litVar ell ∈ freeVars σ := mem_freeVars.mpr hfree
            have hempty : freeVars σ = ∅ := Finset.card_eq_zero.mp hzero
            rw [hempty] at hmem
            simp at hmem
  | succ fuel ih =>
      intro σ x hstars
      by_cases hany : anyTermSat cs σ = true
      · simpa [canonicalEnd, hany, CanonicalTerminal] using hany
      · cases hact : activeTerm cs σ with
        | none => simpa [canonicalEnd, hany, hact, CanonicalTerminal] using hact
        | some T =>
            obtain ⟨ell, hhead, hfree⟩ := activeTerm_first_free hact
            have hdrop : stars (fixVar σ (litVar ell) (x (litVar ell))) ≤ fuel := by
              have hlt := stars_fixVar_lt (b := x (litVar ell)) hfree
              omega
            simpa [canonicalEnd, hany, hact, hhead] using
              ih (fixVar σ (litVar ell) (x (litVar ell))) x hdrop

/-- Rebuilding a canonical tree at a semantic terminal yields a leaf for every fuel. -/
theorem canonicalDT_depth_eq_zero_of_terminal {n : ℕ} (cs : List (Clause n))
    (σ : Restriction n) (hterminal : CanonicalTerminal cs σ) :
    ∀ fuel, (canonicalDT cs fuel σ).depth = 0 := by
  intro fuel
  cases fuel with
  | zero => rw [canonicalDT]; split <;> rfl
  | succ fuel =>
      cases hterminal with
      | inl hany => simp [canonicalDT, hany]
      | inr hactive =>
          by_cases hany : anyTermSat cs σ = true
          · simp [canonicalDT, hany]
          · simp [canonicalDT, hany, hactive]

/-- Ample initial fuel makes the reached canonical restriction stable under rebuilding with any
new fuel. -/
theorem canonicalDT_depth_canonicalEnd_eq_zero {n : ℕ} (cs : List (Clause n))
    (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool) (hstars : stars σ ≤ fuel) :
    ∀ rebuildFuel, (canonicalDT cs rebuildFuel (canonicalEnd cs fuel σ x)).depth = 0 :=
  canonicalDT_depth_eq_zero_of_terminal cs _
    (canonicalEnd_terminal_of_stars_le_fuel cs fuel σ x hstars)

/-- Common-tree form: with ample fuel, fixing a full canonical gate path makes the rebuilt gate
tree a leaf. -/
theorem canonicalDT_depth_pathEndpoint_eq_zero {n : ℕ} (cs : List (Clause n))
    (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool) (hstars : stars σ ≤ fuel) :
    ∀ rebuildFuel, (canonicalDT cs rebuildFuel
      (CommonTree.pathEndpoint σ (CommonTree.ofBool (canonicalDT cs fuel σ)) x)).depth = 0 := by
  rw [← canonicalEnd_eq_pathEndpoint cs fuel σ x]
  exact canonicalDT_depth_canonicalEnd_eq_zero cs fuel σ x hstars

/-- Repaired one-gate semantic bridge.  Under ample initial fuel, a rebuilt gate which is still
positive-depth after the budget prefix forces the normalized canonical trace to use the entire
budget. -/
theorem canonicalGate_deep_prefix_implies_long_trace {n : ℕ} (cs : List (Clause n))
    (fuel rebuildFuel : ℕ) (σ : Restriction n) (x : Fin n → Bool) (budget : ℕ)
    (hstars : stars σ ≤ fuel)
    (hdeep : 0 < (canonicalDT cs rebuildFuel
      (CommonTree.run (CommonTree.prefixEndpoints σ
        (CommonTree.ofBool (canonicalDT cs fuel σ)) budget) x)).depth) :
    budget ≤ (CommonTree.trace
      (CommonTree.readOnce σ (CommonTree.ofBool (canonicalDT cs fuel σ))) x).length := by
  by_contra hnot
  have hshort : (CommonTree.trace
      (CommonTree.readOnce σ (CommonTree.ofBool (canonicalDT cs fuel σ))) x).length ≤ budget :=
    Nat.le_of_lt (Nat.lt_of_not_ge hnot)
  have hend := CommonTree.prefixEndpoint_eq_pathEndpoint_of_trace_length_le
    σ (CommonTree.ofBool (canonicalDT cs fuel σ)) budget x hshort
  have hzero := canonicalDT_depth_pathEndpoint_eq_zero cs fuel σ x hstars rebuildFuel
  rw [CommonTree.prefixEndpoint] at hend
  rw [hend, hzero] at hdeep
  exact Nat.not_lt_zero 0 hdeep

/-- Restriction extension preserves the value at every already-fixed coordinate. -/
theorem restrictionExtends_eq_of_fixed {n : ℕ} {σ τ : Restriction n}
    (hext : RestrictionExtends σ τ) {v : Fin n} (hv : σ v ≠ none) : τ v = σ v := by
  cases hσ : σ v with
  | none => exact (hv hσ).elim
  | some b => exact hext v b hσ

/-- A term already forced true stays forced true under further restriction. -/
theorem termSat_mono_of_restrictionExtends {n : ℕ} {σ τ : Restriction n}
    (hext : RestrictionExtends σ τ) {T : Clause n} (hsat : termSat σ T = true) :
    termSat τ T = true := by
  rw [termSat, List.all_eq_true] at hsat ⊢
  intro ell hell
  exact litTrue_mono (fun v hv => restrictionExtends_eq_of_fixed hext hv) (hsat ell hell)

/-- The list of free literals can only shrink under restriction extension. -/
theorem freeLits_subset_of_restrictionExtends {n : ℕ} {σ τ : Restriction n}
    (hext : RestrictionExtends σ τ) (T : Clause n) : freeLits τ T ⊆ freeLits σ T := by
  intro ell hell
  rw [freeLits, List.mem_filter] at hell ⊢
  refine ⟨hell.1, ?_⟩
  cases hσ : σ (litVar ell) with
  | none => simp [litFree_var, hσ]
  | some b =>
      have hτ : τ (litVar ell) = some b := hext _ _ hσ
      rw [litFree_var, hτ] at hell
      simp at hell

/-- Canonical semantic terminality is monotone under restriction extension. -/
theorem CanonicalTerminal.mono {n : ℕ} {cs : List (Clause n)} {σ τ : Restriction n}
    (hext : RestrictionExtends σ τ) (hterminal : CanonicalTerminal cs σ) :
    CanonicalTerminal cs τ := by
  have hany_mono : anyTermSat cs σ = true → anyTermSat cs τ = true := by
    intro hany
    rw [anyTermSat, List.any_eq_true] at hany ⊢
    obtain ⟨T, hT, hsat⟩ := hany
    exact ⟨T, hT, termSat_mono_of_restrictionExtends hext hsat⟩
  rcases hterminal with hany | hactive
  · exact Or.inl (hany_mono hany)
  · by_cases hanyσ : anyTermSat cs σ = true
    · exact Or.inl (hany_mono hanyσ)
    · by_cases hanyτ : anyTermSat cs τ = true
      · exact Or.inl hanyτ
      · right
        have hfindσ :
            cs.find? (fun T => !termFalsified σ T && decide (0 < (freeLits σ T).length)) =
              none := by
          simpa [activeTerm, hanyσ] using hactive
        have hnoneσ := List.find?_eq_none.mp hfindσ
        simp [activeTerm, hanyτ]
        intro T hT hnotfτ
        have hpσ := hnoneσ T hT
        have hnotfσ : termFalsified σ T = false := by
          cases hfσ : termFalsified σ T with
          | false => rfl
          | true =>
              have hfτ : termFalsified τ T = true :=
                Depth3.termFalsified_mono hext hfσ
              rw [hfτ] at hnotfτ
              contradiction
        have hfreeσ : freeLits σ T = [] := by
          by_contra hne
          have hlenσ : 0 < (freeLits σ T).length := List.length_pos_iff.mpr hne
          exact hpσ (by simp [hnotfσ, hlenσ])
        exact List.eq_nil_of_subset_nil
          (hfreeσ ▸ freeLits_subset_of_restrictionExtends hext T)

/-- Fixing a larger coordinate set along a compatible assignment extends the smaller endpoint. -/
theorem fixOn_restrictionExtends_of_subset {n : ℕ} (σ : Restriction n)
    {S U : Finset (Fin n)} (x : Fin n → Bool) (hext : Rung4Restriction.Extends σ x)
    (hsub : S ⊆ U) : RestrictionExtends (fixOn σ S x) (fixOn σ U x) := by
  intro v b hv
  by_cases hvS : v ∈ S
  · have hvU : v ∈ U := hsub hvS
    simpa [fixOn, hvS, hvU] using hv
  · rw [fixOn, if_neg hvS] at hv
    by_cases hvU : v ∈ U
    · simp [fixOn, hvU, hext v b hv]
    · simpa [fixOn, hvU] using hv

/-- Every normalized member-gate path is contained in the normalized common-family path. -/
theorem gate_pathVars_subset_canonicalFamily {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (hext : Rung4Restriction.Extends σ x) (g : Fin G) :
    CommonTree.pathVars σ (CommonTree.ofBool (canonicalDT (gates g) fuel σ)) x ⊆
      CommonTree.pathVars σ (canonicalFamilyTree gates fuel σ) x := by
  rw [CommonTree.pathVars,
    CommonTree.queryVars_readOnce_toFinset_eq σ
      (CommonTree.ofBool (canonicalDT (gates g) fuel σ)) x hext,
    pathVars_canonicalFamily_eq_raw gates fuel σ x hext]
  · intro v hv
    rw [canonicalFamilyTree, CommonTree.queryVars_commonRefineFin]
    simp only [List.mem_toFinset] at hv ⊢
    apply List.mem_flatten.mpr
    refine ⟨CommonTree.queryVars
      (CommonTree.ofBool (canonicalDT (gates g) fuel σ)) x, ?_, hv⟩
    apply List.mem_map.mpr
    exact ⟨canonicalDT (gates g) fuel σ, List.mem_ofFn.mpr ⟨g, rfl⟩, rfl⟩
  · intro v hv
    apply canonicalDT_queriedVars_subset_free (gates g) fuel σ
    exact CommonTree.queryVars_ofBool_toFinset_subset_queriedVars
      (canonicalDT (gates g) fuel σ) x (List.mem_toFinset.mpr hv)

/-- The full common-family endpoint extends every member gate's own canonical endpoint. -/
theorem gate_pathEndpoint_restrictionExtends_canonicalFamily {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (hext : Rung4Restriction.Extends σ x) (g : Fin G) :
    RestrictionExtends
      (CommonTree.pathEndpoint σ (CommonTree.ofBool (canonicalDT (gates g) fuel σ)) x)
      (CommonTree.pathEndpoint σ (canonicalFamilyTree gates fuel σ) x) := by
  unfold CommonTree.pathEndpoint
  exact fixOn_restrictionExtends_of_subset σ x hext
    (gate_pathVars_subset_canonicalFamily gates fuel σ x hext g)

/-- With ample fuel, the full family endpoint is terminal for every member gate. -/
theorem canonicalFamily_pathEndpoint_terminal {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (hext : Rung4Restriction.Extends σ x) (hstars : stars σ ≤ fuel)
    (g : Fin G) :
    CanonicalTerminal (gates g)
      (CommonTree.pathEndpoint σ (canonicalFamilyTree gates fuel σ) x) := by
  apply CanonicalTerminal.mono
    (gate_pathEndpoint_restrictionExtends_canonicalFamily gates fuel σ x hext g)
  rw [← canonicalEnd_eq_pathEndpoint (gates g) fuel σ x]
  exact canonicalEnd_terminal_of_stars_le_fuel (gates g) fuel σ x hstars

/-- Full-family ample-fuel repair: a positive-depth member residual after a budget prefix forces
the normalized common family trace to have at least that budget. -/
theorem canonicalFamily_deep_prefix_implies_long_trace {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel rebuildFuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (hext : Rung4Restriction.Extends σ x) (budget : ℕ)
    (hstars : stars σ ≤ fuel) (g : Fin G)
    (hdeep : 0 < (canonicalDT (gates g) rebuildFuel
      (CommonTree.run (CommonTree.prefixEndpoints σ
        (canonicalFamilyTree gates fuel σ) budget) x)).depth) :
    budget ≤ (CommonTree.trace
      (CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)) x).length := by
  by_contra hnot
  have hshort : (CommonTree.trace
      (CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)) x).length ≤ budget :=
    Nat.le_of_lt (Nat.lt_of_not_ge hnot)
  have hend := CommonTree.prefixEndpoint_eq_pathEndpoint_of_trace_length_le
    σ (canonicalFamilyTree gates fuel σ) budget x hshort
  have hzero := canonicalDT_depth_eq_zero_of_terminal (gates g)
    (CommonTree.pathEndpoint σ (canonicalFamilyTree gates fuel σ) x)
    (canonicalFamily_pathEndpoint_terminal gates fuel σ x hext hstars g) rebuildFuel
  rw [CommonTree.prefixEndpoint] at hend
  rw [hend, hzero] at hdeep
  exact Nat.not_lt_zero 0 hdeep

/-- On an exact `K`-live shell with `K ≤ fuel`, the canonical semantic failure witness always
supplies the long common prefix required by the sparse encoder. -/
theorem commonShallowBadAssignment_long_of_le_fuel {n G : ℕ}
    {gates : Fin G → List (Clause n)} {fuel K d residualDepth : ℕ}
    (hKfuel : K ≤ fuel) {ρ : Restriction n}
    (hρ : ρ ∈ commonShallowBad gates fuel K d residualDepth) :
    d ≤ (CommonTree.trace
      (CommonTree.readOnce ρ (canonicalFamilyTree gates fuel ρ))
        (commonShallowBadAssignment gates fuel K d residualDepth ρ)).length := by
  obtain ⟨hext, g, hdeep⟩ := commonShallowBadAssignment_spec hρ
  apply canonicalFamily_deep_prefix_implies_long_trace gates fuel fuel ρ
    (commonShallowBadAssignment gates fuel K d residualDepth ρ) hext d
  · rw [(mem_commonShallowBad.mp hρ).1]
    exact hKfuel
  · exact Nat.zero_lt_of_lt hdeep

/-- On an ample-fuel shell, the actual canonical bad-assignment endpoints give an exact fiber
partition of the bad event over the residual shell.  Thus subsequent estimates may sum genuine
endpoint-local multiplicities instead of multiplying every endpoint by one global worst fiber. -/
theorem commonShallowBadAssignment_endpointFiber_aggregate_exact
    {n G fuel K d residualDepth : ℕ} {gates : Fin G → List (Clause n)}
    (hKfuel : K ≤ fuel) :
    (∑ τ ∈ (Finset.univ : Finset (Restriction n)).filter fun τ => stars τ = K - d,
        (commonShallowBadEndpointFiber gates fuel K d residualDepth
          (commonShallowBadAssignment gates fuel K d residualDepth) τ).card) =
      (commonShallowBad gates fuel K d residualDepth).card := by
  apply commonShallowBadEndpointFiber_aggregate_exact
  · intro ρ hρ
    exact (commonShallowBadAssignment_spec hρ).1
  · intro ρ hρ
    exact commonShallowBadAssignment_long_of_le_fuel hKfuel hρ

/-- On an ample-fuel shell, the endpoint-local image of the exact ragged-prefix label is an exact
weighted accounting of the semantic bad event.  This is the canonical specialization of
`commonShallowBadEndpointLabelImage_aggregate_exact`; no global worst-fiber or ambient-label
factor is introduced. -/
theorem commonShallowBadAssignment_endpointLabelImage_aggregate_exact
    {n G w fuel K d residualDepth : ℕ} {gates : Fin G → List (Clause n)}
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel) :
    (∑ τ ∈ (Finset.univ : Finset (Restriction n)).filter fun τ => stars τ = K - d,
        (commonShallowBadEndpointLabelImage gates hnd hw fuel K d residualDepth
          (commonShallowBadAssignment gates fuel K d residualDepth) τ).card) =
      (commonShallowBad gates fuel K d residualDepth).card := by
  apply commonShallowBadEndpointLabelImage_aggregate_exact hnd hw
  · intro ρ hρ
    exact (commonShallowBadAssignment_spec hρ).1
  · intro ρ hρ
    exact commonShallowBadAssignment_long_of_le_fuel hKfuel hρ

/-- The semantic sparse-prefix count now has no separate long-path premise on ample-fuel shells. -/
theorem commonShallowBad_card_le_of_ample_fuel_sparse_prefix
    {n G w d m fuel K residualDepth : ℕ} {gates : Fin G → List (Clause n)}
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hgate : ∀ g, (gates g).length ≤ m)
    (hKfuel : K ≤ fuel) :
    (commonShallowBad gates fuel K d residualDepth).card ≤
      (Finset.univ.filter fun τ : Restriction n => stars τ = K - d).card *
        (((d + 1) * 2 ^ d) * (w + 1) ^ d * (G * m + 1) ^ d) := by
  apply commonShallowBad_card_le_of_semantic_sparse_prefix hnd hw hgate
  intro ρ hρ
  exact commonShallowBadAssignment_long_of_le_fuel hKfuel hρ

/-- Ample-fuel shell count with the compressed prefix multiplicity label.  This removes both the
`(d+1) * 2^d` transcript factor and the per-query `(G*m+1)^d` key factor from the sparse bound. -/
theorem commonShallowBad_card_le_of_ample_fuel_prefix_counts
    {n G w d m fuel K residualDepth : ℕ} {gates : Fin G → List (Clause n)}
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hgate : ∀ g, (gates g).length ≤ m)
    (hKfuel : K ≤ fuel) :
    (commonShallowBad gates fuel K d residualDepth).card ≤
      (Finset.univ.filter fun τ : Restriction n => stars τ = K - d).card *
        ((w + 1) ^ d * ((d + 1) ^ m) ^ G) := by
  apply commonShallowBad_card_le_of_semantic_prefix_counts hnd hw hgate
  intro ρ hρ
  exact commonShallowBadAssignment_long_of_le_fuel hKfuel hρ

/-- Ample-fuel shell count with the exact stars-and-bars multiset of realized prefix keys. -/
theorem commonShallowBad_card_le_of_ample_fuel_prefix_sym
    {n G w d m fuel K residualDepth : ℕ} {gates : Fin G → List (Clause n)}
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hgate : ∀ g, (gates g).length ≤ m)
    (hKfuel : K ≤ fuel) :
    (commonShallowBad gates fuel K d residualDepth).card ≤
      (Finset.univ.filter fun τ : Restriction n => stars τ = K - d).card *
        ((w + 1) ^ d * ((G * m + d - 1).choose d + 1)) := by
  apply commonShallowBad_card_le_of_semantic_prefix_sym hnd hw hgate
  intro ρ hρ
  exact commonShallowBadAssignment_long_of_le_fuel hKfuel hρ

/-- Ample-fuel shell count over the exact ragged family alphabet. -/
theorem commonShallowBad_card_le_of_ample_fuel_prefix_actual_sym
    {n G w d fuel K residualDepth : ℕ} {gates : Fin G → List (Clause n)}
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel) :
    (commonShallowBad gates fuel K d residualDepth).card ≤
      (Finset.univ.filter fun τ : Restriction n => stars τ = K - d).card *
        ((w + 1) ^ d * (((∑ g, (gates g).length) + d - 1).choose d + 1)) := by
  apply commonShallowBad_card_le_of_semantic_prefix_actual_sym hnd hw
  intro ρ hρ
  exact commonShallowBadAssignment_long_of_le_fuel hKfuel hρ

/-- Hybrid ample-fuel count: use whichever of the per-query sparse code and dense multiplicity
table is smaller for the concrete parameters.  Thus prefix-count compression never weakens the
previous verified shell bound. -/
theorem commonShallowBad_card_le_of_ample_fuel_hybrid_prefix
    {n G w d m fuel K residualDepth : ℕ} {gates : Fin G → List (Clause n)}
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hgate : ∀ g, (gates g).length ≤ m)
    (hKfuel : K ≤ fuel) :
    (commonShallowBad gates fuel K d residualDepth).card ≤
      (Finset.univ.filter fun τ : Restriction n => stars τ = K - d).card *
        min (((d + 1) * 2 ^ d) * (w + 1) ^ d * (G * m + 1) ^ d)
          ((w + 1) ^ d * ((d + 1) ^ m) ^ G) := by
  rw [← min_mul_mul_left]
  apply le_min
  · exact commonShallowBad_card_le_of_ample_fuel_sparse_prefix hnd hw hgate hKfuel
  · exact commonShallowBad_card_le_of_ample_fuel_prefix_counts hnd hw hgate hKfuel

/-- Three-way capstone: expose the best verified factor among the per-query word, dense count
table, and exact realized-key multiset. -/
theorem commonShallowBad_card_le_of_ample_fuel_realized_hybrid
    {n G w d m fuel K residualDepth : ℕ} {gates : Fin G → List (Clause n)}
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hgate : ∀ g, (gates g).length ≤ m)
    (hKfuel : K ≤ fuel) :
    (commonShallowBad gates fuel K d residualDepth).card ≤
      (Finset.univ.filter fun τ : Restriction n => stars τ = K - d).card *
        min (((d + 1) * 2 ^ d) * (w + 1) ^ d * (G * m + 1) ^ d)
          (min ((w + 1) ^ d * ((d + 1) ^ m) ^ G)
            ((w + 1) ^ d * ((G * m + d - 1).choose d + 1))) := by
  rw [← min_mul_mul_left]
  apply le_min
  · exact commonShallowBad_card_le_of_ample_fuel_sparse_prefix hnd hw hgate hKfuel
  · rw [← min_mul_mul_left]
    apply le_min
    · exact commonShallowBad_card_le_of_ample_fuel_prefix_counts hnd hw hgate hKfuel
    · exact commonShallowBad_card_le_of_ample_fuel_prefix_sym hnd hw hgate hKfuel

/-- Direct arithmetic gate from the exact realized-key multiset count to a scaled shell bound.
Unlike `commonShallowBad_scaled_le_of_realized_density` below, this theorem does not replace the
stars-and-bars factor by a word-space power.  It is therefore the interface for testing whether
the factorial hidden in `choose (G*m+d-1) d` changes a concrete round recurrence. -/
theorem commonShallowBad_scaled_le_of_realized_balance
    {n G w d m fuel K residualDepth savingExponent : ℕ}
    {gates : Fin G → List (Clause n)}
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hgate : ∀ g, (gates g).length ≤ m)
    (hKfuel : K ≤ fuel)
    (hbalance :
      Nat.choose n (K - d) * 2 ^ (n - (K - d)) *
            ((w + 1) ^ d * ((G * m + d - 1).choose d + 1)) *
            2 ^ savingExponent ≤
          Nat.choose n K * 2 ^ (n - K)) :
    (commonShallowBad gates fuel K d residualDepth).card * 2 ^ savingExponent ≤
      (Finset.univ.filter fun σ : Restriction n => stars σ = K).card := by
  have hcount := commonShallowBad_card_le_of_ample_fuel_prefix_sym
    (gates := gates) (w := w) (m := m) (d := d) (residualDepth := residualDepth)
    hnd hw hgate hKfuel
  have hscaled := Nat.mul_le_mul_right (2 ^ savingExponent) hcount
  calc
    (commonShallowBad gates fuel K d residualDepth).card * 2 ^ savingExponent ≤
        (Finset.univ.filter fun τ : Restriction n => stars τ = K - d).card *
          ((w + 1) ^ d * ((G * m + d - 1).choose d + 1)) *
          2 ^ savingExponent := hscaled
    _ ≤ (Finset.univ.filter fun σ : Restriction n => stars σ = K).card := by
      rw [card_stars_eq (N := n) (K := K - d), card_stars_eq (N := n) (K := K)]
      exact hbalance

/-- Direct scaled-shell interface for the exact ragged family alphabet.  Unlike the rectangular
version above, the stars-and-bars factor charges only genuine clause occurrences. -/
theorem commonShallowBad_scaled_le_of_actual_balance
    {n G w d fuel K residualDepth savingExponent : ℕ}
    {gates : Fin G → List (Clause n)}
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel)
    (hbalance :
      Nat.choose n (K - d) * 2 ^ (n - (K - d)) *
            ((w + 1) ^ d * (((∑ g, (gates g).length) + d - 1).choose d + 1)) *
            2 ^ savingExponent ≤
          Nat.choose n K * 2 ^ (n - K)) :
    (commonShallowBad gates fuel K d residualDepth).card * 2 ^ savingExponent ≤
      (Finset.univ.filter fun σ : Restriction n => stars σ = K).card := by
  have hcount := commonShallowBad_card_le_of_ample_fuel_prefix_actual_sym
    (gates := gates) (w := w) (d := d) (residualDepth := residualDepth)
    hnd hw hKfuel
  have hscaled := Nat.mul_le_mul_right (2 ^ savingExponent) hcount
  calc
    (commonShallowBad gates fuel K d residualDepth).card * 2 ^ savingExponent ≤
        (Finset.univ.filter fun τ : Restriction n => stars τ = K - d).card *
          ((w + 1) ^ d * (((∑ g, (gates g).length) + d - 1).choose d + 1)) *
          2 ^ savingExponent := hscaled
    _ ≤ (Finset.univ.filter fun σ : Restriction n => stars σ = K).card := by
      rw [card_stars_eq (N := n) (K := K - d), card_stars_eq (N := n) (K := K)]
      exact hbalance

/-- If the trunk budget covers every live variable and fuel is ample, the canonical prefix trunk
already leaves every member residual at depth zero. -/
theorem commonShallowAt_zero_of_stars_le_fuel_le_trunk {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n) (trunkDepth : ℕ)
    (hstarsFuel : stars σ ≤ fuel) (hstarsTrunk : stars σ ≤ trunkDepth) :
    CommonShallowAt gates fuel σ trunkDepth 0 := by
  apply commonShallowAt_of_prefix_residual gates fuel σ trunkDepth 0
  intro x hext g
  have htrace : (CommonTree.trace
      (CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)) x).length ≤ trunkDepth :=
    (CommonTree.trace_readOnce_length_le_stars σ
      (canonicalFamilyTree gates fuel σ) x hext).trans hstarsTrunk
  have hend := CommonTree.prefixEndpoint_eq_pathEndpoint_of_trace_length_le
    σ (canonicalFamilyTree gates fuel σ) trunkDepth x htrace
  rw [CommonTree.prefixEndpoint] at hend
  rw [hend]
  exact Nat.le_of_eq (canonicalDT_depth_eq_zero_of_terminal (gates g)
    (CommonTree.pathEndpoint σ (canonicalFamilyTree gates fuel σ) x)
    (canonicalFamily_pathEndpoint_terminal gates fuel σ x hext hstarsFuel g) fuel)

/-- Any genuinely bad common-trunk instance with ample fuel must ask for fewer trunk queries than
there are live variables.  In particular, no sound semantic obstruction to `CommonShallowAt` can
force common-trunk cost strictly above the root's live-coordinate support: querying every live
coordinate always leaves residual depth zero, independently of the gate family. -/
theorem trunkDepth_lt_stars_of_not_commonShallowAt {n G : ℕ}
    {gates : Fin G → List (Clause n)} {fuel : ℕ} {σ : Restriction n}
    {trunkDepth residualDepth : ℕ} (hstarsFuel : stars σ ≤ fuel)
    (hbad : ¬CommonShallowAt gates fuel σ trunkDepth residualDepth) :
    trunkDepth < stars σ := by
  apply Nat.lt_of_not_ge
  intro hstarsTrunk
  apply hbad
  exact (commonShallowAt_zero_of_stars_le_fuel_le_trunk gates fuel σ trunkDepth
    hstarsFuel hstarsTrunk).mono (Nat.le_refl _) (Nat.zero_le _)

/-- Consequently the bad event is empty whenever its trunk budget is at least the exact shell
size and the shell fits within the available fuel. -/
theorem commonShallowBad_card_eq_zero_of_le_trunk {n G : ℕ}
    {gates : Fin G → List (Clause n)} {fuel K trunkDepth residualDepth : ℕ}
    (hKfuel : K ≤ fuel) (hKtrunk : K ≤ trunkDepth) :
    (commonShallowBad gates fuel K trunkDepth residualDepth).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro σ hσ
  obtain ⟨hstars, hbad⟩ := mem_commonShallowBad.mp hσ
  apply hbad
  exact (commonShallowAt_zero_of_stars_le_fuel_le_trunk gates fuel σ trunkDepth
    (hstars ▸ hKfuel) (hstars ▸ hKtrunk)).mono (Nat.le_refl _) (Nat.zero_le _)

/-- Exact arithmetic gate from the verified sparse count to proportional shell contraction.  The
displayed binomial/power balance is needed only in the nontrivial regime `trunkDepth K < K`;
full-budget trunks make the bad event empty, shells above the ambient dimension are empty, and
`n ≤ fuel` supplies ample fuel on every nonempty shell. -/
theorem commonShallowShellContraction_of_sparse_balance
    {n G w m fuel residualDepth savingNum savingDen : ℕ}
    {gates : Fin G → List (Clause n)} (trunkDepth : ℕ → ℕ)
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hgate : ∀ g, (gates g).length ≤ m)
    (hnfuel : n ≤ fuel)
    (hbalance : ∀ K, K ≤ n → trunkDepth K < K →
      (Nat.choose n (K - trunkDepth K) * 2 ^ (n - (K - trunkDepth K)) *
          (((trunkDepth K + 1) * 2 ^ trunkDepth K) * (w + 1) ^ trunkDepth K *
            (G * m + 1) ^ trunkDepth K)) *
          2 ^ ((savingNum * K) / savingDen) ≤
        Nat.choose n K * 2 ^ (n - K)) :
    CommonShallowShellContraction gates fuel residualDepth trunkDepth savingNum savingDen := by
  intro K
  by_cases hKn : K ≤ n
  · by_cases hdK : trunkDepth K < K
    · have hcount := commonShallowBad_card_le_of_ample_fuel_sparse_prefix
        (gates := gates) (w := w) (m := m) (d := trunkDepth K)
        (residualDepth := residualDepth)
        hnd hw hgate (hKn.trans hnfuel)
      have hscaled := Nat.mul_le_mul_right (2 ^ ((savingNum * K) / savingDen)) hcount
      calc
        (commonShallowBad gates fuel K (trunkDepth K) residualDepth).card *
            2 ^ ((savingNum * K) / savingDen) ≤
          ((Finset.univ.filter fun τ : Restriction n =>
              stars τ = K - trunkDepth K).card *
            (((trunkDepth K + 1) * 2 ^ trunkDepth K) * (w + 1) ^ trunkDepth K *
              (G * m + 1) ^ trunkDepth K)) *
            2 ^ ((savingNum * K) / savingDen) := hscaled
        _ ≤ (Finset.univ.filter fun σ : Restriction n => stars σ = K).card := by
          rw [card_stars_eq (N := n) (K := K - trunkDepth K),
            card_stars_eq (N := n) (K := K)]
          exact hbalance K hKn hdK
    · rw [commonShallowBad_card_eq_zero_of_le_trunk
          (hKn.trans hnfuel) (Nat.le_of_not_gt hdK)]
      simp
  · have hshell :
        (Finset.univ.filter fun σ : Restriction n => stars σ = K).card = 0 := by
      rw [card_stars_eq (N := n) (K := K),
        Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hKn)]
      simp
    have hbad :
        (commonShallowBad gates fuel K (trunkDepth K) residualDepth).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact (Finset.card_le_card commonShallowBad_subset_shell).trans_eq hshell
    simp [hbad, hshell]

/-- The polynomial-sized pieces of the current sparse label fit inside one exponential base. -/
theorem sparsePrefix_factor_le_pow {d e w q : ℕ} (he : e ≤ d) :
    2 ^ d * (((d + 1) * 2 ^ d) * (w + 1) ^ d * (q + 1) ^ d) * 2 ^ e ≤
      (16 * ((w + 1) * (q + 1))) ^ d := by
  have hsuccAll : ∀ k : ℕ, k + 1 ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        have hp : 1 ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        calc
          k + 1 + 1 ≤ 2 ^ k + 1 := Nat.add_le_add_right ih 1
          _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left hp (2 ^ k)
          _ = 2 ^ k * 2 := by ring
  have hsucc : d + 1 ≤ 2 ^ d := hsuccAll d
  have hpow : 2 ^ e ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) he
  calc
    2 ^ d * (((d + 1) * 2 ^ d) * (w + 1) ^ d * (q + 1) ^ d) * 2 ^ e ≤
        2 ^ d * (((2 ^ d) * 2 ^ d) * (w + 1) ^ d * (q + 1) ^ d) * 2 ^ d := by
          gcongr
    _ = (16 * ((w + 1) * (q + 1))) ^ d := by
      rw [show 16 * ((w + 1) * (q + 1)) =
        2 * 2 * 2 * 2 * (w + 1) * (q + 1) by ring]
      simp only [mul_pow]
      ring

/-- The exact sparse balance follows from a concrete low-density regime.  The factor `16` absorbs
the shorter-shell `2^d`, the label's `2^d`, `d+1 ≤ 2^d`, and the requested saving `2^e ≤ 2^d`. -/
theorem sparsePrefix_balance_of_density
    {n G w m K d savingNum savingDen : ℕ}
    (hdK : d ≤ K) (hKn : K ≤ n)
    (hsave : (savingNum * K) / savingDen ≤ d)
    (hdensity : (16 * ((w + 1) * (G * m + 1))) * K + K ≤ n + 1) :
    Nat.choose n (K - d) * 2 ^ (n - (K - d)) *
          (((d + 1) * 2 ^ d) * (w + 1) ^ d * (G * m + 1) ^ d) *
          2 ^ ((savingNum * K) / savingDen) ≤
        Nat.choose n K * 2 ^ (n - K) := by
  have hfactor := sparsePrefix_factor_le_pow
    (d := d) (e := (savingNum * K) / savingDen) (w := w) (q := G * m) hsave
  have hreg : (4 * (4 * ((w + 1) * (G * m + 1)))) * K + K ≤ n + 1 := by
    convert hdensity using 1 <;> ring
  have hbin := binomial_ratio_regime
    (w := 4 * ((w + 1) * (G * m + 1))) hdK hreg
  have hbin' :
      (16 * ((w + 1) * (G * m + 1))) ^ d * n.choose (K - d) ≤ n.choose K := by
    convert hbin using 1 <;> ring
  have hexp : n - (K - d) = n - K + d := by omega
  rw [hexp, pow_add]
  calc
    n.choose (K - d) * (2 ^ (n - K) * 2 ^ d) *
          (((d + 1) * 2 ^ d) * (w + 1) ^ d * (G * m + 1) ^ d) *
          2 ^ (savingNum * K / savingDen) =
        2 ^ (n - K) * n.choose (K - d) *
          (2 ^ d * (((d + 1) * 2 ^ d) * (w + 1) ^ d * (G * m + 1) ^ d) *
            2 ^ (savingNum * K / savingDen)) := by ring
    _ ≤ 2 ^ (n - K) * n.choose (K - d) *
          (16 * ((w + 1) * (G * m + 1))) ^ d := by gcongr
    _ = 2 ^ (n - K) *
          ((16 * ((w + 1) * (G * m + 1))) ^ d * n.choose (K - d)) := by ring
    _ ≤ 2 ^ (n - K) * n.choose K := Nat.mul_le_mul_left _ hbin'
    _ = n.choose K * 2 ^ (n - K) := by ring

/-! ### Exact realized-prefix shell audit

The symmetric-power label is a quotient of the corresponding word space.  This elementary
observation retains the exact stars-and-bars count in the bad-event theorem while giving a clean
power bound for shell arithmetic.  Compared with the sparse word label, it removes the transcript,
the `d+1` length code, and two powers of two from the density base. -/

/-- The total optional stars-and-bars code fits in a word over an alphabet enlarged by one symbol.
The positivity hypothesis is necessary: at `d = 0` the optional code has two elements. -/
theorem prefixSymCode_le_pow (A d : ℕ) (hd : 0 < d) :
    (A + d - 1).choose d + 1 ≤ (A + 1) ^ d := by
  have hcard : Fintype.card (Sym (Fin A) d) ≤
      Fintype.card (List.Vector (Fin A) d) := by
    apply Fintype.card_le_of_surjective Sym.ofVector
    intro s
    refine ⟨⟨s.1.toList, ?_⟩, ?_⟩
    · rw [Multiset.length_toList, s.2]
    · apply Sym.ext
      exact Multiset.coe_toList s.1
  rw [card_vector] at hcard
  simp only [Fintype.card_fin] at hcard
  have hsym := Sym.card_sym_eq_choose (α := Fin A) d
  simp only [Fintype.card_fin] at hsym
  rw [← hsym]
  calc
    Fintype.card (Sym (Fin A) d) + 1 ≤ A ^ d + 1 := Nat.add_le_add_right hcard 1
    _ = A ^ d + 1 ^ d := by simp
    _ ≤ (A + 1) ^ d :=
      pow_add_pow_le (by positivity) (by positivity) (Nat.ne_of_gt hd)

/-- A sharp obstruction before any quotient-to-word estimate is used.  At trunk depth one with
one bit of requested saving, the exact stars-and-bars balance forces
`4*(w+1)*(A+1) ≤ n`.  It is therefore false whenever the key alphabet `A` is already at least the
ambient live dimension.  This rules out a uniform all-shell repair from the factorial alone, but
does not decide the proportional-depth (`d ≍ K`) balance used by the scheduled half-shell round. -/
theorem not_realizedPrefix_exact_balance_one_of_live_le_keys
    {n A w : ℕ} (hn : 0 < n) (hle : n ≤ A) :
    ¬(Nat.choose n (1 - 1) * 2 ^ (n - (1 - 1)) *
          ((w + 1) ^ 1 * ((A + 1 - 1).choose 1 + 1)) * 2 ^ 1 ≤
        Nat.choose n 1 * 2 ^ (n - 1)) := by
  intro h
  simp only [Nat.sub_self, Nat.choose_zero_right, Nat.sub_zero, pow_one,
    Nat.add_sub_cancel, Nat.choose_one_right] at h
  have hp : 0 < 2 ^ (n - 1) := by positivity
  have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
    calc
      2 ^ n = 2 ^ (n - 1 + 1) := by congr 1; omega
      _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
  rw [hpow] at h
  have hc : (2 ^ (n - 1)) * (4 * (w + 1) * (A + 1)) ≤
      (2 ^ (n - 1)) * n := by
    convert h using 1 <;> ring
  have hsmall : 4 * (w + 1) * (A + 1) ≤ n :=
    Nat.le_of_mul_le_mul_left hc hp
  nlinarith

/-- The exact quotient does not repair the self-referential key regime at proportional depth
either.  At `K = 2*r`, `d = r`, and saving exponent `r`, the unrelaxed balance is impossible as
soon as the shell is nonempty and the ambient dimension is at most the key alphabet.  The proof
uses the two binomial factors directly: `choose n (2*r) ≤ (choose n r)^2`, while the
stars-and-bars factor is already at least `choose n r`. -/
theorem not_realizedPrefix_exact_balance_half_of_live_le_keys
    {n A w r : ℕ} (hr : 0 < r) (h2rn : 2 * r ≤ n) (hle : n ≤ A) :
    ¬(Nat.choose n (2 * r - r) * 2 ^ (n - (2 * r - r)) *
          ((w + 1) ^ r * ((A + r - 1).choose r + 1)) * 2 ^ r ≤
        Nat.choose n (2 * r) * 2 ^ (n - 2 * r)) := by
  intro h
  have hsub : 2 * r - r = r := by omega
  rw [hsub] at h
  have hexp : n - r = (n - 2 * r) + r := by omega
  rw [hexp, pow_add] at h
  have hp : 0 < 2 ^ (n - 2 * r) := by positivity
  have hc : n.choose r *
        (2 ^ (2 * r) * ((w + 1) ^ r * ((A + r - 1).choose r + 1))) ≤
      n.choose (2 * r) := by
    apply Nat.le_of_mul_le_mul_left _ hp
    convert h using 1 <;> ring
  have hAr : n ≤ A + r - 1 := by omega
  have hlabel : n.choose r ≤ (A + r - 1).choose r :=
    Nat.choose_le_choose r hAr
  have hchoose : n.choose (2 * r) ≤ n.choose r * n.choose r := by
    have hmul := Nat.choose_mul (n := n) (k := 2 * r) (s := r) (by omega)
    have hcentral : 0 < (2 * r).choose r := Nat.choose_pos (by omega)
    have hstep : n.choose (2 * r) ≤ n.choose r * (n - r).choose r := by
      apply Nat.le_of_mul_le_mul_left _ hcentral
      calc
        (2 * r).choose r * n.choose (2 * r) =
            n.choose (2 * r) * (2 * r).choose r := by ring
        _ = n.choose r * (n - r).choose r := by simpa [hsub] using hmul
        _ ≤ (2 * r).choose r * (n.choose r * (n - r).choose r) := by
          exact Nat.le_mul_of_pos_left _ hcentral
    exact hstep.trans (Nat.mul_le_mul_left _
      (Nat.choose_le_choose r (Nat.sub_le n r)))
  have hnr : 0 < n.choose r := Nat.choose_pos (by omega)
  have htwo : 2 ≤ 2 ^ (2 * r) := by
    calc
      2 = 2 ^ 1 := by simp
      _ ≤ 2 ^ (2 * r) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hstrict : n.choose r * n.choose r <
      n.choose r *
        (2 ^ (2 * r) * ((w + 1) ^ r * ((A + r - 1).choose r + 1))) := by
    apply Nat.mul_lt_mul_of_pos_left _ hnr
    have hwpos : 0 < (w + 1) ^ r := by positivity
    have hlabelStrict : n.choose r < (A + r - 1).choose r + 1 :=
      lt_of_le_of_lt hlabel (Nat.lt_succ_self _)
    calc
      n.choose r < (w + 1) ^ r * ((A + r - 1).choose r + 1) := by
        exact lt_of_lt_of_le hlabelStrict (Nat.le_mul_of_pos_left _ hwpos)
      _ < 2 ^ (2 * r) * ((w + 1) ^ r * ((A + r - 1).choose r + 1)) := by
        simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right
          (lt_of_lt_of_le Nat.one_lt_two htwo)
          (show 0 < (w + 1) ^ r * ((A + r - 1).choose r + 1) by positivity)
  exact (Nat.not_lt_of_ge hc) (hchoose.trans_lt hstrict)

/-- Necessary ambient bound for the exact proportional half-shell balance. -/
theorem realizedPrefix_exact_balance_half_keys_lt_live
    {n A w r : ℕ} (hr : 0 < r) (h2rn : 2 * r ≤ n)
    (hbalance :
      Nat.choose n (2 * r - r) * 2 ^ (n - (2 * r - r)) *
            ((w + 1) ^ r * ((A + r - 1).choose r + 1)) * 2 ^ r ≤
          Nat.choose n (2 * r) * 2 ^ (n - 2 * r)) :
    A < n := by
  apply Nat.lt_of_not_ge
  intro hle
  exact not_realizedPrefix_exact_balance_half_of_live_le_keys hr h2rn hle hbalance

/-- Including the downward-shell factor and a saving exponent `e ≤ d`, the realized-prefix label
has exponential base `4 (w+1)(A+1)`. -/
theorem realizedPrefix_factor_le_pow {d e w A : ℕ} (hd : 0 < d) (he : e ≤ d) :
    2 ^ d * ((w + 1) ^ d * ((A + d - 1).choose d + 1)) * 2 ^ e ≤
      (4 * ((w + 1) * (A + 1))) ^ d := by
  have hsym := prefixSymCode_le_pow A d hd
  have hsave : 2 ^ e ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) he
  calc
    2 ^ d * ((w + 1) ^ d * ((A + d - 1).choose d + 1)) * 2 ^ e ≤
        2 ^ d * ((w + 1) ^ d * (A + 1) ^ d) * 2 ^ d := by gcongr
    _ = (4 * ((w + 1) * (A + 1))) ^ d := by
      rw [show 4 * ((w + 1) * (A + 1)) =
        2 * 2 * (w + 1) * (A + 1) by ring]
      simp only [mul_pow]
      ring

/-- Exact stars-and-bars shell balance in a concrete low-density regime, parameterized by the
actual alphabet cardinality `A`. -/
theorem realizedPrefix_balance_of_actual_density
    {n w A K d savingNum savingDen : ℕ}
    (hdpos : 0 < d) (hdK : d ≤ K) (hKn : K ≤ n)
    (hsave : (savingNum * K) / savingDen ≤ d)
    (hdensity : (4 * ((w + 1) * (A + 1))) * K + K ≤ n + 1) :
    Nat.choose n (K - d) * 2 ^ (n - (K - d)) *
          ((w + 1) ^ d * ((A + d - 1).choose d + 1)) *
          2 ^ ((savingNum * K) / savingDen) ≤
        Nat.choose n K * 2 ^ (n - K) := by
  have hfactor := realizedPrefix_factor_le_pow
    (d := d) (e := (savingNum * K) / savingDen) (w := w) (A := A) hdpos hsave
  have hbin := binomial_ratio_regime
    (w := (w + 1) * (A + 1)) hdK hdensity
  have hexp : n - (K - d) = n - K + d := by omega
  rw [hexp, pow_add]
  calc
    n.choose (K - d) * (2 ^ (n - K) * 2 ^ d) *
          ((w + 1) ^ d * ((A + d - 1).choose d + 1)) *
          2 ^ (savingNum * K / savingDen) =
        2 ^ (n - K) * n.choose (K - d) *
          (2 ^ d * ((w + 1) ^ d * ((A + d - 1).choose d + 1)) *
            2 ^ (savingNum * K / savingDen)) := by ring
    _ ≤ 2 ^ (n - K) * n.choose (K - d) *
          (4 * ((w + 1) * (A + 1))) ^ d := by gcongr
    _ = 2 ^ (n - K) *
          ((4 * ((w + 1) * (A + 1))) ^ d * n.choose (K - d)) := by ring
    _ ≤ 2 ^ (n - K) * n.choose K := Nat.mul_le_mul_left _ hbin
    _ = n.choose K * 2 ^ (n - K) := by ring

/-- Rectangular corollary retained for callers that only know a uniform per-gate length bound. -/
theorem realizedPrefix_balance_of_density
    {n G w m K d savingNum savingDen : ℕ}
    (hdpos : 0 < d) (hdK : d ≤ K) (hKn : K ≤ n)
    (hsave : (savingNum * K) / savingDen ≤ d)
    (hdensity : (4 * ((w + 1) * (G * m + 1))) * K + K ≤ n + 1) :
    Nat.choose n (K - d) * 2 ^ (n - (K - d)) *
          ((w + 1) ^ d * ((G * m + d - 1).choose d + 1)) *
          2 ^ ((savingNum * K) / savingDen) ≤
        Nat.choose n K * 2 ^ (n - K) :=
  realizedPrefix_balance_of_actual_density hdpos hdK hKn hsave hdensity

/-- One-shell contraction obtained by combining the ample-fuel realized-prefix count with the
audited stars-and-bars balance. -/
theorem commonShallowBad_scaled_le_of_realized_density
    {n G w d m fuel K residualDepth savingNum savingDen : ℕ}
    {gates : Fin G → List (Clause n)}
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hgate : ∀ g, (gates g).length ≤ m)
    (hKfuel : K ≤ fuel) (hdpos : 0 < d) (hdK : d ≤ K) (hKn : K ≤ n)
    (hsave : (savingNum * K) / savingDen ≤ d)
    (hdensity : (4 * ((w + 1) * (G * m + 1))) * K + K ≤ n + 1) :
    (commonShallowBad gates fuel K d residualDepth).card *
        2 ^ ((savingNum * K) / savingDen) ≤
      (Finset.univ.filter fun σ : Restriction n => stars σ = K).card := by
  have hcount := commonShallowBad_card_le_of_ample_fuel_prefix_sym
    (gates := gates) (w := w) (m := m) (d := d) (residualDepth := residualDepth)
    hnd hw hgate hKfuel
  have hscaled := Nat.mul_le_mul_right (2 ^ ((savingNum * K) / savingDen)) hcount
  calc
    (commonShallowBad gates fuel K d residualDepth).card *
          2 ^ ((savingNum * K) / savingDen) ≤
        (Finset.univ.filter fun τ : Restriction n => stars τ = K - d).card *
          ((w + 1) ^ d * ((G * m + d - 1).choose d + 1)) *
          2 ^ ((savingNum * K) / savingDen) := hscaled
    _ ≤ (Finset.univ.filter fun σ : Restriction n => stars σ = K).card := by
      rw [card_stars_eq (N := n) (K := K - d), card_stars_eq (N := n) (K := K)]
      exact realizedPrefix_balance_of_density hdpos hdK hKn hsave hdensity

/-- One-shell contraction charging the exact total number of clause occurrences in a ragged
family, rather than a rectangular `G*m` envelope. -/
theorem commonShallowBad_scaled_le_of_actual_density
    {n G w d fuel K residualDepth savingNum savingDen : ℕ}
    {gates : Fin G → List (Clause n)}
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hKfuel : K ≤ fuel) (hdpos : 0 < d) (hdK : d ≤ K) (hKn : K ≤ n)
    (hsave : (savingNum * K) / savingDen ≤ d)
    (hdensity :
      (4 * ((w + 1) * ((∑ g, (gates g).length) + 1))) * K + K ≤ n + 1) :
    (commonShallowBad gates fuel K d residualDepth).card *
        2 ^ ((savingNum * K) / savingDen) ≤
      (Finset.univ.filter fun σ : Restriction n => stars σ = K).card := by
  apply commonShallowBad_scaled_le_of_actual_balance hnd hw hKfuel
  exact realizedPrefix_balance_of_actual_density hdpos hdK hKn hsave hdensity

/-- In the concrete growing-family scale `n = 1000 (G*m) r`, the realized-prefix encoder already
supports a genuinely half-shell trunk and a `2^(10*r)` saving.  Thus growth of `G*m` is absorbed by
the ambient dimension in this regime; no factorial refinement is needed for this one-shell bound. -/
theorem commonShallowBad_scaled_le_linearGap_realized
    {G m r fuel residualDepth : ℕ}
    {gates : Fin G → List (Clause (1000 * (G * m) * r))}
    (hG : 0 < G) (hm : 0 < m) (hr : 0 < r)
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ 2)
    (hgate : ∀ g, (gates g).length ≤ m)
    (hKfuel : 20 * r ≤ fuel) :
    (commonShallowBad gates fuel (20 * r) (10 * r) residualDepth).card *
        2 ^ (10 * r) ≤
      (Finset.univ.filter fun σ : Restriction (1000 * (G * m) * r) ↦
        stars σ = 20 * r).card := by
  have hA : 0 < G * m := Nat.mul_pos hG hm
  have hrA : r ≤ (G * m) * r := by
    calc
      r = 1 * r := by simp
      _ ≤ (G * m) * r := Nat.mul_le_mul_right r hA
  have hdpos : 0 < 10 * r := by omega
  have hdK : 10 * r ≤ 20 * r := by omega
  have hKn : 20 * r ≤ 1000 * (G * m) * r := by
    have : 20 ≤ 1000 * (G * m) := by nlinarith
    exact Nat.mul_le_mul_right r this
  have hsave : (1 * (20 * r)) / 2 ≤ 10 * r := by omega
  have hdensity :
      (4 * ((2 + 1) * (G * m + 1))) * (20 * r) + 20 * r ≤
        1000 * (G * m) * r + 1 := by
    norm_num
    nlinarith
  have hbound := commonShallowBad_scaled_le_of_realized_density
    (d := 10 * r) (w := 2) (residualDepth := residualDepth)
    (savingNum := 1) (savingDen := 2)
    hnd hw hgate hKfuel hdpos hdK hKn hsave hdensity
  have hhalf : (20 * r) / 2 = 10 * r := by omega
  simpa [hhalf] using hbound

/-- The concrete realized-prefix contraction has a genuine good root.  This is the strict
nonemptiness consequence missing from the scaled cardinality statement: positivity of `r` makes
the saving factor at least two, while positivity of `G`, `m`, and `r` makes the `20*r` shell
nonempty. -/
theorem exists_commonShallowAt_linearGap_realized
    {G m r fuel residualDepth : ℕ}
    {gates : Fin G → List (Clause (1000 * (G * m) * r))}
    (hG : 0 < G) (hm : 0 < m) (hr : 0 < r)
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ 2)
    (hgate : ∀ g, (gates g).length ≤ m)
    (hKfuel : 20 * r ≤ fuel) :
    ∃ σ : Restriction (1000 * (G * m) * r),
      stars σ = 20 * r ∧
      CommonShallowAt gates fuel σ (10 * r) residualDepth := by
  let shell := Finset.univ.filter fun σ : Restriction (1000 * (G * m) * r) ↦
    stars σ = 20 * r
  let bad := commonShallowBad gates fuel (20 * r) (10 * r) residualDepth
  have hscaled : bad.card * 2 ^ (10 * r) ≤ shell.card := by
    exact commonShallowBad_scaled_le_linearGap_realized
      hG hm hr hnd hw hgate hKfuel
  have hKn : 20 * r ≤ 1000 * (G * m) * r := by
    have hA : 0 < G * m := Nat.mul_pos hG hm
    have : 20 ≤ 1000 * (G * m) := by nlinarith
    exact Nat.mul_le_mul_right r this
  have hshellPos : 0 < shell.card := by
    rw [show shell.card = Nat.choose (1000 * (G * m) * r) (20 * r) *
        2 ^ (1000 * (G * m) * r - 20 * r) by
      simpa [shell] using card_stars_eq (1000 * (G * m) * r) (20 * r)]
    exact Nat.mul_pos (Nat.choose_pos hKn) (pow_pos (by omega) _)
  have hsaving : 2 ≤ 2 ^ (10 * r) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (10 * r) := Nat.pow_le_pow_right (by omega) (by omega)
  have hcard : bad.card < shell.card := by
    nlinarith
  obtain ⟨σ, hσshell, hσbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hstars : stars σ = 20 * r := by
    simpa [shell] using hσshell
  refine ⟨σ, hstars, ?_⟩
  by_contra hnot
  apply hσbad
  simpa [bad, mem_commonShallowBad] using ⟨hstars, hnot⟩

/-- A positive shell contraction theorem with the arithmetic balance discharged.  Its remaining
quantitative assumptions are explicit: the saving exponent fits within the trunk, and every
nontrivial shell lies in the sparse-density regime dictated by the current encoder base. -/
theorem commonShallowShellContraction_of_sparse_density
    {n G w m fuel residualDepth savingNum savingDen : ℕ}
    {gates : Fin G → List (Clause n)} (trunkDepth : ℕ → ℕ)
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hgate : ∀ g, (gates g).length ≤ m)
    (hnfuel : n ≤ fuel)
    (hsave : ∀ K, K ≤ n → (savingNum * K) / savingDen ≤ trunkDepth K)
    (hdensity : ∀ K, K ≤ n → trunkDepth K < K →
      (16 * ((w + 1) * (G * m + 1))) * K + K ≤ n + 1) :
    CommonShallowShellContraction gates fuel residualDepth trunkDepth savingNum savingDen := by
  apply commonShallowShellContraction_of_sparse_balance trunkDepth hnd hw hgate hnfuel
  intro K hKn hdK
  exact sparsePrefix_balance_of_density (Nat.le_of_lt hdK) hKn
    (hsave K hKn) (hdensity K hKn hdK)

/-- Use a half-shell trunk in the sparse regime and the full shell budget otherwise.  The latter
branch is quantitatively trivial but makes the positive contraction statement uniform over shells. -/
def densityAdaptiveTrunk (n base K : ℕ) : ℕ :=
  if base * K + K ≤ n + 1 then K / 2 else K

theorem half_le_densityAdaptiveTrunk (n base K : ℕ) :
    K / 2 ≤ densityAdaptiveTrunk n base K := by
  by_cases h : base * K + K ≤ n + 1
  · simp [densityAdaptiveTrunk, h]
  · simp [densityAdaptiveTrunk, h, Nat.div_le_self]

theorem density_of_densityAdaptiveTrunk_lt {n base K : ℕ}
    (hlt : densityAdaptiveTrunk n base K < K) : base * K + K ≤ n + 1 := by
  by_contra h
  simp [densityAdaptiveTrunk, h] at hlt

/-- Unconditional positive contraction for the adaptive trunk: sparse shells use depth `K/2`, while
dense shells use the full `K` budget and hence have an empty bad event.  This is a real positive
shell-mass theorem, but the dense-shell branch is not yet a useful shallow-trunk iteration bound. -/
theorem commonShallowShellContraction_densityAdaptive
    {n G w m fuel residualDepth : ℕ} {gates : Fin G → List (Clause n)}
    (hnd : ∀ g, (gates g).Nodup)
    (hw : ∀ g T, T ∈ gates g → T.lits.length ≤ w)
    (hgate : ∀ g, (gates g).length ≤ m)
    (hnfuel : n ≤ fuel) :
    CommonShallowShellContraction gates fuel residualDepth
      (densityAdaptiveTrunk n (16 * ((w + 1) * (G * m + 1)))) 1 2 := by
  apply commonShallowShellContraction_of_sparse_density
    (densityAdaptiveTrunk n (16 * ((w + 1) * (G * m + 1)))) hnd hw hgate hnfuel
  · intro K _
    simpa using half_le_densityAdaptiveTrunk n
      (16 * ((w + 1) * (G * m + 1))) K
  · intro K _ hlt
    exact density_of_densityAdaptiveTrunk_lt hlt

end PallLean.Paper93.DeepMath.PathB.MultiSwitching

#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalEnd_extends
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.prefixEndpoint_eq_pathEndpoint_of_trace_length_le
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalEnd_eq_pathEndpoint
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalEnd_terminal_of_stars_le_fuel
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalDT_depth_eq_zero_of_terminal
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.trunkDepth_lt_stars_of_not_commonShallowAt
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalDT_depth_canonicalEnd_eq_zero
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalDT_depth_pathEndpoint_eq_zero
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalGate_deep_prefix_implies_long_trace
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CanonicalTerminal.mono
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.gate_pathVars_subset_canonicalFamily
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalFamily_pathEndpoint_terminal
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalFamily_deep_prefix_implies_long_trace
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBadAssignment_long_of_le_fuel
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBadAssignment_endpointFiber_aggregate_exact
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBadAssignment_endpointLabelImage_aggregate_exact
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_card_le_of_ample_fuel_sparse_prefix
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_card_le_of_ample_fuel_prefix_counts
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_card_le_of_ample_fuel_prefix_sym
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_card_le_of_ample_fuel_prefix_actual_sym
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_card_le_of_ample_fuel_hybrid_prefix
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_card_le_of_ample_fuel_realized_hybrid
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowAt_zero_of_stars_le_fuel_le_trunk
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_card_eq_zero_of_le_trunk
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowShellContraction_of_sparse_balance
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.sparsePrefix_factor_le_pow
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.sparsePrefix_balance_of_density
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_scaled_le_of_realized_balance
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_scaled_le_of_actual_balance
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.prefixSymCode_le_pow
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.not_realizedPrefix_exact_balance_one_of_live_le_keys
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.not_realizedPrefix_exact_balance_half_of_live_le_keys
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.realizedPrefix_exact_balance_half_keys_lt_live
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.realizedPrefix_factor_le_pow
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.realizedPrefix_balance_of_actual_density
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.realizedPrefix_balance_of_density
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_scaled_le_of_realized_density
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_scaled_le_of_actual_density
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_scaled_le_linearGap_realized
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_commonShallowAt_linearGap_realized
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowShellContraction_of_sparse_density
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowShellContraction_densityAdaptive
