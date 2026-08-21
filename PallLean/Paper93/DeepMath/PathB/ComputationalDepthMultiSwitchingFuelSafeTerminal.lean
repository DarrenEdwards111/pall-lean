import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwitchingCommonShallow
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SatRecovery
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingProcessedUnsat

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

end PallLean.Paper93.DeepMath.PathB.MultiSwitching

#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalEnd_extends
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.prefixEndpoint_eq_pathEndpoint_of_trace_length_le
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalEnd_eq_pathEndpoint
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalEnd_terminal_of_stars_le_fuel
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalDT_depth_eq_zero_of_terminal
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalDT_depth_canonicalEnd_eq_zero
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalDT_depth_pathEndpoint_eq_zero
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalGate_deep_prefix_implies_long_trace
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CanonicalTerminal.mono
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.gate_pathVars_subset_canonicalFamily
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalFamily_pathEndpoint_terminal
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalFamily_deep_prefix_implies_long_trace
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBadAssignment_long_of_le_fuel
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_card_le_of_ample_fuel_sparse_prefix
