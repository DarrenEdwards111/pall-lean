import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwitchingCommonShallow

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

end PallLean.Paper93.DeepMath.PathB.MultiSwitching

#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalEnd_extends
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.prefixEndpoint_eq_pathEndpoint_of_trace_length_le
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalEnd_eq_pathEndpoint
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalEnd_terminal_of_stars_le_fuel
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalDT_depth_eq_zero_of_terminal
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalDT_depth_canonicalEnd_eq_zero
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalDT_depth_pathEndpoint_eq_zero
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalGate_deep_prefix_implies_long_trace
