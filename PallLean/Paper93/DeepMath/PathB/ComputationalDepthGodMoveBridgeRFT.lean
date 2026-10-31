/-!
# The God-Move bridge in relational-frame form: observer (in)equivalence and its exact circularity

Darren's proposal: in an RFT-style relational frame the two observers — the **P-class** observer and
the **God/NP-class** observer — are NOT equivalent, because they have different *thermodynamic
boundaries*; different boundaries ⟹ not in the same equivalence class ⟹ unequal ⟹ `P ≠ NP`.  With
the honest caveat, in Darren's own words: *"something about this knowledge seems to assume the
inequality is true."*

This file formalises the argument to see which half is which — and it confirms **both** of Darren's
instincts, precisely:

1. **The reframing is CORRECT — and it is even an `iff`.**  Observer equivalence is *equivalent* to
   `SAT ∈ P` (`equiv_iff_sat_in_P`), so the observers being UNEQUAL is *exactly* `SAT ∉ P`.  His
   instinct that non-equivalent observers ⟹ the separation is right (this is the God-Move / mirror /
   `DischargePiStar` identification, in relational-frame clothing).

2. **The caveat is CORRECT — the thermodynamic BOUNDARY does not deliver it.**  The boundary
   difference actually available (poly budget vs unbounded budget) is CONSISTENT with equivalence
   (`budget_diff_consistent_with_equiv`): there is a world where the budgets differ yet the reachable
   sets coincide (a `P = NP`-like world).  So "different budget" cannot force non-equivalence.  The
   only boundary difference that yields non-equivalence is a difference in the *reachable set* — which
   IS non-equivalence, i.e. the separation itself.

So the knowledge "the boundaries differ *materially*" assumes `SAT ∉ P`.  This is the gauge
circularity the corpus keeps meeting (`curvature_is_cost_super`, `MirrorDuality`, `CappedObserver`,
`KnowingClass`): the frame is correct and the identification is exact, but the *reading* — that the
budget gap bites on SAT — is `cost_super`.  Nothing here proves `P ≠ NP`, and nothing here makes it
unprovable; it pins the argument to the wall.
-/

namespace PallLean.Paper93.DeepMath.PathB.GodMoveBridgeRFT

/-- An **observer** is its reachable set: the problems it decides within its thermodynamic boundary.
`O x` means "observer `O` decides problem `x`". -/
abbrev Observer (Problem : Type) := Problem → Prop

/-- **Observer equivalence** (the RFT equivalence class / mutual substitutability): the two observers
decide exactly the same problems. -/
def ObsEquiv {Problem : Type} (O₁ O₂ : Observer Problem) : Prop := ∀ x, O₁ x ↔ O₂ x

/-! ### The reframing: equivalence ⟺ SAT ∈ P -/

/-- **`P ⊆ G` is free, so equivalence reduces to the reverse inclusion (proved).**  The God-observer
(unbounded) reaches everything the P-observer does; equivalence therefore holds iff the *reverse*
inclusion `G ⊆ P` does — and that reverse inclusion is the open direction. -/
theorem equiv_iff_reverse_incl {Problem : Type} (P G : Observer Problem)
    (hPG : ∀ x, P x → G x) :
    ObsEquiv P G ↔ (∀ x, G x → P x) := by
  constructor
  · intro h x hx; exact (h x).mpr hx
  · intro h x; exact ⟨hPG x, h x⟩

/-- **Observer equivalence IS `SAT ∈ P` (proved).**  With `P ⊆ G` free, `G sat` free (God decides
SAT), and SAT NP-complete (`complete`: if `SAT ∈ P` then all of `G` compiles into `P`), the two
observers are equivalent exactly when `SAT ∈ P`.  Hence asserting they are UNEQUAL is asserting
`SAT ∉ P` — the inequality itself. -/
theorem equiv_iff_sat_in_P {Problem : Type} (P G : Observer Problem) (sat : Problem)
    (hPG : ∀ x, P x → G x) (hGsat : G sat) (complete : P sat → ∀ x, G x → P x) :
    ObsEquiv P G ↔ P sat := by
  rw [equiv_iff_reverse_incl P G hPG]
  constructor
  · intro h; exact h sat hGsat
  · intro h; exact complete h

/-- **Non-equivalence ⟺ the separation (proved).**  Darren's instinct, exactly: the observers being
unequal is `SAT ∉ P`. -/
theorem nonequiv_iff_separation {Problem : Type} (P G : Observer Problem) (sat : Problem)
    (hPG : ∀ x, P x → G x) (hGsat : G sat) (complete : P sat → ∀ x, G x → P x) :
    ¬ ObsEquiv P G ↔ ¬ P sat := by
  constructor
  · intro h hsat; exact h ((equiv_iff_sat_in_P P G sat hPG hGsat complete).mpr hsat)
  · intro h heq; exact h ((equiv_iff_sat_in_P P G sat hPG hGsat complete).mp heq)

/-! ### The circularity: the thermodynamic boundary does not deliver non-equivalence -/

/-- The **thermodynamic boundary** (resource budget) of an observer: the P-observer is `poly`, the
God-observer is `unbounded`. -/
inductive Budget where
  | poly
  | unbounded

/-- Two boundaries *differ* as budgets — the "different thermodynamic boundary" Darren cites. -/
def BudgetDiffers (bP bG : Budget) : Prop := bP ≠ bG

/-- **The budget difference is CONSISTENT with equivalence (proved) — the circularity.**  There is a
world where the two observers have different budgets (`poly ≠ unbounded`) yet identical reachable sets
(both decide everything — a `P = NP`-like world).  So a different thermodynamic *budget* does NOT
force non-equivalence: it cannot, on its own, deliver the separation. -/
theorem budget_diff_consistent_with_equiv (Problem : Type) :
    ∃ (P G : Observer Problem) (bP bG : Budget),
      BudgetDiffers bP bG ∧ (∀ x, P x → G x) ∧ ObsEquiv P G := by
  refine ⟨(fun _ => True), (fun _ => True), Budget.poly, Budget.unbounded, ?_, ?_, ?_⟩
  · intro h; exact Budget.noConfusion h
  · intro _ h; exact h
  · intro _; exact ⟨id, id⟩

/-- **The only boundary difference that yields non-equivalence is the reachable-set difference =
the separation (proved).**  Restating `nonequiv_iff_separation`: the "material" boundary difference
(different reachable sets) is definitionally non-equivalence, which is `SAT ∉ P`.  Combined with
`budget_diff_consistent_with_equiv`, this is the exact content of Darren's caveat: the knowledge that
the boundaries differ *materially* already assumes the inequality. -/
theorem material_boundary_diff_is_separation {Problem : Type} (P G : Observer Problem) (sat : Problem)
    (hPG : ∀ x, P x → G x) (hGsat : G sat) (complete : P sat → ∀ x, G x → P x) :
    ¬ ObsEquiv P G ↔ ¬ P sat :=
  nonequiv_iff_separation P G sat hPG hGsat complete

end PallLean.Paper93.DeepMath.PathB.GodMoveBridgeRFT

#print axioms PallLean.Paper93.DeepMath.PathB.GodMoveBridgeRFT.equiv_iff_reverse_incl
#print axioms PallLean.Paper93.DeepMath.PathB.GodMoveBridgeRFT.equiv_iff_sat_in_P
#print axioms PallLean.Paper93.DeepMath.PathB.GodMoveBridgeRFT.nonequiv_iff_separation
#print axioms PallLean.Paper93.DeepMath.PathB.GodMoveBridgeRFT.budget_diff_consistent_with_equiv
#print axioms PallLean.Paper93.DeepMath.PathB.GodMoveBridgeRFT.material_boundary_diff_is_separation
