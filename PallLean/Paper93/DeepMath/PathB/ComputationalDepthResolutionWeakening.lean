import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionSemanticMeasure

/-!
# Weakening-augmented resolution and its width lower bound (size–width brick 2a)

The restriction of a tree-like resolution refutation (brick 2b) is **not** a plain
resolution derivation: when the pivot edge is fixed by the restriction, one parent
clause is satisfied and disappears, and the surviving parent's restricted clause
must be *weakened* up to the restricted resolvent.  So the natural target of the
restriction operation is resolution **with a weakening rule**.

This file defines that system (`WDerivation`: axioms, resolution, weakening), its
`size` (weakening is free — it adds no node) and `proofWidth`, and re-establishes
the **abstract BSW width lower bound** for it
(`WDerivation.proofWidth_ge_of_medium_wide`).  The only new ingredient over the
plain-resolution descent is measure *monotonicity* (`hmono`, supplied by
`SemanticMeasure.measure_mono`): a weakening `C ⊆ C'` cannot raise the measure, so
the medium-`μ` clause still appears along the derivation.

Consequently a width lower bound transfers verbatim to refutations produced by
restriction — exactly what brick 3 (the log-size recursion) needs to convert the
existing `proofWidth ≥ c·t` bound into an exponential **size** lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB

variable {Lit : Type*} [DecidableEq Lit]

/-- Tree-like resolution **with weakening**: axioms, resolution on a pivot, and a
weakening rule deriving any superclause `C'` of an already-derived clause `C`. -/
inductive WDerivation (compl : Lit → Lit) (Axiom : ResolutionClause Lit → Prop) :
    ResolutionClause Lit → Type _
  | ax {C : ResolutionClause Lit} (h : Axiom C) : WDerivation compl Axiom C
  | resolve {C D : ResolutionClause Lit}
      (L : WDerivation compl Axiom C) (R : WDerivation compl Axiom D) (p : Lit) :
      WDerivation compl Axiom (ResolutionClause.resolvent compl C D p)
  | weaken {C C' : ResolutionClause Lit}
      (D : WDerivation compl Axiom C) (h : C ⊆ C') :
      WDerivation compl Axiom C'

namespace WDerivation

variable {compl : Lit → Lit} {Axiom : ResolutionClause Lit → Prop}

/-- Number of resolution/axiom nodes; weakening is free (adds no node). -/
def size {C : ResolutionClause Lit} (D : WDerivation compl Axiom C) : Nat :=
  match D with
  | ax _ => 1
  | resolve L R _ => size L + size R + 1
  | weaken D _ => size D

/-- Maximum clause width appearing in the derivation. -/
def proofWidth {C : ResolutionClause Lit} (D : WDerivation compl Axiom C) : Nat :=
  match D with
  | ax (C := C) _ => ResolutionClause.width C
  | resolve (C := C) (D := Dp) L R p =>
      max (max (proofWidth L) (proofWidth R))
        (ResolutionClause.width (ResolutionClause.resolvent compl C Dp p))
  | weaken (C' := C') D _ => max (proofWidth D) (ResolutionClause.width C')

@[simp] theorem size_ax {C : ResolutionClause Lit} (h : Axiom C) :
    size (WDerivation.ax (compl := compl) h) = 1 := rfl

@[simp] theorem size_resolve {C D : ResolutionClause Lit}
    (L : WDerivation compl Axiom C) (R : WDerivation compl Axiom D) (p : Lit) :
    size (WDerivation.resolve L R p) = size L + size R + 1 := rfl

@[simp] theorem size_weaken {C C' : ResolutionClause Lit}
    (D : WDerivation compl Axiom C) (h : C ⊆ C') :
    size (WDerivation.weaken D h) = size D := rfl

@[simp] theorem proofWidth_ax {C : ResolutionClause Lit} (h : Axiom C) :
    proofWidth (WDerivation.ax (compl := compl) h) = ResolutionClause.width C := rfl

@[simp] theorem proofWidth_resolve {C D : ResolutionClause Lit}
    (L : WDerivation compl Axiom C) (R : WDerivation compl Axiom D) (p : Lit) :
    proofWidth (WDerivation.resolve L R p) =
      max (max (proofWidth L) (proofWidth R))
        (ResolutionClause.width (ResolutionClause.resolvent compl C D p)) := rfl

@[simp] theorem proofWidth_weaken {C C' : ResolutionClause Lit}
    (D : WDerivation compl Axiom C) (h : C ⊆ C') :
    proofWidth (WDerivation.weaken D h) = max (proofWidth D) (ResolutionClause.width C') := rfl

/-- `PivotsAvoid P D`: every resolution pivot used in the derivation `D` satisfies
the predicate `P`.  Used to certify that a derivation never resolves on a fixed
edge, so that the lift (re-adding a falsified literal) never collides with a pivot. -/
def PivotsAvoid (P : Lit → Prop) :
    {C : ResolutionClause Lit} → WDerivation compl Axiom C → Prop
  | _, ax _ => True
  | _, resolve L R p => P p ∧ PivotsAvoid P L ∧ PivotsAvoid P R
  | _, weaken D _ => PivotsAvoid P D

/-- `PivotsAvoid` is monotone in the predicate. -/
theorem PivotsAvoid.mono {P Q : Lit → Prop} (h : ∀ p, P p → Q p) :
    ∀ {C : ResolutionClause Lit} (D : WDerivation compl Axiom C),
      PivotsAvoid P D → PivotsAvoid Q D
  | _, ax _, _ => trivial
  | _, resolve L R p, hD => by
      obtain ⟨hp, hL, hR⟩ := hD
      exact ⟨h p hp, PivotsAvoid.mono h L hL, PivotsAvoid.mono h R hR⟩
  | _, weaken D _, hD => PivotsAvoid.mono h D hD

/-- **Abstract BSW width lower bound for weakening-resolution.**  If `μ` is
subadditive on resolvents, *monotone* (a superclause has no larger measure),
axioms have `μ ≤ a < 2t`, the root has `μ ≥ t`, and every medium-`μ` clause
(`t ≤ μ < 2t`) is wide (`width ≥ W`), then every derivation has `proofWidth ≥ W`.

The weakening case uses `hmono`: a weakening `C ⊆ C'` keeps `μ C ≥ μ C' ≥ t`, so
the wide medium clause is still forced in the sub-derivation. -/
theorem proofWidth_ge_of_medium_wide
    {a t W : Nat}
    (μ : ResolutionClause Lit → Nat)
    (hsub : ∀ {C D : ResolutionClause Lit} (p : Lit),
        μ (ResolutionClause.resolvent compl C D p) ≤ μ C + μ D)
    (hmono : ∀ {C C' : ResolutionClause Lit}, C ⊆ C' → μ C' ≤ μ C)
    (hax : ∀ {C : ResolutionClause Lit}, Axiom C → μ C ≤ a)
    (ht : a < 2 * t)
    (hwide : ∀ {C : ResolutionClause Lit}, t ≤ μ C → μ C < 2 * t →
        W ≤ ResolutionClause.width C)
    {Target : ResolutionClause Lit}
    (Der : WDerivation compl Axiom Target) :
    t ≤ μ Target → W ≤ proofWidth Der := by
  induction Der with
  | ax h =>
      intro hroot
      rw [proofWidth_ax]
      exact hwide hroot (lt_of_le_of_lt (hax h) ht)
  | @resolve C Dp L R p ihL ihR =>
      intro hroot
      rw [proofWidth_resolve]
      by_cases hlt : μ (ResolutionClause.resolvent compl C Dp p) < 2 * t
      · exact le_trans (hwide hroot hlt) (le_max_right _ _)
      · push_neg at hlt
        have hsum : 2 * t ≤ μ C + μ Dp := le_trans hlt (hsub p)
        rcases Nat.lt_or_ge (μ C) t with hC | hC
        · exact le_trans (ihR (by omega)) (le_trans (le_max_right _ _) (le_max_left _ _))
        · exact le_trans (ihL hC) (le_trans (le_max_left _ _) (le_max_left _ _))
  | @weaken C C' D h ih =>
      intro hroot
      rw [proofWidth_weaken]
      exact le_trans (ih (le_trans hroot (hmono h))) (le_max_left _ _)

end WDerivation

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.WDerivation.proofWidth_ge_of_medium_wide
