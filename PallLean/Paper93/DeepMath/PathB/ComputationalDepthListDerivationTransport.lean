import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivation

/-!
# Grafting list derivations onto a context

The general tool for the asymmetric recombination.  If `M` is already a valid
derivation over `Q`, and every `P`-axiom can be *re-justified* relative to `M`
(as a `Q`-axiom, a resolvent of two clauses of `M`, or a superclause of one), then
any derivation over `P` transports onto `M`: `L ++ M` is a valid derivation over
`Q`.  Because the model references earlier clauses **by value** and `M` sits in the
tail of `L ++ M`, every re-justification witness is available.

This is exactly what lets the recombination re-derive the restricted axioms of one
branch from the unit clause produced by the other branch, at no structural cost.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace LDeriv

variable {Lit : Type*} [DecidableEq Lit] {compl : Lit → Lit}

/-- A clause `C` is justified relative to a context list `M` over axioms `Q`: it is
a `Q`-axiom, the resolvent of two clauses of `M`, or a superclause of one. -/
def Justified (compl : Lit → Lit) (Q : ResolutionClause Lit → Prop)
    (M : List (ResolutionClause Lit)) (C : ResolutionClause Lit) : Prop :=
  Q C ∨
  (∃ D E p, D ∈ M ∧ E ∈ M ∧ C = ResolutionClause.resolvent compl D E p) ∨
  (∃ D, D ∈ M ∧ D ⊆ C)

/-- **Trivial derivation from axioms.**  Any list of axiom clauses is a derivation. -/
theorem ofAxioms {Axiom : ResolutionClause Lit → Prop} :
    ∀ {M : List (ResolutionClause Lit)}, (∀ C ∈ M, Axiom C) → LDeriv compl Axiom M
  | [], _ => LDeriv.nil
  | C :: M, hM =>
    LDeriv.cons (Or.inl (hM C (List.mem_cons.mpr (Or.inl rfl))))
      (ofAxioms (fun C' hC' => hM C' (List.mem_cons.mpr (Or.inr hC'))))

/-- **Transport / graft.**  A derivation over `P` grafts onto a context derivation
`M` over `Q`, provided every `P`-axiom is justified relative to `M`. -/
theorem transport {P Q : ResolutionClause Lit → Prop} {L M : List (ResolutionClause Lit)}
    (hM : LDeriv compl Q M) (hre : ∀ C, P C → Justified compl Q M C)
    (h : LDeriv compl P L) :
    LDeriv compl Q (L ++ M) := by
  induction h with
  | nil => exact hM
  | @cons C L just h ih =>
    refine LDeriv.cons ?_ ih
    rcases just with hax | ⟨D, E, p, hD, hE, heq⟩ | ⟨D, hD, hsub⟩
    · rcases hre C hax with hQ | ⟨D, E, p, hDM, hEM, he⟩ | ⟨D, hDM, hsub⟩
      · exact Or.inl hQ
      · exact Or.inr (Or.inl ⟨D, E, p,
          List.mem_append_right _ hDM, List.mem_append_right _ hEM, he⟩)
      · exact Or.inr (Or.inr ⟨D, List.mem_append_right _ hDM, hsub⟩)
    · exact Or.inr (Or.inl ⟨D, E, p,
        List.mem_append_left _ hD, List.mem_append_left _ hE, heq⟩)
    · exact Or.inr (Or.inr ⟨D, List.mem_append_left _ hD, hsub⟩)

/-- Membership of the empty clause is preserved by appending a context (left). -/
theorem mem_append_empty_left {L M : List (ResolutionClause Lit)}
    (h : (∅ : ResolutionClause Lit) ∈ L) :
    (∅ : ResolutionClause Lit) ∈ L ++ M :=
  List.mem_append_left _ h

/-- Width bound for an appended derivation. -/
theorem width_append_le {L M : List (ResolutionClause Lit)} {W : ℕ}
    (hL : ∀ C ∈ L, ResolutionClause.width C ≤ W)
    (hMw : ∀ C ∈ M, ResolutionClause.width C ≤ W) :
    ∀ C ∈ L ++ M, ResolutionClause.width C ≤ W := by
  intro C hC
  rcases List.mem_append.mp hC with h | h
  · exact hL C h
  · exact hMw C h

end LDeriv

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.ofAxioms
#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.transport
