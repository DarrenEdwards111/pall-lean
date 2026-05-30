import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionMediumClause

/-!
# The semantic resolution measure and its subadditivity (BSW foundation 1)

The Ben-Sasson–Wigderson width argument runs through the measure
`μ(C) = min { |S| : the constraints indexed by S semantically imply C }`.
This file builds that measure **generically** over any constraint family and any
literal-satisfaction relation, and proves the two facts the abstract width bound
(`ResolutionDerivation.proofWidth_ge_of_medium_wide`) needs from it:

* `measure_resolvent_le` — **subadditivity**: `μ(resolvent C D p) ≤ μ C + μ D`,
  the heart of the descent.  It is generic: it is exactly the soundness of
  resolution (a resolvent is implied by its parents), needing only that a literal
  and its complement are never simultaneously satisfied (`hcons`).
* `measure_le_of_implies`, `exists_implies_measure` — `μ` is the attained minimum
  (well-defined because the full constraint set is globally unsatisfiable,
  `hunsat`, so it implies every clause vacuously — the refutation setting).

The Tseitin instantiation (charges/parities for `Constr`, edge literals for
`Sat`) plus the expansion→width link and the root bound `μ(⊥) ≥ n` are the
remaining bricks.
-/

namespace PallLean.Paper93.DeepMath.PathB.SemanticMeasure

open PallLean.Paper93.DeepMath.PathB

variable {Lit : Type*} [DecidableEq Lit] {α ι : Type*} [Fintype ι] [DecidableEq ι]
  (Sat : α → Lit → Prop) (Constr : ι → α → Prop)

/-- A clause is satisfied if some literal in it is satisfied. -/
def clauseSat (a : α) (C : ResolutionClause Lit) : Prop := ∃ l ∈ C, Sat a l

/-- `S` (a set of constraint indices) semantically implies clause `C`. -/
def Implies (S : Finset ι) (C : ResolutionClause Lit) : Prop :=
  ∀ a, (∀ i ∈ S, Constr i a) → clauseSat Sat a C

/-- The BSW measure: the least number of constraints semantically implying `C`. -/
noncomputable def measure (C : ResolutionClause Lit) : ℕ :=
  sInf {n | ∃ S : Finset ι, S.card = n ∧ Implies Sat Constr S C}

/-- If the constraint family is globally unsatisfiable, the full set implies every
clause (vacuously) — so the measure is over a nonempty set. -/
theorem implies_univ (hunsat : ∀ a : α, ∃ i, ¬ Constr i a) (C : ResolutionClause Lit) :
    Implies Sat Constr Finset.univ C := by
  intro a ha
  obtain ⟨i, hi⟩ := hunsat a
  exact absurd (ha i (Finset.mem_univ i)) hi

theorem measure_set_nonempty (hunsat : ∀ a : α, ∃ i, ¬ Constr i a) (C : ResolutionClause Lit) :
    {n | ∃ S : Finset ι, S.card = n ∧ Implies Sat Constr S C}.Nonempty :=
  ⟨Finset.univ.card, Finset.univ, rfl, implies_univ Sat Constr hunsat C⟩

/-- `μ` is a lower bound: any implying set has card `≥ μ`. -/
theorem measure_le_of_implies {S : Finset ι} {C : ResolutionClause Lit}
    (h : Implies Sat Constr S C) : measure Sat Constr C ≤ S.card :=
  Nat.sInf_le ⟨S, rfl, h⟩

/-- The minimum is attained: there is an implying set of card exactly `μ C`. -/
theorem exists_implies_measure (hunsat : ∀ a : α, ∃ i, ¬ Constr i a) (C : ResolutionClause Lit) :
    ∃ S : Finset ι, Implies Sat Constr S C ∧ S.card = measure Sat Constr C := by
  obtain ⟨S, hcard, himp⟩ := Nat.sInf_mem (measure_set_nonempty Sat Constr hunsat C)
  exact ⟨S, himp, hcard⟩

/-- Clause satisfaction is monotone in the clause: a superclause is easier to satisfy. -/
theorem clauseSat_mono {a : α} {C C' : ResolutionClause Lit} (h : C ⊆ C') :
    clauseSat Sat a C → clauseSat Sat a C' :=
  fun ⟨l, hl, hsl⟩ => ⟨l, h hl, hsl⟩

/-- Semantic implication is monotone in the clause: `S ⊨ C` and `C ⊆ C'` give `S ⊨ C'`. -/
theorem implies_mono {S : Finset ι} {C C' : ResolutionClause Lit} (h : C ⊆ C') :
    Implies Sat Constr S C → Implies Sat Constr S C' :=
  fun himp a ha => clauseSat_mono Sat h (himp a ha)

/-- **Monotonicity of the measure**: a superclause has no larger measure
(`C ⊆ C' → μ C' ≤ μ C`).  This is what makes a *weakening* step harmless for the
descent — the input the weakening-augmented width lower bound needs. -/
theorem measure_mono (hunsat : ∀ a : α, ∃ i, ¬ Constr i a)
    {C C' : ResolutionClause Lit} (h : C ⊆ C') :
    measure Sat Constr C' ≤ measure Sat Constr C := by
  obtain ⟨S, himp, hcard⟩ := exists_implies_measure Sat Constr hunsat C
  calc measure Sat Constr C'
      ≤ S.card := measure_le_of_implies Sat Constr (implies_mono Sat Constr h himp)
    _ = measure Sat Constr C := hcard

/-- **Resolution soundness for clause satisfaction.**  A resolvent is satisfied by
any assignment satisfying both parents, provided a literal and its complement are
never both satisfied. -/
theorem clauseSat_resolvent (compl : Lit → Lit)
    (hcons : ∀ (a : α) (l : Lit), Sat a l → ¬ Sat a (compl l))
    {a : α} {C D : ResolutionClause Lit} {p : Lit}
    (hC : clauseSat Sat a C) (hD : clauseSat Sat a D) :
    clauseSat Sat a (ResolutionClause.resolvent compl C D p) := by
  obtain ⟨l, hlC, hl⟩ := hC
  rcases eq_or_ne l p with hlp | hlp
  · obtain ⟨l', hlD, hl'⟩ := hD
    rcases eq_or_ne l' (compl p) with hl'p | hl'p
    · exact absurd (hl'p ▸ hl' : Sat a (compl p)) (hcons a p (hlp ▸ hl))
    · exact ⟨l', Finset.mem_union.mpr (Or.inr (Finset.mem_erase.mpr ⟨hl'p, hlD⟩)), hl'⟩
  · exact ⟨l, Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hlp, hlC⟩)), hl⟩

/-- Implication is closed under resolution: `S ⊨ C` and `T ⊨ D` give `S∪T ⊨ resolvent`. -/
theorem implies_resolvent (compl : Lit → Lit)
    (hcons : ∀ (a : α) (l : Lit), Sat a l → ¬ Sat a (compl l))
    {S T : Finset ι} {C D : ResolutionClause Lit} {p : Lit}
    (hC : Implies Sat Constr S C) (hD : Implies Sat Constr T D) :
    Implies Sat Constr (S ∪ T) (ResolutionClause.resolvent compl C D p) := by
  intro a ha
  exact clauseSat_resolvent Sat compl hcons
    (hC a (fun i hi => ha i (Finset.mem_union.mpr (Or.inl hi))))
    (hD a (fun i hi => ha i (Finset.mem_union.mpr (Or.inr hi))))

/-- **Subadditivity of the measure** (the BSW descent input `hsub`):
`μ(resolvent C D p) ≤ μ C + μ D`. -/
theorem measure_resolvent_le (compl : Lit → Lit)
    (hcons : ∀ (a : α) (l : Lit), Sat a l → ¬ Sat a (compl l))
    (hunsat : ∀ a : α, ∃ i, ¬ Constr i a)
    (C D : ResolutionClause Lit) (p : Lit) :
    measure Sat Constr (ResolutionClause.resolvent compl C D p)
      ≤ measure Sat Constr C + measure Sat Constr D := by
  obtain ⟨S, hSimp, hScard⟩ := exists_implies_measure Sat Constr hunsat C
  obtain ⟨T, hTimp, hTcard⟩ := exists_implies_measure Sat Constr hunsat D
  calc measure Sat Constr (ResolutionClause.resolvent compl C D p)
      ≤ (S ∪ T).card :=
        measure_le_of_implies Sat Constr (implies_resolvent Sat Constr compl hcons hSimp hTimp)
    _ ≤ S.card + T.card := Finset.card_union_le _ _
    _ = measure Sat Constr C + measure Sat Constr D := by rw [hScard, hTcard]

end PallLean.Paper93.DeepMath.PathB.SemanticMeasure

#print axioms PallLean.Paper93.DeepMath.PathB.SemanticMeasure.measure_resolvent_le
#print axioms PallLean.Paper93.DeepMath.PathB.SemanticMeasure.exists_implies_measure
