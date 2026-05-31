import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivationTransport
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivationLift
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionGraft

/-!
# The asymmetric branching recombination

The heart of the general (DAG) size–width method.  From a width-`w₁` refutation of
`F|_{ℓ}` and a width-`w₀` refutation of `F|_{¬ℓ}`, build a refutation of `F` of
width `≤ max(max w₀ (w₁+1)) wF`:

* **lift** the `F|_{ℓ}` refutation by `¬ℓ` (paying `+1`), producing the unit
  clause `{¬ℓ}` from (weakenings of) the axioms — `transport`ed onto the axioms;
* **graft** the `F|_{¬ℓ}` refutation on top, re-deriving each of its restricted
  axioms `C.erase ℓ` as the resolvent `resolvent C {¬ℓ} ℓ` (paying `+0`, the unit
  graft identity) using the `{¬ℓ}` just produced.

Only the first branch pays `+1`; this asymmetry is what yields the `√(n ln S)`
width bound under the double induction.  Axioms are taken as an explicit list `Ax`
(as for a concrete CNF such as Tseitin), so the re-derivations can reference them.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace LDeriv

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

variable {Lit : Type*} [DecidableEq Lit]

/-- Any clause is contained in `insert a (C.erase a)`. -/
theorem subset_insert_erase (C : ResolutionClause Lit) (a : Lit) :
    C ⊆ insert a (C.erase a) := by
  intro x hx
  by_cases h : x = a
  · subst h; exact Finset.mem_insert_self x _
  · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h, hx⟩)

/-- A formula `Axiom`, given as the predicate of membership in an explicit clause
list `Ax`, is **refutable in width `w`** if some derivation over it contains `∅`
with all clauses of width `≤ w`. -/
def RefutableWidth (compl : Lit → Lit) (Axiom : ResolutionClause Lit → Prop) (w : ℕ) : Prop :=
  ∃ L, LDeriv compl Axiom L ∧ (∅ : ResolutionClause Lit) ∈ L ∧
    (∀ C ∈ L, ResolutionClause.width C ≤ w)

/-- The axioms of `F` restricted by setting literal `ℓ` to true: drop the falsified
`compl ℓ` from each `ℓ`-free axiom. -/
def restrictedAxiom (compl : Lit → Lit) (Ax : List (ResolutionClause Lit)) (ℓ : Lit) :
    ResolutionClause Lit → Prop :=
  fun C' => ∃ C, C ∈ Ax ∧ ℓ ∉ C ∧ C.erase (compl ℓ) = C'

variable {Edge : Type*} [DecidableEq Edge]

theorem tcompl_tcompl (l : TLit Edge) : tcompl (tcompl l) = l := by
  show (l.1, l.2 + 1 + 1) = l
  rw [add_assoc, show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]

/-- **Asymmetric branching recombination.**  Refutations of `F|_{ℓ}` (width `w₁`)
and `F|_{¬ℓ}` (width `w₀`) combine into a refutation of `F` of width
`≤ max (max w₀ (w₁+1)) wF`, where `wF` bounds the axiom widths.  Only the
`F|_{ℓ}` branch pays the `+1`. -/
theorem asym_recombination (Ax : List (ResolutionClause (TLit Edge))) (ℓ : TLit Edge)
    {w0 w1 wF : ℕ} (hAx : ∀ C ∈ Ax, ResolutionClause.width C ≤ wF)
    (h1 : RefutableWidth tcompl (restrictedAxiom tcompl Ax ℓ) w1)
    (h0 : RefutableWidth tcompl (restrictedAxiom tcompl Ax (tcompl ℓ)) w0) :
    RefutableWidth tcompl (· ∈ Ax) (max (max w0 (w1 + 1)) wF) := by
  obtain ⟨L1, hLD1, hmt1, hw1⟩ := h1
  obtain ⟨L0, hLD0, hmt0, hw0⟩ := h0
  -- context: the axioms as a trivial derivation
  have hMax : LDeriv tcompl (· ∈ Ax) Ax := ofAxioms (fun C h => h)
  -- lift the F|ℓ refutation by ¬ℓ, then graft onto the axioms (weakenings)
  have hlift := LDeriv.lift (tcompl ℓ) hLD1
  have hre1 : ∀ C'', (∃ C', restrictedAxiom tcompl Ax ℓ C' ∧ insert (tcompl ℓ) C' = C'') →
      Justified tcompl (· ∈ Ax) Ax C'' := by
    rintro C'' ⟨C', ⟨C, hC, _, hCe⟩, hins⟩
    refine Or.inr (Or.inr ⟨C, hC, ?_⟩)
    rw [← hins, ← hCe]
    exact subset_insert_erase C (tcompl ℓ)
  have hM1 : LDeriv tcompl (· ∈ Ax) (L1.map (insert (tcompl ℓ)) ++ Ax) :=
    transport hMax hre1 hlift
  -- the unit {¬ℓ} sits in the context
  have hunit : ({tcompl ℓ} : ResolutionClause (TLit Edge))
      ∈ L1.map (insert (tcompl ℓ)) ++ Ax :=
    List.mem_append_left _ (LDeriv.lift_unit_mem (tcompl ℓ) hmt1)
  -- graft the F|¬ℓ refutation, re-deriving each restricted axiom as a unit resolvent
  have hre0 : ∀ C', restrictedAxiom tcompl Ax (tcompl ℓ) C' →
      Justified tcompl (· ∈ Ax) (L1.map (insert (tcompl ℓ)) ++ Ax) C' := by
    rintro C' ⟨C, hC, _, hCe⟩
    refine Or.inr (Or.inl ⟨C, {tcompl ℓ}, ℓ, List.mem_append_right _ hC, hunit, ?_⟩)
    rw [← hCe, tcompl_tcompl, ResolutionClause.resolvent_unit_eq_erase]
  have hM0 : LDeriv tcompl (· ∈ Ax) (L0 ++ (L1.map (insert (tcompl ℓ)) ++ Ax)) :=
    transport hM1 hre0 hLD0
  refine ⟨L0 ++ (L1.map (insert (tcompl ℓ)) ++ Ax), hM0, List.mem_append_left _ hmt0, ?_⟩
  intro C hC
  rcases List.mem_append.mp hC with h | h
  · exact le_trans (hw0 C h) (le_trans (le_max_left _ _) (le_max_left _ _))
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨C2, hC2, rfl⟩ := List.mem_map.mp h
      calc ResolutionClause.width (insert (tcompl ℓ) C2)
          ≤ ResolutionClause.width C2 + 1 := Finset.card_insert_le _ _
        _ ≤ w1 + 1 := Nat.add_le_add_right (hw1 C2 hC2) 1
        _ ≤ max (max w0 (w1 + 1)) wF := le_trans (le_max_right _ _) (le_max_left _ _)
    · exact le_trans (hAx C h) (le_max_right _ _)

end LDeriv

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.asym_recombination
