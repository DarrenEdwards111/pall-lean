import PallLean.Paper93.DeepMath.PathB.ComputationalDepthThreeKillFoundation

/-!
# THE THREE-KILL NO-GO: the two-kill guard is per-step optimal

Stress-testing the recorded three-kill design refutes it, machine-checked:

* **`bitMediated_trivial` (proved)**: `BitMediated f i` holds for *every* `f` and
  `i` — take `op := fst`, `u := const`, `H w x := f (x[i := w])`.  The foundation
  file's proposed guard `¬ BitMediated` is unsatisfiable; the proposed theorem is
  vacuous.  Semantic factorizations through a Boolean are unconstrained.

* **`threekill_per_step_no_go` (proved)**: no per-step three-kill follows from the
  two-kill guard.  Witness `f = (x₀ ⊕ x₁) ∧ x₂` at `i = 0`: both restrictions
  (`x₁ ∧ x₂` and `¬x₁ ∧ x₂`) are nonconstant, unequal, and non-complementary — the
  guard holds — yet `cbudget f = 5` and `cbudget (f|₀) = 3` (both computed exactly:
  explicit circuits above, the cone bound below), so exactly **two** gates die.
  The xor-tap configuration realizes the escape, and no `f`-level hypothesis can
  exclude it while keeping the guard satisfiable.

**Moral, recorded**: the per-step ladder ends at two kills.  Progress past `2n` in
this model must amortize — global accounting over the whole restriction sequence
(Schnorr `2.5n`, FGHK/Li–Yang `3n+`-style case analysis with credited gates), not a
stronger per-step theorem.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor

/-- **`BitMediated` is vacuous (proved)**: every function bit-mediates at every
variable — the foundation file's proposed three-kill guard is unsatisfiable. -/
theorem bitMediated_trivial {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) :
    BitMediated f i := by
  refine ⟨fun w x => f (Function.update x i w), fun a _ => a, fun _ => false,
    fun x b => rfl, ?_, ?_⟩
  · intro w x b
    show f (Function.update (Function.update x i b) i w) = f (Function.update x i w)
    rw [Function.update_idem]
  · intro x
    show f x = f (Function.update x i (x i))
    rw [Function.update_eq_self]

/-! ### The counterexample: `(x₀ ⊕ x₁) ∧ x₂` -/

/-- The escape function. -/
def exf : (Fin 3 → Bool) → Bool := fun x => (Bool.xor (x 0) (x 1)) && x 2

/-- A 5-gate circuit for `exf`. -/
def exfC : List (CGate 3) :=
  [.var 0, .var 1, .var 2, .bin (fun a b => Bool.xor a b) 0 1, .bin (fun a b => a && b) 3 2]

/-- A 3-gate circuit for the restriction `exf|₍x₀:=false₎ = x₁ ∧ x₂`. -/
def exfC0 : List (CGate 3) :=
  [.var 1, .var 2, .bin (fun a b => a && b) 0 1]

theorem exfC_computes : computes exfC exf := by
  show ∀ x : Fin 3 → Bool, output exfC x = exf x
  decide

theorem exfC0_computes : computes exfC0 (restrictF exf 0 false) := by
  show ∀ x : Fin 3 → Bool, output exfC0 x = restrictF exf 0 false x
  decide

theorem cbudget_exf : cbudget exf = 5 := by
  have hup : cbudget exf ≤ 5 := by
    have hmem : exfC.length ∈ {s | ∃ c : List (CGate 3), computes c exf ∧ c.length = s} :=
      ⟨exfC, exfC_computes, rfl⟩
    exact Nat.sInf_le hmem
  have huniv : depSet exf = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro j
    fin_cases j
    · exact mem_depSet.mpr ⟨fun _ => true, false, by decide⟩
    · exact mem_depSet.mpr ⟨fun _ => true, false, by decide⟩
    · exact mem_depSet.mpr ⟨fun k => decide (k.val ≠ 1), false, by decide⟩
  have hcone := cone_bound exf
  rw [huniv, Finset.card_univ, Fintype.card_fin] at hcone
  omega

theorem cbudget_exf_restrict : cbudget (restrictF exf 0 false) = 3 := by
  have hup : cbudget (restrictF exf 0 false) ≤ 3 := by
    have hmem : exfC0.length
        ∈ {s | ∃ c : List (CGate 3), computes c (restrictF exf 0 false) ∧ c.length = s} :=
      ⟨exfC0, exfC0_computes, rfl⟩
    exact Nat.sInf_le hmem
  have hsub : ({1, 2} : Finset (Fin 3)) ⊆ depSet (restrictF exf 0 false) := by
    intro j hj
    rcases Finset.mem_insert.mp hj with he | he
    · subst he
      exact mem_depSet.mpr ⟨fun _ => true, false, by decide⟩
    · rw [Finset.mem_singleton] at he
      subst he
      exact mem_depSet.mpr ⟨fun _ => true, false, by decide⟩
  have hcard : 2 ≤ (depSet (restrictF exf 0 false)).card := by
    have h2 : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
    exact le_trans (le_of_eq h2.symm) (Finset.card_le_card hsub)
  have hcone := cone_bound (restrictF exf 0 false)
  omega

/-- The two-kill guard holds for `exf` at `x₀`. -/
theorem exf_guard :
    (∃ x y, restrictF exf 0 false x ≠ restrictF exf 0 false y) ∧
    (∃ x y, restrictF exf 0 true x ≠ restrictF exf 0 true y) ∧
    restrictF exf 0 true ≠ restrictF exf 0 false ∧
    restrictF exf 0 true ≠ (fun x => !(restrictF exf 0 false x)) := by
  refine ⟨⟨fun _ => true, fun _ => false, by decide⟩,
    ⟨fun k => decide (k.val ≠ 1), fun _ => false, by decide⟩, ?_, ?_⟩
  · intro heq
    exact absurd (congrFun heq (fun _ => true)) (by decide)
  · intro heq
    exact absurd (congrFun heq (fun _ => false)) (by decide)

/-- **THE PER-STEP THREE-KILL NO-GO (proved).**  The two-kill guard does not imply a
third kill: the per-step elimination ladder ends at two. -/
theorem threekill_per_step_no_go :
    ¬ ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (i : Fin n) (b : Bool),
        (∃ x y, restrictF f i false x ≠ restrictF f i false y) →
        (∃ x y, restrictF f i true x ≠ restrictF f i true y) →
        restrictF f i true ≠ restrictF f i false →
        restrictF f i true ≠ (fun x => !(restrictF f i false x)) →
        cbudget (restrictF f i b) + 3 ≤ cbudget f := by
  intro hall
  obtain ⟨h0, h1, hne, hnc⟩ := exf_guard
  have h := hall 3 exf 0 false h0 h1 hne hnc
  rw [cbudget_exf, cbudget_exf_restrict] at h
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.bitMediated_trivial
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.threekill_per_step_no_go
