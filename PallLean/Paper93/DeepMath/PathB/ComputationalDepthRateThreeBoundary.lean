import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAmortizedKillChain

/-!
# The rate-3 boundary: no good variable at the cone floor

Stress-testing the rate-3 lemma before attempting it, in the discipline of the
three-kill no-go — and the ∃-form also has a machine-checked boundary:

* **`rate3_no_go_at_floor` (proved)**: for `xor₃ = x₀ ⊕ x₁ ⊕ x₂`, NO variable and
  no value gives a 3-kill: `cbudget xor₃ = 5` (the cone floor `2·3 − 1`), every
  restriction is a two-variable parity with `cbudget ≥ 3`, so every restriction
  kills exactly two gates.  The existence-form rate-3 step fails outright on
  cone-floor functions.

* **`rate3_step_needs_slack` (proved)**: any single rate-3 step at `f` (with
  dependence dropping by at most one) already forces `2·deps(f) ≤ cbudget f` —
  strictly above the cone floor `2·deps − 1`.

**The delineation, recorded**: a rate-3 invariant class `P` must *maintain*
above-floor slack along the whole chain — the slack cannot be assumed, it must be
supplied by structure (for the SAT slices, proving that slack **is** the sought
lower bound: the circularity is broken only by SAT-specific structure, which is
the genuinely open Schnorr/FGHK-style content).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor

/-- Any rate-3 step (dependence dropping by at most one) forces the source strictly
above the cone floor. -/
theorem rate3_step_needs_slack {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n)
    (b : Bool) (h3 : cbudget (restrictF f i b) + 3 ≤ cbudget f)
    (hd : (depSet f).card ≤ (depSet (restrictF f i b)).card + 1) :
    2 * (depSet f).card ≤ cbudget f := by
  have := cone_bound (restrictF f i b)
  omega

/-! ### The floor witness: three-variable parity -/

def xor3 : (Fin 3 → Bool) → Bool := fun x => Bool.xor (Bool.xor (x 0) (x 1)) (x 2)

def xor3C : List (CGate 3) :=
  [.var 0, .var 1, .var 2, .bin (fun a b => Bool.xor a b) 0 1,
    .bin (fun a b => Bool.xor a b) 3 2]

theorem xor3C_computes : computes xor3C xor3 := by
  show ∀ x : Fin 3 → Bool, output xor3C x = xor3 x
  decide

theorem cbudget_xor3_le : cbudget xor3 ≤ 5 := by
  have hmem : xor3C.length ∈ {s | ∃ c : List (CGate 3), computes c xor3 ∧ c.length = s} :=
    ⟨xor3C, xor3C_computes, rfl⟩
  exact Nat.sInf_le hmem

/-- Two live coordinates put any function at `cbudget ≥ 3`. -/
theorem cbudget_ge_three_of_two_deps (g : (Fin 3 → Bool) → Bool) (j k : Fin 3)
    (hjk : j ≠ k) (hj : j ∈ depSet g) (hk : k ∈ depSet g) :
    3 ≤ cbudget g := by
  have hsub : ({j, k} : Finset (Fin 3)) ⊆ depSet g := by
    intro t ht
    rcases Finset.mem_insert.mp ht with he | he
    · subst he
      exact hj
    · rw [Finset.mem_singleton] at he
      subst he
      exact hk
  have hcard : ({j, k} : Finset (Fin 3)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hjk]), Finset.card_singleton]
  have h1 := Finset.card_le_card hsub
  have h2 := cone_bound g
  omega

/-- **THE RATE-3 BOUNDARY (proved)**: at the cone-floor function `xor₃`, no variable
and no value yields a three-kill — every restriction kills exactly two gates. -/
theorem rate3_no_go_at_floor :
    ¬ ∃ (i : Fin 3) (b : Bool), cbudget (restrictF xor3 i b) + 3 ≤ cbudget xor3 := by
  rintro ⟨i, b, h3⟩
  have hup := cbudget_xor3_le
  have hlow : 3 ≤ cbudget (restrictF xor3 i b) := by
    fin_cases i <;> cases b
    · exact cbudget_ge_three_of_two_deps _ 1 2 (by decide)
        (mem_depSet.mpr ⟨fun _ => false, true, by decide⟩)
        (mem_depSet.mpr ⟨fun _ => false, true, by decide⟩)
    · exact cbudget_ge_three_of_two_deps _ 1 2 (by decide)
        (mem_depSet.mpr ⟨fun _ => false, true, by decide⟩)
        (mem_depSet.mpr ⟨fun _ => false, true, by decide⟩)
    · exact cbudget_ge_three_of_two_deps _ 0 2 (by decide)
        (mem_depSet.mpr ⟨fun _ => false, true, by decide⟩)
        (mem_depSet.mpr ⟨fun _ => false, true, by decide⟩)
    · exact cbudget_ge_three_of_two_deps _ 0 2 (by decide)
        (mem_depSet.mpr ⟨fun _ => false, true, by decide⟩)
        (mem_depSet.mpr ⟨fun _ => false, true, by decide⟩)
    · exact cbudget_ge_three_of_two_deps _ 0 1 (by decide)
        (mem_depSet.mpr ⟨fun _ => false, true, by decide⟩)
        (mem_depSet.mpr ⟨fun _ => false, true, by decide⟩)
    · exact cbudget_ge_three_of_two_deps _ 0 1 (by decide)
        (mem_depSet.mpr ⟨fun _ => false, true, by decide⟩)
        (mem_depSet.mpr ⟨fun _ => false, true, by decide⟩)
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.rate3_step_needs_slack
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.rate3_no_go_at_floor
