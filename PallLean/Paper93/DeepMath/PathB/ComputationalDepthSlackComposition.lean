import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATSlackTransfer

/-!
# The composition test: does the slack add across disjoint gadgets?

Step 3 of the slack program, framed as a machine-checked test.  `AEm m` is the
conjunction of `m` disjoint `AllEqual₃` gadgets on `3m` variables — the direct-sum
family whose behavior decides whether above-floor slack **composes**:

* **`depSet_AEm` / `cbudget_AEm_floor` (proved)**: every coordinate is live, so
  `6m − 1 ≤ cbudget (AEm m)` at every `m` — the cone floor;
* **`AEm_one` / `cbudget_AEm_one` (proved)**: the `m = 1` anchor is the
  above-floor bound `6 ≤ cbudget (AEm 1)`;
* **`SlackComposes` (the test, stated)**: `∀ m, 1 ≤ m → 7m − 1 ≤ cbudget (AEm m)`
  — one extra gate per gadget.  NOT proved, NOT claimed.

## Honest scope

Between the proved floor `6m − 1` and the conjectured `7m − 1` lies the whole
question.  The designed next datapoint (guarded chain over `3(m−1)` signs plus the
mask/retract residual) would give `6m` — slack survives composition but only `+1`
globally.  If no argument collects `+1` **per gadget**, composition stalls at
`floor + O(1)` and that barrier must be recorded — direct-sum lower bounds fail in
many models, and nothing here assumes otherwise.  A proof of `SlackComposes` would
still be linear; it is a mechanism probe, not a route to superpolynomial.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- `m` disjoint `AllEqual₃` gadgets, conjoined. -/
def AEm (m : ℕ) : (Fin (3 * m) → Bool) → Bool := fun x =>
  (List.finRange m).all fun j =>
    allEq3 (x ⟨3 * j.val, by have := j.isLt; omega⟩)
      (x ⟨3 * j.val + 1, by have := j.isLt; omega⟩)
      (x ⟨3 * j.val + 2, by have := j.isLt; omega⟩)

/-- The `m = 1` gadget is `AllEqual₃` itself. -/
theorem AEm_one : AEm 1 = allEq3Fin := by
  funext x
  rw [AEm, show List.finRange 1 = [(0 : Fin 1)] from by decide, List.all_cons,
    List.all_nil, Bool.and_true]
  rfl

/-- **The `m = 1` anchor (proved)**: above-floor slack at a single gadget. -/
theorem cbudget_AEm_one : 6 ≤ cbudget (AEm 1) := by
  rw [AEm_one]
  exact cbudget_allEq3Fin

/-- Every coordinate of the gadget family is live. -/
theorem depSet_AEm (m : ℕ) : depSet (AEm m) = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro i
  refine mem_depSet.mpr ⟨fun _ => true, false, ?_⟩
  have h1 : AEm m (fun _ => true) = true := by
    rw [AEm, List.all_eq_true]
    intro j _
    rfl
  have hu : ∀ (t : ℕ) (h : t < 3 * m),
      Function.update (fun _ : Fin (3 * m) => true) i false ⟨t, h⟩
        = if t = i.val then false else true := by
    intro t h
    by_cases ht : t = i.val
    · rw [if_pos ht]
      have he : (⟨t, h⟩ : Fin (3 * m)) = i := Fin.ext ht
      rw [he, Function.update_self]
    · rw [if_neg ht]
      have hne : (⟨t, h⟩ : Fin (3 * m)) ≠ i := fun he => ht (by rw [← he])
      exact Function.update_of_ne hne false (fun _ : Fin (3 * m) => true)
  have h2 : AEm m (Function.update (fun _ => true) i false) = false := by
    have hj : i.val / 3 < m := by
      have := i.isLt
      omega
    rw [AEm]
    refine Bool.eq_false_iff.mpr ?_
    intro hall
    rw [List.all_eq_true] at hall
    have hg := hall ⟨i.val / 3, hj⟩ (List.mem_finRange _)
    rw [hu, hu, hu] at hg
    rw [show ((⟨i.val / 3, hj⟩ : Fin m) : ℕ) = i.val / 3 from rfl] at hg
    have hcase : i.val = 3 * (i.val / 3) ∨ i.val = 3 * (i.val / 3) + 1
        ∨ i.val = 3 * (i.val / 3) + 2 := by
      omega
    rcases hcase with hc | hc | hc
    · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)] at hg
      simp [allEq3] at hg
    · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega)] at hg
      simp [allEq3] at hg
    · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)] at hg
      simp [allEq3] at hg
  rw [h1, h2]
  simp

/-- **The cone floor at every `m` (proved)**: `6m − 1 ≤ cbudget (AEm m)`. -/
theorem cbudget_AEm_floor (m : ℕ) (hm : 1 ≤ m) : 6 * m - 1 ≤ cbudget (AEm m) := by
  have h := cone_bound (AEm m)
  rw [depSet_AEm, Finset.card_univ, Fintype.card_fin] at h
  omega

/-- **THE COMPOSITION TEST (stated, open)**: one extra gate per gadget.  A proof
would show above-floor slack adds across disjoint gadgets; a refutation or a stall
at `floor + O(1)` is the barrier to record. -/
def SlackComposes : Prop := ∀ m, 1 ≤ m → 7 * m - 1 ≤ cbudget (AEm m)

/-- The test's honest lower anchor: proving `SlackComposes` is exactly the gap
between the proved floor and one-per-gadget. -/
theorem slackComposes_iff_gap :
    SlackComposes ↔ ∀ m, 1 ≤ m → 7 * m - 1 ≤ cbudget (AEm m) := Iff.rfl

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_AEm_one
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_AEm_floor
