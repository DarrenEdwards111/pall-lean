import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA8

/-!
# Shrinkage brick A9a: restriction monotonicity

The ingredient that lets "≥ 1 free variable per block" suffice for Andreev
(rather than the exponentially-rare "exactly one per block"): restricting more
variables can only shrink the formula.

* **`dmsizeC_restrict_le` (proved)** — one restriction:
  `dmsizeC (f↾ᵢ₌ᵦ) ≤ dmsizeC f`;
* `restrF` — restriction of a whole set `T` to values `v`;
* **`dmsizeC_restrF_le` (proved)** — `dmsizeC (restrF T v f) ≤ dmsizeC f`.

With these, a hit block (≥ 1 free var) can be further restricted to one
survivor — giving `φ(±z)` with `dmsizeC = B` — and monotonicity transfers the
`B` back up.  This is what rescues the `resSum` route for Andreev (see the arc
log: the exact-transversal obstruction is avoided by leaving a larger free
set).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- **One-variable restriction monotonicity (proved).** -/
theorem dmsizeC_restrict_le {n : ℕ} (i : Fin n) (b : Bool)
    (f : (Fin n → Bool) → Bool) :
    dmsizeC (restrictF1 i b f) ≤ dmsizeC f := by
  obtain ⟨t, hte, htl⟩ := Nat.sInf_mem (dmsizeC_set_nonempty f)
  have hmem : (subst1 i b t).lsize0
      ∈ {L | ∃ t' : DMTreeC n, (∀ x, t'.eval x = restrictF1 i b f x)
        ∧ t'.lsize0 = L} := by
    refine ⟨subst1 i b t, ?_, rfl⟩
    intro x
    rw [subst1_eval]
    exact hte (Function.update x i b)
  have h1 : dmsizeC (restrictF1 i b f) ≤ (subst1 i b t).lsize0 :=
    Nat.sInf_le hmem
  have h2 : (subst1 i b t).lsize0 ≤ t.lsize0 := by
    have := subst1_lsize0 i b t
    omega
  have htl2 : t.lsize0 = dmsizeC f := htl
  omega

/-- Restriction of a whole set `T` of variables to the values `v`. -/
def restrF {n : ℕ} (T : Finset (Fin n)) (v : Fin n → Bool)
    (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → Bool :=
  fun x => f (fun i => if i ∈ T then v i else x i)

theorem restrF_empty {n : ℕ} (v : Fin n → Bool) (f : (Fin n → Bool) → Bool) :
    restrF ∅ v f = f := by
  funext x
  simp only [restrF, Finset.notMem_empty, if_false]

theorem restrF_insert {n : ℕ} {T : Finset (Fin n)} {j : Fin n} (hj : j ∉ T)
    (v : Fin n → Bool) (f : (Fin n → Bool) → Bool) :
    restrF (insert j T) v f = restrictF1 j (v j) (restrF T v f) := by
  funext x
  show f (fun i => if i ∈ insert j T then v i else x i)
    = f (fun i => if i ∈ T then v i else (Function.update x j (v j)) i)
  congr 1
  funext i
  by_cases hiT : i ∈ T
  · rw [if_pos (Finset.mem_insert_of_mem hiT), if_pos hiT]
  · by_cases hij : i = j
    · subst hij
      rw [if_pos (Finset.mem_insert_self i T), if_neg hiT, Function.update_self]
    · have hins : i ∉ insert j T := by
        rw [Finset.mem_insert]
        push_neg
        exact ⟨hij, hiT⟩
      rw [if_neg hins, if_neg hiT, Function.update_of_ne hij]

/-- **Set-restriction monotonicity (proved).** -/
theorem dmsizeC_restrF_le {n : ℕ} (T : Finset (Fin n)) (v : Fin n → Bool)
    (f : (Fin n → Bool) → Bool) :
    dmsizeC (restrF T v f) ≤ dmsizeC f := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [restrF_empty]
  | @insert j T hj ih =>
    rw [restrF_insert hj v f]
    calc dmsizeC (restrictF1 j (v j) (restrF T v f))
        ≤ dmsizeC (restrF T v f) := dmsizeC_restrict_le j (v j) (restrF T v f)
      _ ≤ dmsizeC f := ih

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.dmsizeC_restrict_le
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.dmsizeC_restrF_le
