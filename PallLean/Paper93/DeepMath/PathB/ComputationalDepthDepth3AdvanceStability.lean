import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ForwardScan

/-!
# The advance-stability of the active term: the provable core of the backward-scan invariant

The backward-scan decoder for `ReconstructionCorrect` (Håstad's canonical encoding, replayed
clause-order first) rests on a single identification claim: *the first live term found by scanning
`cs` under the reconstructed state is exactly the active term of the original step*.  The user's
strategy is to prove this as a scan invariant rather than to hunt for falsified clauses.

This file proves the **forward half** of that identification — the genuinely provable core:

* `activeTerm_fixVar_stable` — **the scan re-finds the active term across an advance step.**  If `T`
  is the active term under `σ`, and we fix any free variable `v` to a bit `b` such that under the
  successor state `σ' := fixVar σ v b` (i) no term is satisfied, (ii) `T` is still not falsified, and
  (iii) `T` still has a free literal, then `T` is **again** the active term: `activeTerm cs σ' = some T`.

  Proof: `activeTerm = cs.find? P` where `P U := ¬termFalsified U ∧ 0 < |freeLits U|`
  (`activeTerm_eq_find`).  Decompose `cs = pre ++ T :: suf` with `find?_eq_some`.  Every `U ∈ pre`
  has `P U = false` under `σ`, and (since `anyTermSat σ = false`) the "no free literal" alternative
  forces `U` to be *falsified* under `σ` (`term_falsified_of_not_sat_no_free`); falsification then
  **persists** to `σ'` (`termFalsified_fixVar_of_free`, the monotonicity backbone).  So `pre` still
  fails the predicate under `σ'`, while `T` satisfies it by (ii)+(iii) — hence `find?` returns `T`.

* `activeTerm_advance_stable` — the same specialised to the canonical active literal
  `activeTermLit cs σ = some ℓ` and `v = litVar ℓ` (the step's own variable), the exact shape the
  decoder's scan uses.

So when the deepest branch *advances within a term* (the `true`/satisfy-direction step, which keeps
`T` live), the forward scan provably re-identifies `T`.  This is the half of the scan invariant that
holds with no extra hypotheses; the complementary *falsify* steps (where `T` dies) are recovered
label-free by `decodedSel` (`decodedSel_subset_deepestSel`).  Together these are the two mechanisms
the backward-scan invariant composes — this file discharges the advance mechanism, **not** faked.

The remaining open content is purely the *threading*: that the interleaving of advance steps (handled
here) and falsify steps (handled by `decodedSel`) reconstructs the full `deepestSel` along the
deepest branch.  The per-step identification is what is proved here.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The scan re-finds the active term across an advance step.**  If `T` is active under `σ`, and
fixing a free variable `v` to `b` leaves (under `σ' := fixVar σ v b`) no term satisfied, `T` still
not falsified, and `T` still with a free literal, then `T` is again the active term under `σ'`.

This is the forward half of the backward-scan identification invariant: an advance step (one that
keeps `T` live) is provably re-identified by the deterministic clause-order scan, with the falsified
prefix carried forward by the monotonicity backbone `termFalsified_fixVar_of_free`. -/
theorem activeTerm_fixVar_stable {cs : List (Clause n)} {σ : Restriction n} {v : Fin n} {b : Bool}
    {T : Clause n} (hact : SwitchingCounting.activeTerm cs σ = some T) (hv : σ v = none)
    (hns' : SwitchingCounting.anyTermSat cs (fixVar σ v b) = false)
    (hnf' : SwitchingCounting.termFalsified (fixVar σ v b) T = false)
    (hfree' : 0 < (SwitchingCounting.freeLits (fixVar σ v b) T).length) :
    SwitchingCounting.activeTerm cs (fixVar σ v b) = some T := by
  have hns : SwitchingCounting.anyTermSat cs σ = false := SwitchingCounting.activeTerm_anyTermSat_false hact
  -- `activeTerm σ = cs.find? P = some T`, with the standard prefix decomposition.
  have hfind := hact
  rw [SwitchingCounting.activeTerm_eq_find hns, List.find?_eq_some_iff_append] at hfind
  obtain ⟨_hPT, pre, suf, hsplit, hpre⟩ := hfind
  -- Goal: `activeTerm σ' = cs.find? P' = some T`.
  rw [SwitchingCounting.activeTerm_eq_find hns', List.find?_eq_some_iff_append]
  refine ⟨?_, pre, suf, hsplit, ?_⟩
  · -- `T` satisfies the predicate under `σ'`: not falsified, still has a free literal.
    simp only [hnf', Bool.not_false, Bool.true_and, decide_eq_true_eq]
    exact hfree'
  · -- Every term in the prefix stays falsified under `σ'`, hence fails the predicate.
    intro U hU
    -- `P U = false` under `σ` unpacks to: `U` falsified, or `U` has no free literal.
    have hPUfalse : SwitchingCounting.termFalsified σ U = true ∨
        SwitchingCounting.freeLits σ U = [] := by simpa using hpre U hU
    have hUmem : U ∈ cs := by rw [hsplit]; exact List.mem_append_left _ hU
    -- Either way `termFalsified σ U = true` (the no-free-lit case is unsatisfied, hence falsified).
    have hfalsσ : SwitchingCounting.termFalsified σ U = true := by
      rcases hPUfalse with h | h
      · exact h
      · have hsatU : SwitchingCounting.termSat σ U = false := by
          by_contra hsc
          rw [Bool.not_eq_false] at hsc
          have : SwitchingCounting.anyTermSat cs σ = true := by
            rw [SwitchingCounting.anyTermSat, List.any_eq_true]; exact ⟨U, hUmem, hsc⟩
          rw [hns] at this; exact absurd this (by simp)
        exact SwitchingCounting.term_falsified_of_not_sat_no_free hsatU h
    -- Falsification persists to `σ'`.
    have hfalsσ' : SwitchingCounting.termFalsified (fixVar σ v b) U = true :=
      termFalsified_fixVar_of_free hfalsσ hv
    simp [hfalsσ']

/-- **Advance stability at the canonical active literal.**  Specialisation of
`activeTerm_fixVar_stable` to `v = litVar ℓ` for the canonical active literal
`activeTermLit cs σ = some ℓ` — the exact form the scan invariant consumes (the step's own
variable is free, by `activeTermLit_var_free`). -/
theorem activeTerm_advance_stable {cs : List (Clause n)} {σ : Restriction n}
    {ℓ : Rung4Literal n} {b : Bool} {T : Clause n}
    (hact : SwitchingCounting.activeTerm cs σ = some T)
    (hatl : SwitchingCounting.activeTermLit cs σ = some ℓ)
    (hns' : SwitchingCounting.anyTermSat cs (fixVar σ (litVar ℓ) b) = false)
    (hnf' : SwitchingCounting.termFalsified (fixVar σ (litVar ℓ) b) T = false)
    (hfree' : 0 < (SwitchingCounting.freeLits (fixVar σ (litVar ℓ) b) T).length) :
    SwitchingCounting.activeTerm cs (fixVar σ (litVar ℓ) b) = some T :=
  activeTerm_fixVar_stable hact (activeTermLit_var_free hatl) hns' hnf' hfree'

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.activeTerm_fixVar_stable
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.activeTerm_advance_stable
