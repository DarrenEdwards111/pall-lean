import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3AdvanceStability

/-!
# Active-clause non-backtracking: the structural backbone of leaf identification

The multi-step backward decoder must, from the deepest leaf, sequence the active clauses of the
forward steps.  Its structural backbone is **non-backtracking**: across a deepest step the active
clause never moves to an *earlier* clause in `cs`.  Equivalently, every clause strictly before the
current active clause is already falsified, and falsification persists (`termFalsified_fixVar_of_free`),
so the next active clause lies at or after the current one.

* `activeTerm_prefix_falsified` — the prefix lemma: in the canonical decomposition
  `cs = pre ++ T :: suf` of `activeTerm cs σ = some T`, every `U ∈ pre` is **falsified** at `σ`
  (a non-falsified prefix clause would have to be satisfied — impossible since `anyTermSat σ = false`).
* `activeTerm_fixVar_no_backtrack` — **non-backtracking.**  After fixing any free variable, the new
  active clause (if any) lies in the suffix `T :: suf` — never strictly before `T`.  Holds for **any**
  bit (advance *or* falsify step), with no read-once or "ρ falsifies nothing" hypothesis.

So along the whole deepest branch the active clause advances monotonically through `cs`.  This is the
ordering structure the leaf-to-step identification rests on; the identification itself (which clause is
active at *each* step, read from the non-satisfying leaf) remains the open core and is **not** faked.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The prefix of the active clause is falsified.**  In the decomposition `cs = pre ++ T :: suf`
witnessing `activeTerm cs σ = some T`, every clause `U ∈ pre` is falsified at `σ`: it fails the active
predicate, and the "no free literal" alternative would force it satisfied — impossible since
`anyTermSat cs σ = false`. -/
theorem activeTerm_prefix_falsified {cs : List (Clause n)} {σ : Restriction n} {T : Clause n}
    (hact : SwitchingCounting.activeTerm cs σ = some T) :
    ∃ pre suf, cs = pre ++ T :: suf ∧
      ∀ U ∈ pre, SwitchingCounting.termFalsified σ U = true := by
  have hns : SwitchingCounting.anyTermSat cs σ = false :=
    SwitchingCounting.activeTerm_anyTermSat_false hact
  have hfind := hact
  rw [SwitchingCounting.activeTerm_eq_find hns, List.find?_eq_some_iff_append] at hfind
  obtain ⟨_, pre, suf, hsplit, hpre⟩ := hfind
  refine ⟨pre, suf, hsplit, ?_⟩
  intro U hU
  have hUmem : U ∈ cs := by rw [hsplit]; exact List.mem_append_left _ hU
  have hPUfalse : SwitchingCounting.termFalsified σ U = true ∨
      SwitchingCounting.freeLits σ U = [] := by simpa using hpre U hU
  rcases hPUfalse with h | h
  · exact h
  · have hsatU : SwitchingCounting.termSat σ U = false := by
      by_contra hsc
      rw [Bool.not_eq_false] at hsc
      have : SwitchingCounting.anyTermSat cs σ = true := by
        rw [SwitchingCounting.anyTermSat, List.any_eq_true]; exact ⟨U, hUmem, hsc⟩
      rw [hns] at this; exact absurd this (by simp)
    exact SwitchingCounting.term_falsified_of_not_sat_no_free hsatU h

/-- **Non-backtracking.**  If `T` is active under `σ` and we fix any free variable to any bit, the new
active clause (if it exists) lies in the suffix `T :: suf` — it never moves strictly before `T`.  The
prefix `pre` is falsified at `σ` and stays falsified, so the `find?`-based active clause skips it. -/
theorem activeTerm_fixVar_no_backtrack {cs : List (Clause n)} {σ : Restriction n} {v : Fin n}
    {b : Bool} {T : Clause n} (hact : SwitchingCounting.activeTerm cs σ = some T) (hv : σ v = none)
    {T' : Clause n} (hact' : SwitchingCounting.activeTerm cs (fixVar σ v b) = some T') :
    ∃ pre suf, cs = pre ++ T :: suf ∧ (T' = T ∨ T' ∈ suf) := by
  obtain ⟨pre, suf, hsplit, hprefals⟩ := activeTerm_prefix_falsified hact
  refine ⟨pre, suf, hsplit, ?_⟩
  -- `T'` satisfies the σ'-predicate (it is the `find?` result).
  have hns' : SwitchingCounting.anyTermSat cs (fixVar σ v b) = false :=
    SwitchingCounting.activeTerm_anyTermSat_false hact'
  have hfind' : cs.find?
      (fun U => !SwitchingCounting.termFalsified (fixVar σ v b) U &&
        decide (0 < (SwitchingCounting.freeLits (fixVar σ v b) U).length)) = some T' := by
    rw [← SwitchingCounting.activeTerm_eq_find hns']; exact hact'
  have hPT' : (!SwitchingCounting.termFalsified (fixVar σ v b) T' &&
      decide (0 < (SwitchingCounting.freeLits (fixVar σ v b) T').length)) = true := by
    simpa using List.find?_some hfind'
  have hT'mem : T' ∈ cs := List.mem_of_find?_eq_some hfind'
  -- `T'` is not in the prefix: prefix clauses are falsified at `σ`, hence at `σ'`, hence fail the predicate.
  have hT'notpre : T' ∉ pre := by
    intro hin
    have hfalsσ' : SwitchingCounting.termFalsified (fixVar σ v b) T' = true :=
      termFalsified_fixVar_of_free (hprefals T' hin) hv
    rw [hfalsσ', Bool.not_true, Bool.false_and] at hPT'
    exact absurd hPT' (by simp)
  -- so `T' ∈ T :: suf`.
  rw [hsplit, List.mem_append] at hT'mem
  rcases hT'mem with h | h
  · exact absurd h hT'notpre
  · rcases List.mem_cons.mp h with h | h
    · exact Or.inl h
    · exact Or.inr h

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.activeTerm_prefix_falsified
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.activeTerm_fixVar_no_backtrack
