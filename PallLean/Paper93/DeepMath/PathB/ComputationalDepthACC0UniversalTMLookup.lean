import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMEncoding

/-!
# Entry 336 — universal-TM-table build, brick 3: the rule-lookup, sound and complete (proved)

Brick 1 (entry 334) gave the tape-traversal scanner; brick 2 (entry 335) the `(machine, input)` encoding.  Brick 3 is
the heart of the simulation cycle: **rule lookup** — given the current `(state, symbol)`, find the matching transition
in the (decoded) machine's rule table, and apply it.

**The lookup.**  Logically, the lookup is `List.find?` over the machine's rules for the one whose left-hand side matches
`(c.1, readSym c)`: `lookup M c := M.find? (· .1 = (c.1, readSym c))`, and `applyLookup M c := (lookup M c).map
(applyTrans c)`.  The key theorems tie this to the machine's step relation: a found-and-applied rule **is** a
`concreteStep` (soundness), and conversely whenever a step exists the lookup finds a rule (completeness).  This is the
*logic* the universal machine's table-scan realises; the bit-level scan loop that physically computes `find?` over the
encoded table (via the brick-1 traversal, comparing the encoded fields) is the lowest engineering layer beneath it.

## What is proved (clean axioms, no `sorry`)

* **`lookup`, `applyLookup`** — find the matching rule / find-and-apply it (`Option`-valued).
* **`lookup_sound`** (PROVED) — `lookup M c = some t → concreteStep M c (applyTrans c t)`: a found rule yields a genuine
  step.
* **`applyLookup_sound`** (PROVED) — `applyLookup M c = some d → concreteStep M c d`: find-and-apply yields a step.
* **`lookup_complete`** (PROVED) — `concreteStep M c d → ∃ t, lookup M c = some t`: whenever a step exists, the lookup
  finds a matching rule.

## Honest scope

This proves the **rule-lookup logic** of the universal machine — the matching-transition search is sound and complete
w.r.t. `concreteStep`, exactly what the simulation cycle's lookup step must compute.  It does **not** build the bit-level
scan loop that physically realises `find?` over the encoded transition table on the tape (walking the encoding with the
brick-1 traversal, comparing each rule's encoded `(state, symbol)` to the current pair) — that realisation, then the
apply-step, the simulation loop, accept detection, and `Realizes physU U φ cost`, remain the substantial construction,
built as verified bricks, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLookup

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
  (TMachine TMTrans CConfig concreteStep readSym applyTrans)

/-- **The rule lookup.**  Find the first rule of `M` whose left-hand side `(state, read)` matches the current config
`(c.1, readSym c)`. -/
def lookup (M : TMachine) (c : CConfig) : Option TMTrans :=
  M.find? (fun r => decide (r.1 = (c.1, readSym c)))

/-- **Find and apply.**  Look up the matching rule and apply it to get the next config. -/
def applyLookup (M : TMachine) (c : CConfig) : Option CConfig :=
  (lookup M c).map (applyTrans c)

/-- **Lookup is sound (PROVED).**  A found rule applied to `c` is a genuine `concreteStep`: it is in `M` and its
left-hand side matches `(c.1, readSym c)`. -/
theorem lookup_sound (M : TMachine) (c : CConfig) (t : TMTrans) (h : lookup M c = some t) :
    concreteStep M c (applyTrans c t) := by
  unfold lookup at h
  have hp := List.find?_some h
  exact ⟨t, List.mem_of_find?_eq_some h, of_decide_eq_true hp, rfl⟩

/-- **Find-and-apply is sound (PROVED).**  `applyLookup M c = some d` yields `concreteStep M c d`. -/
theorem applyLookup_sound (M : TMachine) (c d : CConfig) (h : applyLookup M c = some d) :
    concreteStep M c d := by
  unfold applyLookup at h
  cases hl : lookup M c with
  | none => rw [hl] at h; simp at h
  | some t =>
      rw [hl] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact lookup_sound M c t hl

/-- **Lookup is complete (PROVED).**  Whenever a `concreteStep M c d` exists — so some rule's left-hand side matches —
the lookup finds a matching rule. -/
theorem lookup_complete (M : TMachine) (c d : CConfig) (h : concreteStep M c d) :
    ∃ t, lookup M c = some t := by
  obtain ⟨t, htmem, ht1, _⟩ := h
  cases hl : lookup M c with
  | some t' => exact ⟨t', rfl⟩
  | none =>
      exfalso
      unfold lookup at hl
      rw [List.find?_eq_none] at hl
      have hcontra := hl t htmem
      rw [ht1] at hcontra
      simp at hcontra

/-!
**Brick 3, built.**  `lookup`/`applyLookup` are sound (`lookup_sound`, `applyLookup_sound`: a found-and-applied rule is a
`concreteStep`) and complete (`lookup_complete`: a step's existence guarantees a match) w.r.t. the machine's step
relation — the verified lookup logic of the universal simulation cycle.  Next: the bit-level scan realising `find?` over
the encoded table (via the brick-1 traversal), then the apply-step, the simulation loop, accept detection, and
`Realizes physU U φ cost` — built as verified bricks, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLookup

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLookup.lookup_sound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLookup.applyLookup_sound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLookup.lookup_complete
