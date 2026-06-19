import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Sym

/-!
# Entry 384 — universal-TM-table build: composition over the 3-symbol model (proved)

The wiring law `reachIn_seq` and the non-interference lemmas (entry 347) are stated for the `Bool` step relation
`concreteStep`.  The marker-based comparison is built over the 3-symbol model (entry 383), so it needs the same
composition lemmas for `concreteStep3`.  The proofs are identical: `concreteStep3` is existential over rules, so a step
of a sub-table is a step of the union, and reachability composes.

## What is proved (clean axioms, no `sorry`)

* **`concreteStep3_append_left` / `concreteStep3_append_right`** (PROVED) — a step of `M₁` (resp. `M₂`) is a step of
  `M₁ ++ M₂`.
* **`reachIn_toNTM3_mono`** (PROVED) — step monotonicity lifts to reachability.
* **`reachIn_append_left3` / `reachIn_append_right3`** (PROVED) — a run of a sub-table lifts to the union.
* **`reachIn_seq3`** (PROVED) — sequential composition inside the union machine.

## Honest scope

This **ports the composition lemmas** to the 3-symbol model — the wiring needed to assemble marker-based machines.  It
does **not** yet build any marker comparison, nor the rule-table loop.  Building those fragment by fragment is the
genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (TMachine3 CConfig3 concreteStep3 toNTM3)

/-- **A step of `M₁` is a step of `M₁ ++ M₂` (PROVED).** -/
theorem concreteStep3_append_left (M₁ M₂ : TMachine3) (c d : CConfig3)
    (h : concreteStep3 M₁ c d) : concreteStep3 (M₁ ++ M₂) c d := by
  obtain ⟨t, ht, hkey, happ⟩ := h
  exact ⟨t, List.mem_append.mpr (Or.inl ht), hkey, happ⟩

/-- **A step of `M₂` is a step of `M₁ ++ M₂` (PROVED).** -/
theorem concreteStep3_append_right (M₁ M₂ : TMachine3) (c d : CConfig3)
    (h : concreteStep3 M₂ c d) : concreteStep3 (M₁ ++ M₂) c d := by
  obtain ⟨t, ht, hkey, happ⟩ := h
  exact ⟨t, List.mem_append.mpr (Or.inr ht), hkey, happ⟩

/-- **Step monotonicity lifts to reachability (PROVED).** -/
theorem reachIn_toNTM3_mono (M M' : TMachine3)
    (hstep : ∀ c d, concreteStep3 M c d → concreteStep3 M' c d) :
    ∀ (k : ℕ) (c c' : CConfig3), reachIn (toNTM3 M) k c c' → reachIn (toNTM3 M') k c c' := by
  intro k
  induction k with
  | zero => intro c c' h; exact h
  | succ k ih =>
      intro c c' h
      obtain ⟨d, hs, hr⟩ := h
      exact ⟨d, hstep c d hs, ih d c' hr⟩

/-- **A run of a sub-table lifts to the union (left) (PROVED).** -/
theorem reachIn_append_left3 (M₁ M₂ : TMachine3) (k : ℕ) (c c' : CConfig3)
    (h : reachIn (toNTM3 M₁) k c c') : reachIn (toNTM3 (M₁ ++ M₂)) k c c' :=
  reachIn_toNTM3_mono M₁ (M₁ ++ M₂) (concreteStep3_append_left M₁ M₂) k c c' h

/-- **A run of a sub-table lifts to the union (right) (PROVED).** -/
theorem reachIn_append_right3 (M₁ M₂ : TMachine3) (k : ℕ) (c c' : CConfig3)
    (h : reachIn (toNTM3 M₂) k c c') : reachIn (toNTM3 (M₁ ++ M₂)) k c c' :=
  reachIn_toNTM3_mono M₂ (M₁ ++ M₂) (concreteStep3_append_right M₁ M₂) k c c' h

/-- **Sequential composition inside the union (PROVED).** -/
theorem reachIn_seq3 (M₁ M₂ : TMachine3) (a b : ℕ) (c d e : CConfig3)
    (h1 : reachIn (toNTM3 M₁) a c d) (h2 : reachIn (toNTM3 M₂) b d e) :
    reachIn (toNTM3 (M₁ ++ M₂)) (a + b) c e :=
  (reachIn_add (toNTM3 (M₁ ++ M₂)) a b c e).mpr
    ⟨d, reachIn_append_left3 M₁ M₂ a c d h1, reachIn_append_right3 M₁ M₂ b d e h2⟩

/-!
**Composition over the 3-symbol model, ported.**  `reachIn_seq3` and the non-interference lemmas mirror entry 347 over
`concreteStep3` — the wiring for marker-based machines.  Next: the marker-based varying-distance comparison primitives,
then the rule-table loop — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose.reachIn_seq3
