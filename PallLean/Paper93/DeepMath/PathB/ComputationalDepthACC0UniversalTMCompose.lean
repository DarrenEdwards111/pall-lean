import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMScanField

/-!
# Entry 347 — universal-TM-table build: rule-list non-interference and sequential composition (proved)

Entry 346 built the relocatable field scanner `scanNatFrom s s'`.  To chain disjoint-state copies (e.g.
`scanNatFrom 0 1`, `scanNatFrom 1 2`, …) into *one* machine that scans a whole transition, we need the **non-interference
law for the union of transition tables**: a step of a sub-table is still a step of the union.

This is immediate from the *shape* of `concreteStep`: a step `concreteStep M c d` is an existential over rules `t ∈ M`,
so enlarging `M` to a superset `M ⊆ M'` only adds rules — the witnessing rule of any step of `M` is still a rule of `M'`.
Hence **no disjointness hypothesis is needed for reachability to survive**: a run in a sub-table lifts verbatim to the
union (`reachIn_append_left` / `reachIn_append_right`), and two runs compose back-to-back inside the union
(`reachIn_seq`).  This is exactly the wiring law for chaining field scanners.

## What is proved (clean axioms, no `sorry`)

* **`concreteStep_append_left` / `concreteStep_append_right`** (PROVED) — a step of `M₁` (resp. `M₂`) is a step of
  `M₁ ++ M₂` (the witnessing rule survives under `List.mem_append`).
* **`reachIn_toNTM_mono`** (PROVED) — step monotonicity lifts to reachability: if every `concreteStep M` is a
  `concreteStep M'`, then every `reachIn (toNTM M) k` run is a `reachIn (toNTM M') k` run.
* **`reachIn_append_left` / `reachIn_append_right`** (PROVED) — a `k`-step run of a sub-table lifts verbatim to the
  union machine `M₁ ++ M₂`.
* **`reachIn_seq`** (PROVED) — sequential composition inside the union: a run of `M₁` from `c` to `d` followed by a run
  of `M₂` from `d` to `e` is a single run of `M₁ ++ M₂` from `c` to `e` (total step count added).

## Honest scope

This proves the **non-interference / sequential-composition law** for unions of transition tables — the wiring
primitive that lets `scanNatFrom` copies be combined into one machine and run back-to-back.  It does **not** yet
instantiate it on the five fields of `encodeTransBits` (that needs threading each field's tape-preservation through to
the next field's content hypothesis — the next fragment), nor the rule-table scan-and-match, nor the apply.  Building
those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine CConfig concreteStep toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)

/-- **A step of `M₁` is a step of `M₁ ++ M₂` (PROVED).**  The witnessing rule of the step survives in the union. -/
theorem concreteStep_append_left (M₁ M₂ : TMachine) (c d : CConfig)
    (h : concreteStep M₁ c d) : concreteStep (M₁ ++ M₂) c d := by
  obtain ⟨t, ht, hkey, happ⟩ := h
  exact ⟨t, List.mem_append.mpr (Or.inl ht), hkey, happ⟩

/-- **A step of `M₂` is a step of `M₁ ++ M₂` (PROVED).** -/
theorem concreteStep_append_right (M₁ M₂ : TMachine) (c d : CConfig)
    (h : concreteStep M₂ c d) : concreteStep (M₁ ++ M₂) c d := by
  obtain ⟨t, ht, hkey, happ⟩ := h
  exact ⟨t, List.mem_append.mpr (Or.inr ht), hkey, happ⟩

/-- **Step monotonicity lifts to reachability (PROVED).**  If every `concreteStep M` is a `concreteStep M'`, then every
`reachIn (toNTM M) k` run is a `reachIn (toNTM M') k` run. -/
theorem reachIn_toNTM_mono (M M' : TMachine)
    (hstep : ∀ c d, concreteStep M c d → concreteStep M' c d) :
    ∀ (k : ℕ) (c c' : CConfig), reachIn (toNTM M) k c c' → reachIn (toNTM M') k c c' := by
  intro k
  induction k with
  | zero => intro c c' h; exact h
  | succ k ih =>
      intro c c' h
      obtain ⟨d, hs, hr⟩ := h
      exact ⟨d, hstep c d hs, ih d c' hr⟩

/-- **A run of a sub-table lifts to the union (left) (PROVED).** -/
theorem reachIn_append_left (M₁ M₂ : TMachine) (k : ℕ) (c c' : CConfig)
    (h : reachIn (toNTM M₁) k c c') : reachIn (toNTM (M₁ ++ M₂)) k c c' :=
  reachIn_toNTM_mono M₁ (M₁ ++ M₂) (concreteStep_append_left M₁ M₂) k c c' h

/-- **A run of a sub-table lifts to the union (right) (PROVED).** -/
theorem reachIn_append_right (M₁ M₂ : TMachine) (k : ℕ) (c c' : CConfig)
    (h : reachIn (toNTM M₂) k c c') : reachIn (toNTM (M₁ ++ M₂)) k c c' :=
  reachIn_toNTM_mono M₂ (M₁ ++ M₂) (concreteStep_append_right M₁ M₂) k c c' h

/-- **Sequential composition inside the union (PROVED).**  A run of `M₁` from `c` to `d` (`a` steps) followed by a run
of `M₂` from `d` to `e` (`b` steps) is a single run of `M₁ ++ M₂` from `c` to `e` in `a + b` steps — the wiring law for
chaining field scanners. -/
theorem reachIn_seq (M₁ M₂ : TMachine) (a b : ℕ) (c d e : CConfig)
    (h1 : reachIn (toNTM M₁) a c d) (h2 : reachIn (toNTM M₂) b d e) :
    reachIn (toNTM (M₁ ++ M₂)) (a + b) c e :=
  (reachIn_add (toNTM (M₁ ++ M₂)) a b c e).mpr
    ⟨d, reachIn_append_left M₁ M₂ a c d h1, reachIn_append_right M₁ M₂ b d e h2⟩

/-!
**The wiring law, proved.**  `reachIn_seq` composes a sub-table run with another inside the union machine `M₁ ++ M₂` —
no disjointness needed, since `concreteStep` is existential over rules and a superset only adds witnesses.  Next: thread
each `scanNatFrom` field's tape-preservation into the next field's content hypothesis to scan a whole `encodeTransBits`
layout in one machine, then the rule-table scan-and-match and the apply — fragment by verified fragment, not faked.  Not
a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose.concreteStep_append_left
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose.reachIn_toNTM_mono
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose.reachIn_seq
