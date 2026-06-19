import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ConcreteNTM

/-!
# Entry 329 — routing-machine assembly: sub-table monotonicity (proved)

Entry 328 built and verified the lazy-diagonal *decision procedure*; entry 327 reduced the concrete hierarchy to a
routing `TMachine` realising it within `f`.  Building that routing table means assembling it from phase sub-machines —
the decode, the universal simulator (296–298), the bounded-complement search (299) — into **one** transition table.
This file proves the foundational assembly lemma that makes such composition sound: a concrete machine's computation is
preserved when its transition table is **embedded in a larger one**.

**The mechanism.**  `concreteStep M c d := ∃ t ∈ M, t.1 = (c.1, readSym c) ∧ d = applyTrans c t` quantifies over the
machine's rules.  So if `M ⊆ M'` (the routing table contains the phase's rules), every step of `M` is a step of `M'`,
hence every run and every acceptance of `M` lifts to `M'`.  This is exactly how the routing table is built: lay the
phase sub-tables on disjoint state ranges and `union` them; each phase's *already-proved* run (universal simulation,
complement search) then holds in the combined table by monotonicity.

## What is proved (clean axioms, no `sorry`)

* **`concreteStep_mono`** (PROVED) — `M ⊆ M' → concreteStep M c d → concreteStep M' c d`.
* **`reachIn_mono`** (PROVED) — `M ⊆ M' →` every `k`-step run of `toNTM M` is a `k`-step run of `toNTM M'`.
* **`acceptsWithin_mono_machine`** (PROVED) — `M ⊆ M' →` every bounded acceptance of `toNTM M` is one of `toNTM M'`
  (same init `(0,0,x)`, same accept `state = 1`).
* **`acceptsWithin_union_left` / `acceptsWithin_union_right`** (PROVED) — acceptance by either part of a `M₁ ++ M₂`
  combined table lifts to the union — the two-phase assembly primitive.

## Honest scope

This proves the **assembly foundation** for the routing `TMachine`: phase sub-tables embed into the combined table with
their runs and acceptances preserved (`acceptsWithin_mono_machine`), and the two-table union lifts either part's
acceptance.  It is the sound mechanism for *combining* the (already-proved) universal-simulation and bounded-complement
sub-machines into one transition table.  It does **not** yet build the routing table itself: that additionally needs the
**control-flow wiring** (state-offsetting the phases and redirecting decode → dispatch → simulate/complement via the
transition structure) and the **`f`-timing** analysis — the genuine remaining low-level engineering, **not built here and
not faked**.  This entry is the first verified brick of that build.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineComposition

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM concreteStep)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn acceptsWithin)

/-- **A step survives table enlargement (PROVED).**  If `M ⊆ M'`, any matching rule of `M` is a rule of `M'`, so the
step relation only grows. -/
theorem concreteStep_mono {M M' : TMachine} (h : M ⊆ M') {c d : ℕ × ℕ × List Bool}
    (hs : concreteStep M c d) : concreteStep M' c d := by
  obtain ⟨t, ht, h1, h2⟩ := hs
  exact ⟨t, h ht, h1, h2⟩

/-- **A run survives table enlargement (PROVED).**  Every `k`-step run of `toNTM M` is a `k`-step run of `toNTM M'`
when `M ⊆ M'`. -/
theorem reachIn_mono {M M' : TMachine} (h : M ⊆ M') :
    ∀ (k : ℕ) (c c' : ℕ × ℕ × List Bool), reachIn (toNTM M) k c c' → reachIn (toNTM M') k c c' := by
  intro k
  induction k with
  | zero => intro c c' hr; exact hr
  | succ k ih =>
      intro c c' hr
      obtain ⟨d, hstep, hrest⟩ := hr
      exact ⟨d, concreteStep_mono h hstep, ih d c' hrest⟩

/-- **Acceptance survives table enlargement (PROVED).**  `toNTM M` and `toNTM M'` share the initial config `(0,0,x)` and
the accept test `state = 1`; with the run lifted by `reachIn_mono`, any bounded acceptance of `M` is one of `M'`. -/
theorem acceptsWithin_mono_machine {M M' : TMachine} (h : M ⊆ M') {x : List Bool} {t : ℕ}
    (ha : acceptsWithin (toNTM M) x t) : acceptsWithin (toNTM M') x t := by
  obtain ⟨k, hk, c, hr, hacc⟩ := ha
  exact ⟨k, hk, c, reachIn_mono h k _ c hr, hacc⟩

/-- **Two-phase union, left (PROVED).**  Acceptance by the first sub-table lifts to the combined table `M₁ ++ M₂`. -/
theorem acceptsWithin_union_left {M₁ M₂ : TMachine} {x : List Bool} {t : ℕ}
    (ha : acceptsWithin (toNTM M₁) x t) : acceptsWithin (toNTM (M₁ ++ M₂)) x t :=
  acceptsWithin_mono_machine (List.subset_append_left M₁ M₂) ha

/-- **Two-phase union, right (PROVED).**  Acceptance by the second sub-table lifts to the combined table `M₁ ++ M₂`. -/
theorem acceptsWithin_union_right {M₁ M₂ : TMachine} {x : List Bool} {t : ℕ}
    (ha : acceptsWithin (toNTM M₂) x t) : acceptsWithin (toNTM (M₁ ++ M₂)) x t :=
  acceptsWithin_mono_machine (List.subset_append_right M₁ M₂) ha

/-!
**The assembly foundation, proved.**  A concrete machine's runs and acceptances are preserved under enlarging its
transition table (`concreteStep_mono`, `reachIn_mono`, `acceptsWithin_mono_machine`), and the two-table union lifts
either part's acceptance (`acceptsWithin_union_left/right`).  So the routing table is built by laying the phase
sub-machines (decode, universal simulation 296–298, bounded complement 299) into one combined table, each phase's proved
computation surviving by monotonicity.  What remains is the **control-flow wiring** (state offsets, decode → dispatch →
simulate/complement redirection) and the **`f`-timing** — the genuine remaining low-level engineering, not faked.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineComposition

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineComposition.concreteStep_mono
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineComposition.reachIn_mono
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineComposition.acceptsWithin_mono_machine
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineComposition.acceptsWithin_union_left
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineComposition.acceptsWithin_union_right
