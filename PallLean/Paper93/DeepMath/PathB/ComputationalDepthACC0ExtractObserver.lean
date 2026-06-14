import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ResidueObserver

/-!
# Extracting a residue/mixed observer from arbitrary `ACC0Circuit` syntax

The normalization files so far *assumed* the `MOD`-bottom structure (`modComb`, `and_of_mods`).  This file
**derives** it from the raw `ACC0Circuit` inductive: by induction on the circuit, every circuit (with positive `MOD`
moduli) is `ObservedBy` a product statistic built from the observer combinators — `modGate_observedBy` for `MOD`
leaves, the projection-to-a-coordinate for `var` leaves, and `ObservedBy.comp`/`.and`/`.or` for the gates — with
state count the **occurrence product** `stateBound` (`q` per `MOD` gate, `2` per `var` leaf, multiplied through
`∧`/`∨`).

So `acc0_modcircuit_searchable`: any `ACC⁰` circuit with `stateBound C < 2^n` is SAT-searchable below brute force —
derived from circuit syntax, no assumed decomposition.  The residue gain is real precisely when the circuit has few
leaves but its `MOD` gates read many variables (e.g. `MOD ∧ MOD` over all inputs: `stateBound = q₁·q₂`, while the
junta bound is `2^n`).

## What is proved (clean axioms, no `sorry`)

* `stateBound`, `ModsPos` — the occurrence-product bound and the positive-modulus predicate.
* `acc0_residueObserved` — **by induction, `eval C` is `ObservedBy` a statistic of state count `≤ stateBound C`**.
* `acc0_modcircuit_searchable` — any `ACC⁰` circuit with `stateBound C < 2^n` is SAT-searchable in `< 2^n` cells.

## Honest scope

The genuine "arbitrary circuit → observer" derivation, via observer-induction over the `ACC0Circuit` syntax — no
assumed bottom.  The bound `stateBound` is the *occurrence* product, so the gain is for circuits with few leaves
(where `MOD` gates supply the residue compression).  It does **not** give a *small* bound for an arbitrary `ACC⁰`
circuit — that requires the structural shrinkage of the full Yao–Beigel–Tarui normal form (still open).  Still the
cell-count model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ExtractObserver

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver

variable {n : ℕ}

/-- The occurrence-product state bound: `q` per `MOD` gate, `2` per `var` leaf, multiplied through `∧`/`∨`. -/
def stateBound : ACC0Circuit n → ℕ
  | .const _ => 1
  | .var _ => 2
  | .not c => stateBound c
  | .and a b => stateBound a * stateBound b
  | .or a b => stateBound a * stateBound b
  | .mod q _ _ => q

/-- Every `MOD` gate in the circuit has positive modulus (so its residue space is finite). -/
def ModsPos : ACC0Circuit n → Prop
  | .const _ => True
  | .var _ => True
  | .not c => ModsPos c
  | .and a b => ModsPos a ∧ ModsPos b
  | .or a b => ModsPos a ∧ ModsPos b
  | .mod q _ _ => 0 < q

/-- `f` is observed by some statistic of state count `≤ B`. -/
def ResidueObservedBy (f : (Fin n → Bool) → Bool) (B : ℕ) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (stat : (Fin n → Bool) → S),
    ObservedBy f stat ∧ Fintype.card S ≤ B

/-- **The extraction (proved, induction on the circuit): `eval C` is observed by a statistic of state count
`≤ stateBound C`.**  `MOD` leaves contribute their residue observer (`ZMod q`, `card q`), `var` leaves a
single-coordinate projection (`Bool`, `card 2`), and `∧`/`∨`/`¬` compose via the observer combinators. -/
theorem acc0_residueObserved :
    ∀ (C : ACC0Circuit n), ModsPos C → ResidueObservedBy (eval C) (stateBound C) := by
  intro C
  induction C with
  | const b =>
      intro _
      exact ⟨Unit, inferInstance, inferInstance, fun _ => (), ⟨fun _ => b, fun _ => rfl⟩, by simp [stateBound]⟩
  | var i =>
      intro _
      exact ⟨Bool, inferInstance, inferInstance, fun x => x i, ⟨id, fun _ => rfl⟩, by simp [stateBound]⟩
  | not c ih =>
      intro h
      obtain ⟨S, fS, dS, stat, obs, hcard⟩ := ih h
      exact ⟨S, fS, dS, stat, obs.comp (fun b => !b), hcard⟩
  | and a b iha ihb =>
      intro h
      obtain ⟨Sa, fa, da, sta, oba, hca⟩ := iha h.1
      obtain ⟨Sb, fb, db, stb, obb, hcb⟩ := ihb h.2
      letI := fa; letI := da; letI := fb; letI := db
      refine ⟨Sa × Sb, inferInstance, inferInstance, fun x => (sta x, stb x), ObservedBy.and oba obb, ?_⟩
      rw [Fintype.card_prod]
      exact Nat.mul_le_mul hca hcb
  | or a b iha ihb =>
      intro h
      obtain ⟨Sa, fa, da, sta, oba, hca⟩ := iha h.1
      obtain ⟨Sb, fb, db, stb, obb, hcb⟩ := ihb h.2
      letI := fa; letI := da; letI := fb; letI := db
      refine ⟨Sa × Sb, inferInstance, inferInstance, fun x => (sta x, stb x), ObservedBy.or oba obb, ?_⟩
      rw [Fintype.card_prod]
      exact Nat.mul_le_mul hca hcb
  | mod q S t =>
      intro h
      letI : NeZero q := ⟨h.ne'⟩
      exact ⟨ZMod q, inferInstance, inferInstance, fun x => modQStatOn S q x,
        modGate_observedBy ⟨q, S, t⟩, le_of_eq (ZMod.card q)⟩

/-- **Any `ACC⁰` circuit with `stateBound C < 2^n` is SAT-searchable below brute force (proved).**  The observer is
*derived* from the circuit syntax (`acc0_residueObserved`); its image search decides SAT in `< 2^n` cells. -/
theorem acc0_modcircuit_searchable (C : ACC0Circuit n) (h : ModsPos C) (hregime : stateBound C < 2 ^ n) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (stat : (Fin n → Bool) → S) (g : S → Bool),
      (Satisfiable (eval C) ↔ ∃ s ∈ Finset.univ.image stat, g s = true)
        ∧ (Finset.univ.image stat).card < 2 ^ n := by
  obtain ⟨S, fS, dS, stat, ⟨g, hg⟩, hcard⟩ := acc0_residueObserved C h
  letI := fS; letI := dS
  exact ⟨S, fS, dS, stat, g, observed_sat_iff g hg,
    lt_of_le_of_lt (le_trans (observed_cellCount_le stat) hcard) hregime⟩

end PallLean.Paper93.DeepMath.PathB.ACC0ExtractObserver

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExtractObserver.acc0_residueObserved
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExtractObserver.acc0_modcircuit_searchable
