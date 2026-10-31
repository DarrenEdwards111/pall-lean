import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ExtractObserver

/-!
# Deduplicated state bound: collapsing the occurrence overcount

`acc0_residueObserved` (`…ACC0ExtractObserver`) bounds the observer state count by the *occurrence* product
`stateBound C`: a variable read by `k` leaves contributes `2^k`, and the same `var` leaf appearing under both arms of
an `∧` is double-counted.  This file proves a **strictly smaller** bound by splitting the observer into two shared
parts:

* a `MOD`-residue part of card `≤ modOcc C` (the product of the `MOD`-gate moduli — variables read *inside* a `MOD`
  gate are absorbed into its residue, never costing `2`);
* a **single** projection onto the *deduplicated* union support `varSupp C` of the `var`-leaves — card `2^|varSupp C|`,
  counting each variable **once** no matter how many leaves read it.

The key structural step is the `∧`/`∨` case: instead of pairing two independent projections (which would give
`2^(|vsₐ|+|vs_b|)`), both arms share **one** projection onto `varSupp a ∪ varSupp b`, recovering each arm's
projection by restriction along the inclusion `vsₐ ⊆ vsₐ ∪ vs_b`.  Hence the bound carries `2^|vsₐ ∪ vs_b|`, and
`|vsₐ ∪ vs_b| ≤ |vsₐ| + |vs_b|` is exactly the collapse.

So `acc0_dedup_searchable`: any `ACC⁰` circuit (positive `MOD` moduli) with `modOcc C · 2^|varSupp C| < 2^n` is
SAT-searchable below brute force — and this fires on circuits that neither the pure-support bound
(`2^|support C|`, useless once the `MOD` gates read all variables) nor the pure occurrence bound (`stateBound C`,
which double-counts shared `var`-leaves) can reach.

## What is proved (clean axioms, no `sorry`)

* `modOcc`, `varSupp` — the `MOD`-occurrence product and the deduplicated `var`-leaf support.
* `acc0_dedupObserved` — **by induction, `eval C` is observed by `(mod-residue, projection to varSupp C)` with the
  residue part of card `≤ modOcc C`**; the `∧`/`∨` arms share one union-support projection.
* `acc0_dedup_searchable` — `modOcc C · 2^|varSupp C| < 2^n` ⇒ SAT-searchable in `< 2^n` cells.

## Honest scope

This is a *strict tightening* of the occurrence bound (variables counted once, `MOD`-internal variables absorbed),
not a new separation.  It still does **not** give a small bound for an arbitrary `ACC⁰` circuit whose `var`-leaves
read all `n` variables (`varSupp C = univ` ⇒ `2^n`); the structural shrinkage that an arbitrary `ACC⁰` circuit
reduces to a *small* `MOD`/bounded-support bottom is the full Yao–Beigel–Tarui normal form (still open).  Still the
cell-count model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DedupShrink

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ExtractObserver

variable {n : ℕ}

/-- The `MOD`-occurrence product: `q` per `MOD` gate, `1` for `var`/`const` leaves (variables read inside a `MOD`
gate are absorbed into its residue and never cost `2`), multiplied through `∧`/`∨`. -/
def modOcc : ACC0Circuit n → ℕ
  | .const _ => 1
  | .var _ => 1
  | .not c => modOcc c
  | .and a b => modOcc a * modOcc b
  | .or a b => modOcc a * modOcc b
  | .mod q _ _ => q

/-- The **deduplicated** support of the `var`-leaves: the *set* of variables read by `var` leaves (so a variable
read by several leaves is counted once), with `MOD` gates contributing nothing. -/
def varSupp : ACC0Circuit n → Finset (Fin n)
  | .const _ => ∅
  | .var i => {i}
  | .not c => varSupp c
  | .and a b => varSupp a ∪ varSupp b
  | .or a b => varSupp a ∪ varSupp b
  | .mod _ _ _ => ∅

/-- **The deduplicated extraction (proved, induction on the circuit).**  `eval C` is observed by the pair statistic
`(mstat, projection to varSupp C)`, where the residue part `mstat` has card `≤ modOcc C`.  In the `∧`/`∨` cases the
two arms share a *single* projection onto `varSupp a ∪ varSupp b`, so the deduplicated support — not the sum of the
arms' supports — controls the cost. -/
theorem acc0_dedupObserved :
    ∀ (C : ACC0Circuit n), ModsPos C →
      ∃ (Sm : Type) (_ : Fintype Sm) (_ : DecidableEq Sm) (mstat : (Fin n → Bool) → Sm),
        Fintype.card Sm ≤ modOcc C ∧
          ObservedBy (eval C) (fun x => (mstat x, fun i : ↥(varSupp C) => x i.val)) := by
  intro C
  induction C with
  | const b =>
      intro _
      exact ⟨Unit, inferInstance, inferInstance, fun _ => (), by simp [modOcc],
        ⟨fun _ => b, fun _ => rfl⟩⟩
  | var i =>
      intro _
      exact ⟨Unit, inferInstance, inferInstance, fun _ => (), by simp [modOcc],
        ⟨fun p => p.2 ⟨i, Finset.mem_singleton_self i⟩, fun _ => rfl⟩⟩
  | not c ih =>
      intro h
      obtain ⟨Sm, fSm, dSm, mstat, hcard, gc, hgc⟩ := ih h
      refine ⟨Sm, fSm, dSm, mstat, hcard, fun p => !(gc p), fun x => ?_⟩
      show (!(eval c x)) = (!(gc (mstat x, fun i : ↥(varSupp c) => x i.val)))
      rw [hgc x]
  | and a b iha ihb =>
      intro h
      obtain ⟨Sa, fa, da, msa, hca, ga, hga⟩ := iha h.1
      obtain ⟨Sb, fb, db, msb, hcb, gb, hgb⟩ := ihb h.2
      letI := fa; letI := da; letI := fb; letI := db
      refine ⟨Sa × Sb, inferInstance, inferInstance, fun x => (msa x, msb x), ?_, ?_⟩
      · rw [Fintype.card_prod]; exact Nat.mul_le_mul hca hcb
      · refine ⟨fun p =>
          ga (p.1.1, fun i : ↥(varSupp a) => p.2 ⟨i.val, Finset.mem_union.mpr (Or.inl i.2)⟩) &&
          gb (p.1.2, fun i : ↥(varSupp b) => p.2 ⟨i.val, Finset.mem_union.mpr (Or.inr i.2)⟩), fun x => ?_⟩
        show (eval a x && eval b x) =
          (ga (msa x, fun i : ↥(varSupp a) => x i.val) && gb (msb x, fun i : ↥(varSupp b) => x i.val))
        rw [hga x, hgb x]
  | or a b iha ihb =>
      intro h
      obtain ⟨Sa, fa, da, msa, hca, ga, hga⟩ := iha h.1
      obtain ⟨Sb, fb, db, msb, hcb, gb, hgb⟩ := ihb h.2
      letI := fa; letI := da; letI := fb; letI := db
      refine ⟨Sa × Sb, inferInstance, inferInstance, fun x => (msa x, msb x), ?_, ?_⟩
      · rw [Fintype.card_prod]; exact Nat.mul_le_mul hca hcb
      · refine ⟨fun p =>
          ga (p.1.1, fun i : ↥(varSupp a) => p.2 ⟨i.val, Finset.mem_union.mpr (Or.inl i.2)⟩) ||
          gb (p.1.2, fun i : ↥(varSupp b) => p.2 ⟨i.val, Finset.mem_union.mpr (Or.inr i.2)⟩), fun x => ?_⟩
        show (eval a x || eval b x) =
          (ga (msa x, fun i : ↥(varSupp a) => x i.val) || gb (msb x, fun i : ↥(varSupp b) => x i.val))
        rw [hga x, hgb x]
  | mod q S t =>
      intro h
      letI : NeZero q := ⟨h.ne'⟩
      obtain ⟨g0, hg0⟩ := modGate_observedBy (⟨q, S, t⟩ : ModGate n)
      exact ⟨ZMod q, inferInstance, inferInstance, fun x => modQStatOn S q x, le_of_eq (ZMod.card q),
        ⟨fun p => g0 p.1, fun x => hg0 x⟩⟩

/-- **Any `ACC⁰` circuit with `modOcc C · 2^|varSupp C| < 2^n` is SAT-searchable below brute force (proved).**  The
observer is the deduplicated `(residue, union-support projection)` statistic of `acc0_dedupObserved`; its image search
decides SAT in `< 2^n` cells.  Fires precisely where the pure-support and pure-occurrence bounds do not. -/
theorem acc0_dedup_searchable (C : ACC0Circuit n) (h : ModsPos C)
    (hreg : modOcc C * 2 ^ (varSupp C).card < 2 ^ n) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (stat : (Fin n → Bool) → S) (g : S → Bool),
      (Satisfiable (eval C) ↔ ∃ s ∈ Finset.univ.image stat, g s = true)
        ∧ (Finset.univ.image stat).card < 2 ^ n := by
  obtain ⟨Sm, fSm, dSm, mstat, hcard, g, hg⟩ := acc0_dedupObserved C h
  letI := fSm; letI := dSm
  refine ⟨Sm × (↥(varSupp C) → Bool), inferInstance, inferInstance,
    fun x => (mstat x, fun i : ↥(varSupp C) => x i.val), g, observed_sat_iff g hg, ?_⟩
  have hfun : Fintype.card (↥(varSupp C) → Bool) = 2 ^ (varSupp C).card := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  calc (Finset.univ.image (fun x => (mstat x, fun i : ↥(varSupp C) => x i.val))).card
      ≤ Fintype.card (Sm × (↥(varSupp C) → Bool)) := observed_cellCount_le _
    _ = Fintype.card Sm * 2 ^ (varSupp C).card := by rw [Fintype.card_prod, hfun]
    _ ≤ modOcc C * 2 ^ (varSupp C).card := Nat.mul_le_mul_right _ hcard
    _ < 2 ^ n := hreg

end PallLean.Paper93.DeepMath.PathB.ACC0DedupShrink

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DedupShrink.acc0_dedupObserved
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DedupShrink.acc0_dedup_searchable
