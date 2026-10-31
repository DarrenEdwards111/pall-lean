import Mathlib.Data.Nat.Basic

/-!
# What a proof that "SAT resists" would need — the resistance measure

The goal (`BatchVsResist`): show SAT's DAG resists, `cbudget(T d) ≥ 2^d`.  This file writes down *exactly*
the object such a proof must produce — a **resistance measure** — and the tension that makes it hard.

A proof cannot argue about `cbudget` directly (it is a minimum over all circuits, including unknown
batching tricks).  Every known circuit lower bound instead exhibits a **measure** `μ` on functions that
under-approximates `cbudget` and can be *tracked through composition*:

## The spec (structure `ResistanceMeasure`)

* **`lower_bound`** — `∀ f, μ f ≤ cbudget f`: `μ` is a valid lower bound (proving `μ` large proves
  `cbudget` large).
* **`superadditive`** — `∀ d, 2·μ(T d) ≤ μ(T (d+1))`: `μ` **doubles** through the tower — it *survives
  batching* (this is the content: `cbudget` itself need not double, but `μ` provably does).
* **`base`** — `1 ≤ μ(T 0)`.

## What is proved

* **`resistance_measure_separates`** — such a measure *is* the proof: `2^d ≤ μ(T d) ≤ cbudget(T d)`.  A
  resistance measure yields `cbudget(SAT) ≥ 2^d` — SAT resists.
* **`no_measure_below_batched`** — the tension: a superadditive measure with nonzero base **cannot** stay
  bounded (`≤ 1`).  So `μ` cannot be superadditive *universally* — on the easy `sharingTower`
  (`cbudget = 1`) it would force `2^d ≤ 1`.  The superadditivity must be **specific to the SAT tower**:
  the measure has to *know* SAT resists where easy functions batch.

## What such a proof needs, and why it's open

1. **A measure `μ ≤ cbudget`** — a valid lower-bound method (KW communication complexity, a formal
   complexity measure, …).
2. **A proof that `μ` doubles on the SAT tower** (`superadditive`) — the composition / KRW-style step.
   This is the hard half: it must hold for SAT specifically, not universally (`no_measure_below_batched`).
3. **Non-natural** — else Razborov–Rudich rules it out.

The obstruction: measures for which (2) is provable **cap polynomially** — Khrapchenko `n²`, shrinkage
`n^{5/2}→n^3`; and proving (2) for a strong enough measure is the KRW conjecture, open.  Reaching `2^d`
needs a measure that is superadditive on SAT yet not universally so — exactly what no one has.

**Honest scope.**  This *specifies* the proof object and shows it would separate; it does **not** build a
resistance measure.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ResistanceProof

/-- A **resistance measure** for the SAT tower `T`: a measure `μ` that under-approximates `cbudget` and
provably **doubles** through the tower (survives batching).  This is the object a proof that SAT resists
must produce. -/
structure ResistanceMeasure (Fn : Type) (cbudget : Fn → ℕ) (T : ℕ → Fn) where
  /-- the measure on functions. -/
  mu : Fn → ℕ
  /-- `μ` is a valid circuit lower bound. -/
  lower_bound : ∀ f, mu f ≤ cbudget f
  /-- `μ` doubles through the tower — it survives batching (the content). -/
  superadditive : ∀ d, 2 * mu (T d) ≤ mu (T (d + 1))
  /-- nonzero base. -/
  base : 1 ≤ mu (T 0)

/-- **A resistance measure separates (proved).**  It telescopes to `2^d ≤ μ(T d)`, and `μ ≤ cbudget`
gives `2^d ≤ cbudget(T d)` — SAT resists, `cbudget(SAT) ≥ 2^d`.  Producing such a measure *is* the proof. -/
theorem resistance_measure_separates {Fn : Type} {cbudget : Fn → ℕ} {T : ℕ → Fn}
    (rm : ResistanceMeasure Fn cbudget T) (d : ℕ) : 2 ^ d ≤ cbudget (T d) := by
  have h : 2 ^ d ≤ rm.mu (T d) := by
    induction d with
    | zero => rw [Nat.pow_zero]; exact rm.base
    | succ d ih =>
      rw [Nat.pow_succ]
      calc 2 ^ d * 2 = 2 * 2 ^ d := Nat.mul_comm _ _
      _ ≤ 2 * rm.mu (T d) := Nat.mul_le_mul (Nat.le_refl 2) ih
      _ ≤ rm.mu (T (d + 1)) := rm.superadditive d
  exact le_trans h (rm.lower_bound (T d))

/-- **The tension — superadditivity cannot be universal (proved).**  A measure that is superadditive with
nonzero base cannot stay bounded (`≤ 1`): from `1 ≤ μ 0` and `2·μ 0 ≤ μ 1` we get `μ 1 ≥ 2 > 1`.  So on
the easy `sharingTower` (`cbudget = 1`) no such measure exists — the resistance measure's superadditivity
must be **specific to the SAT tower**, knowing SAT resists where easy functions batch. -/
theorem no_measure_below_batched :
    ¬ ∃ mu : ℕ → ℕ, (1 ≤ mu 0) ∧ (∀ d, 2 * mu d ≤ mu (d + 1)) ∧ (∀ d, mu d ≤ 1) := by
  rintro ⟨mu, hbase, hsuper, hle⟩
  have h1 : 2 * mu 0 ≤ mu 1 := hsuper 0
  have h2 : mu 1 ≤ 1 := hle 1
  omega

end PallLean.Paper93.DeepMath.PathB.ResistanceProof

#print axioms PallLean.Paper93.DeepMath.PathB.ResistanceProof.resistance_measure_separates
#print axioms PallLean.Paper93.DeepMath.PathB.ResistanceProof.no_measure_below_batched
