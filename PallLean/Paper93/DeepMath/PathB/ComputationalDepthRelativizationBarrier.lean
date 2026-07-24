import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSeparatingMeasure

/-!
# The relativization and algebrization obligations for a separating measure

`SeparatingMeasure` already forces **non-naturalness** (`separatingMeasure_nonnatural`).  This file adds
the other two barriers, at the same honest abstraction as the Razborov–Rudich formalization: the
*logical structure* of the obstruction, with the collapse fact carried as a **named hypothesis** (never
asserted), and the impossibility of a barrier-crossing measure **proved**.

## The single abstraction that captures both barriers

An **oracle-relativized size class** `SIZErel : 𝒪 → (n) → ℕ → Set (BoolFn n)` — `SIZErel O n s` is the
set of functions computed by size-`≤ s` circuits with access to oracle `O`.

* Instantiating `𝒪`/`SIZErel` with **plain oracle circuits** ⇒ **relativization** (Baker–Gill–Solovay):
  the collapse hypothesis is "some oracle `O` gives `P^O = NP^O`", i.e. `L^O ∈ P^O/poly`.
* Instantiating with **algebraic / low-degree-extension oracles** ⇒ **algebrization**
  (Aaronson–Wigderson): the collapse hypothesis is an *algebraic* oracle making the target easy.

Both are the same theorem below; the difference is only which oracle class you plug in.

## What is proved vs assumed

* **`OracleCollapseBarrier`** — a **named `Prop`** (BGS / AW), *not asserted*: some oracle collapses the
  target.
* **`no_relativizing_separatingMeasure` (proved)** — a measure that separates `L` relative to **every**
  oracle is impossible once the collapse barrier holds: relative to the collapse oracle, (A) bounds `I`
  on `L` by a polynomial, contradicting (B).  Same one-line shape as `separatingMeasure_not_ppoly`.
* **`separatingMeasure_nonrelativizing` (proved)** — therefore, under the barrier, **no relativizing
  separating measure exists**: a genuine separating measure's (A)/(B) proof *must break* relative to the
  collapse oracle — it must read structure the oracle abstracts away.

Nothing here is `P ≠ NP`.  It is the precise statement of the last two barrier obligations, and the
proof that any separating measure must satisfy them.
-/

namespace PallLean.Paper93.DeepMath.PathB.RelativizationBarrier

open PallLean.Paper93.DeepMath.PathB

/-- A **relativizing separating measure**: (A)+(B) hold *relative to every oracle* `O` in `𝒪`, through
the oracle-relativized size class `SIZErel`. -/
structure RelativizingSeparatingMeasure (L : Layer7.BoolLang) {𝒪 : Type*}
    (SIZErel : 𝒪 → (n : ℕ) → ℕ → Set ((Fin n → Bool) → Bool)) where
  /-- The oracle-relativized measure. -/
  I : 𝒪 → (n : ℕ) → ((Fin n → Bool) → Bool) → ℕ
  h : ℕ → ℕ
  hpoly : Layer7.IsPolyBounded h
  /-- **(A) relative to every oracle.** -/
  circuitBoundedRel : ∀ (O : 𝒪) (n s : ℕ) (f : (Fin n → Bool) → Bool),
    f ∈ SIZErel O n s → I O n f ≤ h s
  /-- **(B) relative to every oracle.** -/
  hardOnTargetRel : ∀ (O : 𝒪),
    ¬ ∃ p : ℕ → ℕ, Layer7.IsPolyBounded p ∧ ∀ n, I O n (L n) ≤ h (p n)

/-- **The oracle-collapse barrier** (named hypothesis, not asserted): some oracle `O` makes the target
`L` easy — `L^O ∈ P^O/poly`.  BGS gives such an `O` for plain oracles; AW gives an algebraic one. -/
def OracleCollapseBarrier (L : Layer7.BoolLang) {𝒪 : Type*}
    (SIZErel : 𝒪 → (n : ℕ) → ℕ → Set ((Fin n → Bool) → Bool)) : Prop :=
  ∃ (O : 𝒪) (p : ℕ → ℕ), Layer7.IsPolyBounded p ∧ ∀ n, (L n) ∈ SIZErel O n (p n)

variable {L : Layer7.BoolLang}

/-- **THE RELATIVIZATION / ALGEBRIZATION OBSTRUCTION (proved).**  A measure that separates `L` relative
to every oracle cannot exist once some oracle collapses the target: relative to that oracle (A) makes
`I` on `L` polynomially bounded, contradicting (B). -/
theorem no_relativizing_separatingMeasure {𝒪 : Type*}
    (SIZErel : 𝒪 → (n : ℕ) → ℕ → Set ((Fin n → Bool) → Bool))
    (rm : RelativizingSeparatingMeasure L SIZErel)
    (barrier : OracleCollapseBarrier L SIZErel) : False := by
  obtain ⟨O, p, hp, hmem⟩ := barrier
  exact rm.hardOnTargetRel O
    ⟨p, hp, fun n => rm.circuitBoundedRel O n (p n) (L n) (hmem n)⟩

/-- **A separating measure must be non-relativizing and non-algebrizing (proved).**  Under the collapse
barrier there is **no** measure separating `L` relative to every oracle.  So a genuine separating
measure fails to relativize/algebrize — its (A)/(B) proof must break relative to the collapse oracle. -/
theorem separatingMeasure_nonrelativizing {𝒪 : Type*}
    (SIZErel : 𝒪 → (n : ℕ) → ℕ → Set ((Fin n → Bool) → Bool))
    (barrier : OracleCollapseBarrier L SIZErel) :
    ¬ Nonempty (RelativizingSeparatingMeasure L SIZErel) := by
  rintro ⟨rm⟩
  exact no_relativizing_separatingMeasure SIZErel rm barrier

/-- **Bridge to `SeparatingMeasure` (proved).**  If a concrete separating measure is the base-oracle
slice of a relativizing one, the barrier refutes it — i.e. no separating measure that extends
oracle-uniformly can survive.  (`base` is the "empty oracle" recovering the unrelativized measure.) -/
theorem separatingMeasure_not_oracleUniform {𝒪 : Type*}
    (SIZErel : 𝒪 → (n : ℕ) → ℕ → Set ((Fin n → Bool) → Bool)) (base : 𝒪)
    (sm : SeparatingMeasure.SeparatingMeasure L)
    (rm : RelativizingSeparatingMeasure L SIZErel)
    (hbase : rm.I base = sm.I)
    (barrier : OracleCollapseBarrier L SIZErel) : False :=
  no_relativizing_separatingMeasure SIZErel rm barrier

end PallLean.Paper93.DeepMath.PathB.RelativizationBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.RelativizationBarrier.no_relativizing_separatingMeasure
#print axioms PallLean.Paper93.DeepMath.PathB.RelativizationBarrier.separatingMeasure_nonrelativizing
