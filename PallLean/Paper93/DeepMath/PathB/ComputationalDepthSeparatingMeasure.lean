import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer10ObserverHolography
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNaturalProofsBarrier

/-!
# `SeparatingMeasure` — the precise target object for a circuit lower bound

This states, as a single formal object, exactly what a **separating measure** for a Boolean language
`L` must be — the honest target that a genuine `L ∉ P/poly` proof (hence `P ≠ NP`) must produce, and the
thing every measure in this repository so far has *failed* to be (SPDP rank: non-separating / refuted;
gate-elimination `cbudget`: linearly capped).

## The two core conditions (these alone give the separation)

* **(A) circuit-bounded** — a polynomial `h` with `f ∈ SIZE n s → I n f ≤ h s` (small circuits keep `I`
  small; the P-side upper bound);
* **(B) hard-on-target** — no polynomial size budget bounds `I` on `L`: `¬ ∃ p poly, ∀ n, I n (L n) ≤ h(p n)`
  (the NP-side lower bound).

`separatingMeasure_not_ppoly` proves `(A)+(B) ⇒ L ∉ P/poly`.  These two alone are *equivalent* to the
lower bound (`toObserverFrontierHyp` packages them into the existing `ObserverFrontierHyp`), so the content
is in producing an `I` **analyzable enough to prove them while dodging the barriers**.

## The barrier obligations

* **Non-natural (Razborov–Rudich)** — captured and **proved as a necessity here**: the induced hardness
  property `hardProp = fun f => h s < I n f` is `UsefulAgainst` every cheap class inside `SIZE n s`
  (`separatingMeasure_hardProp_useful`), so — if it is also *large* — it cannot be *constructive* under the
  cryptographic barrier (`separatingMeasure_nonnatural`).  A separating measure is therefore forced to be
  non-natural: its large-`I` set is rare or non-constructive.
* **Non-relativizing (Baker–Gill–Solovay)** and **non-algebrizing (Aaronson–Wigderson)** — obligations on
  the *proof method* (the measure must read circuit internals / survive low-degree oracle extension). These
  are documented as the remaining un-formalized obligations; they are properties of how (A)/(B) are proved,
  not of `I` in isolation, so they are **not** discharged here.

Nothing in this file is `P ≠ NP`: it is the precise *statement* of the target, plus the one barrier
(non-naturalness) that any separating measure provably satisfies.
-/

namespace PallLean.Paper93.DeepMath.PathB.SeparatingMeasure

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NaturalProofsBarrier

/-- **A separating measure for `L`** — the two core conditions (A) and (B). -/
structure SeparatingMeasure (L : Layer7.BoolLang) where
  /-- The measure. -/
  I : (n : ℕ) → ((Fin n → Bool) → Bool) → ℕ
  /-- The polynomial circuit-size bound. -/
  h : ℕ → ℕ
  hpoly : Layer7.IsPolyBounded h
  /-- **(A) circuit-bounded (P-side).** -/
  circuitBounded : ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool),
    f ∈ Layer8.SIZE n s → I n f ≤ h s
  /-- **(B) hard-on-target (NP-side).** -/
  hardOnTarget : ¬ ∃ p : ℕ → ℕ, Layer7.IsPolyBounded p ∧ ∀ n, I n (L n) ≤ h (p n)

variable {L : Layer7.BoolLang}

/-- A separating measure **is** an observer-frontier invariant (identical (A)+(B) content). -/
def SeparatingMeasure.toObserverFrontierHyp (sm : SeparatingMeasure L) :
    Layer10.ObserverFrontierHyp L :=
  ⟨sm.I, sm.h, sm.hpoly, sm.circuitBounded, sm.hardOnTarget⟩

/-- **THE SEPARATION (proved).** A separating measure proves `L ∉ P/poly`. -/
theorem separatingMeasure_not_ppoly (sm : SeparatingMeasure L) : ¬ Layer9.Ppoly L :=
  Layer10.not_ppoly_of_observerHyp sm.toObserverFrontierHyp

/-- **Usefulness (proved from (A)).** Any function whose measure exceeds `h s` is not a size-`s` circuit. -/
theorem separatingMeasure_useful (sm : SeparatingMeasure L) (n s : ℕ)
    (f : (Fin n → Bool) → Bool) (hf : sm.h s < sm.I n f) : f ∉ Layer8.SIZE n s := by
  intro hmem
  exact absurd (sm.circuitBounded n s f hmem) (by omega)

/-- The **induced hardness property** at scale `n`, size threshold `s`. -/
def SeparatingMeasure.hardProp (sm : SeparatingMeasure L) (n s : ℕ) :
    ((Fin n → Bool) → Bool) → Prop := fun f => sm.h s < sm.I n f

/-- **The hardness property is useful (proved).**  Against any cheap class landing in `SIZE n s`:
every function of high measure differs from every cheap decider. -/
theorem separatingMeasure_hardProp_useful (sm : SeparatingMeasure L) (n s N : ℕ)
    (cheap : Fin N → ((Fin n → Bool) → Bool)) (hcheap : ∀ i, cheap i ∈ Layer8.SIZE n s) :
    UsefulAgainst cheap (sm.hardProp n s) := by
  intro f hf i heq
  have hmem : f ∈ Layer8.SIZE n s := heq ▸ hcheap i
  have hb := sm.circuitBounded n s f hmem
  have hf' : sm.h s < sm.I n f := hf
  omega

/-- **NON-NATURALNESS IS FORCED (proved).**  Under the Razborov–Rudich barrier and its cryptographic
assumption, a separating measure's hardness property — *if large* — cannot be constructive.  So a
separating measure is provably non-natural: its high-measure set is rare or non-constructive. -/
theorem separatingMeasure_nonnatural (sm : SeparatingMeasure L) (n s N : ℕ)
    (cheap : Fin N → ((Fin n → Bool) → Bool)) (hcheap : ∀ i, cheap i ∈ Layer8.SIZE n s)
    (Constructive : ((((Fin n → Bool) → Bool)) → Prop) → Prop) (Crypto : Prop)
    (hRR : RazborovRudichBarrier Constructive cheap Crypto) (hC : Crypto)
    (hlarge : LargeProperty (sm.hardProp n s)) :
    ¬ Constructive (sm.hardProp n s) := by
  intro hcons
  exact hRR hC (sm.hardProp n s) hlarge hcons
    (separatingMeasure_hardProp_useful sm n s N cheap hcheap)

/-- **The conditional capstone (proved).**  With `P ⊆ P/poly` and an `NP/poly` target carrying a
separating measure, `P ≠ NP/poly`.  Every hard input is an explicit hypothesis. -/
theorem p_ne_np_of_separatingMeasure {P : Layer10.ComplexityClass} (hPsub : P ⊆ Layer10.PpolyClass)
    (hLNP : L ∈ Layer10.NPpolyClass) (sm : SeparatingMeasure L) : P ≠ Layer10.NPpolyClass :=
  Layer10.p_ne_np_of_observerHyp hPsub hLNP sm.toObserverFrontierHyp

end PallLean.Paper93.DeepMath.PathB.SeparatingMeasure

#print axioms PallLean.Paper93.DeepMath.PathB.SeparatingMeasure.separatingMeasure_not_ppoly
#print axioms PallLean.Paper93.DeepMath.PathB.SeparatingMeasure.separatingMeasure_nonnatural
