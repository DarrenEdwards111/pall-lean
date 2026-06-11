import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer10NPBridge

/-!
# Layer 10D — observer-space / branching-holography invariant (research sandbox)

A candidate frontier framework, formalized under the 10D discipline (named hypothesis, conditional bridges,
**never asserted**): the "observer/holographic invariant" idea — find a measure `I` on Boolean functions
that small circuits cannot inflate, but the target language can.  See
`SCOPE_LAYER10D_OBSERVER_BRANCHING_HOLOGRAPHY.md` for what the observer space / branching map / Ramanujan
expanders would have to supply, and the barrier analysis.

* `ObserverFrontierHyp L` — **CANDIDATE HYPOTHESIS (OPEN)**: an invariant `I n : BoolFn n → ℕ`, polynomially
  bounded by circuit *size* (A), whose value on the target `L` is not bounded by any `h ∘ poly` (B).
* `not_ppoly_of_observerHyp` — **(→) bridge**: such an invariant proves `L ∉ P/poly`.
* `p_ne_np_of_observerHyp` — with `P ⊆ P/poly` and an `NP/poly` target, `P ≠ NP/poly`.

## The honest verdict (why this is not a shortcut)

`not_ppoly_of_observerHyp` shows `ObserverFrontierHyp L → ¬ Ppoly L`: **the hypothesis is at least as strong
as the lower bound it would prove.**  So the framework *relocates* the difficulty (to "construct `I`"), it
does **not** remove it.  Indeed it is *equivalent* to the lower bound — taking `I n :=` the minimum circuit
size of `f` (with `h = id`) witnesses the converse (this uses the standard "every function has a circuit"
universality; stated in the scope doc, not formalized here).  Moreover, by Layer 10A, if the induced
predicate "`I n f` is large" is *constructive and large* it is a **natural property** and breaks PRFs — so a
working `I` must be non-natural.  The framework is viable only insofar as observer-space / holography /
expanders yield a `non-natural`, `non-relativizing` invariant; nothing here establishes that.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer10

open PallLean.Paper93.DeepMath.PathB

/-- **CANDIDATE HYPOTHESIS (OPEN, never asserted).**  An *observer/holographic invariant*: a measure
`I n : BoolFn n → ℕ` such that

* **(A)** `I` is bounded by a polynomial `h` of circuit *size*: `f ∈ SIZE n s → I n f ≤ h s`; and
* **(B)** on the target `L`, `I n (L n)` is **not** bounded by `h ∘ p` for any polynomial `p` — no
  polynomial circuit-size budget keeps the invariant bounded.

A candidate `I` is exactly what an observer-space / branching-holography / Ramanujan-expander construction
must produce. -/
def ObserverFrontierHyp (L : Layer7.BoolLang) : Prop :=
  ∃ (I : (n : ℕ) → ((Fin n → Bool) → Bool) → ℕ) (h : ℕ → ℕ),
    Layer7.IsPolyBounded h ∧
    (∀ (n s : ℕ) (f : (Fin n → Bool) → Bool), f ∈ Layer8.SIZE n s → I n f ≤ h s) ∧
    (¬ ∃ p : ℕ → ℕ, Layer7.IsPolyBounded p ∧ ∀ n, I n (L n) ≤ h (p n))

/-- **Bridge (→).**  An observer invariant separating `L` from polynomial circuit size proves
`L ∉ P/poly`.  (Hence the hypothesis is *at least as strong* as the lower bound: no shortcut.) -/
theorem not_ppoly_of_observerHyp {L : Layer7.BoolLang} (hyp : ObserverFrontierHyp L) :
    ¬ Layer9.Ppoly L := by
  rintro ⟨p, hp, hsize⟩
  obtain ⟨I, h, hh, hbound, hno⟩ := hyp
  exact hno ⟨p, hp, fun n => hbound n (p n) (L n) (hsize n)⟩

/-- **Conditional capstone.**  With `P ⊆ P/poly` (standard) and an `NP/poly` target carrying an observer
invariant, `P ≠ NP/poly`.  All hard inputs are explicit hypotheses; none is asserted. -/
theorem p_ne_np_of_observerHyp {P : ComplexityClass} (hPsub : P ⊆ PpolyClass)
    {L : Layer7.BoolLang} (hLNP : L ∈ NPpolyClass) (hyp : ObserverFrontierHyp L) :
    P ≠ NPpolyClass :=
  p_ne_np_of_np_hard hPsub hLNP (not_ppoly_of_observerHyp hyp)

end PallLean.Paper93.DeepMath.PathB.Layer10

#print axioms PallLean.Paper93.DeepMath.PathB.Layer10.not_ppoly_of_observerHyp
#print axioms PallLean.Paper93.DeepMath.PathB.Layer10.p_ne_np_of_observerHyp
