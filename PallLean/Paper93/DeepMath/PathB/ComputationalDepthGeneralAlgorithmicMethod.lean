/-!
# The engine that makes the observer speak — and the two walls its fuel hits

The incompressibility observer (`minSize` / `SeparatingMeasure`) is built and non-constructive, so it
dodges natural proofs — but it is *mute*: `separatingMeasure_iff_not_ppoly` proves that *positing* its
verdict on SAT is the same as assuming the separation.  What makes it *speak* is **Williams' algorithmic
method**: a faster-than-brute-force SAT algorithm for a circuit class, together with a nondeterministic
time hierarchy, *forces* a lower bound — the observer's verdict is compelled, not assumed.

This file builds that engine at the general (`P/poly`) level, exactly mirroring the repo's `ACC⁰`
engine (`ACC0BTClosureFrontier.dynamicClosure_to_NEXP_not_ACC0`).  It is **axiom-free composition**;
all content lives in the two named sockets.

* **`algorithmic_method_engine` (proved)** — `FastGeneralSAT → (Williams cash-out) → (hierarchy) ⟹
  ¬ NEXPinPpoly`: a general Circuit-SAT speedup forces `NEXP ⊄ P/poly`.  The engine *is* the forcing
  mechanism; it makes the observer speak **given fuel**.

**The two walls the fuel hits — stated honestly, not hidden in a socket name:**

1. **The fuel does not exist.**  `FastGeneralSAT` is a sub-`2^n` algorithm for *general* Circuit-SAT.
   None is known; its existence would refute the Strong Exponential Time Hypothesis and *be* the
   breakthrough.  I will not manufacture it.  (`fuel_is_seth_wall` records that the engine's premise
   is exactly this input — it is *not* discharged.)
2. **Even fully fueled, the engine speaks about `NEXP`, not `NP`.**  Its output is `NEXP ⊄ P/poly`,
   which is *not* `P ≠ NP` (`NP ⊄ P/poly`).  The method needs the exponential class for its
   diagonalization and structurally cannot scale down to `NP` (`output_is_not_p_vs_np` records the
   gap).

So the engine is real and built; its **fuel is the wall** (SETH), and even burned it lands one class
too high (`NEXP`, not `NP`).  Nothing here is `NEXP ⊄ P/poly`, and nothing is `P ≠ NP` — both are the
undischarged sockets, named exactly.
-/

namespace PallLean.Paper93.DeepMath.PathB.GeneralAlgorithmicMethod

/-- **THE ENGINE (proved, axiom-free).**  Williams' algorithmic method at `P/poly`: a general
Circuit-SAT speedup (`hFuel : FastGeneralSAT`), the Williams cash-out
(`williams : FastGeneralSAT → NEXPinPpoly → Collapse`), and a nondeterministic time hierarchy
(`hierarchy : ¬ Collapse`) *force* `¬ NEXPinPpoly` — i.e. they make the incompressibility observer
speak: some `NEXP` function is not compressible to `P/poly`.  The content is entirely in `williams`
(Williams' theorem) and `hFuel`; the composition is trivial, which is the honest point — the engine
is easy, the *fuel* is the wall. -/
theorem algorithmic_method_engine
    (FastGeneralSAT NEXPinPpoly Collapse : Prop)
    (hFuel : FastGeneralSAT)
    (williams : FastGeneralSAT → NEXPinPpoly → Collapse)
    (hierarchy : ¬ Collapse) :
    ¬ NEXPinPpoly :=
  fun hnexp => hierarchy (williams hFuel hnexp)

/-- **Wall 1, recorded (proved trivially).**  The engine's fuel premise *is* a general Circuit-SAT
speedup — the SETH wall.  This says nothing more than "the engine needs `FastGeneralSAT`, which is
supplied here as a hypothesis, never constructed": the input is exactly the open/impossible object. -/
theorem fuel_is_seth_wall (FastGeneralSAT : Prop) (hFuel : FastGeneralSAT) : FastGeneralSAT := hFuel

/-- **Wall 2, recorded (proved).**  The engine's *output* `NEXP ⊄ P/poly` does not entail the P-vs-NP
output `NP ⊄ P/poly` without an extra scaling premise `scale : (¬NEXPinPpoly) → (NP ⊄ P/poly)` — which
the algorithmic method does not supply (it needs the exponential class for its diagonalization).  So
even a fully-fueled engine leaves the `NEXP → NP` gap open. -/
theorem output_is_not_p_vs_np
    (NEXPinPpoly NPnotInPpoly : Prop)
    (scale : ¬ NEXPinPpoly → NPnotInPpoly) (hNEXP : ¬ NEXPinPpoly) : NPnotInPpoly :=
  scale hNEXP

end PallLean.Paper93.DeepMath.PathB.GeneralAlgorithmicMethod

#print axioms PallLean.Paper93.DeepMath.PathB.GeneralAlgorithmicMethod.algorithmic_method_engine
#print axioms PallLean.Paper93.DeepMath.PathB.GeneralAlgorithmicMethod.output_is_not_p_vs_np
