import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameArithVerifier
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameNecessity

/-!
# N-Frame: discharging the saturation (necessity) leg for the arithmetic-verifier class

The necessity direction (`nframe_gap_necessary`) needs `NFrameSaturates F InClass B` — the class contains *every*
low-N-Frame function (the upper-bound / expressiveness half).  This file discharges that leg for the arithmetic-verifier
class of the realizability side: by universality (`exists_verifier_realizing`) the arithmetic verifier realizes *every*
function, so it certainly contains every low-N-Frame one.  The upper-bound half is genuinely provable.

  `ArithRealizable` — a function is realized by some arithmetic verifier.
  `arithRealizable_all` — **PROVED**: *every* function is arith-realizable (the class is `⊤`).
  `arithRealizable_saturates` — **PROVED**: hence it saturates the N-Frame invariant at every bound `B` — the necessity
        leg's containment is discharged.

## Honest scope — saturation is easy, capture is the hard half

Saturation is dischargeable precisely *because* the arithmetic verifier is universal — but that same universality means the
class is `⊤`, so *nothing* is separated from it (`arithRealizable_all` shows the target is in it too).  This concretely
confirms the structural point of the necessity file: the **upper-bound (saturation)** half is easy, but on its own it
yields no separation.  The separating power lives entirely in the **capture (lower-bound)** half — bounding a class
*above* by the low-N-Frame region — which for the real P-time model is the open, `P ≠ NP`-strength member.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameSaturationClose

open PallLean.Paper93.DeepMath.PathB.NFrameLoadBearing
open PallLean.Paper93.DeepMath.PathB.NFrameNecessity
open PallLean.Paper93.DeepMath.PathB.NFrameArithVerifier

variable {n : ℕ} {F : Type*} [Field F]

/-- A function is **arithmetic-verifier realizable** when some arithmetic verifier's witnessed sum equals it. -/
def ArithRealizable (F : Type*) [Field F] {n : ℕ} (f : (Fin n → Bool) → F) : Prop :=
  ∃ V : ArithVerifier F n, V.realized = f

/-- **The arithmetic-verifier class is `⊤` (proved).**  Every function is arith-realizable — the universality of the
witnessed-sum model. -/
theorem arithRealizable_all (f : (Fin n → Bool) → F) : ArithRealizable F f :=
  exists_verifier_realizing f

/-- **The arithmetic-verifier class saturates (proved).**  It contains every low-N-Frame function, so it saturates the
N-Frame invariant at every bound — the necessity leg's upper-bound containment, discharged. -/
theorem arithRealizable_saturates (B : ℕ) :
    NFrameSaturates F (ArithRealizable (n := n) F) B :=
  fun f _ => arithRealizable_all f

end PallLean.Paper93.DeepMath.PathB.NFrameSaturationClose

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSaturationClose.arithRealizable_all
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSaturationClose.arithRealizable_saturates
