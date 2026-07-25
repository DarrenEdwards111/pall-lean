import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNaturalProofsBarrier

/-!
# MCSP is the wall, named: detecting incompressibility is what cryptography forbids

The **Minimum Circuit Size Problem** (MCSP): given a function's truth table, decide whether it has a
*small* circuit — i.e. decide whether the truth table is **compressible** or is **noise
(incompressible)**.  This is precisely the "tell structure from noise" problem, and it is exactly the
face of the natural-proofs wall.

The connection (Kabanets–Cai; the meta-complexity view): a *natural property* — an efficient test that
distinguishes hard functions from easy ones — is essentially an **efficient MCSP algorithm**.  And an
efficient MCSP algorithm distinguishes a pseudorandom function from random, **breaking cryptography**.
So:

> **MCSP is easy ⟺ natural proofs exist ⟺ cryptography is broken.**
> Equivalently, **MCSP is hard** (assuming crypto) — and that hardness *is* the barrier.

This file states it directly on the barrier already built in `NaturalProofsBarrier`.  "Solving MCSP
against the cheap class" is having a `Constructive` (efficient) decision of the hardness property
`Hard cheap` — an efficient incompressibility detector.

* **`MCSPSolvable`** — an efficient decider for `Hard cheap` (an MCSP algorithm);
* **`mcsp_property_large` / `mcsp_property_useful` (proved)** — MCSP tests a property that most
  functions satisfy (noise is generic) and that certifies hardness;
* **`mcsp_not_solvable_under_crypto` (proved)** — under the Razborov–Rudich barrier and a crypto
  assumption, **MCSP is not solvable**: you cannot efficiently detect incompressibility.

So the wall is not a fog — it is a **named computational problem** (`MCSP`) whose intractability is
equivalent to the existence of cryptography.  Williams-style (non-natural) proofs sidestep it by *not*
being MCSP algorithms.  Nothing here is `P ≠ NP`; it is the wall, stated exactly.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPBarrier

open PallLean.Paper93.DeepMath.PathB.NaturalProofsBarrier
open PallLean.Paper93.DeepMath.PathB.RestrictedCashout

variable {n N : ℕ}

/-- **`MCSP` as property-decision.**  To solve `MCSP` against the cheap (small-circuit) class is to
have a `Constructive` (efficient) decision of the hardness property `Hard cheap` — i.e. to efficiently
decide, from a function's truth table, whether it is incompressible (needs a large circuit). -/
def MCSPSolvable (Constructive : (BoolFun n → Prop) → Prop) (cheap : Fin N → BoolFun n) : Prop :=
  Constructive (Hard cheap)

/-- **MCSP tests a *large* property (proved)**: most truth tables are incompressible — noise is
generic (`> half` of all functions are hard for a small class). -/
theorem mcsp_property_large (cheap : Fin N → BoolFun n)
    (hN : 2 * N < Fintype.card (BoolFun n)) : LargeProperty (Hard cheap) :=
  counting_property_is_large cheap hN

/-- **MCSP tests a *useful* property (proved)**: anything it accepts is hard for the cheap class. -/
theorem mcsp_property_useful (cheap : Fin N → BoolFun n) :
    UsefulAgainst cheap (Hard cheap) :=
  hard_property_useful cheap

/-- **THE MCSP CHARACTERIZATION OF THE WALL (proved).**  Under the Razborov–Rudich barrier and a
cryptographic assumption, **MCSP is not solvable** — you cannot efficiently detect incompressibility.
Because the tested property is large and useful, an efficient MCSP solver would be a natural property
against `P/poly`, contradicting crypto.  So "detect noise vs structure" is exactly what the wall
forbids: MCSP-hardness *is* the barrier. -/
theorem mcsp_not_solvable_under_crypto (cheap : Fin N → BoolFun n)
    (hN : 2 * N < Fintype.card (BoolFun n))
    (Constructive : (BoolFun n → Prop) → Prop) (Crypto : Prop)
    (hRR : RazborovRudichBarrier Constructive cheap Crypto) (hC : Crypto) :
    ¬ MCSPSolvable Constructive cheap :=
  counting_property_not_constructive cheap hN Constructive Crypto hRR hC

end PallLean.Paper93.DeepMath.PathB.MCSPBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPBarrier.mcsp_property_large
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPBarrier.mcsp_not_solvable_under_crypto
