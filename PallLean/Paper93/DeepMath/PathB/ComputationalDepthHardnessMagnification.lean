import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposablePpolyDischarge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPBarrier

/-!
# Hardness magnification: a tiny gap-MCSP bound magnifies to `SAT ∉ P`

The fuzzy pass singled out **hardness magnification** as the one live route that both reaches
`P ≠ NP`-strength *and* connects to the meta-complexity machinery already here.  Its content is a
change of target: instead of a *superpolynomial* lower bound for SAT, one needs a *barely
super-linear* — `n^{1+ε}`-type — circuit lower bound for a *specific* compression problem
(**gap-MCSP**), which **magnifies** (Oliveira–Pich–Santhanam) to `NP ⊄ P/poly`, hence `SAT ∉ P`.

This file formalizes that implication as an explicit two-socket chain, wired to the repository's SAT
circuit target (`ComposablePpolyDischarge`) and to its MCSP wall (`MCSPBarrier`).

* **`GapMCSPLowerBound gapMCSP thr`** — the magnifying lower bound: the gap-MCSP family on `2ⁿ`-bit
  truth tables requires circuits of size `≥ thr n` (the magnifying threshold `thr n = (2ⁿ)^{1+ε}`
  is carried by the magnification socket).
* **`magnification_implies_SAT_not_in_P` (proved, socketed)** — given the magnifying lower bound and
  the magnification theorem `magnify`, `SAT ∉ P` follows (chaining through
  `sat_superpoly_cbudget_implies_SAT_not_in_P`).

**The two sockets, named exactly.**
1. `magnify` — the **hardness-magnification theorem** itself (Oliveira–Pich–Santhanam and relatives):
   a gap-MCSP lower bound at the magnifying threshold ⟹ superpolynomial `cbudget(SAT)`.  A real, deep
   theorem, socketed here, not re-proved.
2. `hLB : GapMCSPLowerBound …` — the **`n^{1+ε}` lower bound for gap-MCSP**.  This is the crux, and it
   is **barriered**: gap-MCSP is precisely the compression/`Hard`-detection problem of `MCSPBarrier`,
   and the known techniques for such bounds are *local/natural*, hitting the Razborov–Rudich wall
   (`NaturalProofsBarrier`) — the "locality barrier".  So magnification makes the crux **small and
   concrete** but does **not** remove the wall; it relocates it to a threshold bound that current
   methods cannot reach.

**Honest scope.**  Nothing here proves `P ≠ NP`.  It is the precise conditional — *tiny gap-MCSP bound
⟹ separation* — with both the magnification theorem and the tiny bound as named open sockets, and the
tiny bound explicitly identified with the (barriered) MCSP hardness this repository already maps.
-/

namespace PallLean.Paper93.DeepMath.PathB.HardnessMagnification

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.RestrictedCashout
open PallLean.Paper93.DeepMath.PathB.NaturalProofsBarrier
open PallLean.Paper93.DeepMath.PathB.MCSPBarrier

/-- **The magnifying gap-MCSP lower bound.**  The gap-MCSP family `gapMCSP` on `2ⁿ`-bit truth tables
requires circuits of size at least `thr n` for every `n`.  In the magnification regime `thr n` is the
super-linear threshold `(2ⁿ)^{1+ε}`; it is a parameter here, fixed by the magnification socket. -/
def GapMCSPLowerBound (gapMCSP : (n : ℕ) → BoolFun (2 ^ n)) (thr : ℕ → ℕ) : Prop :=
  ∀ n, thr n ≤ cbudget (gapMCSP n)

/-- **THE MAGNIFICATION IMPLICATION (proved, socketed).**  Given a gap-MCSP family with the magnifying
lower bound `hLB`, and the hardness-magnification theorem `magnify` (a gap-MCSP bound at the magnifying
threshold ⟹ superpolynomial `cbudget(SAT)`), `SAT ∉ P` follows.  The magnifying bound `hLB` and the
theorem `magnify` are the two named open sockets; everything downstream is the repository's discharged
circuit route. -/
theorem magnification_implies_SAT_not_in_P
    (gapMCSP : (n : ℕ) → BoolFun (2 ^ n)) (thr : ℕ → ℕ)
    (magnify : GapMCSPLowerBound gapMCSP thr → (∀ k, ∃ n, n ^ k + k < cbudget (SATFamily n)))
    (hLB : GapMCSPLowerBound gapMCSP thr) :
    ¬ InP SATLang :=
  ComposablePpolyDischarge.sat_superpoly_cbudget_implies_SAT_not_in_P (magnify hLB)

/-- **The chain with both sockets exposed (proved).**  Explicitly: the hardness-magnification theorem
composed with the tiny gap-MCSP bound yields `SAT ∉ P`.  This is the whole magnification route in one
line — the two hypotheses are exactly where the difficulty lives. -/
theorem magnification_route
    (gapMCSP : (n : ℕ) → BoolFun (2 ^ n)) (thr : ℕ → ℕ)
    (magnify : GapMCSPLowerBound gapMCSP thr → (∀ k, ∃ n, n ^ k + k < cbudget (SATFamily n)))
    (hLB : GapMCSPLowerBound gapMCSP thr) :
    ¬ InP SATLang :=
  magnification_implies_SAT_not_in_P gapMCSP thr magnify hLB

/-- **The locality barrier on the crux (proved wiring).**  The tiny gap-MCSP bound is not free: any
attempt to obtain it from a *natural property* (a constructive, large, useful test against the cheap
class) breaks cryptography, by the Razborov–Rudich barrier — exactly the `MCSPBarrier` wall.  So the
magnifying bound cannot come from a natural argument; this is the honest reason magnification relocates
the wall rather than removing it. -/
theorem crux_not_natural {n N : ℕ} (cheap : Fin N → BoolFun n)
    (hN : 2 * N < Fintype.card (BoolFun n))
    (Constructive : (BoolFun n → Prop) → Prop) (Crypto : Prop)
    (hRR : RazborovRudichBarrier Constructive cheap Crypto) (hC : Crypto) :
    ¬ MCSPSolvable Constructive cheap :=
  mcsp_not_solvable_under_crypto cheap hN Constructive Crypto hRR hC

end PallLean.Paper93.DeepMath.PathB.HardnessMagnification

#print axioms PallLean.Paper93.DeepMath.PathB.HardnessMagnification.magnification_implies_SAT_not_in_P
#print axioms PallLean.Paper93.DeepMath.PathB.HardnessMagnification.crux_not_natural
