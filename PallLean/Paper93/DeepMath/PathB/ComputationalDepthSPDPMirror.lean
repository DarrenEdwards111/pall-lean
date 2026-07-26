import Mathlib.Data.Nat.Basic

/-!
# The mirror over any rank — SPDP as the strong measure, and where it caps

Darren's connection: the mirror `Π★` is *rank-monotone*, and the paper's rank is **SPDP** (shifted
partial derivatives).  That is the right observation — the mirror mechanism works over *any* rank measure,
and the *strength* of the resulting bound is exactly the strength of the rank on the witness.

* **`mirror_transfers` (proved)** — the mirror over an abstract `rank`: a rank-monotone `Π★` with
  `Π★ comp = witness` reflects the witness's bound onto the compilation, `high ≤ rank comp`.  Instantiate
  `rank` with *gate count*, *support*, *Khrapchenko*, or **SPDP** — same reflection.

## Why SPDP is the strong rank (Darren's instinct)

The syntactic ranks cap polynomially (support `→ n`, Khrapchenko `→ n²`).  **SPDP rank** — the dimension
of the shifted partial derivatives of a polynomial — does **not**: it reaches **superpolynomial** for the
witness in restricted arithmetic circuits (GKKS: depth-4 homogeneous `ΣΠΣΠ` lower bounds).  So plugging
`rank = SPDP` into `mirror_transfers` gives a *superpolynomial* restricted lower bound — the mirror carries
SPDP's superpoly reach onto the compilation.  That is genuinely past the syntactic ladder.

## Where it caps — and the "dynamic" question

Two honest ceilings on the *static* SPDP mirror:

1. **Depth.**  SPDP's superpoly reach is a restricted-*depth* phenomenon (the chasm at depth 4); the
   method has known barriers at higher depth — SPDP of general (unbounded-depth) circuits is not known to
   be superpoly.
2. **Model.**  SPDP is algebraic; for general *Boolean* circuits the paper's God-Move uses an assumed
   bridge (`P-observer ⇒ low SPDP rank`, asserted, `P≠NP`-strength — the audited load-bearing gap).

A **dynamic** SPDP — a rank that adapts/evolves through the computation rather than the static derivative
space — is precisely an attempt to break ceiling 1 (carry the superpoly reach past bounded depth).  That
would be the mirror surviving to *general* circuits, which is `cost_super`.  It is a real direction, and
it is the wall: the static SPDP mirror reaches superpoly at bounded depth; making it *dynamic* enough to
reach general depth is exactly the open problem.

**Honest scope.**  Proved: the mirror works over any rank (so SPDP plugs in), and SPDP's superpoly reach
(restricted arithmetic, GKKS — cited, not re-proved) makes the SPDP mirror the strong lens.  The static
SPDP mirror caps at bounded depth / arithmetic model; the dynamic/general version is `cost_super`, open.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPMirror

/-- **The mirror over an abstract rank (proved).**  A rank-monotone `Π★` (`rank (Π★ x) ≤ rank x`) with
`Π★ comp = witness` reflects the witness's lower bound onto the compilation: `high ≤ rank comp`.  Works for
any rank — gate count, support, Khrapchenko, or **SPDP**. -/
theorem mirror_transfers {Fn : Type} (rank : Fn → ℕ) (piStar : Fn → Fn)
    (mono : ∀ x, rank (piStar x) ≤ rank x)
    (comp witness : Fn) (high : ℕ)
    (mirror : piStar comp = witness) (witness_high : high ≤ rank witness) :
    high ≤ rank comp := by
  calc high ≤ rank witness := witness_high
    _ = rank (piStar comp) := by rw [mirror]
    _ ≤ rank comp := mono comp

/-- **The reach is the rank's reach (proved).**  If the rank reaches `2^d` on the witness (as SPDP does,
restricted), the mirror carries `2^d` onto the compilation.  With `rank = SPDP` this is a superpolynomial
reflection — past the syntactic ladder's polynomial cap. -/
theorem mirror_reaches_superpoly {Fn : Type} (rank : Fn → ℕ) (piStar : Fn → Fn)
    (mono : ∀ x, rank (piStar x) ≤ rank x)
    (comp witness : Fn) (d : ℕ)
    (mirror : piStar comp = witness) (witness_superpoly : 2 ^ d ≤ rank witness) :
    2 ^ d ≤ rank comp :=
  mirror_transfers rank piStar mono comp witness (2 ^ d) mirror witness_superpoly

end PallLean.Paper93.DeepMath.PathB.SPDPMirror

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPMirror.mirror_transfers
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPMirror.mirror_reaches_superpoly
