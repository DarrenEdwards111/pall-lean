import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCircuitUpgrade
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHardExists
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPBarrier

/-!
# The holographic reading of P vs NP — and why it lands on the wall

The fuzzy pass identified the one honest incarnation of the "black-hole holography" intuition: the
**area-not-volume** (Bekenstein) incompressibility bound.  This file makes the dictionary precise and
machine-checks where it lands.

The holographic dictionary:

| holography | complexity |
|---|---|
| **boundary** description | a circuit `c` computing `f` |
| **area** of the boundary | circuit size `c.length` |
| minimal area / the observer | `cbudget f` (min circuit size) |
| the **bulk** | the truth table of `f` (`2ⁿ` bits) |
| a bulk that fits on area-`a` boundary | `HoloEncodable f a` |
| **Bekenstein bound**: most bulks don't fit | counting: hard functions exist |
| efficiently deciding which bulks fit | a **natural property** (MCSP) |

* **`HoloEncodable f a`** — `f` has a boundary (circuit) of area `≤ a`.
* **`holoEncodable_iff_cbudget_le` (proved)** — the area observer *is* `cbudget`: encodable at area `a`
  ⟺ `cbudget f ≤ a`.  So "holographic area" is exactly the repository's min-circuit-size measure.
* **`exists_incompressible` (proved)** — the Bekenstein bound: if the area-`a` bulks are a minority,
  an **incompressible** function exists (no area-`a` boundary holds it).  This is nothing but the
  counting existence of hard functions (`HardExists`).
* **`hard_iff_incompressible` (proved)** — deciding "incompressible" is exactly the `Hard`-detection
  predicate: `Hard cheap f ⟺ ¬ HoloEncodable f a` when `cheap` enumerates the area-`a` bulks.
* **`incompressibility_detector_barriered` (proved)** — and *that* detector is barriered: an efficient
  test for holographic incompressibility is a natural property, which under Razborov–Rudich + crypto
  cannot exist (`MCSPBarrier`).

**Honest scope.**  This is the machine-checked reason holography **renames the wall** rather than
crossing it: the "area not volume" incompressibility bound is precisely the `cbudget` incompressibility
observer, its Bekenstein form is the (non-constructive) counting existence, and its efficient form is
the natural-proofs-forbidden MCSP detector.  A faithful re-description of the incompressibility wall —
not a way through it.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HolographicIncompressibility

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.RestrictedCashout
open PallLean.Paper93.DeepMath.PathB.NaturalProofsBarrier
open PallLean.Paper93.DeepMath.PathB.HardExists
open PallLean.Paper93.DeepMath.PathB.MCSPBarrier

variable {n : ℕ}

/-- **Holographic encoding.**  `f` is encodable at *area* `a` iff it has a boundary description — a
circuit — of size `≤ a`.  The bulk (truth table) fits on a boundary of area `a`. -/
def HoloEncodable (f : BoolFun n) (a : ℕ) : Prop :=
  ∃ c : List (CGate n), computes c f ∧ c.length ≤ a

/-- **The area observer is `cbudget` (proved).**  Holographic encodability at area `a` is exactly
`cbudget f ≤ a`: the minimal boundary area is the minimal circuit size.  (Needs `f` to have some
boundary — every Boolean function does.) -/
theorem holoEncodable_iff_cbudget_le (f : BoolFun n) (a : ℕ)
    (hf : ∃ c : List (CGate n), computes c f) :
    HoloEncodable f a ↔ cbudget f ≤ a := by
  unfold HoloEncodable cbudget
  constructor
  · rintro ⟨c, hc, hlen⟩
    exact le_trans (Nat.sInf_le ⟨c, hc, rfl⟩) hlen
  · intro h
    obtain ⟨c0, hc0⟩ := hf
    obtain ⟨c, hc, hclen⟩ :=
      Nat.sInf_mem (⟨c0.length, c0, hc0, rfl⟩ :
        {s | ∃ c : List (CGate n), computes c f ∧ c.length = s}.Nonempty)
    exact ⟨c, hc, by rw [hclen]; exact h⟩

/-- **The Bekenstein bound (proved): most bulks don't fit.**  If the area-`a`-encodable functions are
a minority — their enumeration `cheap` is smaller than half of all functions — then a holographically
**incompressible** function exists: a bulk no area-`a` boundary can hold.  This is precisely the
counting existence of hard functions. -/
theorem exists_incompressible {N : ℕ} (a : ℕ) (cheap : Fin N → BoolFun n)
    (hcov : ∀ f : BoolFun n, HoloEncodable f a → ∃ i, cheap i = f)
    (hN : 2 * N < Fintype.card (BoolFun n)) :
    ∃ f : BoolFun n, ¬ HoloEncodable f a := by
  obtain ⟨f, hf⟩ := exists_hard_function cheap hN
  refine ⟨f, fun henc => ?_⟩
  obtain ⟨i, hi⟩ := hcov f henc
  exact hf i hi

/-- **Detecting incompressibility = the `Hard` predicate (proved).**  When `cheap` enumerates *exactly*
the area-`a` bulks (sound and complete), "holographically incompressible" is literally `Hard cheap`. -/
theorem hard_iff_incompressible {N : ℕ} (a : ℕ) (cheap : Fin N → BoolFun n)
    (hcov : ∀ f : BoolFun n, HoloEncodable f a → ∃ i, cheap i = f)
    (hsound : ∀ i, HoloEncodable (cheap i) a) (f : BoolFun n) :
    Hard cheap f ↔ ¬ HoloEncodable f a := by
  constructor
  · intro hhard henc
    obtain ⟨i, hi⟩ := hcov f henc
    exact hhard i hi
  · intro hinc i hif
    exact hinc (hif ▸ hsound i)

/-- **The incompressibility detector is barriered (proved).**  An *efficient* test for holographic
incompressibility (deciding `Hard cheap`) is a natural property; under the Razborov–Rudich barrier and
a cryptographic assumption it cannot exist.  So the Bekenstein "area not volume" bound, made an
efficient detector, breaks cryptography — holography lands on the natural-proofs wall. -/
theorem incompressibility_detector_barriered {N : ℕ} (cheap : Fin N → BoolFun n)
    (hN : 2 * N < Fintype.card (BoolFun n))
    (Constructive : (BoolFun n → Prop) → Prop) (Crypto : Prop)
    (hRR : RazborovRudichBarrier Constructive cheap Crypto) (hC : Crypto) :
    ¬ MCSPSolvable Constructive cheap :=
  mcsp_not_solvable_under_crypto cheap hN Constructive Crypto hRR hC

end PallLean.Paper93.DeepMath.PathB.HolographicIncompressibility

#print axioms PallLean.Paper93.DeepMath.PathB.HolographicIncompressibility.holoEncodable_iff_cbudget_le
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicIncompressibility.exists_incompressible
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicIncompressibility.hard_iff_incompressible
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicIncompressibility.incompressibility_detector_barriered
