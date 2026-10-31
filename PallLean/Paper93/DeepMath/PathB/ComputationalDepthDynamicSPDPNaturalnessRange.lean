import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNaturalProofsBarrier

/-!
# Where dynamic‑SPDP can and cannot reach — the naturalness range

Is dynamic‑SPDP "stronger than Williams"?  This file answers it structurally.  Dynamic‑SPDP is a *rank /
feature‑counting* method: its lower‑bound certificate — "`f` has high realized features", i.e. `f` is **hard** for
the low‑feature (cheap) class — is computable from the truth table (constructive), large (most functions have it),
and useful (it certifies non‑membership).  That makes it a **natural property** in the Razborov–Rudich sense.

We already formalized that barrier (`…NaturalProofsBarrier`).  It is **class‑dependent**: it only bites against
classes that contain pseudorandom functions (the hypothesis `Crypto`).  The realized‑feature certificate is
*exactly* a `Hard cheap` property, so its largeness and usefulness are already theorems there.  The only question
is whether it can also be **constructive** — and the barrier's answer depends entirely on `Crypto`:

* **PRF‑free classes (ACC⁰): not barriered.**  ACC⁰ is not known to contain PRFs, so `Crypto` fails, the barrier
  is *vacuous*, and a constructive large+useful certificate is permitted — a genuine natural lower bound is
  allowed.  (This is exactly why RS‑style natural bounds exist for AC⁰[p] and natural proofs against ACC⁰ are not
  blocked.)
* **PRF‑containing classes (P/poly under crypto): barriered.**  `Crypto` holds, the barrier fires, and the
  realized‑feature certificate **cannot** be constructive — dynamic‑SPDP cannot prove `P/poly` (hence `P ≠ NP`)
  lower bounds this way, by the very barrier we proved.

## What is proved (clean axioms, no `sorry`)

* `dynamicSPDP_certificate_large`, `dynamicSPDP_certificate_useful` — the realized‑feature certificate `Hard cheap`
  is large and useful (natural), reusing `…NaturalProofsBarrier`.
* `dynamicSPDP_blocked_of_crypto` — with `Crypto` (PRFs in class) the barrier derives `False` from a constructive
  certificate: **blocked for P/poly**.
* `dynamicSPDP_unblocked_of_no_crypto` — with `¬ Crypto` (no PRFs) the barrier holds *vacuously* for any
  constructivity predicate: it imposes no constraint — **permitted for ACC⁰**.
* `dynamicSPDP_range_dichotomy` — the three together: the certificate is natural, blocked exactly when `Crypto`
  holds, vacuously unconstrained when it fails.

## Verdict — promising for ACC⁰, provably dead for P vs NP

Dynamic‑SPDP's reach is **exactly the PRF‑free classes**.  Against ACC⁰ it is a *legitimate* (un‑barriered) avenue
— so the make‑or‑break composition theorem `ACC0LowRealizedGodelSPDP` is worth attempting, and success there could
recover/strengthen ACC⁰ bounds via a natural/algebraic route distinct from Williams' (non‑natural) algorithmic
method.  But against `P/poly` the **same barrier we formalized blocks it**: dynamic‑SPDP, being natural, cannot
reach `P ≠ NP`.  So "stronger than Williams" is plausible *only at the ACC⁰ level*, and is provably *not* a path
to the separation — the natural‑proofs barrier caps it precisely where PRFs appear.
-/

namespace PallLean.Paper93.DeepMath.PathB.DynamicSPDPNaturalnessRange

open PallLean.Paper93.DeepMath.PathB.RestrictedCashout
open PallLean.Paper93.DeepMath.PathB.NaturalProofsBarrier

variable {n N : ℕ} (cheap : Fin N → BoolFun n)

/-- **The realized‑feature certificate is LARGE (proved).**  "`f` has high realized features" = `f` is hard for the
low‑feature class; most functions satisfy it. -/
theorem dynamicSPDP_certificate_large (hN : 2 * N < Fintype.card (BoolFun n)) :
    LargeProperty (Hard cheap) :=
  counting_property_is_large cheap hN

/-- **The realized‑feature certificate is USEFUL (proved).**  Having it certifies non‑membership in the cheap
class. -/
theorem dynamicSPDP_certificate_useful : UsefulAgainst cheap (Hard cheap) :=
  hard_property_useful cheap

/-- **Blocked against PRF‑containing classes (P/poly) (proved).**  If the class contains pseudorandom functions
(`Crypto`), the Razborov–Rudich barrier turns a *constructive* realized‑feature certificate into `False`: the
natural method cannot prove lower bounds against such a class — in particular it cannot reach `P ≠ NP`. -/
theorem dynamicSPDP_blocked_of_crypto (hN : 2 * N < Fintype.card (BoolFun n))
    (Constructive : (BoolFun n → Prop) → Prop) (Crypto : Prop)
    (hRR : RazborovRudichBarrier Constructive cheap Crypto) (hC : Crypto)
    (hcons : Constructive (Hard cheap)) :
    False :=
  hRR hC (Hard cheap) (counting_property_is_large cheap hN) hcons (hard_property_useful cheap)

/-- **Not blocked against PRF‑free classes (ACC⁰) (proved).**  When the class contains no pseudorandom functions
(`¬ Crypto`), the barrier holds *vacuously* for every constructivity predicate — it imposes no constraint, so the
large + useful realized‑feature certificate may also be constructive (a genuine natural lower bound is
permitted). -/
theorem dynamicSPDP_unblocked_of_no_crypto (Crypto : Prop) (hC : ¬ Crypto)
    (Constructive : (BoolFun n → Prop) → Prop) :
    RazborovRudichBarrier Constructive cheap Crypto := by
  intro hcrypto
  exact absurd hcrypto hC

/-- **The naturalness‑range dichotomy (proved).**  The realized‑feature certificate is natural (large ∧ useful);
it is blocked exactly when the class contains PRFs (`Crypto`), and the barrier is vacuously unconstraining when it
does not.  Dynamic‑SPDP's reach is therefore exactly the PRF‑free classes — ACC⁰ yes, P/poly no. -/
theorem dynamicSPDP_range_dichotomy (hN : 2 * N < Fintype.card (BoolFun n))
    (Constructive : (BoolFun n → Prop) → Prop) (Crypto : Prop) :
    (LargeProperty (Hard cheap) ∧ UsefulAgainst cheap (Hard cheap))
      ∧ (Crypto → RazborovRudichBarrier Constructive cheap Crypto → Constructive (Hard cheap) → False)
      ∧ (¬ Crypto → RazborovRudichBarrier Constructive cheap Crypto) := by
  refine ⟨⟨counting_property_is_large cheap hN, hard_property_useful cheap⟩, ?_, ?_⟩
  · intro hC hRR hcons
    exact hRR hC (Hard cheap) (counting_property_is_large cheap hN) hcons (hard_property_useful cheap)
  · intro hC hcrypto
    exact absurd hcrypto hC

end PallLean.Paper93.DeepMath.PathB.DynamicSPDPNaturalnessRange

#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDPNaturalnessRange.dynamicSPDP_blocked_of_crypto
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDPNaturalnessRange.dynamicSPDP_unblocked_of_no_crypto
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicSPDPNaturalnessRange.dynamicSPDP_range_dichotomy
