import Mathlib

/-!
# A MOD₃ candidate passing the stated filters — EXPLORATORY, and an honest finding about the battery

The AND gadget was filtered out: it is *modulus-agnostic* (step 5), so it fails the ACC⁰/modular filter.  The
natural fix for filter 3 is a genuinely **modulus-specific** primitive — `MOD₃`.  This file builds a MOD₃
candidate and proves it passes the two filters the AND gadget could not both clear:

* **Filter 1 (non-affine over `F₂`)** — escapes the Gaussian/affine shortcut.
* **Filter 3 (modulus-specific)** — `mod 3` and `mod 2` classify it differently, so it is *not*
  modulus-agnostic (the AND gadget's failure mode).

But the build's real value is the honest finding it forces — see the conclusion.

## Proved (clean axioms, no `sorry`)

* `mod3Gadget_not_affine` — the MOD₃ predicate's `F₂` solution set is not affine (explicit `a,b,c` solutions
  with `a+b+c` violating): it escapes the linear/Gaussian shortcut.
* `mod3Gadget_modulus_specific` — there is an input where `mod 3` and `mod 2` classifications disagree (bit-sum
  `3`: `≡0 mod 3` but `≢0 mod 2`).  The candidate is modulus-specific — passes the ACC⁰/modular filter the AND
  gadget failed.

## Honest finding — passing the stated battery is necessary, not sufficient; completion = the ACC⁰ frontier

This candidate passes filters 1 and 3 (and, being additive rather than AND-transitive, plausibly filter 2 —
not formalized).  **But it is not decision-hard, and the reason is the genuinely important takeaway:**

* The battery as formalized tests the `F₂`-linear shortcut (filter 1) and modulus-*agnosticism* (filter 3).
  MOD₃ is **additive over `F₃`** — it has an `F₃`-linear structure — so a *strengthened* filter 1 ("non-affine
  over **every** `F_p`") would catch it.  The AND gadget was the dual failure: non-affine over every `F_p` but
  low-degree/modulus-agnostic.  Neither, nor their combination, escapes the polynomial method.
* **Every** explicit gadget built from `AND` / `XOR` / `MOD_q` primitives lies in **ACC⁰** (`ACC⁰` *contains*
  all `MOD_m` gates).  So it always has *some* algebraic shortcut.  A candidate that **provably** clears the
  *complete* battery — resisting all `F_p`-linear, all low-degree, and all modular shortcuts — would be an
  explicit function **outside `ACC⁰`**, and no such explicit function is known: that is exactly the open `ACC⁰`
  frontier (and `NP ⊄ ACC⁰` is open; only `NEXP ⊄ ACC⁰` is known, via Williams).

**Conclusion.** "Build a candidate that passes all three filters" is achievable for the *stated/local* filters
(this file passes 1 and 3; the AND gadget passed 1).  But the filters, taken to completion, are an
**`ACC⁰`-membership detector**, and certifying a candidate as *decision-hard* means producing an explicit
function outside `ACC⁰` — the open frontier, equivalently `DecisionHolonomyHyp`.  The lab narrows candidates; it
cannot, with explicit modular/algebraic gadgets, certify decision hardness.  No `P ≠ NP` step — the honest
edge of what construction can do here.
-/

namespace PallLean.Paper93.DeepMath.PathB.ModularCandidate

/-- The integer bit-sum of four `F₂` variables. -/
def modSum (x : Fin 4 → ZMod 2) : ℕ := (x 0).val + (x 1).val + (x 2).val + (x 3).val

/-- The **MOD₃ candidate**: bit-sum `≡ 0 (mod 3)`.  A genuinely modulus-specific primitive (unlike the
modulus-agnostic AND gadget). -/
def mod3Gadget (x : Fin 4 → ZMod 2) : Prop := modSum x % 3 = 0

/-- **Filter 1 — non-affine over `F₂` (proved).**  Explicit solutions `a, b, c` whose affine combination
`a + b + c` violates the constraint: the MOD₃ candidate escapes the Gaussian/affine shortcut. -/
theorem mod3Gadget_not_affine :
    ∃ a b c : Fin 4 → ZMod 2,
      mod3Gadget a ∧ mod3Gadget b ∧ mod3Gadget c ∧ ¬ mod3Gadget (a + b + c) :=
  ⟨![0, 0, 0, 0], ![1, 1, 1, 0], ![1, 1, 0, 1],
    by unfold mod3Gadget modSum; decide, by unfold mod3Gadget modSum; decide,
    by unfold mod3Gadget modSum; decide, by unfold mod3Gadget modSum; decide⟩

/-- **Filter 3 — modulus-specific (proved).**  An input where `mod 3` and `mod 2` classifications disagree
(bit-sum `3`: `≡ 0 mod 3` but `≢ 0 mod 2`).  Unlike the AND gadget, this candidate is **not** modulus-agnostic
— it passes the ACC⁰/modular filter the AND gadget failed. -/
theorem mod3Gadget_modulus_specific :
    ∃ x : Fin 4 → ZMod 2, (modSum x % 3 = 0) ≠ (modSum x % 2 = 0) :=
  ⟨![1, 1, 1, 0], by unfold modSum; decide⟩

end PallLean.Paper93.DeepMath.PathB.ModularCandidate

#print axioms PallLean.Paper93.DeepMath.PathB.ModularCandidate.mod3Gadget_not_affine
#print axioms PallLean.Paper93.DeepMath.PathB.ModularCandidate.mod3Gadget_modulus_specific
