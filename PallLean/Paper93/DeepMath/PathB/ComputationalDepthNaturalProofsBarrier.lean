import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictedCashout

/-!
# The natural‑proofs barrier: why "most functions are hard" cannot constructively isolate `NP`

The counting cash‑out proves *most* Boolean functions are hard for a small (cheap) decider class.  This file
formalizes the Razborov–Rudich obstruction to turning that into a `P ≠ NP` proof: the counting hardness property
is **large** and **useful**, but — under a cryptographic assumption — it cannot also be **constructive**.  So
"most functions are hard" provably cannot be made into an efficient property isolating an explicit `NP` family.

A *natural property* (Razborov–Rudich) against a class is (i) **large** (most functions have it),
(ii) **constructive** (efficiently decidable), (iii) **useful** (every function with it is outside the class).
The barrier: if strong PRGs exist, no natural property is useful against a rich class.

## Proved (clean axioms, no `sorry`)

* `nonHard_card_le` — the *non‑hard* functions (those equal to some cheap decider) number `≤ N`.
* `counting_property_is_large` — when `2N < 2^{2^n}`, the hardness property `Hard cheap` is **large**: more than
  half of all functions are hard.
* `hard_property_useful` — `Hard cheap` is **useful** against the cheap class (tautologically — it *is* the
  hardness).
* `counting_property_not_constructive` — **the structural warning**: given the Razborov–Rudich barrier and a
  cryptographic assumption (both *named hypotheses*, not claimed), the large+useful counting property is **not
  constructive**.  Hence the counting route cannot be upgraded into a constructive natural proof isolating `NP`.

## Honest scope

`RazborovRudichBarrier` and `Crypto` are **parameters**, not theorems — the barrier holds *under* the standard
cryptographic assumption (strong PRGs), which we do not prove.  What is proved is the framework‑side fact that
the counting property is large and useful, so the *only* property a natural proof could be missing is
constructivity — exactly what the barrier forbids.  This blocks any "explicitness by counting" shortcut: you
cannot reach an explicit `NP` lower bound by making the counting property algorithmic.  Crossing to explicit
hardness therefore requires a *non‑natural* argument — the genuinely open part.
-/

namespace PallLean.Paper93.DeepMath.PathB.NaturalProofsBarrier

open PallLean.Paper93.DeepMath.PathB.RestrictedCashout
open Classical

/-- `f` is **hard** for the cheap decider class `cheap : Fin N → BoolFun n`: it equals no cheap decider. -/
def Hard {n N : ℕ} (cheap : Fin N → BoolFun n) (f : BoolFun n) : Prop := ∀ i, cheap i ≠ f

/-- A property is **large** if more than half of all `2^{2^n}` functions satisfy it. -/
def LargeProperty {n : ℕ} (P : BoolFun n → Prop) : Prop :=
  Fintype.card (BoolFun n) < 2 * (Finset.univ.filter (fun f => P f)).card

/-- A property is **useful** against the cheap class if every function with it is hard for that class. -/
def UsefulAgainst {n N : ℕ} (cheap : Fin N → BoolFun n) (P : BoolFun n → Prop) : Prop :=
  ∀ f, P f → Hard cheap f

/-- **The non‑hard functions number `≤ N` (proved).**  A function fails `Hard` iff it equals some cheap decider,
so the non‑hard set is contained in the image of `cheap`, of size `≤ N`. -/
theorem nonHard_card_le {n N : ℕ} (cheap : Fin N → BoolFun n) :
    (Finset.univ.filter (fun f => ¬ Hard cheap f)).card ≤ N := by
  have hsub : (Finset.univ.filter (fun f => ¬ Hard cheap f)) ⊆ Finset.univ.image cheap := by
    intro f hf
    rw [Finset.mem_filter] at hf
    have h2 := hf.2
    unfold Hard at h2
    push_neg at h2
    obtain ⟨i, hi⟩ := h2
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  calc (Finset.univ.filter (fun f => ¬ Hard cheap f)).card
      ≤ (Finset.univ.image cheap).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_image_le
    _ = N := by rw [Finset.card_univ, Fintype.card_fin]

/-- **The counting hardness property is large (proved).**  When the cheap class is small (`2N < 2^{2^n}`), more
than half of all Boolean functions are hard for it. -/
theorem counting_property_is_large {n N : ℕ} (cheap : Fin N → BoolFun n)
    (hN : 2 * N < Fintype.card (BoolFun n)) :
    LargeProperty (Hard cheap) := by
  unfold LargeProperty
  have hcompl : (Finset.univ.filter (fun f => Hard cheap f)).card
              + (Finset.univ.filter (fun f => ¬ Hard cheap f)).card = Fintype.card (BoolFun n) := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hnh := nonHard_card_le cheap
  omega

/-- **The counting hardness property is useful (proved).**  Tautologically — `Hard cheap` *is* hardness. -/
theorem hard_property_useful {n N : ℕ} (cheap : Fin N → BoolFun n) :
    UsefulAgainst cheap (Hard cheap) :=
  fun _ h => h

/-- The **Razborov–Rudich barrier**, as a *named hypothesis* (not claimed): under a cryptographic assumption
`Crypto` (strong PRGs), no large + `Constructive` property is useful against the cheap class. -/
def RazborovRudichBarrier {n N : ℕ} (Constructive : (BoolFun n → Prop) → Prop)
    (cheap : Fin N → BoolFun n) (Crypto : Prop) : Prop :=
  Crypto → ∀ P : BoolFun n → Prop, LargeProperty P → Constructive P → UsefulAgainst cheap P → False

/-- **The structural warning (proved): the counting property cannot be made constructive.**  It is large and
useful; so by the Razborov–Rudich barrier (under the cryptographic assumption), it is **not** constructive.
Hence "most functions are hard" cannot be upgraded into an efficient property isolating an explicit `NP` family —
the explicitness gap is *not* bridgeable by making the counting property algorithmic. -/
theorem counting_property_not_constructive {n N : ℕ} (cheap : Fin N → BoolFun n)
    (hN : 2 * N < Fintype.card (BoolFun n))
    (Constructive : (BoolFun n → Prop) → Prop) (Crypto : Prop)
    (hRR : RazborovRudichBarrier Constructive cheap Crypto) (hC : Crypto) :
    ¬ Constructive (Hard cheap) := by
  intro hcons
  exact hRR hC (Hard cheap) (counting_property_is_large cheap hN) hcons (hard_property_useful cheap)

end PallLean.Paper93.DeepMath.PathB.NaturalProofsBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.NaturalProofsBarrier.counting_property_is_large
#print axioms PallLean.Paper93.DeepMath.PathB.NaturalProofsBarrier.counting_property_not_constructive
