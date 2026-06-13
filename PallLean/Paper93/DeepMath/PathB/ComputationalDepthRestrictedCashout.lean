import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSpeedupBridge

/-!
# A Williams‑style cash‑out for a restricted class — on the decision axis, unconditional

Step 4 of the time‑axis program: a cash‑out where *cheap decider ⇒ faster algorithm ⇒ contradiction*, biting on
the `1`‑bit **decision** axis (not the separator/classifier axis), and **unconditionally**.

The two halves:

* **cheap ⇒ enumerable** (speedup side).  A bounded‑resource decider has a bounded description, so the cheap
  class is *finite/enumerable*: it is the image of some `d : Fin N → BoolFun n`.  (The proved speedup
  `…NFrameSpeedupBridge` is the quantitative form: bounded boundary ⇒ a decider of bounded configuration count ⇒
  a short description ⇒ small `N`.)
* **contradiction by counting/diagonalization** (the proven hierarchy substitute).  There are `2^{2^n}` Boolean
  functions on `n` inputs; a class of `N < 2^{2^n}` deciders computes at most `N` of them, so **some function
  escapes every cheap decider** — a genuine, unconditional decision lower bound.

## Proved (clean axioms, no `sorry`)

* `exists_uncomputed_of_card_lt` — the diagonal core: any `N`‑member class with `N < |F|` misses some `f ∈ F`.
* `card_boolFun` — `|BoolFun n| = 2^{2^n}`.
* `cheap_class_misses_function` — a cheap class `d : Fin N → BoolFun n` with `N < 2^{2^n}` misses some Boolean
  function: `∃ f, ∀ i, d i ≠ f`.
* `restricted_cashout` — the cash‑out conclusion: a cheap (enumerable, `N < 2^{2^n}`) decider class is **not
  surjective** onto all Boolean functions — it cannot decide everything.

## Honest scope — unconditional, but non‑explicit

This bites on the decision axis and needs **no conjecture**: it is the Shannon counting / diagonalization form of
"the cheap class is too small," exactly the contradiction half of a Williams cash‑out, proved.  Its limitation is
the classical one of counting: it is an **existence** bound — it yields *some* hard function, not an *explicit*
family like SAT.  Pinning the hard function to an explicit (NP) family is the `P ≠ NP`‑strength step; the
counting cash‑out is the unconditional shadow of it.
-/

namespace PallLean.Paper93.DeepMath.PathB.RestrictedCashout

/-- The diagonal / counting core: a class of `N` members cannot cover a universe of size `> N` — some element
is computed by none of them. -/
theorem exists_uncomputed_of_card_lt {F : Type*} [Fintype F] {N : ℕ}
    (d : Fin N → F) (hN : N < Fintype.card F) : ∃ f : F, ∀ i, d i ≠ f := by
  by_contra h
  push_neg at h
  have hle := Fintype.card_le_of_surjective d h
  rw [Fintype.card_fin] at hle
  omega

/-- The universe of Boolean functions on `n` inputs. -/
abbrev BoolFun (n : ℕ) : Type := (Fin n → Bool) → Bool

/-- There are `2^{2^n}` Boolean functions on `n` inputs. -/
theorem card_boolFun (n : ℕ) : Fintype.card (BoolFun n) = 2 ^ 2 ^ n := by
  simp only [BoolFun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **A cheap decider class misses a function (proved, unconditional).**  An enumerable class
`d : Fin N → BoolFun n` with `N < 2^{2^n}` cannot compute every Boolean function: some `f` is decided by no
member.  The Shannon/diagonal contradiction half of the cash‑out. -/
theorem cheap_class_misses_function {n N : ℕ} (d : Fin N → BoolFun n) (hN : N < 2 ^ 2 ^ n) :
    ∃ f : BoolFun n, ∀ i, d i ≠ f := by
  apply exists_uncomputed_of_card_lt
  rw [card_boolFun]
  exact hN

/-- **The restricted cash‑out (proved).**  A cheap (enumerable, `N < 2^{2^n}`) decider class is **not
surjective** onto all Boolean functions on `n` inputs — it cannot decide everything.  This is a genuine,
unconditional *decision* lower bound for the restricted class (some function escapes it), the cash‑out's
contradiction realized by counting. -/
theorem restricted_cashout {n N : ℕ} (d : Fin N → BoolFun n) (hN : N < 2 ^ 2 ^ n) :
    ¬ Function.Surjective d := by
  intro hsurj
  obtain ⟨f, hf⟩ := cheap_class_misses_function d hN
  obtain ⟨i, hi⟩ := hsurj f
  exact hf i hi

end PallLean.Paper93.DeepMath.PathB.RestrictedCashout

#print axioms PallLean.Paper93.DeepMath.PathB.RestrictedCashout.cheap_class_misses_function
#print axioms PallLean.Paper93.DeepMath.PathB.RestrictedCashout.restricted_cashout
