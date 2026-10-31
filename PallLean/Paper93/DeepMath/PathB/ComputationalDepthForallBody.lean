import Mathlib.Data.Nat.Basic

/-!
# "Take any circuit C" is free — the reason inside the ∀ is the whole content

Darren: apply the trick to P vs NP — "take any circuit `C` that computes SAT, [general argument], therefore
`C` can't share below the doubling line."  The `∀` reaches all of them; the proof is finite.  **This is
correct — and it pinpoints exactly what's missing.**

Every universal claim has two parts: the **quantifier** ("take any `x`") and the **body** (the reason
`premise x → conclusion x`).  The quantifier is *free* — you just `intro x`.  The body is the *content* — you
must prove it for an *arbitrary* `x`, using nothing special about it.  For "every even number is `2k`" the
body has a one-line reason (the definition).  For `cost_super` the body is the *open* implication — no known
reason derives "can't share below doubling" from "computes SAT" for arbitrary `C`, and the barriers say the
reason must be non-natural.

So "take any `C`" is the right form, the reach is free — but the **form is not the proof**; the reason inside
is, and that reason is `cost_super`.

## What is proved

* **`claim_is_the_body`** — a universal claim *is* its body: `Claim U ↔ ∀ x, premise x → conclusion x`
  (`Iff.rfl`).  Writing `∀` adds nothing; you still owe the reason for arbitrary `x`.
* **`take_any_reduces_to_body`** — "take any `x`" reduces the claim to supplying the reason:
  `(∀ x, premise x → conclusion x) → Claim U`.  The quantifier is free; the reason is the obligation.
* **`even_claim_proved`** — the even case: the body has a reason (the definition), so the claim is *proved* —
  `∀ n, n % 2 = 0 → ∃ k, n = 2·k`.
* **`cost_super_form`** — the SAT case has the *same form*: given the reason `∀ C, computesSAT C → cantShare
  C`, the universal follows.  The reason is a *hypothesis* here — open for SAT — because supplying it is
  `cost_super`.

## Honest scope — the reach is free, the reason is the wall

The `∀` dissolves the "too many circuits" worry entirely (`take_any_reduces_to_body`: you never enumerate
them).  So the difficulty is *not* the reach and *not* our boundedness — it is localized to one thing: the
**body**, the general reason `computesSAT C → cantShare C` for arbitrary `C`.  For even numbers that reason
is the definition; for SAT it is the open, non-natural argument — `cost_super`.  "Take any `C`" is the
correct opening of the proof; the sentence that must follow it is the theorem no one has.  This confirms the
map's thesis rather than crossing it: the wall is the *reason*, not the *reach*.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ForallBody

/-- A universal claim over `Obj`: a `premise` and a `conclusion`.  The claim is `∀ x, premise x →
conclusion x`. -/
structure UniversalClaim (Obj : Type) where
  /-- the premise (e.g. "C computes SAT") -/
  premise : Obj → Prop
  /-- the conclusion (e.g. "C can't share below the doubling line") -/
  conclusion : Obj → Prop

/-- The universal claim: for every `x`, the premise gives the conclusion. -/
def Claim {Obj : Type} (U : UniversalClaim Obj) : Prop := ∀ x, U.premise x → U.conclusion x

/-- **A claim IS its body (proved, `Iff.rfl`).**  `Claim U ↔ ∀ x, premise x → conclusion x`.  Writing the
`∀` adds nothing — you still owe the reason for arbitrary `x`. -/
theorem claim_is_the_body {Obj : Type} (U : UniversalClaim Obj) :
    Claim U ↔ ∀ x, U.premise x → U.conclusion x := Iff.rfl

/-- **"Take any x" reduces to the reason (proved).**  The quantifier is free: given the general reason, the
universal follows.  The reach is free; the reason is the obligation. -/
theorem take_any_reduces_to_body {Obj : Type} (U : UniversalClaim Obj)
    (reason : ∀ x, U.premise x → U.conclusion x) : Claim U := reason

/-- The even-number claim: `n % 2 = 0 → ∃ k, n = 2·k`. -/
def evenClaim : UniversalClaim ℕ := ⟨fun n => n % 2 = 0, fun n => ∃ k, n = 2 * k⟩

/-- **The even case is proved (proved).**  The body has a one-line reason (the definition): take any `n`,
`n = 2·(n/2)`.  The `∀` reaches every even number because the reason uses nothing special about `n`. -/
theorem even_claim_proved : Claim evenClaim := by
  intro n h
  have h2 : n % 2 = 0 := h
  show ∃ k, n = 2 * k
  exact ⟨n / 2, by omega⟩

/-- **The SAT case has the same form (proved).**  Given the reason `∀ C, computesSAT C → cantShare C`, the
universal follows — identical to the even case.  The reason is a *hypothesis* here: for SAT, supplying it is
`cost_super`, the open, non-natural argument.  The form is free; the body is the wall. -/
theorem cost_super_form {Circuit : Type} (computesSAT cantShare : Circuit → Prop)
    (reason : ∀ C, computesSAT C → cantShare C) : ∀ C, computesSAT C → cantShare C := reason

end PallLean.Paper93.DeepMath.PathB.ForallBody

#print axioms PallLean.Paper93.DeepMath.PathB.ForallBody.claim_is_the_body
#print axioms PallLean.Paper93.DeepMath.PathB.ForallBody.even_claim_proved
