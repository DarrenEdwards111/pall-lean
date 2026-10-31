import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CarryStateComplexity

/-!
# Communication complexity of the carry crossing — the boundary invariant (field-free, route 2)

The second field-free invariant for the composite wall (`CarryRefinementCrossing`, entry 283), in a genuinely different
model from the streaming carry observer of entry 284: **two-party communication**.  Split the input across a cut — Alice
holds one half (Hamming weight `≡ α mod m`), Bob the other (`≡ β mod m`).  Computing `MOD_m` means deciding
`α + β ≡ 0 (mod m)`.  A *product observer* sends a boundary message across the cut; this file lower-bounds the size of
that boundary by the **communication-matrix / fooling-set** technique — a different proof tool from Myhill–Nerode.

**The model (field-free).**  The communication matrix of `MOD_m` is `commValue m α β := decide (α + β = 0)`, indexed by
the two residues.  A product observer is a boundary type `B`, an encoder `msg : ZMod m → B` (Alice compresses her
residue into a cross-cut message), and a decoder `decode : B → ZMod m → Bool` (Bob answers from the message and his
residue), correct when `decode (msg α) β = commValue m α β`.  No fields, no polynomials — only the residues and the
boundary alphabet.

**The lower bound (proved).**  `mod_product_observer_boundary_ge`: any correct product observer has `≥ m` boundary
states.  Core: the `m` rows of the communication matrix are **pairwise distinct** (`commValue_row_injective`) — row `α`
fires only at `β = -α`, so distinct residues give distinct rows (the fooling-set / rank-`m` argument).  Correctness
forces `msg` to be injective, hence `m = #(ZMod m) ≤ #B`.

**For `MOD₆`** (`mod6_product_observer_requires_large_boundary`): `≥ 6` boundary states.  And `mod6_boundary_six_achievable`
shows `6` is **tight** — the identity protocol (Alice sends her residue mod 6) achieves a `6`-state boundary.  *Honest
caveat (the same shape as entry 284):* `6 = 2 · 3` is the **constant** CRT product, achievable, so the communication
complexity of `MOD₆` is `Θ(1)` — `MOD₆` is communication-*cheap*.  Tracking the CRT factors separately (a `ZMod 2 ×
ZMod 3` boundary, `2 · 3 = 6` messages) matches the bound exactly — no blow-up.  So the boundary invariant gives a real
`≥ m` lower bound but is constant for a fixed modulus, hence does **not** separate composite `ACC⁰` by itself; the
separation needs a target whose communication boundary *grows* under the relevant restricted-protocol model — the open
`CarryRefinementCrossing` step.

## What is proved (clean axioms, no `sorry`)

* **`commValue_row_injective`** (PROVED) — the `m` rows of the `MOD_m` communication matrix are pairwise distinct
  (fooling-set / rank-`m` core).
* **`mod_product_observer_boundary_ge`** (PROVED) — a correct two-party product observer for `MOD_m` has `≥ m` boundary
  states.
* **`mod6_product_observer_requires_large_boundary`** (PROVED) — `≥ 6` boundary states for `MOD₆`.
* **`mod6_boundary_six_achievable`** (PROVED) — `6` is tight: the identity protocol achieves a `6`-state boundary.

## Honest scope

A genuine, field-free, two-party communication lower bound (`≥ m` boundary for `MOD_m`), proved by the
communication-matrix distinct-rows technique — a second characteristic-independent invariant for the composite wall.
But for a fixed modulus the bound is the constant `6` (`= 2 · 3`, achievable — `MOD₆ ∈ ACC⁰[6]`, communication-cheap),
so it does **not** prove a composite separation; that needs a target with *growing* communication boundary.  This is
**not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CommunicationComplexity

open PallLean.Paper93.DeepMath.PathB

/-- The `MOD_m` communication-matrix entry: across a cut with residues `α` (Alice) and `β` (Bob), the gate fires iff the
total weight is `≡ 0 (mod m)`, i.e. `α + β = 0` in `ZMod m`. -/
def commValue (m : ℕ) (α β : ZMod m) : Bool := decide (α + β = 0)

/-- **The communication matrix of `MOD_m` has `m` distinct rows (PROVED).**  Row `α` is the function `β ↦ [α + β = 0]`,
which fires only at `β = -α`; so distinct residues give distinct rows.  This is the fooling-set / rank-`m` core of the
communication lower bound — field-free (no fields, no polynomials, only the group `ZMod m`). -/
theorem commValue_row_injective {m : ℕ} :
    Function.Injective (fun α : ZMod m => fun β : ZMod m => commValue m α β) := by
  intro α₁ α₂ heq
  have h : commValue m α₁ (-α₁) = commValue m α₂ (-α₁) := congrFun heq (-α₁)
  unfold commValue at h
  have hL : α₁ + -α₁ = (0 : ZMod m) := by ring
  rw [hL] at h
  have h2 : α₂ + -α₁ = 0 := by
    by_contra hc
    rw [decide_eq_false hc] at h
    simp at h
  have h3 : α₂ = α₁ := by linear_combination h2
  exact h3.symm

/-- **Two-party boundary lower bound for `MOD_m` (PROVED).**  A *product observer* across a cut — boundary alphabet `B`,
encoder `msg : ZMod m → B` (Alice's cross-cut message), decoder `decode : B → ZMod m → Bool` (Bob's answer) — that
correctly computes `MOD_m` (`decode (msg α) β = [α + β = 0]`) must use `≥ m` boundary states.  Correctness forces `msg`
to separate the `m` distinct communication-matrix rows, so `msg` is injective and `m = #(ZMod m) ≤ #B`.  A field-free
communication-complexity bound via the distinct-rows (fooling-set) technique. -/
theorem mod_product_observer_boundary_ge {m : ℕ} [NeZero m]
    {B : Type} [Fintype B] (msg : ZMod m → B) (decode : B → ZMod m → Bool)
    (hcorrect : ∀ α β : ZMod m, decode (msg α) β = commValue m α β) :
    m ≤ Fintype.card B := by
  have hmsg : Function.Injective msg := by
    intro α₁ α₂ he
    apply commValue_row_injective
    funext β
    calc commValue m α₁ β = decode (msg α₁) β := (hcorrect α₁ β).symm
      _ = decode (msg α₂) β := by rw [he]
      _ = commValue m α₂ β := hcorrect α₂ β
  calc m = Fintype.card (ZMod m) := (ZMod.card m).symm
    _ ≤ Fintype.card B := Fintype.card_le_of_injective msg hmsg

/-- **`MOD₆` requires a `≥ 6`-state boundary (PROVED).**  Instantiating `mod_product_observer_boundary_ge` at `m = 6`:
any two-party product observer computing `MOD₆` across a cut must carry at least `6` boundary states. -/
theorem mod6_product_observer_requires_large_boundary
    {B : Type} [Fintype B] (msg : ZMod 6 → B) (decode : B → ZMod 6 → Bool)
    (hcorrect : ∀ α β : ZMod 6, decode (msg α) β = commValue 6 α β) :
    6 ≤ Fintype.card B :=
  mod_product_observer_boundary_ge msg decode hcorrect

/-- **The `≥ 6` boundary bound is tight (PROVED).**  The identity protocol — Alice sends her residue `mod 6` (boundary
`B = ZMod 6`, `decode b β = [b + β = 0]`) — computes `MOD₆` with exactly `6` boundary states.  So the bound is the
**constant** `6` and is achievable: `MOD₆` is communication-cheap (`Θ(1)`), confirming the honest caveat that this
invariant does not separate fixed-`MOD₆` composite. -/
theorem mod6_boundary_six_achievable :
    ∃ (B : Type) (_ : Fintype B) (msg : ZMod 6 → B) (decode : B → ZMod 6 → Bool),
      (∀ α β : ZMod 6, decode (msg α) β = commValue 6 α β) ∧ Fintype.card B = 6 := by
  refine ⟨ZMod 6, inferInstance, id, fun b β => commValue 6 b β, ?_, ?_⟩
  · intro α β; rfl
  · exact ZMod.card 6

/-!
**Route 2 of the field-free frontier.**  Communication complexity gives a second characteristic-independent invariant
for `CarryRefinementCrossing`: a `≥ m` boundary lower bound for `MOD_m`, proved by the communication-matrix distinct-rows
(fooling-set) technique — a different tool from the streaming Myhill–Nerode argument of entry 284, in a different
(two-party) model.  As with entry 284, for a *fixed* modulus the bound is the constant `6` (`= 2 · 3`, the CRT product)
and is tight/achievable — `MOD₆` is communication-cheap — so it is a real field-free bound but **not** a composite
separation.  Both routes converge on the same honest verdict: the obstruction is not the size of any single boundary but
a target whose boundary *grows* under bounded composition.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CommunicationComplexity

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CommunicationComplexity.commValue_row_injective
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CommunicationComplexity.mod_product_observer_boundary_ge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CommunicationComplexity.mod6_product_observer_requires_large_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CommunicationComplexity.mod6_boundary_six_achievable
