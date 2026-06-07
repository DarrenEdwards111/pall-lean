import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SatEncode

/-!
# The s-step peel iteration (branch only)

The one-step recovery (`firstSat_eq_active` / `firstSat_satExtend`) reads the active term off the
encoded boundary as the first *satisfied* term.  The `s`-step decoder **peels**: find the first
satisfied term `T`, *remove* it (re-falsify its filled variables, via `rem`), and repeat.  This file
builds that iteration and proves it correct, composing the proven one-step recovery into `s` steps.

* `peelStream cs rem k σ` — peel `k` times: find first satisfied term, remove it, recurse.
* `RecoverableBy cs rem σ Ts` — the precise per-step chain: at each state the first satisfied term is
  the next element of `Ts`, and `rem` advances the state.  (Each link is exactly one instance of the
  proven one-step recovery.)
* `peelStream_eq` — **the iteration theorem**: `RecoverableBy cs rem σ Ts → peelStream cs rem Ts.length
  σ = Ts`.  So the whole active-clause list is recovered from the boundary, holographically, once each
  link holds.
* `recoverableBy_head` — the head link is discharged by `firstSat_satExtend`: a consistent active term
  *is* the first satisfied term of its satisfying encoding.

This is the iteration logic, reducing the `s`-step recovery to `s` copies of the (proven) one-step
recovery.  Building the single global encoded restriction `σ_enc` (satisfying every block's term) and the
removal `rem` that realises the descent — so that `RecoverableBy` holds end-to-end — is the remaining
construction; the iteration that consumes it is proved here.

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The peel decoder.**  Find the first satisfied term, remove it (`rem`), recurse — `k` times. -/
def peelStream (cs : List (Clause n)) (rem : Clause n → Restriction n → Restriction n) :
    ℕ → Restriction n → List (Clause n)
  | 0, _ => []
  | k + 1, σ =>
    match cs.find? (SwitchingCounting.termSat σ) with
    | none => []
    | some T => T :: peelStream cs rem k (rem T σ)

/-- **The per-step recovery chain.**  Starting at `σ`, the first satisfied term is the head of `Ts`,
and after removing it the rest of `Ts` is recoverable from the advanced state. -/
def RecoverableBy (cs : List (Clause n)) (rem : Clause n → Restriction n → Restriction n) :
    Restriction n → List (Clause n) → Prop
  | _, [] => True
  | σ, T :: rest =>
      cs.find? (SwitchingCounting.termSat σ) = some T ∧ RecoverableBy cs rem (rem T σ) rest

/-- **The iteration theorem.**  If every link of the recovery chain holds, the peel decoder recovers
the whole list `Ts`. -/
theorem peelStream_eq (cs : List (Clause n)) (rem : Clause n → Restriction n → Restriction n) :
    ∀ (Ts : List (Clause n)) (σ : Restriction n),
      RecoverableBy cs rem σ Ts → peelStream cs rem Ts.length σ = Ts := by
  intro Ts
  induction Ts with
  | nil => intro σ _; rfl
  | cons T rest ih =>
    intro σ hrec
    obtain ⟨hhead, htail⟩ := hrec
    rw [List.length_cons, peelStream, hhead]
    exact congrArg (List.cons T) (ih (rem T σ) htail)

/-- **The head link, discharged.**  A consistent active term is the first satisfied term of its
satisfying encoding — so the head condition of `RecoverableBy` is exactly the proven one-step recovery,
with `rem` chosen to start the next state from `satExtendTerm ρ T`. -/
theorem recoverableBy_head {cs : List (Clause n)} {ρ : Restriction n} {T : Clause n}
    (hcons : Consistent T) (hact : SwitchingCounting.activeTerm cs ρ = some T) :
    cs.find? (SwitchingCounting.termSat (satExtendTerm ρ T)) = some T :=
  firstSat_satExtend hcons hact

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.peelStream_eq
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.recoverableBy_head
