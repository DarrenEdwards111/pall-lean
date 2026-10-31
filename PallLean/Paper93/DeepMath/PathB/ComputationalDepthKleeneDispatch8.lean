import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneCase

/-!
# Kleene interpreter project — step 5: the full multi-way dispatch (PROVED)

The multi-way dispatch is the nested peel `mkDispatch [b₀,…,bₙ] = caseCode b₀ (caseCode b₁ (… ))`, selecting
the body indexed by the tag.  Proved correct **for any list of bodies** (so the 8-way constructor dispatch
is the instance with 8 bodies):

  `mkDispatch` — nested `caseCode` over a list of body codes.
  `dom_mkDispatch` — if every body halts on `payload`, the dispatch halts at every tag (double induction on
    list and tag — this discharges the `prec`-chain `Dom` obligations of the peel).
  `eval_mkDispatch` — `(mkDispatch codes).eval (pair payload tag) = (codes.getD tag zero).eval payload` for
    `tag < codes.length`: the dispatch selects body `tag`.

This is the complete dispatch selection mechanism.  Instantiated with the eight constructor bodies, it is
the interpreter's `evaln` dispatch; the bodies for `pair`/`comp`/`prec`/`rfind'` are the recursive `evaln`
calls (the double recursion), the remaining core.

## What is proved (clean axioms, no `sorry`)

* `mkDispatch`, `dom_mkDispatch`, `eval_mkDispatch`.

## Honest scope

The full multi-way dispatch selection (proved for any body list).  The constructor bodies — the double
recursion — remain the core.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

/-- Multi-way dispatch: nested `caseCode` selecting the body indexed by the tag. -/
def mkDispatch : List Code → Code
  | [] => Code.zero
  | [b] => Code.comp b Code.left
  | b :: rest => caseCode b (mkDispatch rest)

/-- **The dispatch halts at every tag when all bodies halt (proved).**  Double induction on the body list
and the tag — this discharges the peel's `prec`-chain `Dom` obligations. -/
theorem dom_mkDispatch (payload : ℕ) : ∀ (codes : List Code),
    (∀ c ∈ codes, (c.eval payload).Dom) →
      ∀ tag, ((mkDispatch codes).eval (Nat.pair payload tag)).Dom := by
  intro codes
  induction codes with
  | nil => intro _ tag; exact ⟨⟩
  | cons b rest ihrest =>
    intro hdom tag
    cases rest with
    | nil =>
      have h : (mkDispatch [b]).eval (Nat.pair payload tag) = b.eval payload := by
        simp [mkDispatch, Code.eval]
      rw [h]; exact hdom b (by simp)
    | cons b1 r1 =>
      induction tag with
      | zero =>
        show ((caseCode b (mkDispatch (b1 :: r1))).eval (Nat.pair payload 0)).Dom
        rw [eval_caseCode_zero]; exact hdom b (by simp)
      | succ t iht =>
        show ((caseCode b (mkDispatch (b1 :: r1))).eval (Nat.pair payload (t + 1))).Dom
        rw [eval_caseCode_succ b (mkDispatch (b1 :: r1)) payload t iht]
        exact ihrest (fun c hc => hdom c (by simp [hc])) t

/-- **The dispatch selects the body indexed by the tag (proved).** -/
theorem eval_mkDispatch (payload : ℕ) : ∀ (codes : List Code),
    (∀ c ∈ codes, (c.eval payload).Dom) → ∀ tag, tag < codes.length →
      (mkDispatch codes).eval (Nat.pair payload tag) = (codes.getD tag Code.zero).eval payload := by
  intro codes
  induction codes with
  | nil => intro _ tag htag; simp at htag
  | cons b rest ihrest =>
    intro hdom tag htag
    cases rest with
    | nil =>
      have h1 : tag = 0 := by simp at htag; omega
      subst h1
      show (Code.comp b Code.left).eval (Nat.pair payload 0) = _
      simp [Code.eval]
    | cons b1 r1 =>
      cases tag with
      | zero =>
        show (caseCode b (mkDispatch (b1 :: r1))).eval (Nat.pair payload 0) = _
        rw [eval_caseCode_zero]; rfl
      | succ t =>
        show (caseCode b (mkDispatch (b1 :: r1))).eval (Nat.pair payload (t + 1)) = _
        rw [eval_caseCode_succ b (mkDispatch (b1 :: r1)) payload t
            (dom_mkDispatch payload (b :: b1 :: r1) hdom t)]
        rw [ihrest (fun c hc => hdom c (by simp [hc])) t (by simp at htag ⊢; omega)]
        rfl

/-!
**Multi-way dispatch proved.**  `mkDispatch` selects the body indexed by the tag, correct for any body list
(`eval_mkDispatch`), with the peel `Dom` obligations discharged by `dom_mkDispatch`.  Instantiated with the
eight constructor bodies it is the interpreter's dispatch; the bodies (the double recursion) remain the
core.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_mkDispatch
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.dom_mkDispatch
