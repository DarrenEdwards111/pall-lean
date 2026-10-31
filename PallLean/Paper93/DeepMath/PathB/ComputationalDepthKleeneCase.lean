import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEq

/-!
# Kleene interpreter project — step 5: the tag-peel primitive `caseCode` (PROVED)

The 8-way dispatch is built by *peeling* the tag.  The key fact: in `prec f cg`, the `cg`-branch input
`pair payload (pair (tag-1) prev)` carries **both** the payload and the decremented tag — so a clean peel
primitive is realizable:

  `caseCode f g` — on `(payload, tag)`: `tag = 0 → f payload`; `tag > 0 → g (payload, tag-1)`.

This is exactly the structure for nesting into an 8-way dispatch
`caseCode b₀ (caseCode b₁ (… (caseCode b₆ (comp b₇ left))))`: each `f`-branch is a constructor body on the
payload, and the `g`-branch forwards `(payload, tag-1)` to the next level.

  `eval_caseCode_zero` — `tag = 0` branch (clean).
  `eval_caseCode_succ` — `tag > 0` branch, given the `prec` chain at `tag-1` halts (the `prec`-contamination
    made explicit; discharged in the bounded interpreter where all bodies halt).

## What is proved (clean axioms, no `sorry`)

* `caseCode`, `eval_caseCode_zero`, `eval_caseCode_succ`.

## Honest scope

The tag-peel primitive.  Nesting it into the full 8-way dispatch (mechanical) and the double recursion
(the constructor bodies = recursive `evaln` calls) remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

/-- Tag-peel: `(payload, tag) ↦ f payload` if `tag = 0`, else `g (payload, tag-1)`. -/
def caseCode (f g : Code) : Code :=
  Code.prec f (Code.comp g (Code.pair Code.left (Code.comp Code.left Code.right)))

/-- **Peel, `tag = 0` (proved).** -/
theorem eval_caseCode_zero (f g : Code) (payload : ℕ) :
    (caseCode f g).eval (Nat.pair payload 0) = f.eval payload := by
  simp [caseCode, Code.eval]

/-- **Peel, `tag > 0` (proved), given the `prec` chain at `tag-1` halts.** -/
theorem eval_caseCode_succ (f g : Code) (payload t : ℕ)
    (h : ((caseCode f g).eval (Nat.pair payload t)).Dom) :
    (caseCode f g).eval (Nat.pair payload (t + 1)) = g.eval (Nat.pair payload t) := by
  have hbody : ∀ prev,
      (Code.comp g (Code.pair Code.left (Code.comp Code.left Code.right))).eval
          (Nat.pair payload (Nat.pair t prev)) = g.eval (Nat.pair payload t) := by
    intro prev
    have e : (Code.comp g (Code.pair Code.left (Code.comp Code.left Code.right))).eval
          (Nat.pair payload (Nat.pair t prev))
        = ((Code.pair Code.left (Code.comp Code.left Code.right)).eval
            (Nat.pair payload (Nat.pair t prev))).bind g.eval := rfl
    rw [e, show ((Code.pair Code.left (Code.comp Code.left Code.right)).eval
          (Nat.pair payload (Nat.pair t prev))) = Part.some (Nat.pair payload t)
        from by simp [Code.eval, Part.map_some, Seq.seq, Part.bind_some, Nat.unpair_pair], Part.bind_some]
  rw [show (caseCode f g).eval (Nat.pair payload (t + 1))
        = ((caseCode f g).eval (Nat.pair payload t)) >>= fun prev =>
            (Code.comp g (Code.pair Code.left (Code.comp Code.left Code.right))).eval
              (Nat.pair payload (Nat.pair t prev))
      from prec_eval_succ _ _ _ _]
  simp only [hbody]
  exact bind_const_of_dom h

/-!
**Peel primitive proved.**  `caseCode` cleanly peels the tag (`tag=0` selects `f` on the payload; `tag>0`
forwards `(payload, tag-1)` to `g`).  The full 8-way dispatch is its nesting; the constructor bodies (the
double recursion) remain the core.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_caseCode_succ
