import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDispatch

/-!
# Kleene interpreter project — step 5 (control layer): a conditional Code (PROVED)

The dispatch's control layer must branch on the constructor tag.  `Code`'s only branching primitive is
`prec`, and a key finding here (the concrete reason the control layer is hard) is that **`prec` entangles
the recursion chain**: `(prec f cg).eval (pair a (m+1))` first evaluates the prec recursion at all lower
indices, so the branch value is reached only *modulo* the lower chain halting.

We nonetheless build a usable **conditional** `ifzCode f g := prec f (comp g left)` — `cg = comp g left`
ignores the recursive argument, computing `g` on the original input — with:

  `eval_ifzCode_zero` — selector `0`: `(ifzCode f g).eval (pair a 0) = f.eval a` (clean).
  `eval_ifzCode_step` — the recursion-collapse: `eval (pair a (m+1)) = eval (pair a m) >>= fun _ => g.eval a`.
  `eval_ifzCode_pos` — selector `> 0`, **given both branches halt** (`hf`,`hg`): `= g.eval a`.

The branch-halting hypotheses (`hf`,`hg`) are exactly the `prec`-contamination made explicit — for the
dispatch's use, the branches are total extraction/recursion codes, so they are discharged.

## What is proved (clean axioms, no `sorry`)

* `ifzCode`, `bind_const_of_dom`, `eval_ifzCode_zero`, `eval_ifzCode_step`, `eval_ifzCode_pos`.

## Honest scope

A conditional control primitive (with the honest branch-halting caveat that documents why `prec` makes the
control layer hard).  Assembling the full 8-way dispatch + the double recursion as one `Code` remains the
indivisible core.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

/-- Conditional code: on `(a, sel)`, returns `f a` if `sel = 0`, else `g a` (the `comp g left` body ignores
the recursive argument). -/
def ifzCode (f g : Code) : Code := Code.prec f (Code.comp g Code.left)

/-- **Bind over a halting part with a constant continuation collapses (proved).** -/
theorem bind_const_of_dom {p q : Part ℕ} (h : p.Dom) : (p >>= fun _ => q) = q := by
  conv_lhs => rw [← Part.some_get h]
  rw [Part.bind_eq_bind, Part.bind_some]

/-- **Selector `0` branch (proved): `f a`.** -/
theorem eval_ifzCode_zero (f g : Code) (a : ℕ) :
    (ifzCode f g).eval (Nat.pair a 0) = f.eval a := by
  simp [ifzCode, Code.eval]

/-- **Recursion-collapse step (proved): the body reduces to `g.eval a`, independent of the chain value.** -/
theorem eval_ifzCode_step (f g : Code) (a m : ℕ) :
    (ifzCode f g).eval (Nat.pair a (m + 1))
      = ((ifzCode f g).eval (Nat.pair a m)) >>= fun _ => g.eval a := by
  simp only [ifzCode, Code.eval, Nat.unpaired, Nat.unpair_pair, Nat.rec_add_one]
  congr 1
  funext i
  simp [Nat.unpair_pair]

/-- **Selector `> 0` branch (proved), given both branches halt: `g a`.** -/
theorem eval_ifzCode_pos (f g : Code) (a : ℕ) (hf : (f.eval a).Dom) (hg : (g.eval a).Dom) :
    ∀ m, (ifzCode f g).eval (Nat.pair a (m + 1)) = g.eval a := by
  intro m
  induction m with
  | zero => rw [eval_ifzCode_step, eval_ifzCode_zero]; exact bind_const_of_dom hf
  | succ m ih => rw [eval_ifzCode_step, ih]; exact bind_const_of_dom hg

/-!
**Step 5 conditional proved.**  `ifzCode` branches on a zero/non-zero selector, with the `prec`-recursion
collapse made explicit (`eval_ifzCode_step`) and the branch-halting caveat (`hf`,`hg`) documenting why the
control layer is delicate.  The full 8-way dispatch + double recursion as one `Code` remains the indivisible
core.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_ifzCode_pos
