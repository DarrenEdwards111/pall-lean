import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModqInfinite

/-!
# Brick (MOD_q infinite set) — the `MOD_q`-hard arities form an infinite set (proved)

The set-theoretic packaging of the asymptotic `MOD_q` separation (Brick MOD_q infinite): the set of arities `n` at which
`MOD_q` is not computed by any depth-`d` `AC⁰[p]` circuit is **infinite** (`Set.Infinite`).  This is the cleanest standard
form of "for infinitely many `n`, `MOD_q ∉ AC⁰[p]`" — derived from unboundedness (`exists_large_arity_modq_not_acc0p`).

## What is proved (clean axioms, no `sorry`)

* **`modq_hard_arities_infinite`** (PROVED) — `{n | ¬∃ C : ACC0Circuit n, ModpOnly p C ∧ depth C ≤ d ∧ eval C = MOD_q}` is
  `Set.Infinite`.

## Honest scope

The infinitude of the `q>2` `MOD_q`-hard arities (the `n ≡ 1 mod (p−1)` family).  It does **not** give *all* large `n` (the
full RS rank bound; tree's `Layer4`) nor the Williams cash-out.  General YBT and `NEXP ⊄ ACC⁰` remain open.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModqInfiniteSet

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit depth)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqWitness (modqFn)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqInfinite (exists_large_arity_modq_not_acc0p)

variable {p : ℕ} [Fact p.Prime]

/-- **The `MOD_q`-hard arities form an infinite set (PROVED).** -/
theorem modq_hard_arities_infinite (hp2 : p ≠ 2) (q : ℕ) (hq2 : 2 ≤ q) (hq : (q : ZMod p) ≠ 0)
    (ζ : ZMod p) (hord : orderOf ζ = q) (d : ℕ) :
    {n : ℕ | ¬ ∃ C : ACC0Circuit n,
        ModpOnly p C ∧ depth C ≤ d ∧ ACC0CircuitModel.eval C = modqFn q}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro N
  obtain ⟨n, hn, hnS⟩ := exists_large_arity_modq_not_acc0p hp2 q hq2 hq ζ hord d N
  exact ⟨n, hnS, hn⟩

/-!
**The `MOD_q`-hard arities are infinite, proved.**  `{n | MOD_q ∉ depth-d AC⁰[p]}` is an infinite set of naturals — the
standard set-theoretic form of the unconditional `q>2` Razborov–Smolensky separation.  Remaining (open, not faked): all large
`n` (RS rank bound), Williams cash-out.  Not `NEXP ⊄ ACC⁰`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModqInfiniteSet

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModqInfiniteSet.modq_hard_arities_infinite
