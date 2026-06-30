import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DepthTreeField

/-!
# N-Frame complexity socket: bounded-fan-in AC⁰ has low N-Frame complexity (over `F_{p^k}`)

This file gives the **N-Frame object a formal socket into the existing ACC⁰ representation work**, as the honest
nearest Lean step toward "ACC from N-Frame".  We define one precise invariant that the monoAND/SYM∘AND machinery
controls — the **minimal monomial-`AND` span degree** of a function — and call it `NFrameComplexity`.  It is the
concrete proxy for the N-Frame invariant (observer dimension / SPDP-rank / holonomy of the boundary): a function with
a degree-`≤D` `monoAND` representation lives on a `≤(∑_{i≤D}C(n,i))`-dimensional boundary slice, the low-rank /
low-observer-dimension regime.

The socket theorem:

  `andOrTree_nframeComplexity_le` — every bounded-fan-in AC⁰ (de Morgan basis) circuit `t : AndOrTree` has
        `NFrameComplexity (evalT F t) ≤ t.deg` (degree adds over the circuit);
  `nframeComplexity_le_two_pow_depth` — hence `≤ 2^{depth} · leafWidth`, so **constant depth + bounded fan-in/leaf
        width ⇒ bounded N-Frame complexity**.

This is the `acc0_implies_low_nframe` direction of the separation skeleton, *for the bounded-fan-in fragment*.

## Honest scope — what this is and is NOT

`NFrameComplexity` here is the **monoAND-span degree**, a concrete well-defined measure, used as the formal stand-in
for the N-Frame invariant.  Two genuinely open pieces remain (where N-Frame must contribute something new):

1. **Connecting this proxy to the literal N-Frame object** (observer dimension / SPDP-rank / holonomy) — i.e. a
   theorem `NFrameComplexity f = (the actual N-Frame invariant of f)`.
2. **Extending from bounded-fan-in AC⁰ / `MOD_p` to full ACC⁰ with *unbounded composite `MOD`* gates** — the
   composite-`MOD` barrier, exactly where the polynomial method stops.  This socket does **not** cross it; it gives
   N-Frame a clean entry point without pretending to solve Beigel–Tarui.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0

open PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact (sqfGens AndOrTree)

variable {n : ℕ} {F : Type*} [Field F]

/-- **N-Frame complexity (the formal invariant).**  The minimal degree `D` such that `f` lies in the degree-`≤D`
monomial-`AND` span over `F` — the concrete proxy for the N-Frame observer-dimension / SPDP-rank of `f`. -/
noncomputable def NFrameComplexity (F : Type*) [Field F] {n : ℕ} (f : (Fin n → Bool) → F) : ℕ :=
  sInf {D | f ∈ Submodule.span F (sqfGens F n D)}

/-- **The bridge from span membership.**  If `f` has a degree-`≤D` monomial-`AND` representation, its N-Frame
complexity is `≤ D`. -/
theorem nframeComplexity_le_of_mem_span {f : (Fin n → Bool) → F} {D : ℕ}
    (h : f ∈ Submodule.span F (sqfGens F n D)) : NFrameComplexity F f ≤ D :=
  Nat.sInf_le h

/-- **The socket: bounded-fan-in AC⁰ ⇒ low N-Frame complexity.**  Every AC⁰ (de Morgan basis) circuit `t` has
`NFrameComplexity (evalT F t) ≤ t.deg`. -/
theorem andOrTree_nframeComplexity_le (t : AndOrTree n) :
    NFrameComplexity F (AndOrTree.evalT F t) ≤ AndOrTree.deg t :=
  nframeComplexity_le_of_mem_span (AndOrTree.evalT_mem_span t)

/-- The circuit depth (longest gate path). -/
def treeDepth : AndOrTree n → ℕ
  | AndOrTree.leaf _ => 0
  | AndOrTree.andN l r => max (treeDepth l) (treeDepth r) + 1
  | AndOrTree.orN l r => max (treeDepth l) (treeDepth r) + 1
  | AndOrTree.notN t => treeDepth t + 1

/-- The maximum leaf width (largest monomial-`AND` fan-in). -/
def treeLeafWidth : AndOrTree n → ℕ
  | AndOrTree.leaf S => S.card
  | AndOrTree.andN l r => max (treeLeafWidth l) (treeLeafWidth r)
  | AndOrTree.orN l r => max (treeLeafWidth l) (treeLeafWidth r)
  | AndOrTree.notN t => treeLeafWidth t

/-- **Degree is bounded by `2^{depth} · leafWidth` (proved).**  Fan-in-`2` depth-`d` circuits over width-`w` leaves
have degree `≤ 2^d · w`. -/
theorem deg_le_two_pow_depth_mul_leafWidth (t : AndOrTree n) :
    AndOrTree.deg t ≤ 2 ^ treeDepth t * treeLeafWidth t := by
  induction t with
  | leaf S => simp [AndOrTree.deg, treeDepth, treeLeafWidth]
  | andN l r ihl ihr =>
    have hl : AndOrTree.deg l ≤ 2 ^ max (treeDepth l) (treeDepth r) * max (treeLeafWidth l) (treeLeafWidth r) :=
      le_trans ihl (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)) (le_max_left _ _))
    have hr : AndOrTree.deg r ≤ 2 ^ max (treeDepth l) (treeDepth r) * max (treeLeafWidth l) (treeLeafWidth r) :=
      le_trans ihr (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)) (le_max_right _ _))
    show AndOrTree.deg l + AndOrTree.deg r
        ≤ 2 ^ (max (treeDepth l) (treeDepth r) + 1) * max (treeLeafWidth l) (treeLeafWidth r)
    calc AndOrTree.deg l + AndOrTree.deg r
        ≤ 2 ^ max (treeDepth l) (treeDepth r) * max (treeLeafWidth l) (treeLeafWidth r)
          + 2 ^ max (treeDepth l) (treeDepth r) * max (treeLeafWidth l) (treeLeafWidth r) :=
          Nat.add_le_add hl hr
      _ = 2 ^ (max (treeDepth l) (treeDepth r) + 1) * max (treeLeafWidth l) (treeLeafWidth r) := by
          rw [pow_succ]; ring
  | orN l r ihl ihr =>
    have hl : AndOrTree.deg l ≤ 2 ^ max (treeDepth l) (treeDepth r) * max (treeLeafWidth l) (treeLeafWidth r) :=
      le_trans ihl (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)) (le_max_left _ _))
    have hr : AndOrTree.deg r ≤ 2 ^ max (treeDepth l) (treeDepth r) * max (treeLeafWidth l) (treeLeafWidth r) :=
      le_trans ihr (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)) (le_max_right _ _))
    show AndOrTree.deg l + AndOrTree.deg r
        ≤ 2 ^ (max (treeDepth l) (treeDepth r) + 1) * max (treeLeafWidth l) (treeLeafWidth r)
    calc AndOrTree.deg l + AndOrTree.deg r
        ≤ 2 ^ max (treeDepth l) (treeDepth r) * max (treeLeafWidth l) (treeLeafWidth r)
          + 2 ^ max (treeDepth l) (treeDepth r) * max (treeLeafWidth l) (treeLeafWidth r) :=
          Nat.add_le_add hl hr
      _ = 2 ^ (max (treeDepth l) (treeDepth r) + 1) * max (treeLeafWidth l) (treeLeafWidth r) := by
          rw [pow_succ]; ring
  | notN t iht =>
    refine le_trans iht (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)))

/-- **Constant depth + bounded leaf width ⇒ bounded N-Frame complexity (proved).**  The `acc0_implies_low_nframe`
direction for the bounded-fan-in fragment: an AC⁰ circuit of depth `d` over width-`w` `monoAND` leaves has
`NFrameComplexity ≤ 2^d · w`. -/
theorem nframeComplexity_le_two_pow_depth (t : AndOrTree n) :
    NFrameComplexity F (AndOrTree.evalT F t) ≤ 2 ^ treeDepth t * treeLeafWidth t :=
  le_trans (andOrTree_nframeComplexity_le t) (deg_le_two_pow_depth_mul_leafWidth t)

end PallLean.Paper93.DeepMath.PathB.NFrameACC0

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.andOrTree_nframeComplexity_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.nframeComplexity_le_two_pow_depth
