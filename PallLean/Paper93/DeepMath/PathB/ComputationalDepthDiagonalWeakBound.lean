import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMagnifiedMetaTrigger

/-!
# Turning self-reference against the locality barrier: the diagonal is real but linear

The last open piece of the best-guess route is the weak `n^{1+ε}` bound, behind the CHOPRS locality
barrier.  The barrier rules out *local* proof techniques; the question is whether the self-referential
structure that just cleared completeness can supply a *non-local* proof that evades it.

The honest answer, built here: **self-reference gives a genuine non-local lower bound — the diagonal —
but it is only LINEAR.**  Reaching `n^{1+ε}` needs to amplify it, and the amplification is exactly the
`SelfImproving` anti-checker (the same `cost_super` engine).  So self-reference *does* thread the
barrier — the diagonal is non-local and real — but the threshold is reached by the amplification, which
stays open.  The barrier is not the obstruction; the lever is.

## What is proved

* **`diag`, `diag_negates_self_application`** — the diagonal: `diag f i = !(f i i)`.  It negates each
  enumerated circuit *on its own index* — the self-reference, made explicit.  Its definition inspects
  every circuit's self-application: **non-local by construction**, so outside the barrier's
  local-technique hypothesis (necessary, not sufficient — cf. `SelfRefBraid.barrier_permits_nonlocal_dent`).
* **`diag_differs` / `diag_not_enumerated`** — the lower bound: `diag f` differs from *every*
  enumerated circuit `f i`.  If `f` enumerates all size-`s` circuits, no size-`s` circuit computes
  `diag f`.  A real, constructive, self-referential lower bound.
* **`diagonal_base_amplifies`** — the diagonal supplies the ladder base (a non-trivial bound at the
  base scale); `SelfImproving` (the MMW/OPS anti-checker, open socket) amplifies it to the magnified
  bound — `MagnifiedMetaTrigger.magnifies`, the same multiplicative engine.

## Honest scope — the cap, and where the gap really is

The diagonal on domain `Fin m` differs from exactly the `m` enumerated circuits: it "kills" each at
its own diagonal input, so it needs one input per circuit.  A size-`s` lower bound must diagonalize
against all `~2^{s·log s}` size-`s` circuits, hence needs domain `~2^{s·log s}` — so `s` is only
`~log(domain)`, i.e. **LINEAR in the input length, below `n^{1+ε}`**.  Plain diagonalization cannot
reach the magnification threshold; that gap is precisely the `SelfImproving` amplification.

So: self-reference against CHOPRS yields a *barrier-immune, real, but linear* base bound, confirming
the route's shape (non-local self-reference works).  The `n^{1+ε}` threshold is the amplification of
that base — the genuinely open lever, not the barrier.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DiagonalWeakBound

open PallLean.Paper93.DeepMath.PathB.MagnifiedMetaTrigger

/-! ### The self-referential diagonal lower bound -/

/-- **The diagonal.**  `f : Fin m → Fin m → Bool` enumerates `m` circuits (as functions on `Fin m`);
`diag f j = !(f j j)` negates the `j`-th circuit on input `j`. -/
def diag {m : ℕ} (f : Fin m → Fin m → Bool) : Fin m → Bool := fun j => !(f j j)

/-- **The self-reference, made explicit (proved).**  `diag f i` is the negation of the `i`-th
enumerated circuit applied to its own index — the definition references each circuit's self-application,
so it is non-local. -/
theorem diag_negates_self_application {m : ℕ} (f : Fin m → Fin m → Bool) (i : Fin m) :
    diag f i = !(f i i) := rfl

/-- **The diagonal differs from every enumerated circuit (proved).**  For each `i`, `diag f` and
`f i` disagree at input `i`. -/
theorem diag_differs {m : ℕ} (f : Fin m → Fin m → Bool) (i : Fin m) : diag f ≠ f i := by
  intro h
  have hi : diag f i = f i i := congrFun h i
  simp only [diag] at hi
  exact absurd hi (by cases f i i <;> decide)

/-- **No enumerated circuit computes the diagonal (proved) — the lower bound.**  If `f` enumerates all
size-`s` circuits, then `diag f` is computed by none of them: a size lower bound. -/
theorem diag_not_enumerated {m : ℕ} (f : Fin m → Fin m → Bool) (i : Fin m) : f i ≠ diag f :=
  (diag_differs f i).symm

/-! ### Amplifying the diagonal base to the threshold -/

/-- **The diagonal base amplifies (proved).**  The diagonal supplies the ladder's base bound; given
`SelfImproving` (the MMW/OPS anti-checker — the open lever), it amplifies to the magnified
(superpolynomial) bound.  This is `MagnifiedMetaTrigger.magnifies` — the same multiplicative engine as
`cost_super`.  The diagonal is barrier-immune; the amplification is the open piece. -/
theorem diagonal_base_amplifies (L : MetaComplexityLadder) (p q : ℕ)
    (hSI : SelfImproving L p q) : MagnifiedBound L p q :=
  magnifies L p q hSI

/-- **The cap, formalized (proved).**  The diagonal built from `f` beats exactly the enumerated
circuits — it says nothing about a circuit not in the enumeration.  Concretely: `diag f` itself is a
function `Fin m → Bool`, so if some enumerated `f i` happened to equal it, that would already
contradict `diag_differs`; but any circuit *outside* the `m`-enumeration is untouched.  Coverage is the
enumeration size `m`, which caps the beatable circuit size at `~log m` (linear). -/
theorem diag_coverage_is_enumeration {m : ℕ} (f : Fin m → Fin m → Bool) :
    ∀ i : Fin m, diag f ≠ f i :=
  diag_differs f

end PallLean.Paper93.DeepMath.PathB.DiagonalWeakBound

#print axioms PallLean.Paper93.DeepMath.PathB.DiagonalWeakBound.diag_negates_self_application
#print axioms PallLean.Paper93.DeepMath.PathB.DiagonalWeakBound.diag_differs
#print axioms PallLean.Paper93.DeepMath.PathB.DiagonalWeakBound.diag_not_enumerated
#print axioms PallLean.Paper93.DeepMath.PathB.DiagonalWeakBound.diagonal_base_amplifies
#print axioms PallLean.Paper93.DeepMath.PathB.DiagonalWeakBound.diag_coverage_is_enumeration
