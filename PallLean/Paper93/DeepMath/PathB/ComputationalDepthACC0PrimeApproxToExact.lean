import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymTopCrossLayer
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Amplification

/-!
# Prime-modulus approx→exact assembly: majority-correct ⇒ exact SYM∘AND (PROVED)

The prime side of the approx→exact barrier — where amplification **works**.  Combining the proved
exactness skeleton (`maj_exact`: majority-correct-everywhere ⇒ majority `= f` exactly) with the proved
decode structure (`topGate_crossLayer_hasMultiSymRep`: any symmetric top over `SYM∘AND` subcircuits is
multi-count), we get the full assembly:

  `exact_hasMultiSymRep_of_majorityCorrect` — if each approximant `g i` is `SYM∘AND` and the family is
  **majority-correct at every input** for `f`, then `f` is **exactly** a (multi-count) `SYM∘AND`.

For **prime** modulus `p`, the majority-correct-everywhere hypothesis is *achievable*: Razborov–Smolensky
amplification (`amplified_form_balance`) drives each approximant's per-input error to `(1/p)^t`, and `k`
independent low-degree approximants are then majority-correct everywhere — so `f` is exactly `SYM∘AND`.
This is precisely the step that **fails for composite modulus** (`ACC⁰[m]`): there is no prime field in
which the same amplification works, which is the Razborov–Smolensky barrier.

## What is proved (clean axioms, no `sorry`)

* `exact_hasMultiSymRep_of_majorityCorrect` — majority-correct family of `SYM∘AND` approximants ⇒ `f`
  is exactly `HasMultiSymRep` (the prime approx→exact assembly, modulo the majority-correct hypothesis).

## Honest scope

This assembles the *exactness* (`maj_exact`) and the *structure* (`topGate_crossLayer_hasMultiSymRep`)
into an exact `SYM∘AND` representation, **given** a majority-correct-everywhere family.  That hypothesis
is achievable for **prime** `p` (amplification works) and is the **barrier** for composite `m`
(amplification provably fails — the `ApproxToExactCount` / Razborov–Smolensky wall).  The probabilistic
construction of the majority-correct family from `amplified_form_balance` (the Chernoff/union step) is
the remaining prime-side ingredient and is not assembled here.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PrimeApproxToExact

open PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition
open PallLean.Paper93.DeepMath.PathB.ACC0ModGateCrossLayer (HasMultiSymRep)
open PallLean.Paper93.DeepMath.PathB.ACC0SymTopCrossLayer (topGate_crossLayer_hasMultiSymRep)
open PallLean.Paper93.DeepMath.PathB.ACC0Amplification (MajVote majBool maj_exact)

variable {n : ℕ}

/-- **Prime approx→exact assembly (proved).**  If each approximant `g i` has a `SYM∘AND` representation
and the family `g` is majority-correct at every input for `f` (`k < 2·#{i | g i x = f x}` for all `x`),
then `f` is **exactly** a multi-count `SYM∘AND` (`HasMultiSymRep`).  Combines `maj_exact` (exactness)
with `topGate_crossLayer_hasMultiSymRep` (the majority decode is a symmetric top, hence multi-count). -/
theorem exact_hasMultiSymRep_of_majorityCorrect {k : ℕ}
    {g : Fin k → ((Fin n → Bool) → Bool)} {f : (Fin n → Bool) → Bool}
    (hg : ∀ i, HasSymAndRep (g i))
    (hgood : ∀ x, k < 2 * (Finset.univ.filter (fun i => g i x = f x)).card) :
    HasMultiSymRep f := by
  rw [← maj_exact g f hgood]
  show HasMultiSymRep (fun x => majBool (fun i => g i x))
  exact topGate_crossLayer_hasMultiSymRep majBool hg

/-!
**Prime approx→exact assembly proved.**  A majority-correct-everywhere family of `SYM∘AND` approximants
yields an *exact* multi-count `SYM∘AND` for `f`.  The majority-correct hypothesis is achievable for
**prime** `p` (Razborov–Smolensky amplification, `amplified_form_balance`) and is the **barrier** for
composite `m`.  The Chernoff/union construction of the family is the remaining prime-side step; nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0PrimeApproxToExact

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimeApproxToExact.exact_hasMultiSymRep_of_majorityCorrect
