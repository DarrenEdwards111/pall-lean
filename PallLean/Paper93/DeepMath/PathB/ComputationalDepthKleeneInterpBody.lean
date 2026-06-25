import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleenePairHandler
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneCompHandler
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleenePrecHandler
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneRfindHandler
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneBaseHandlers
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDispatch8
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDecode

/-!
# Kleene interpreter project — the per-cell interpreter body (constructed)

The body passed to `buildTableCtx`.  Given input `pair ctx (pair N T)` (`ctx = pair E B`, `T` the table of
earlier cells), it:

1. decodes `N` to `(k, ec, n)` via `decodeRankCode` (`decodedSrc`),
2. builds each handler's bundle `pair (whole input) (pair k (pair ec n))` (`bundleSrc`, `idCode` returning the
   input),
3. dispatches on `ec`'s tag (`tagSrc = (unpair ec).1`) via `mkDispatch` over all 8 handlers — base handlers
   wrapped by `baseAdapt` to take `pair (k-1) n` (the guard convention), recursive handlers take the bundle
   directly,
4. zeroes the result when `k = 0` (`evalnStep 0 = none`) via the `isPos k` factor.

  `baseAdapt`, `decodedSrc`, `bundleSrc`, `ecSrc`, `tagSrc`, `kSrcBody`, `interpBody`.

## What is here (compiles clean, `[propext]`)

* `interpBody : Code` — the constructed body.  **No correctness theorem yet**: `hbody` (`interpBody` computes
  `spec N` for every cell — the 8-way case analysis connecting each handler to `encodeOpt ∘ evaln` via the
  encode identities + `evalnStep_correct`) is the next piece.

## Honest scope

The body `Code` is constructed and type-checks.  Its correctness (`hbody`), the `spec` definition + the
`UCode ↔ Code` bridge, the interpreter `U`, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

/-- Adapt a base handler (which takes `pair k n`) to the bundle, feeding `pair (k-1) n` (guard convention). -/
noncomputable def baseAdapt (h : Code) : Code :=
  Code.comp h (Code.pair (Code.comp predCode (Code.comp Code.left Code.right))
    (Code.comp Code.right (Code.comp Code.right Code.right)))

/-- `(k, ec, n) = decode N` from the body input (`ctx = left input`, `N = left (right input)`). -/
noncomputable def decodedSrc : Code :=
  Code.comp decodeRankCode (Code.pair Code.left (Code.comp Code.left Code.right))
/-- Each handler's bundle: `pair (whole input) (pair k (pair ec n))`. -/
noncomputable def bundleSrc : Code := Code.pair idCode decodedSrc
/-- `ec` from the decoded triple. -/
noncomputable def ecSrc : Code := Code.comp Code.left (Code.comp Code.right decodedSrc)
/-- `ec`'s tag `(unpair ec).1`. -/
noncomputable def tagSrc : Code := Code.comp Code.left ecSrc
/-- `k` from the decoded triple. -/
noncomputable def kSrcBody : Code := Code.comp Code.left decodedSrc

/-- The per-cell interpreter body: decode → dispatch over 8 handlers → zero on fuel 0. -/
noncomputable def interpBody : Code :=
  Code.comp mulCode (Code.pair (Code.comp isPosCode kSrcBody)
    (Code.comp (mkDispatch [baseAdapt zeroHandler, baseAdapt succHandler, baseAdapt leftHandler,
        baseAdapt rightHandler, pairHandler, compHandler, precHandler, rfindHandler])
      (Code.pair bundleSrc tagSrc)))

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.interpBody
