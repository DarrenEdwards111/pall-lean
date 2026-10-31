import Mathlib

/-!
# Kleene interpreter project — the correctness target, via computability (PROVED)

The **correctness** North-Star — a single `Code` that simulates `Code.evaln` for every code and fuel — is
achievable directly from Mathlib's computability framework: the universal function
`m ↦ evaln (decode m)` is computable (`primrec_evaln` + `ofNat` + `unpair`), so `exists_code` yields a code
computing it.

  `universal_code_exists` — `∃ U : Code, ∀ k c n, U.eval (pair k (pair (encode c) n)) = ↑(Code.evaln k c n)`.

This proves the correctness half of the project's target (in Mathlib's `Code` encoding): the universal
interpreter exists and is correct.

## Honest scope and relation to the explicit construction

This `U` is **opaque** — produced by `exists_code`, with **no exposed runtime bound**.  It therefore does
*not* discharge `UniversalCodeRuntimePoly` / `DiagRuntimePolyBounded` (the efficient-hierarchy goal), which
needs an *explicit* `U` whose fuel the EffSim machinery can bound.  That explicit `U` is what the dispatch /
arithmetic / peel library (the `KleeneUCode` files) and the remaining double-recursion core are for.

So: correctness is settled here cheaply; the *efficiency* of simulation — the actual obstruction — still
requires the explicit interpreter.  The frozen `UniversalCodeCorrect` (stated with the tagged `UCode.enc`)
differs from this only by a re-encoding (`UCode.enc ↔ Encodable.encode ∘ toCode`).

## What is proved (clean axioms, no `sorry`)

* `universal_code_exists` — the universal interpreter exists and correctly simulates `evaln`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUniversal

open Nat.Partrec

/-- **The universal interpreter exists and correctly simulates `evaln` (proved).**  Opaque `U` (via
`exists_code`); no runtime bound — the explicit construction is needed for efficiency. -/
theorem universal_code_exists : ∃ U : Code, ∀ (k : ℕ) (c : Code) (n : ℕ),
    U.eval (Nat.pair k (Nat.pair (Encodable.encode c) n)) = (Code.evaln k c n : Part ℕ) := by
  have hrest : Computable (fun m : ℕ => (Nat.unpair m).2) := (Primrec.snd.comp Primrec.unpair).to_comp
  have hk : Computable (fun m : ℕ => (Nat.unpair m).1) := (Primrec.fst.comp Primrec.unpair).to_comp
  have hec : Computable (fun m : ℕ => (Nat.unpair (Nat.unpair m).2).1) :=
    (Primrec.fst.comp Primrec.unpair).to_comp.comp hrest
  have hn : Computable (fun m : ℕ => (Nat.unpair (Nat.unpair m).2).2) :=
    (Primrec.snd.comp Primrec.unpair).to_comp.comp hrest
  have hc : Computable (fun m : ℕ => Denumerable.ofNat Code (Nat.unpair (Nat.unpair m).2).1) :=
    (Computable.ofNat Code).comp hec
  have hg : Computable (fun m : ℕ =>
      Code.evaln (Nat.unpair m).1 (Denumerable.ofNat Code (Nat.unpair (Nat.unpair m).2).1)
        (Nat.unpair (Nat.unpair m).2).2) :=
    Code.primrec_evaln.to_comp.comp (hk.pair hc |>.pair hn)
  have hpart : Nat.Partrec (fun m => ((fun m : ℕ =>
      Code.evaln (Nat.unpair m).1 (Denumerable.ofNat Code (Nat.unpair (Nat.unpair m).2).1)
        (Nat.unpair (Nat.unpair m).2).2) m : Part ℕ)) := by
    rw [← Partrec.nat_iff]; exact Computable.ofOption hg
  obtain ⟨U, hU⟩ := Code.exists_code.mp hpart
  refine ⟨U, fun k c n => ?_⟩
  rw [hU]
  simp only [Nat.unpair_pair, Denumerable.ofNat_encode]

/-!
**Correctness target proved (opaque `U`).**  The universal interpreter exists and simulates `evaln`.  The
efficient-simulation goal (`UniversalCodeRuntimePoly`) needs the *explicit* interpreter — the dispatch +
arithmetic library + the double-recursion core.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUniversal

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUniversal.universal_code_exists
