import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneInterpCorrect
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneLookup

/-! # Kleene interpreter project — the explicit universal interpreter `universalInterp` (PROVED) ⭐

A SINGLE explicit `Code`, `universalInterp = comp headCode (buildTableCtx interpBody)`, that universally
simulates any `Code`: run to the diagonal rank it builds the memoised DP table and returns its top cell,
which equals `encodeOpt (Code.evaln K c0.toCode n0)` — the (encoded) bounded universal simulation, for any
`c0 : UCode`, fuel `K ≤ B`, input `n0`.  This is the explicit replacement for the opaque `exists_code`,
and the goal of the EffSim construction arc.

  `universalInterp` — the interpreter Code.  `universalInterp_correct` — its correctness.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`; it is a clean, reusable, fully verified universal interpreter.
The remaining EffSim work is the polynomial runtime bound. -/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList headCode eval_headCode_list)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

/-- The explicit Kleene universal interpreter: build the memoised DP table, extract the top cell. -/
noncomputable def universalInterp : Code := Code.comp headCode (buildTableCtx interpBody)

/-- **The explicit universal interpreter computes the (encoded) bounded universal simulation of any Code.** -/
theorem universalInterp_correct (E B K n0 : ℕ) (c0 : UCode)
    (hKB : K ≤ B) (hcE : c0.enc < E + 1) (hn0 : n0 < B + 1) :
    universalInterp.eval (Nat.pair (Nat.pair E B) (cfgRank E B K c0.enc n0 + 1))
      = Part.some (encodeOpt (Code.evaln K c0.toCode n0)) := by
  rw [universalInterp, comp_eval _ _ _ _ (universal_interp_table E B K n0 c0 hKB hcE hn0),
      eval_headCode_list]
  show Part.some ((tableList (specOf E B) (cfgRank E B K c0.enc n0 + 1)).headD 0) = _
  rw [show (tableList (specOf E B) (cfgRank E B K c0.enc n0 + 1)).headD 0
        = specOf E B (cfgRank E B K c0.enc n0) from rfl, spec_top E B K n0 c0 hcE hn0]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.universalInterp_correct
