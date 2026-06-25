import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneTableCorrect

/-! # Kleene interpreter project — bounded table correctness (PROVED)

A variant of `buildTableCtx_correct` whose `hbody` hypothesis is only required for cells `M < T`.  This is
what lets `hbody_dispatch` (which needs `k ≤ B`) discharge the table at the diagonal target `T = cfgRank E
B K c0 n0`: every cell `M < T` has decode-fuel `≤ K ≤ B`.  `buildTableCtx_correct_bounded`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. -/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)

theorem buildTableCtx_correct_bounded (body : Code) (ctx : ℕ) (spec : ℕ → ℕ) :
    ∀ T, (∀ M, M < T → body.eval (Nat.pair ctx (Nat.pair M (encodeList (tableList spec M)))) = Part.some (spec M)) →
      (buildTableCtx body).eval (Nat.pair ctx T) = Part.some (encodeList (tableList spec T)) := by
  intro T
  induction T with
  | zero => intro _; rw [eval_buildTableCtx_zero]; rfl
  | succ T ih =>
    intro hb
    rw [eval_buildTableCtx_succ, ih (fun M hM => hb M (by omega))]
    simp only [Part.bind_eq_bind, Part.bind_some, hb T (by omega)]
    rfl

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.buildTableCtx_correct_bounded
