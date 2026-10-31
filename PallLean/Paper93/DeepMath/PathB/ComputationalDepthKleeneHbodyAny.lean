import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneHbodyDispatch

/-! # Kleene interpreter project — rank reconstruction + per-cell hbody for any M (PROVED)

`cfgRank_reconstruct`: any `M` is the rank of its own decode `(M/(B+1)/(E+1), (M/(B+1))%(E+1), M%(B+1))`.
Hence `hbody_any`: `interpBody` computes `specOf E B M` for ANY `M` whose decode-fuel is `≤ B` (decode,
reconstruct, apply `hbody_dispatch`).  This is the `hbody` hypothesis `buildTableCtx_correct_bounded` needs.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. -/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

theorem cfgRank_reconstruct (E B M : ℕ) :
    cfgRank E B (M / (B+1) / (E+1)) ((M / (B+1)) % (E+1)) (M % (B+1)) = M := by
  unfold cfgRank
  rw [Nat.div_add_mod' (M / (B+1)) (E+1), Nat.div_add_mod' M (B+1)]

-- per-cell hbody for ANY M (decode M, reconstruct, apply hbody_dispatch) when fuel ≤ B
theorem hbody_any (E B M : ℕ) (hkB : M / (B+1) / (E+1) ≤ B) :
    interpBody.eval (Nat.pair (Nat.pair E B) (Nat.pair M (encodeList (tableList (specOf E B) M))))
      = Part.some (specOf E B M) := by
  have hrec := cfgRank_reconstruct E B M
  have hd := hbody_dispatch E B (M / (B+1) / (E+1)) ((M / (B+1)) % (E+1)) (M % (B+1))
    (Nat.lt_succ_iff.mp (Nat.mod_lt _ (by omega))) (Nat.lt_succ_iff.mp (Nat.mod_lt _ (by omega))) hkB
  rw [hrec] at hd
  exact hd

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.hbody_any
