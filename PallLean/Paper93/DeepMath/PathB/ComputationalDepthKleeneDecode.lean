import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneCfgRankCode
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDivMod
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneRankDecode

/-!
# Kleene interpreter project — the rank-decode Code (PROVED)

The per-cell body recovers `(k, ec, n)` from a rank.  `decodeRankCode` realizes the inverse of `cfgRank`
(`cfgRank_decode`) as a `Code`, applying `divmodCode` twice (by `B+1`, then `E+1`) — assembled cleanly with
the compose workhorses.

  `pair_eval` — the `pair`-headed workhorse (companion to `comp_eval`/`comp_pair_eval`).
  `decodeRankCode` — input `pair (pair E B) rank`; on a valid rank `cfgRank E B k ec n`
    (`ec < E+1`, `n < B+1`) returns `pair k (pair ec n)`.

## What is proved (clean axioms, no `sorry`)

* `pair_eval`, `decodeRankCode`, `eval_decodeRankCode`.

## Honest scope

The rank-decode Code.  The per-cell body (`mkDispatch` + `cfgRankCode` + `lookupCode`), the correctness
chain, the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank cfgRank_decode)

/-- **`pair`-headed workhorse (proved).** -/
theorem pair_eval (g h : Code) (X a b : ℕ) (hg : g.eval X = Part.some a) (hh : h.eval X = Part.some b) :
    (Code.pair g h).eval X = Part.some (Nat.pair a b) := by
  rw [show (Code.pair g h).eval X = Nat.pair <$> g.eval X <*> h.eval X from rfl, hg, hh]
  simp [Part.map_some, Seq.seq, Part.bind_some]

/-- Decode a rank to `(k, ec, n)`: input `pair (pair E B) rank`; `divmodCode` by `B+1` then `E+1`. -/
def decodeRankCode : Code :=
  Code.pair
    (Code.comp Code.left (Code.comp divmodCode (Code.pair
      (Code.comp Code.succ (Code.comp Code.left Code.left))
      (Code.comp Code.left (Code.comp divmodCode (Code.pair
        (Code.comp Code.succ (Code.comp Code.right Code.left)) Code.right))))))
    (Code.pair
      (Code.comp Code.right (Code.comp divmodCode (Code.pair
        (Code.comp Code.succ (Code.comp Code.left Code.left))
        (Code.comp Code.left (Code.comp divmodCode (Code.pair
          (Code.comp Code.succ (Code.comp Code.right Code.left)) Code.right))))))
      (Code.comp Code.right (Code.comp divmodCode (Code.pair
        (Code.comp Code.succ (Code.comp Code.right Code.left)) Code.right))))

/-- **Rank-decode correctness (proved): recovers `(k, ec, n)` from a valid rank.** -/
theorem eval_decodeRankCode (E B k ec n : ℕ) (hec : ec < E + 1) (hn : n < B + 1) :
    decodeRankCode.eval (Nat.pair (Nat.pair E B) (cfgRank E B k ec n))
      = Part.some (Nat.pair k (Nat.pair ec n)) := by
  obtain ⟨hmod, hecd, hkd⟩ := cfgRank_decode E B k ec n hec hn
  set X := Nat.pair (Nat.pair E B) (cfgRank E B k ec n) with hX
  set R := cfgRank E B k ec n with hR
  have hB1 : (Code.comp Code.succ (Code.comp Code.right Code.left)).eval X = Part.some (B + 1) := by
    rw [comp_eval _ _ _ _ (show (Code.comp Code.right Code.left).eval X = Part.some B from by
      rw [hX]; simp [Code.eval, Nat.unpair_pair])]; simp [Code.eval]
  have hE1 : (Code.comp Code.succ (Code.comp Code.left Code.left)).eval X = Part.some (E + 1) := by
    rw [comp_eval _ _ _ _ (show (Code.comp Code.left Code.left).eval X = Part.some E from by
      rw [hX]; simp [Code.eval, Nat.unpair_pair])]; simp [Code.eval]
  have hRk : (Code.right : Code).eval X = Part.some R := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hdm1 : (Code.comp divmodCode (Code.pair (Code.comp Code.succ (Code.comp Code.right Code.left))
        Code.right)).eval X = Part.some (Nat.pair (R / (B + 1)) (R % (B + 1))) := by
    rw [comp_pair_eval _ _ _ _ _ _ hB1 hRk, eval_divmodCode _ _ (Nat.succ_pos B)]
  have hq1 : (Code.comp Code.left (Code.comp divmodCode (Code.pair
        (Code.comp Code.succ (Code.comp Code.right Code.left)) Code.right))).eval X
      = Part.some (R / (B + 1)) := by rw [comp_eval _ _ _ _ hdm1]; simp [Code.eval, Nat.unpair_pair]
  have hn' : (Code.comp Code.right (Code.comp divmodCode (Code.pair
        (Code.comp Code.succ (Code.comp Code.right Code.left)) Code.right))).eval X
      = Part.some (R % (B + 1)) := by rw [comp_eval _ _ _ _ hdm1]; simp [Code.eval, Nat.unpair_pair]
  have hdm2 : (Code.comp divmodCode (Code.pair (Code.comp Code.succ (Code.comp Code.left Code.left))
        (Code.comp Code.left (Code.comp divmodCode (Code.pair
          (Code.comp Code.succ (Code.comp Code.right Code.left)) Code.right))))).eval X
      = Part.some (Nat.pair (R / (B + 1) / (E + 1)) (R / (B + 1) % (E + 1))) := by
    rw [comp_pair_eval _ _ _ _ _ _ hE1 hq1, eval_divmodCode _ _ (Nat.succ_pos E)]
  have hk : (Code.comp Code.left (Code.comp divmodCode (Code.pair
        (Code.comp Code.succ (Code.comp Code.left Code.left))
        (Code.comp Code.left (Code.comp divmodCode (Code.pair
          (Code.comp Code.succ (Code.comp Code.right Code.left)) Code.right)))))).eval X
      = Part.some (R / (B + 1) / (E + 1)) := by rw [comp_eval _ _ _ _ hdm2]; simp [Code.eval, Nat.unpair_pair]
  have hecc : (Code.comp Code.right (Code.comp divmodCode (Code.pair
        (Code.comp Code.succ (Code.comp Code.left Code.left))
        (Code.comp Code.left (Code.comp divmodCode (Code.pair
          (Code.comp Code.succ (Code.comp Code.right Code.left)) Code.right)))))).eval X
      = Part.some (R / (B + 1) % (E + 1)) := by rw [comp_eval _ _ _ _ hdm2]; simp [Code.eval, Nat.unpair_pair]
  show (Code.pair _ (Code.pair _ _)).eval X = _
  rw [pair_eval _ _ _ _ _ hk (pair_eval _ _ _ _ _ hecc hn'), hkd, hecd, hmod]

/-!
**Rank-decode Code proved.**  `decodeRankCode` recovers `(k, ec, n)` from a valid rank.  The per-cell body,
the correctness chain, the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_decodeRankCode
