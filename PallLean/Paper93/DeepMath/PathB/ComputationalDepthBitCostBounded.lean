import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitCostTotal
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneSpec
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEncodeOpt
import Mathlib.Tactic

/-!
# Bit-cost model — the bit-bounded class where the operand bit-length is provably polynomial (PROVED)

The flat-DP cost `interp_total_cost_poly` carries a parameter `s` — the operand bit-length — which is the one
input not fixed by `(B, E)`.  This file characterises exactly when `s` is provably polynomial, making the
efficient-simulation bound **unconditional** for a class.

The cells hold `specOf E B M = encodeOpt (evaln output)`, so a cell value is `≤ V + 1` whenever the config's
`evaln` output is `≤ V` (`specOf_le_of_output`).  Define the **bit-bounded class** `OutputBounded E B K ec n V`
= every config up to the diagonal has `evaln` output `≤ V`.  For it:

* the charge `s = bitlen (V+1)` is **faithful** — every cell's bit-length is `≤ bitlen (V+1)`
  (`outputBounded_faithful`);
* `bitlen (V+1) ≤ V+1` (`bitlen_le_self`), so `s` is polynomial whenever `V` is;
* hence the total flat-DP cost is `≤ 3·P² + P·(Σ_{t<9} g t)·bitlen(V+1)²` — **polynomial in `(B,E,V)`**,
  *unconditionally* (`bitBounded_efficient`).

Natural members: decision problems (`V = 1`), `B`-bounded-output computations (`V = B`).  This is a genuine
restriction — not all `Code`s are output-bounded (`Nat.pair` squares magnitude, `pair_ge_sq`) — and it pins
down precisely the computations the memoised DP simulates with polynomial bit-cost.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

open PallLean.Paper93.DeepMath.PathB.KleeneUCode
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)
open Nat.Partrec

namespace PallLean.Paper93.DeepMath.PathB.BitCost

/-- If the config-`M` `evaln` output is bounded by `V`, the cell value `specOf E B M` is `≤ V + 1`. -/
theorem specOf_le_of_output (E B M V : ℕ)
    (hb : ∀ w, UCode.evaln (M / (B + 1) / (E + 1)) (decodeU ((M / (B + 1)) % (E + 1))) (M % (B + 1)) = some w → w ≤ V) :
    specOf E B M ≤ V + 1 := by
  unfold specOf
  cases he : UCode.evaln (M / (B + 1) / (E + 1)) (decodeU ((M / (B + 1)) % (E + 1))) (M % (B + 1)) with
  | none => simp [encodeOpt]
  | some w => simp only [encodeOpt]; have := hb w he; omega

/-- `bitlen` never exceeds the number itself. -/
theorem bitlen_le_self (n : ℕ) : bitlen n ≤ n := by
  rw [bitlen, Nat.size_le]; exact Nat.lt_two_pow_self

/-- **The bit-bounded class**: at parameters `(E,B,K,ec,n)`, every config up to the diagonal has `evaln`
output `≤ V`. -/
def OutputBounded (E B K ec n V : ℕ) : Prop :=
  ∀ M, M < cfgRank E B K ec n + 1 →
    ∀ w, UCode.evaln (M / (B + 1) / (E + 1)) (decodeU ((M / (B + 1)) % (E + 1))) (M % (B + 1)) = some w → w ≤ V

/-- **For the bit-bounded class the charge `s = bitlen (V+1)` is faithful**: every cell value's bit-length is
`≤ bitlen (V+1)`. -/
theorem outputBounded_faithful (E B K ec n V : ℕ) (hb : OutputBounded E B K ec n V) :
    ∀ M, M < cfgRank E B K ec n + 1 → bitlen (specOf E B M) ≤ bitlen (V + 1) :=
  fun M hM => bitlen_mono (specOf_le_of_output E B M V (hb M hM))

/-- **Unconditional polynomial efficient simulation for the bit-bounded class.**  When all outputs are `≤ V`,
the faithful operand bit-length `s = bitlen (V+1)` satisfies `s ≤ V+1`, and the flat DP's total cost
(reads + arithmetic) is `≤ 3·P² + P·(Σ_{t<9} g t)·s²` with `P = (B+1)²(E+1)+1` — polynomial in `(B,E,V)`. -/
theorem bitBounded_efficient (g : ℕ → ℕ) (E B K ec n V : ℕ) (hK : K ≤ B) (hec : ec ≤ E) (hn : n ≤ B)
    (hb : OutputBounded E B K ec n V) :
    (∀ M, M < cfgRank E B K ec n + 1 → bitlen (specOf E B M) ≤ bitlen (V + 1))
    ∧ bitlen (V + 1) ≤ V + 1
    ∧ buildReadCost (interpReads E B) (cfgRank E B K ec n + 1)
        + buildArithCost (fun M => g (cappedTag E B M)) (bitlen (V + 1)) (cfgRank E B K ec n + 1)
      ≤ 3 * ((B + 1) * (B + 1) * (E + 1) + 1) * ((B + 1) * (B + 1) * (E + 1) + 1)
        + ((B + 1) * (B + 1) * (E + 1) + 1) * (((List.range 9).map g).sum * opBitCost (bitlen (V + 1))) :=
  ⟨outputBounded_faithful E B K ec n V hb, bitlen_le_self (V + 1),
   interp_total_cost_poly g E B K ec n (bitlen (V + 1)) hK hec hn⟩

end PallLean.Paper93.DeepMath.PathB.BitCost

#print axioms PallLean.Paper93.DeepMath.PathB.BitCost.bitBounded_efficient
