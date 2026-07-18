import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOneWayCommLB
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDIndexMachine

/-!
# P is not contained in sublinear one-way communication (unconditional)

Combining the two proved facts about the doubled-INDEX language `dIndexLang` gives a clean,
unconditional separation: it is decided in polynomial *time* (`dIndexInP`), yet at the balanced
cut it needs exponentially many one-way *messages* — linearly many communication bits.  So
polynomial time does not imply sublinear one-way communication (equivalently, sublinear
one-pass streaming space): `dIndexLang ∈ P` but `dIndexLang ∉ o(n)`-one-way-communication.

* `OneWayCost L a b k` — `L`'s `(a,b)`-balanced slice has a `k`-message one-way protocol.
* `dIndex_cost_lb` — the doubled-INDEX slice at `a = b = 3m+3` forces `k ≥ 2^m`.
* `dIndex_P_but_linear_oneWay` — the separation: `dIndexLang ∈ P`, and every one-way protocol
  for its balanced length-`(6m+6)` slice needs `≥ 2^m` messages (`≥ m` bits), i.e. `Ω(n)`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsOneWayComm

open PallLean.Paper93.DeepMath.PathB.ComposableMachine (InP)
open PallLean.Paper93.DeepMath.PathB.LangRankKill (dIndexLang)
open PallLean.Paper93.DeepMath.PathB.OneWayCommLB
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (dIndexInP)

/-- `L`'s `(a,b)`-balanced slice (Alice holds `a` bits, Bob holds `b` bits, input `= u ++ v`)
has a `k`-message one-way protocol. -/
def OneWayCost (L : List Bool → Bool) (a b k : ℕ) : Prop :=
  ∃ P : OneWayProtocol (Fin a → Bool) (Fin b → Bool) k,
    Computes P fun u v => L (List.ofFn u ++ List.ofFn v)

/-- **The doubled-INDEX slice lower bound.**  Any one-way protocol for the balanced
`(3m+3, 3m+3)` slice of `dIndexLang` needs at least `2^m` messages. -/
theorem dIndex_cost_lb (m k : ℕ) (h : OneWayCost dIndexLang (3 * m + 3) (3 * m + 3) k) :
    2 ^ m ≤ k := by
  obtain ⟨P, hP⟩ := h
  exact dIndex_oneWay_card_ge m k P hP

/-- **P ⊄ sublinear one-way communication (unconditional).**  `dIndexLang` is decided in
polynomial time, yet at the balanced cut of its length-`(6m+6)` inputs every one-way protocol
needs `≥ 2^m` messages — `≥ m` bits, linear in the input length.  Polynomial time does not
imply sublinear one-way communication. -/
theorem dIndex_P_but_linear_oneWay :
    InP dIndexLang
      ∧ ∀ m k, OneWayCost dIndexLang (3 * m + 3) (3 * m + 3) k → 2 ^ m ≤ k :=
  ⟨dIndexInP, dIndex_cost_lb⟩

/-- The bit form: the one-way message length at the balanced cut is at least `m`, while
`dIndexLang ∈ P`. -/
theorem dIndex_P_but_linear_oneWay_bits :
    InP dIndexLang
      ∧ ∀ m k, OneWayCost dIndexLang (3 * m + 3) (3 * m + 3) k → m ≤ Nat.log 2 k :=
  ⟨dIndexInP, fun m k h => by
    obtain ⟨P, hP⟩ := h
    exact dIndex_oneWay_bits_ge m k P hP⟩

end PallLean.Paper93.DeepMath.PathB.PvsOneWayComm
