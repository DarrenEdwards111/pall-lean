import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEqInP

/-!
# Two-way communication capstone: EQUALITY is in P but interactively hard

The self-contained *two-way* (interactive) communication arc, in one statement.  Where the
one-way / oblivious arc (`RestrictedModelCapstone`) is built on the **subfunction count** — a
measure that only bounds *one-pass* models, and which doubled INDEX defeats one-way but *not*
two-way — this arc is built on the **fooling-set method**, whose bounds survive full interaction.

The witness is EQUALITY (`EQ`): Alice and Bob each hold an `n`-bit string and must decide whether
they are equal.  It is decided in polynomial *time* (`eqLang_inP`, the scan machine `eqMachine`),
yet every deterministic two-way protocol for it needs **`≥ 2^n` leaves** — `≥ n` bits of
interactive communication — because the diagonal `{(x, x)}` is a size-`2^n` fooling set.

The arc, assembled here:

* **The method** — `fooling_method`: any `b`-valued fooling set lower-bounds the leaf count of any
  protocol (rectangle + monochromaticity forbid two fooling inputs sharing a leaf).
* **In P** — `eqLang_inP` (the self-delimiting equality scan machine, `EqInP`), and the encoded
  input decides `EQ` exactly (`eqLang_encFn`).
* **The witness** — the diagonal fooling set `diagFool n` of size `2^n` (`diagFool_isFooling`,
  `diagFool_card`).
* **The bound** — every protocol has `≥ 2^n` leaves (`eq_leaves_ge`), i.e. `≥ n` two-way bits
  (`eq_twoway_ge`).

`eq_in_P_but_hard_two_way` bundles these; `P_not_sublinear_twoWay` is the separation form:
polynomial time is not contained in sublinear two-way communication — a bound the subfunction
method cannot reach, since it holds against interaction, not just one pass.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoWayCommCapstone

open PallLean.Paper93.DeepMath.PathB.ComposableMachine (InP)
open PallLean.Paper93.DeepMath.PathB.TwoWayCommFooling
open PallLean.Paper93.DeepMath.PathB.EqInP

/-- **The fooling method.**  Any `b`-valued fooling set of `f` lower-bounds the number of leaves of
*any* two-way deterministic protocol computing `f`: distinct fooling inputs occupy distinct leaves,
so `|S| ≤ k`.  This is the engine of the whole arc, and — unlike the subfunction count — it bounds
interactive protocols. -/
theorem fooling_method {α β : Type} (f : α → β → Bool) (k : ℕ) (R : RectPartition f k)
    (S : Finset (α × β)) (b : Bool) (hS : FoolingSet f S b) : S.card ≤ k :=
  fooling_card_le f k R S b hS

/-- **THE TWO-WAY CAPSTONE.**  EQUALITY is decided in polynomial time yet is `Ω(exponential)`-hard
against every two-way (interactive) deterministic protocol, from one explicit fooling set:

1. **In P**;
2. **computes EQUALITY** — the poly-time language, on an encoded `(x, y)`, is exactly `x = y`;
3. **explicit witness** — the diagonal is a size-`2^n` fooling set;
4. **leaf lower bound** — every two-way protocol has `≥ 2^n` leaves;
5. **bit lower bound** — every two-way protocol uses `≥ n` bits of interactive communication.

A single explicit polynomial-time witness that `P` is not contained in sublinear two-way
communication — a separation unreachable by the one-way subfunction method. -/
theorem eq_in_P_but_hard_two_way :
    -- (1) in P
    InP eqLang
    -- (2) computes EQUALITY on encoded inputs
    ∧ (∀ (n : ℕ) (x y : Fin n → Bool),
        eqLang (encPairs ((List.ofFn x).zip (List.ofFn y))) = EQ n x y)
    -- (3) explicit size-2^n diagonal fooling set
    ∧ (∀ n : ℕ, FoolingSet (EQ n) (diagFool n) true ∧ (diagFool n).card = 2 ^ n)
    -- (4) leaf lower bound
    ∧ (∀ (n k : ℕ), RectPartition (EQ n) k → 2 ^ n ≤ k)
    -- (5) two-way bit lower bound
    ∧ ∀ (n k : ℕ), RectPartition (EQ n) k → n ≤ Nat.log 2 k :=
  ⟨eqLang_inP,
    fun _ x y => eqLang_encFn x y,
    fun n => ⟨diagFool_isFooling n, diagFool_card n⟩,
    fun n k R => eq_leaves_ge n k R,
    fun n k R => eq_twoway_ge n k R⟩

/-- **The separation form.**  Polynomial time is not contained in sublinear two-way communication:
`eqLang ∈ P`, and every deterministic two-way protocol for the length-`n` equality problem uses
`≥ n` bits.  Interactive communication does not shrink the equality problem below linear, even
though it is polynomial-time decidable. -/
theorem P_not_sublinear_twoWay :
    InP eqLang ∧ ∀ (n k : ℕ), RectPartition (EQ n) k → n ≤ Nat.log 2 k :=
  ⟨eqLang_inP, fun n k R => eq_twoway_ge n k R⟩

end PallLean.Paper93.DeepMath.PathB.TwoWayCommCapstone
