import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOneWayCommTight
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOBDDWidthLB
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsOneWayComm

/-!
# Restricted-model capstone: doubled INDEX is in P but hard in every oblivious model

The self-contained restricted-complexity arc, in one statement.  The doubled-INDEX language
`dIndexLang` — decided in polynomial *time* (`dIndexInP`) — requires **exponential** resources
in every one-way / oblivious model, all from a single combinatorial fact (its `≥ 2^m`
subfunctions at the middle cut), and the one-way bound is *tight*.

The arc, assembled here:

* **In P** — `dIndexInP` (the two-pointer marking machine, `DIndexMachine`).
* **One-way communication** — every protocol for the balanced slice needs `≥ 2^m` messages
  (`OneWayCommLB`), and *exactly* the subfunction count suffices (`OneWayCommTight`) — tight.
* **Streaming** — the one-way bound is the one-pass streaming space bound (`PvsOneWayComm`).
* **Branching programs** — every OBDD computing it has width `≥ 2^m` (`OBDDWidthLB`).

`dIndex_hard_in_all_oblivious_models` bundles these: `P ⊄` sublinear one-way communication,
sublinear streaming space, or sub-exponential OBDD width — witnessed, tightly, by one explicit
polynomial-time language.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RestrictedModelCapstone

open PallLean.Paper93.DeepMath.PathB.ComposableMachine (InP)
open PallLean.Paper93.DeepMath.PathB.LangRankKill (dIndexLang subfunCountAt)
open PallLean.Paper93.DeepMath.PathB.OneWayCommLB
open PallLean.Paper93.DeepMath.PathB.OneWayCommTight (dIndex_oneWay_exact)
open PallLean.Paper93.DeepMath.PathB.OBDDWidthLB (OBDD dIndex_obdd_width_ge)
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (dIndexInP)

/-- **THE RESTRICTED-MODEL CAPSTONE.**  The doubled-INDEX language is decided in polynomial
time yet is `Ω(exponential)`-hard in every oblivious model, from one subfunction count:

1. **In P**;
2. **one-way communication** — the balanced slice needs `≥ 2^m` messages;
3. **branching-program width** — every OBDD needs `≥ 2^m` states;
4. **tight** — the one-way bound equals the exact subfunction count (both suffices and
   necessary).

A single explicit polynomial-time witness that `P` is not contained in sublinear one-way
communication, sublinear one-pass streaming space, or sub-exponential OBDD width. -/
theorem dIndex_hard_in_all_oblivious_models :
    -- (1) in P
    InP dIndexLang
    -- (2) one-way communication lower bound
    ∧ (∀ (m k : ℕ) (P : OneWayProtocol _ _ k), Computes P (dIndexComm m) → 2 ^ m ≤ k)
    -- (3) OBDD / branching-program width lower bound
    ∧ (∀ (m : ℕ) (Q : Type) [Fintype Q] (bp : OBDD Q),
        bp.Computes dIndexLang → 2 ^ m ≤ Fintype.card Q)
    -- (4) the one-way bound is tight: exactly the subfunction count
    ∧ (∀ m : ℕ,
        (∃ P : OneWayProtocol _ _ (subfunCountAt dIndexLang (3 * m + 3) (3 * m + 3)),
            Computes P (dIndexComm m))
          ∧ ∀ k (P : OneWayProtocol _ _ k), Computes P (dIndexComm m)
              → subfunCountAt dIndexLang (3 * m + 3) (3 * m + 3) ≤ k) :=
  ⟨dIndexInP,
    fun m k P hP => dIndex_oneWay_card_ge m k P hP,
    fun m Q _ bp hf => @dIndex_obdd_width_ge Q _ bp hf m,
    fun m => dIndex_oneWay_exact m⟩

/-- **The separation form.**  Polynomial time is not contained in sublinear one-way
communication: `dIndexLang ∈ P`, and every one-way protocol for its balanced length-`(6m+6)`
slice needs `≥ m` bits. -/
theorem P_not_sublinear_oneWay :
    InP dIndexLang
      ∧ ∀ (m k : ℕ) (P : OneWayProtocol _ _ k), Computes P (dIndexComm m) → m ≤ Nat.log 2 k :=
  ⟨dIndexInP, fun m k P hP => dIndex_oneWay_bits_ge m k P hP⟩

/-- **The branching-program separation form.**  Polynomial time is not contained in
sub-exponential OBDD width. -/
theorem P_not_subexp_obdd :
    InP dIndexLang
      ∧ ∀ (m : ℕ) (Q : Type) [Fintype Q] (bp : OBDD Q),
          bp.Computes dIndexLang → 2 ^ m ≤ Fintype.card Q :=
  ⟨dIndexInP, fun m Q _ bp hf => @dIndex_obdd_width_ge Q _ bp hf m⟩

end PallLean.Paper93.DeepMath.PathB.RestrictedModelCapstone
