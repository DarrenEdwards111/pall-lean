import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictedModelCapstone
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTwoWayCommCapstone
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNondetCommLB
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthIPInP

/-!
# Communication-complexity meta-capstone: P is not in sublinear communication, four ways

The whole communication-complexity program in one statement.  Four *different* lower-bound
techniques, on three explicit polynomial-time languages, each separating `P` from a restricted
communication model:

| Regime | Technique | Witness ∈ P |
|---|---|---|
| **one-way / oblivious streaming** | subfunction count | doubled INDEX (`dIndexLang`) |
| **two-way deterministic** | fooling sets / rectangles | EQUALITY (`eqLang`) |
| **nondeterministic** | 1-cover number | EQUALITY (`eqLang`) |
| **randomized (bounded-error)** | discrepancy + Lindsey's lemma | INNER PRODUCT (`ipLang`) |

Each is an *unconditional* separation: an explicit language decided in polynomial **time**
(`InP …`, on the faithful `ComposableMachine` model — three real machines: the two-pointer marking
machine, the self-delimiting equality scanner, the self-delimiting parity scanner) whose
communication problem provably requires **linear** communication in the named model.

`P_not_in_sublinear_communication` conjoins all four.  The moral: polynomial time buys nothing in
any of these communication models — and the four regimes are genuinely distinct (doubled INDEX is
hard one-way but *easy* two-way; EQUALITY is hard deterministically/nondeterministically but *easy*
randomized; INNER PRODUCT is the randomized-hard witness).

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CommComplexityCapstone

open PallLean.Paper93.DeepMath.PathB.ComposableMachine (InP)
open PallLean.Paper93.DeepMath.PathB.LangRankKill (dIndexLang)
open PallLean.Paper93.DeepMath.PathB.OneWayCommLB (OneWayProtocol Computes dIndexComm)
open PallLean.Paper93.DeepMath.PathB.EqInP (eqLang)
open PallLean.Paper93.DeepMath.PathB.TwoWayCommFooling (EQ RectPartition)
open PallLean.Paper93.DeepMath.PathB.NondetCommLB (Cover)
open PallLean.Paper93.DeepMath.PathB.IPInP (ipLang)
open PallLean.Paper93.DeepMath.PathB.LindseyIP (IP unif)
open PallLean.Paper93.DeepMath.PathB.RandCommDisc (DistProtocol errμ)

/-- **THE COMMUNICATION-COMPLEXITY META-CAPSTONE.**  Polynomial time is not contained in sublinear
communication in any of the four regimes, each witnessed by an explicit polynomial-time language:

1. **one-way / streaming** — `dIndexLang ∈ P`, yet its balanced slice needs `≥ m` one-way bits
   (subfunction count);
2. **two-way deterministic** — `eqLang ∈ P`, yet EQUALITY needs `≥ n` interactive bits (fooling
   sets);
3. **nondeterministic** — `eqLang ∈ P`, yet EQUALITY needs `≥ n` nondeterministic bits (1-cover
   number);
4. **randomized** — `ipLang ∈ P`, yet a `c`-bit bounded-error protocol for INNER PRODUCT with
   error `≤ ε` forces `1 − 2ε ≤ 2^c · 2^{-n/2}`, i.e. `c ≥ n/2 − O(1)` (discrepancy + Lindsey).

Four techniques, three machines, one conclusion: `P` gains nothing in any restricted communication
model. -/
theorem P_not_in_sublinear_communication :
    -- (1) one-way / oblivious streaming
    (InP dIndexLang
      ∧ ∀ (m k : ℕ) (P : OneWayProtocol _ _ k), Computes P (dIndexComm m) → m ≤ Nat.log 2 k)
    -- (2) two-way deterministic
    ∧ (InP eqLang ∧ ∀ (n k : ℕ), RectPartition (EQ n) k → n ≤ Nat.log 2 k)
    -- (3) nondeterministic
    ∧ (InP eqLang ∧ ∀ (n k : ℕ), Cover (EQ n) k → n ≤ Nat.log 2 k)
    -- (4) randomized (bounded-error)
    ∧ (InP ipLang
      ∧ ∀ (n c : ℕ) (P : DistProtocol (Fin n → Bool) (Fin n → Bool) (2 ^ c)) (ε : ℝ),
          errμ P IP unif ≤ ε → 1 - 2 * ε ≤ (2 ^ c : ℕ) * Real.sqrt (((2 : ℝ) ^ n)⁻¹)) :=
  ⟨PallLean.Paper93.DeepMath.PathB.RestrictedModelCapstone.P_not_sublinear_oneWay,
    PallLean.Paper93.DeepMath.PathB.TwoWayCommCapstone.P_not_sublinear_twoWay,
    PallLean.Paper93.DeepMath.PathB.NondetCommLB.P_not_sublinear_nondet,
    IPInP.IP_in_P_but_randomized_hard.1, IPInP.IP_in_P_but_randomized_hard.2.2⟩

/-- **The witnesses are genuinely three distinct languages in P** — the separations are not a single
result in disguise: doubled INDEX, EQUALITY, and INNER PRODUCT are each decided in polynomial time
by their own `ComposableMachine`. -/
theorem three_poly_time_witnesses : InP dIndexLang ∧ InP eqLang ∧ InP ipLang :=
  ⟨PallLean.Paper93.DeepMath.PathB.DIndexMachine.dIndexInP, EqInP.eqLang_inP, IPInP.ipLang_inP⟩

end PallLean.Paper93.DeepMath.PathB.CommComplexityCapstone
