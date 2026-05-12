import PallLean.Paper93.Paper283.BridgeAKappaTwoCrossBlockNonsingular
import PallLean.Paper93.Paper283.BridgeAKappaTwoFourFamilyComputation
import PallLean.Paper93.Paper283.BridgeAKappaTwoCrossBlockProbe
import PallLean.Paper93.Paper283.BridgeAKappaTwoCrossBlockConcrete
import PallLean.Paper93.Paper283.BridgeABoolDerivative
import PallLean.Paper93.Paper283.BridgeABlockProductRule
import PallLean.Paper93.Paper283.BridgeABlockEvalAtZero
import PallLean.Paper93.Paper283.BridgeAMlProjLinear
import PallLean.IterDerivHelpers

/-!
# Four monomial-coefficient identities for κ = 2 Bridge A on `cookLevinLocalBlockQ`

This file is the follow-up to commit `475d12b`
(`BridgeAKappaTwoCrossBlockNonsingular`).  The conditional theorem
`cookLevinLocalBlockQ_rank_two_le_real` of that commit closes the
κ = 2 cross-block target on the real Cook-Levin local block product
**modulo** four monomial-coefficient identities at the two-fold
derivative of `Q_b`:

```
(1)   coeff(probeRight, mlProj(∂_{rowRight} Q_b)) = 2 K
(2)   coeff(probeRight, mlProj(∂_{rowLeft}  Q_b)) =   K
(3)   coeff(probeLeft , mlProj(∂_{rowRight} Q_b)) =   K
(4)   coeff(probeLeft , mlProj(∂_{rowLeft}  Q_b)) = 2 K
```

with `rowRight = [⟨3k+2⟩, ⟨3k+3⟩]`, `rowLeft = [⟨3k-1⟩, ⟨3k⟩]`,
`probeRight = X_{3k+1} · X_{3k+2}`, `probeLeft = X_{3k} · X_{3k+1}`,
and `K = (1 + Σ_q transCoeff_q) · (Σ_q transCoeff_q)`.

## Layering note after the κ = 2 package closure

The four coefficient identities are now closed in the downstream
assembled package path:

* `BridgeAKappaTwoIdentityOneResidualActive`,
* `BridgeAKappaTwoIdentityTwoResidualActive`,
* `BridgeAKappaTwoIdentityThreeResidualActive`,
* `BridgeAKappaTwoIdentityFourResidualActive`,
* `BridgeAKappaTwoKPositive`, and
* `BridgeAKappaTwoFourIdentitiesAssembled`.

This file intentionally does **not** import
`BridgeAKappaTwoFourIdentitiesAssembled`: that would create an import
cycle, since the assembled file depends on this package interface
through `BridgeAKappaTwoFourIdentitiesDischarged` and the identity
files.  This module therefore remains the low-level typed interface:
it defines `CookLevinLocalBlockQFourIdentitiesPackage`, preserves the
legacy residual-obstruction-shaped API as `Nonempty` of that package,
and exposes compatibility rank wrappers that consume any closed package
witness supplied by downstream layers.

## Historical report on the original kernel-only proof gap

The closed-form computation in commit `97daa11`
(`BridgeAKappaTwoFourFamilyComputation`) gives the *informal* path
enumeration of the two-fold Leibniz expansion of `pderiv_{w} pderiv_{v} Q_b`
into four families of contributions, summing to the closed-form
coefficient matrix `[[2K, K], [K, 2K]]`.  Historically, translating
this informal path enumeration to a kernel-only Lean proof of the four
identities ran into the following structural barrier:

* `cookLevinLocalBlockQ` is the `List.prod` over a *filtered* list of
  Cook-Levin compiler constraints.  For an interior locality block `k`
  the filtered list contains:
    - 3 booleanity factors, one per variable in `{3k, 3k+1, 3k+2}`;
    - up to 4 adjacency factors, at index `i ∈ {3k-1, 3k, 3k+1, 3k+2}`;
    - up to `4 · numStates` transition-skeleton factors, one per state
      and per `i ∈ {3k-1, 3k, 3k+1, 3k+2}`.

* The two-fold partial derivative `pderiv w (pderiv v _)` of such a
  list product expands to a double sum over (i, j) factor pairs, with
  three sub-cases (`i = j` self-factor, `i ≠ j` cross-factor, and
  inert factors handled in the outer "rest" product).  Computing the
  coefficient of a specific multilinear monomial of the result
  requires:
    1.  Splitting the filtered constraint list into four named
        sub-lists (boolean, adjacency, transition-skeleton, neighbours);
    2.  Proving for every (i, j) pair what the per-pair contribution
        is to the target monomial;
    3.  Summing the per-pair contributions across all
        `O((numStates)²)` cross-factor pairs and `O(numStates)`
        self-factor terms;
    4.  Verifying that all booleanity-cross-talk paths sum to zero
        for the chosen monomial probe.

* Each of steps (1)–(4) is a substantial computation in its own
  right.  A direct kernel-only proof of even *one* of the four
  identities requires hundreds of lines of case analysis at the
  level of `MvPolynomial.coeff_mul`, `MvPolynomial.pderiv`,
  `Finsupp.single`, and the explicit form of every constraint
  polynomial.  The original obstruction was that the existing
  `BridgeABoolDerivative` / `BridgeABlockProductRule` /
  `BridgeABlockEvalAtZero` / `BridgeAMlProjLinear` infrastructure
  evaluates *constant terms* of derivatives, not coefficients of
  multilinear monomials of the form `X_v · X_w` with `v ≠ w`.  The
  downstream residual-active files now provide the bespoke κ = 2
  coefficient closure on top of this package interface.

The task of this file is therefore to provide the stable package API:

1. Expose a typed predicate
   `CookLevinLocalBlockQFourIdentitiesPackage` recording the four
   identities at the type level, together with the rational `K`,
   `0 < K`, and the probe pair.

2. Prove the **named compositional theorem**
   `cookLevinLocalBlockQ_rank_two_le_real_unconditional` taking such
   a witness together with the positivity hypothesis `0 < K`, and
   delivering the rank lower bound by composition with
   `475d12b`'s `cookLevinLocalBlockQ_rank_two_le_real`.

3. Provide a `crossBlockKValue`-flavoured variant
   `cookLevinLocalBlockQ_rank_two_le_real_unconditional_of_K_value`
   that takes the canonical `K = (1 + S) · S` form.

4. Provide an existence-shaped sub-package
   `CookLevinLocalBlockQFourIdentitiesPackage` capturing all the data
   needed to discharge the conditional theorem in one shot.

The headline statement at this layer is the named theorem
`cookLevinLocalBlockQ_rank_two_le_real_unconditional`: it is the
end-to-end κ = 2 rank lower bound on the real Cook-Levin local block
product, conditional only on the typed package witnessing the four
identities and `0 < K`.  The downstream assembled module supplies that
package witness without adding an import edge back into this file.

No new axioms are introduced; the kernel-only set
`[propext, Classical.choice, Quot.sound]` is preserved.  No `sorry`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP

attribute [local instance] Classical.dec

/-! ## Section A: the typed four-identity predicate

The four-identity predicate is exposed as the data needed to discharge
the conditional `cookLevinLocalBlockQ_rank_two_le_real` of `475d12b`.
Because the row constructors `nsRowRight`, `nsRowLeft`, and
`nsInteriorBlock` of `BridgeAKappaTwoCrossBlockNonsingular` are
file-private, we expose the identities through a typed `structure`
that bundles them with the four hypotheses of the upstream theorem,
ready to feed in. -/

/-- A bundled witness package recording the rational `K`, its
positivity, the probe pair, and the four monomial-coefficient
identities at the two-fold derivative of `cookLevinLocalBlockQ` for
the cross-block rows `nsRowRight n k hk2` and `nsRowLeft n k hk1 hk2`.

This is the precise input shape required by
`cookLevinLocalBlockQ_rank_two_le_real`: each field aligns with the
corresponding hypothesis of the conditional theorem. -/
structure CookLevinLocalBlockQFourIdentitiesPackage
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    : Type where
  K     : Rat
  hKpos : 0 < K
  probe : Fin 2 → Fin n →₀ Nat
  /-- Identity (1): right probe vs right row `= 2K`. -/
  h00 :
    MvPolynomial.coeff (probe 0)
        (mlProj (iterDerivList
          [(⟨3 * k + 2, by omega⟩ : Fin n),
           (⟨3 * k + 3, hk2⟩ : Fin n)]
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      2 * K
  /-- Identity (2): right probe vs left row `= K`. -/
  h01 :
    MvPolynomial.coeff (probe 0)
        (mlProj (iterDerivList
          [(⟨3 * (k - 1) + 2, by
              have heq : 3 * (k - 1) + 3 = 3 * k := by
                rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
                congr 1; omega
              omega⟩ : Fin n),
           (⟨3 * k + 0, by omega⟩ : Fin n)]
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      K
  /-- Identity (3): left probe vs right row `= K`. -/
  h10 :
    MvPolynomial.coeff (probe 1)
        (mlProj (iterDerivList
          [(⟨3 * k + 2, by omega⟩ : Fin n),
           (⟨3 * k + 3, hk2⟩ : Fin n)]
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      K
  /-- Identity (4): left probe vs left row `= 2K`. -/
  h11 :
    MvPolynomial.coeff (probe 1)
        (mlProj (iterDerivList
          [(⟨3 * (k - 1) + 2, by
              have heq : 3 * (k - 1) + 3 = 3 * k := by
                rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
                congr 1; omega
              omega⟩ : Fin n),
           (⟨3 * k + 0, by omega⟩ : Fin n)]
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      2 * K

/-! ## Section B: end-to-end unconditional rank lower bound from a witness

We now wrap the four-identity package in the existing
`cookLevinLocalBlockQ_rank_two_le_real` of commit `475d12b`.

The result is the **named compositional theorem**
`cookLevinLocalBlockQ_rank_two_le_real_unconditional`: any user-supplied
witness for the four identities plus the positivity hypothesis `0 < K`
gives the κ = 2 rank lower bound. -/

/-- End-to-end κ = 2 rank lower bound for the real Cook-Levin local
block product, conditional **only** on a typed witness for the four
monomial-coefficient identities and `0 < K`.

This is the headline of this file: a direct composition of
`cookLevinLocalBlockQ_rank_two_le_real` of commit `475d12b` with the
typed four-identity package of this file.  Once a kernel-only proof
of the four identities is supplied (as a
`CookLevinLocalBlockQFourIdentitiesPackage`), the unconditional rank
lower bound follows. -/
theorem cookLevinLocalBlockQ_rank_two_le_real_unconditional
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (pkg :
      CookLevinLocalBlockQFourIdentitiesPackage
        M n hn htb hns k hk1 hk2) :
    (2 : Nat) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        2 2
        (cookLevinLocalBlockQ M n hn htb hns
          ⟨k, by rw [cook_levin_numBlocks]; omega⟩) := by
  -- Feed the four identities of the package into the conditional
  -- theorem of `475d12b`.  Because `nsRowRight`, `nsRowLeft`, and
  -- `nsInteriorBlock` are private to that file, we let Lean unfold
  -- them via the upstream theorem's type signature: each
  -- `nsRowRight n k hk2` is defeq to the literal list
  -- `[⟨3k+2,_⟩, ⟨3k+3,_⟩]` used in the package.
  exact
    cookLevinLocalBlockQ_rank_two_le_real
      M n hn htb hns k hk1 hk2 pkg.K pkg.hKpos pkg.probe
      pkg.h00 pkg.h01 pkg.h10 pkg.h11

/-- Variant taking the canonical `K = crossBlockKValue S = (1 + S) · S`
form, with `S > 0` discharging the positivity hypothesis automatically. -/
theorem cookLevinLocalBlockQ_rank_two_le_real_unconditional_of_K_value
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (S : Rat) (hSpos : 0 < S)
    (probe : Fin 2 → Fin n →₀ Nat)
    (h00 :
      MvPolynomial.coeff (probe 0)
          (mlProj (iterDerivList
            [(⟨3 * k + 2, by omega⟩ : Fin n),
             (⟨3 * k + 3, hk2⟩ : Fin n)]
            (cookLevinLocalBlockQ M n hn htb hns
              ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
        2 * crossBlockKValue S)
    (h01 :
      MvPolynomial.coeff (probe 0)
          (mlProj (iterDerivList
            [(⟨3 * (k - 1) + 2, by
                have heq : 3 * (k - 1) + 3 = 3 * k := by
                  rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
                  congr 1; omega
                omega⟩ : Fin n),
             (⟨3 * k + 0, by omega⟩ : Fin n)]
            (cookLevinLocalBlockQ M n hn htb hns
              ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
        crossBlockKValue S)
    (h10 :
      MvPolynomial.coeff (probe 1)
          (mlProj (iterDerivList
            [(⟨3 * k + 2, by omega⟩ : Fin n),
             (⟨3 * k + 3, hk2⟩ : Fin n)]
            (cookLevinLocalBlockQ M n hn htb hns
              ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
        crossBlockKValue S)
    (h11 :
      MvPolynomial.coeff (probe 1)
          (mlProj (iterDerivList
            [(⟨3 * (k - 1) + 2, by
                have heq : 3 * (k - 1) + 3 = 3 * k := by
                  rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
                  congr 1; omega
                omega⟩ : Fin n),
             (⟨3 * k + 0, by omega⟩ : Fin n)]
            (cookLevinLocalBlockQ M n hn htb hns
              ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
        2 * crossBlockKValue S) :
    (2 : Nat) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        2 2
        (cookLevinLocalBlockQ M n hn htb hns
          ⟨k, by rw [cook_levin_numBlocks]; omega⟩) := by
  let pkg :
      CookLevinLocalBlockQFourIdentitiesPackage M n hn htb hns k hk1 hk2 :=
    { K := crossBlockKValue S
      hKpos := crossBlockKValue_pos_of_pos hSpos
      probe := probe
      h00 := h00
      h01 := h01
      h10 := h10
      h11 := h11 }
  exact
    cookLevinLocalBlockQ_rank_two_le_real_unconditional
      M n hn htb hns k hk1 hk2 pkg

/-! ## Section C: legacy residual wrapper for the package witness

The historical residual API was phrased as a Prop.  At this layer that
Prop is exactly `Nonempty CookLevinLocalBlockQFourIdentitiesPackage`.
The downstream assembled module now supplies such a package, but this
file cannot import it without an import cycle. -/

/-- Legacy residual-obstruction shape for the κ = 2 package path.

This is no longer a mathematical marker for an unsolved global package
input; it is a backward-compatible name for the proposition that the
typed four-identity package has been constructed.  The closed
construction lives downstream in
`BridgeAKappaTwoFourIdentitiesAssembled`. -/
def cookLevinLocalBlockQ_residual_four_identity_obstruction
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Prop :=
  Nonempty
    (CookLevinLocalBlockQFourIdentitiesPackage
      M n hn htb hns k hk1 hk2)

/-- The legacy residual-obstruction Prop holds whenever a package
witness exists. -/
theorem cookLevinLocalBlockQ_residual_four_identity_obstruction_of_package
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (pkg :
      CookLevinLocalBlockQFourIdentitiesPackage
        M n hn htb hns k hk1 hk2) :
    cookLevinLocalBlockQ_residual_four_identity_obstruction
      M n hn htb hns k hk1 hk2 :=
  ⟨pkg⟩

/-- Backward-compatible closed-package alias for
`cookLevinLocalBlockQ_residual_four_identity_obstruction_of_package`.

The assembled module constructs the package witness downstream; this
file exposes the consumption side without importing that module. -/
theorem cookLevinLocalBlockQ_residual_four_identity_obstruction_of_closed_package
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (pkg :
      CookLevinLocalBlockQFourIdentitiesPackage
        M n hn htb hns k hk1 hk2) :
    cookLevinLocalBlockQ_residual_four_identity_obstruction
      M n hn htb hns k hk1 hk2 :=
  cookLevinLocalBlockQ_residual_four_identity_obstruction_of_package
    M n hn htb hns k hk1 hk2 pkg

/-- The unconditional rank lower bound follows from the residual
obstruction Prop being inhabited.  Equivalent statement of the
headline theorem in classical-logic form. -/
theorem cookLevinLocalBlockQ_rank_two_le_real_of_residual_obstruction
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (hres :
      cookLevinLocalBlockQ_residual_four_identity_obstruction
        M n hn htb hns k hk1 hk2) :
    (2 : Nat) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        2 2
        (cookLevinLocalBlockQ M n hn htb hns
          ⟨k, by rw [cook_levin_numBlocks]; omega⟩) := by
  classical
  obtain ⟨pkg⟩ := hres
  exact
    cookLevinLocalBlockQ_rank_two_le_real_unconditional
      M n hn htb hns k hk1 hk2 pkg

/-- Clear closed-package alias for the rank lower bound.  This is the
same composition as `cookLevinLocalBlockQ_rank_two_le_real_unconditional`,
with a name that emphasizes the post-closure package flow. -/
theorem cookLevinLocalBlockQ_rank_two_le_real_of_closed_package
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (pkg :
      CookLevinLocalBlockQFourIdentitiesPackage
        M n hn htb hns k hk1 hk2) :
    (2 : Nat) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        2 2
        (cookLevinLocalBlockQ M n hn htb hns
          ⟨k, by rw [cook_levin_numBlocks]; omega⟩) :=
  cookLevinLocalBlockQ_rank_two_le_real_unconditional
    M n hn htb hns k hk1 hk2 pkg

/-! ## Section D: current package status

This file is now the low-level interface consumed by the closed
κ = 2 package path.  It does not import the assembled proof because
that would introduce a cycle; instead it keeps the package type,
legacy residual-obstruction Prop, and compatibility rank wrappers.

The kernel-closed construction of the package witness is downstream in
`BridgeAKappaTwoFourIdentitiesAssembled`, using the closed identity
(1), (2), (3), and (4) residual-active files plus the closed positivity
lemma for `crossBlockKValue (transCoeffSum M)`. -/

/-! ## Axiom audit anchors -/

#print axioms CookLevinLocalBlockQFourIdentitiesPackage
#print axioms cookLevinLocalBlockQ_rank_two_le_real_unconditional
#print axioms cookLevinLocalBlockQ_rank_two_le_real_unconditional_of_K_value
#print axioms cookLevinLocalBlockQ_residual_four_identity_obstruction
#print axioms cookLevinLocalBlockQ_residual_four_identity_obstruction_of_package
#print axioms cookLevinLocalBlockQ_residual_four_identity_obstruction_of_closed_package
#print axioms cookLevinLocalBlockQ_rank_two_le_real_of_residual_obstruction
#print axioms cookLevinLocalBlockQ_rank_two_le_real_of_closed_package

end PallLean.Paper93.Paper283
