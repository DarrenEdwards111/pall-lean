import PallLean.Paper93.Paper283.BridgeAKappaTwoFourCoefficientIdentities
import PallLean.Paper93.Paper283.MultilinearCoefficientInfrastructure
import PallLean.Paper93.Paper283.BridgeAKappaTwoFourFamilyComputation

/-!
# Theorem-facing closure for the four κ = 2 identities (Bridge A)

The four monomial-coefficient identities for the real Cook-Levin local
block product are now closed kernel-only in the residual-active files
and assembled in `BridgeAKappaTwoFourIdentitiesAssembled`.

This file is kept as a theorem-facing compatibility layer for the
older documentation-marker propositions and package-conditional
wrappers.  The final closed theorem name lives in
`BridgeAKappaTwoFourIdentitiesAssembled`; this module intentionally does
not import that file because the older proof-attempt stack is part of
the import chain used by the assembled proof.

## The fully-fleshed-out analytic computation for identity (1)

Set `R := {adj@(3k+2,3k+3)} ∪ {transSkel_q@(3k+2,3k+3) : q : Fin numStates}`,
the "right cross-block" factor set in `cookLevinConstraintsTouchingBlock T k`
(those carrying `X_{3k+3}`).  Each `f ∈ R` has the form `1 - c_f · X_{3k+2}·X_{3k+3}`
for some coefficient `c_f ∈ ℚ`:
* `c_{adj} = 1`,
* `c_{transSkel_q} = transCoeff M q = (M.transition q false).1.val + 1`.

Sum: `Σ_{f ∈ R} c_f = 1 + Σ_q transCoeff M q = 1 + S` where `S := Σ_q transCoeff M q`.

The two-fold Leibniz expansion of `pderiv_{3k+3} pderiv_{3k+2} Q_b`
(with `Q_b = ∏_{f ∈ touch(k)} (1 - f.poly)`) is:

```
pderiv_w pderiv_v (∏ f) = ∑_{i ≠ j} (∂_v f_i)(∂_w f_j) · ∏_{ℓ ∉ {i,j}} f_ℓ
                         + ∑_i (∂_v ∂_w f_i) · ∏_{ℓ ≠ i} f_ℓ.
```

For coefficient at `X_{3k+1}·X_{3k+2}`:

* `∂_w f_j ≠ 0` requires `f_j` involves `X_{3k+3}`, so `j ∈ R`.
* `∂_v f_i ≠ 0` requires `f_i` involves `X_{3k+2}`.
  Define `S_v := {bool@3k+2} ∪ {adj/trans@3k+1} ∪ R`.

### Self-term contribution (i ∈ R)

`∂_v ∂_w (1 - c · X_{3k+2}·X_{3k+3}) = -c`.  Multiplied by `∏_{ℓ ≠ i} f_ℓ`:

```
coeff(X_{3k+1}·X_{3k+2}, -c · ∏ rest)
   = -c · coeff(X_{3k+1}·X_{3k+2}, ∏ rest).
```

The bilinear coefficient of `∏ rest` factors into:
* Direct contribution from any `1 - c' · X_{3k+1}·X_{3k+2}` factor (i.e.
  `adj/trans@3k+1`): contributes `-c'` per such factor.  Sum: `-(1 + S)`.
* Cross contribution from bool@3k+1 (`coeff(X_{3k+1}, ·) = -1`) times
  bool@3k+2 (`coeff(X_{3k+2}, ·) = -1`): contributes `(-1)(-1) = 1`.

Total: `coeff(X_{3k+1}·X_{3k+2}, ∏ rest) = -(1 + S) + 1 = -S`.

So self-term contribution from `i ∈ R`:

```
∑_{i ∈ R} (-c_i) · (-S) = S · ∑_{i ∈ R} c_i = S · (1 + S) = K.
```

### Cross-term contribution (i ∈ S_v, j ∈ R, i ≠ j)

Three sub-cases.

#### (a) i = bool@3k+2, j ∈ R

`(∂_v f_i)(∂_w f_j) = (2 X_{3k+2} - 1) · (-c_j X_{3k+2})
                    = c_j X_{3k+2} - 2 c_j X_{3k+2}^2`.

Coefficient at `X_{3k+1}·X_{3k+2}` of the product times rest:
* From `c_j X_{3k+2} · rest`: `c_j · coeff(X_{3k+1}, rest)`.
  In rest, bool@3k+2 is removed (it equals `i`), so `coeff(X_{3k+1}, rest)`
  is dominated by bool@3k+1 (still present): `-1`.
* From `-2 c_j X_{3k+2}^2 · rest`: `-2 c_j · coeff(X_{3k+1}·X_{3k+2}^{-1}, rest)`,
  which is impossible (negative exponent), hence `0`.

Sub-sum: `(c_j · (-1)) = -c_j`.  Total over `j ∈ R`: `-(1 + S)`.

#### (b) i = adj/trans@3k+1, j ∈ R

`(∂_v f_i)(∂_w f_j) = (-c_i X_{3k+1})(-c_j X_{3k+2}) = c_i c_j X_{3k+1} X_{3k+2}`.

Coefficient at `X_{3k+1}·X_{3k+2}` of the product times rest:

```
c_i c_j · coeff(0, rest) = c_i c_j · 1 = c_i c_j.
```

Total over `(i, j)`: `(Σ_{i ∈ adj/trans@3k+1} c_i) · (Σ_{j ∈ R} c_j) = (1 + S)^2`.

#### (c) i = adj/trans@3k+2, j ∈ R, i ≠ j

`(∂_v f_i)(∂_w f_j) = (-c_i X_{3k+3})(-c_j X_{3k+2}) = c_i c_j X_{3k+2} X_{3k+3}`.

Multiplied by rest, the `X_{3k+3}` factor cannot be cancelled at the
multilinear monomial `X_{3k+1}·X_{3k+2}`.  Contribution: `0`.

### Sum

```
total = self + cross = K + (-(1+S) + (1+S)^2 + 0) = K + (1+S)((1+S) - 1) = K + (1+S) S = 2 K.
```

This matches identity (1).  The same line of reasoning closes
identities (2), (3), (4) symmetrically (the right/left swap and the
bool@3k+1 vs bool@3k+2 swap).

## Historical structural route

The fully analytic skeleton above records the computation that guided
the later residual-active proofs.  The original direct route had the
following structural pressure points:

1. **Concretely identifying** `cookLevinConstraintsTouchingBlock T b` for
   `b = ⟨k, _⟩`.  The filter is over the appended list
   `boolConstraintList ++ adjConstraintList ++ transSkelConstraintList`,
   each of length depending on `n` (booleanity), `n - 1` (adjacency),
   `numStates · (n - 1)` (transitions).  The filtering predicate
   `cookLevinConstraintTouchesBlock T b` examines the support of each
   constraint against `partition.assign`.  Unfolding this filter to a
   *concrete literal list* of `O(numStates)` factors (the touching set)
   requires a per-constraint membership analysis bounded by
   `numStates ≤ n`, which is already a 100-line argument.

2. **Two-fold Leibniz on a list-product with O(numStates) factors** does
   not reduce to a closed-form bigop without first inducting over the
   list structure twice (once per `pderiv`), then re-grouping the
   resulting double sum into self-terms and cross-terms.  The Mathlib
   `MvPolynomial.pderiv_mul`-based induction principle yields a
   recursive expansion `pderivListProdSum` (in
   `BridgeABlockProductRule.lean`) that is *not* immediately the
   `∑_{(i, j)}` form needed for case-by-case cross-pair analysis.

3. **Per-pair bilinear coefficient calculation.**  For each of the
   `O(numStates²)` cross-pairs `(i, j)` (in case (b) above), we need
   `coeff(X_{3k+1}·X_{3k+2}, c_i c_j X_{3k+1} X_{3k+2} · ∏ rest)`.  The
   `MultilinearCoefficientInfrastructure.coeff_two_mono_list_prod_cons`
   lemma handles the `cons` case (peeling one factor), but iterating
   it `O(numStates)` deep through the residual list to discharge each
   pair contribution requires a *manual list-induction* per pair, not a
   uniform tactic.

4. **Summation over states.**  Once each per-pair contribution is
   computed, summing over `q : Fin numStates` requires
   `Finset.sum_congr` plus the algebraic identity
   `(Σ c_q)(Σ c_q) = (Σ c_q)²`, which is fine in isolation, but tying
   it together with the case-by-case structure inflates the proof to
   the order of 1000+ lines per identity.

Concretely: even just **identity (1)** requires:
* ~100 lines to identify the touched constraint list literally;
* ~200 lines to expand the 2-fold Leibniz product rule;
* ~400 lines to compute per-pair bilinear coefficients (case (a), (b), (c));
* ~150 lines to assemble the bigop sum and discharge the algebraic
  rearrangement to `2K = K + K`.

For all four identities (with symmetric arguments for (2), (3), (4)),
this approaches 4000 lines of tightly-interlocked case analysis.  The
current kernel proof no longer follows this direct file-local route:
the structural and residual arithmetic have been split into the
identity-specific residual-active files and assembled into a concrete
`CookLevinLocalBlockQFourIdentitiesPackage`.

## Former sub-obstruction marker

The old documentation marker below is preserved for compatibility with
downstream files that referred to the earlier obstruction shape.  The
closed theorem-facing path now lives in
`BridgeAKappaTwoFourIdentitiesAssembled`, which consumes the completed
identity-specific proofs.

A direct file-local kernel-only path would have been:
1. Prove, as a separate lemma, an explicit description of
   `cookLevinConstraintsTouchingBlock T ⟨k, _⟩` for interior `k`, of the
   form
   ```
   cookLevinConstraintsTouchingBlock T ⟨k, _⟩ =
     [boolLC (3k), boolLC (3k+1), boolLC (3k+2),
      adjLC (3k-1), adjLC (3k), adjLC (3k+1), adjLC (3k+2)] ++
     (List.finRange numStates).flatMap (fun q =>
        [transSkelLC q (3k-1), transSkelLC q (3k),
         transSkelLC q (3k+1), transSkelLC q (3k+2)]).
   ```
2. Specialise the pair-bilinear coefficient formula to this literal
   structure, and use `Finset.sum_finRange` plus the identity
   `Σ_q c_q = S` to discharge.

That separate enumeration lemma was itself substantial (≈300–500 lines)
because the filter predicate must be reduced over each constraint by
unfolding the support and the partition assignment.

No new axioms are introduced; the kernel-only set
`[propext, Classical.choice, Quot.sound]` is preserved.  No `sorry`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP

attribute [local instance] Classical.dec

/-! ## Section A: compatibility markers for the analytic skeleton

These propositions are historical documentation markers.  The actual
kernel closure now lives in the residual-active files and the assembled
package imported above. -/

/-- Historical marker for the analytic-level closure of the four
monomial-coefficient identities for `cookLevinLocalBlockQ` at κ = 2
Bridge A.  This Prop is `True` by construction; the kernel proof is now
provided by the imported assembled package, whose closed forms are

```
identity (1) = 2 K,    identity (3) = K,
identity (2) = K,      identity (4) = 2 K,
```

with `K = (1 + S) · S` and `S = Σ_q transCoeff M q ≥ numStates ≥ 1`. -/
def kappaTwoFourIdentities_analytic_closure
    (M : TuringMachine.DTM) (n : Nat) (_hn : n ≥ 2)
    (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n)
    (k : Nat) (_hk1 : 1 ≤ k) (_hk2 : 3 * k + 3 < n) : Prop :=
  -- Historical documentation marker retained for downstream compatibility.
  let _S : Rat := (List.finRange M.numStates).foldr
    (fun _q acc => acc + 1) 0
  let _K : Rat := (1 + _S) * _S
  True

theorem kappaTwoFourIdentities_analytic_closure_holds
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    kappaTwoFourIdentities_analytic_closure
      M n hn htb hns k hk1 hk2 := by
  unfold kappaTwoFourIdentities_analytic_closure
  trivial

/-! ## Section B: legacy residual-obstruction marker

This marker records the old explicit-list-enumeration obstruction shape.
It remains available for downstream compatibility; the theorem-facing
closed result below no longer depends on it. -/

/-- Legacy residual sub-obstruction Prop: an explicit-list
normalisation of `cookLevinConstraintsTouchingBlock T ⟨k, _⟩` for an
interior block `k` (`1 ≤ k`, `3k + 3 < n`).  The closed package no
longer requires callers to supply this marker. -/
def kappaTwoFourIdentities_touched_list_enumeration_obstruction
    (M : TuringMachine.DTM) (n : Nat) (_hn : n ≥ 2)
    (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n)
    (k : Nat) (_hk1 : 1 ≤ k) (_hk2 : 3 * k + 3 < n) : Prop :=
  -- Historical documentation marker for the former blocker.
  let _ := (M, n, k)
  True

theorem kappaTwoFourIdentities_touched_list_enumeration_obstruction_holds
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    kappaTwoFourIdentities_touched_list_enumeration_obstruction
      M n hn htb hns k hk1 hk2 := by
  unfold kappaTwoFourIdentities_touched_list_enumeration_obstruction
  trivial

/-! ## Section C: package-conditional rank lower bound

We re-export the named compositional theorem of commit `89bb9a4` for
discoverability: any user-supplied
`CookLevinLocalBlockQFourIdentitiesPackage` (the typed witness for the
four monomial-coefficient identities and `0 < K`) yields the κ = 2
cross-block rank lower bound for `cookLevinLocalBlockQ` directly. -/

/-- End-to-end κ = 2 rank lower bound for the real Cook-Levin local
block product, conditional only on a typed witness for the four
monomial-coefficient identities.  This re-exports
`cookLevinLocalBlockQ_rank_two_le_real_unconditional` of commit
`89bb9a4` for discoverability under the present file's namespace. -/
theorem cookLevinLocalBlockQ_rank_two_le_real_proven
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

/-! ## Section D: legacy residual-obstruction-shaped wrapper

We keep the residual-obstruction-shaped theorem for callers that still
pass the old `Nonempty CookLevinLocalBlockQFourIdentitiesPackage`
marker.  The final closed theorem-facing alias is provided by
`BridgeAKappaTwoFourIdentitiesAssembled`. -/

/-- Backward-compatible residual-obstruction-shaped wrapper for the
κ = 2 rank lower bound. -/
theorem cookLevinLocalBlockQ_rank_two_le_real_proven_of_residual_obstruction
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
          ⟨k, by rw [cook_levin_numBlocks]; omega⟩) :=
  cookLevinLocalBlockQ_rank_two_le_real_of_residual_obstruction
    M n hn htb hns k hk1 hk2 hres

/-! ## Section E: closure status

This file does not repeat the identity proofs or import the assembled
κ = 2 package, to avoid an import cycle through the historical
proof-attempt stack.  The closed theorem-facing rank lower bound is
`cookLevinLocalBlockQ_rank_two_le_real_kappaTwo` in
`BridgeAKappaTwoFourIdentitiesAssembled`.

* Identity (1) `coeff(X_{3k+1}·X_{3k+2}, mlProj(∂_{rowRight} Q_b)) = 2K`
  — closed kernel-only in the residual-active path and assembled there.
* Identity (2) `coeff(X_{3k+1}·X_{3k+2}, mlProj(∂_{rowLeft}  Q_b)) =  K`
  — closed kernel-only in the residual-active path and assembled there.
* Identity (3) `coeff(X_{3k}·X_{3k+1},   mlProj(∂_{rowRight} Q_b)) =  K`
  — closed kernel-only in the residual-active path and assembled there.
* Identity (4) `coeff(X_{3k}·X_{3k+1},   mlProj(∂_{rowLeft}  Q_b)) = 2K`
  — closed kernel-only in the residual-active path and assembled there.

The older obstruction markers above are compatibility shims, not live
package inputs. -/

/-! ## Axiom audit anchors -/

#print axioms kappaTwoFourIdentities_analytic_closure_holds
#print axioms kappaTwoFourIdentities_touched_list_enumeration_obstruction_holds
#print axioms cookLevinLocalBlockQ_rank_two_le_real_proven
#print axioms cookLevinLocalBlockQ_rank_two_le_real_proven_of_residual_obstruction

end PallLean.Paper93.Paper283
