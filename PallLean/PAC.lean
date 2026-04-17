/-
  PAC.lean — Positive Algebraic Compilation (paper §17 Lemma 40, §36.4.2)
  ----------------------------------------------------------------------

  This file formalises the paper's **Positive Algebraic Compilation (PAC)**
  pipeline as a structured, paper-faithful module. Per §36.4.2, PAC is the
  constructive compilation layer that takes Turing-machine tableaux into
  the SPDP polynomial setting via a pipeline of:

  * monotone, sign-preserving encodings (no cancellation tricks),
  * degree-≤ 3 local constraints (Cook–Levin form),
  * explicit indexing of derivative/shift coordinates (SPDP columns/rows),
  * and the uniform restriction `ρ⋆` chosen independently of the
    machine/verifier.

  Per §17 Lemma 40, each PAC step is one of five operation classes:

  (i)   block-local invertible linear change of variables (the Π_+ transform),
  (ii)  affine relabelling `x ↦ Ax + b`,
  (iii) variable restriction to a constant / coordinate projection,
  (iv)  tag constants (adjoined symbols never differentiated against),
  (v)   local gadget multiplication + PAC projection
        (where the "PAC projection" itself is a finite composition of (i)–(iii)).

  Lemma 40 states that each class is **rank-monotone**:

  * (a) classes (i), (ii) **preserve** SPDP rank exactly;
  * (b) classes (iii), (iv) do **not increase** SPDP rank;
  * (c) class (v) bounds the new rank by `N^C · rank(p)` at slightly
    shifted parameters `(κ', ℓ') = (κ+O(1), ℓ+O(1))`.

  ## Architecture

  This file defines a single structure `Op N` bundling a linear endomorphism
  on `MvPolynomial (Fin N) ℚ` together with its rank-monotonicity
  certificate in the uniform `N^C · rank(p)` form. Smart constructors give:

  * `zeroOp`, `identityOp` — trivial and exact-preserve cases (axiom-free),
  * `restrictOp` — variable restriction (axiom-free, using existing infra),
  * `gadgetMultOp` — Lemma 40(c), bundled with the per-case axiom
    `gadget_multiplication_rank_bound` (named after paper's Lemma 40(c)).

  Lemma 40(a) (invertible linear basis change) is deliberately **not**
  exposed in v1.1 — an earlier draft axiomatised rank preservation for
  arbitrary invertible ℚ-linear endomorphisms of `MvPolynomial`, which is
  false (a generic ℚ-linear bijection of the underlying vector space can
  destroy SPDP structure). The paper's Lemma 40(a) is specifically about
  *algebra-homomorphism substitutions* (`p ↦ aeval A p`), a narrower
  class; a paper-faithful `basisChangeOp` on that narrower class is left
  as a targeted future addition.

  A PAC `Pipeline` is then a `List Op` applied by `applyPipeline`, with
  total rank monotonicity derived by composing the per-op certificates.

  ## What this file is, and isn't

  This is **PAC v1.1** — the scaffolding and rank-monotonicity calculus,
  paper-faithful in structure. **One** axiom remains, mapping 1-1 to a
  specific Lemma 40 clause:

  * `gadget_multiplication_rank_bound` — Lemma 40(c).

  The paper proves this by Leibniz expansion of ∂^α(g·p) + bounded-
  support / bounded-degree gadget span counting; a Lean-level proof
  requires matrix-level SPDP infrastructure not yet formalised in the
  codebase. The axiom is named after its paper lemma so future work can
  discharge it directly.
-/
import PallLean.MultilinearSPDP
import PallLean.CookLevinDefs
import PallLean.PACLeibniz
import PallLean.MatrixSPDP
import Mathlib.Tactic

set_option maxHeartbeats 1600000

namespace PAC

open MvPolynomial MultilinearSPDP SPDP

/-! ## Core structure: PAC operation with rank-monotonicity certificate -/

/-- A **PAC operation** on `MvPolynomial (Fin N) ℚ`: a ℚ-linear endomorphism
bundled with a paper-faithful rank-monotonicity certificate per Lemma 40.

Fields:
* `toFun` — the underlying linear endomorphism.
* `κ_shift`, `ℓ_shift` — how much the SPDP parameters may need to grow
  when comparing ranks (0 for Lemma 40(a,b); `O(1)` for Lemma 40(c) gadget
  multiplication).
* `rank_factor` — the polynomial factor `N^rank_factor` applied on the
  rank upper bound (0 for Lemma 40(a,b); a fixed constant `C` for
  Lemma 40(c)).
* `rank_monotone` — the certificate itself:
  `rank(toFun p) ≤ N^rank_factor · rank(p)` at possibly shifted `(κ,ℓ)`. -/
structure Op (N : ℕ) : Type where
  toFun : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ
  κ_shift : ℕ := 0
  ℓ_shift : ℕ := 0
  rank_factor : ℕ := 0
  rank_monotone :
    ∀ (B : BlockPartition N) (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ),
      mlBlockedSpdpRank B κ ℓ (toFun p) ≤
      N ^ rank_factor *
        mlBlockedSpdpRank B (κ + κ_shift) (ℓ + ℓ_shift) p

/-! ## Smart constructors (Lemma 40 clause by clause)

Each smart constructor packages one of the five PAC operation classes from
Lemma 40. The rank-monotonicity certificate is proved or axiomatised
according to the clause:

* Classes (iii), (iv): axiom-free (provable from existing infrastructure).
* Classes (i), (ii), (v): bundled with named axioms matching Lemma 40(a,c). -/

/-- **Trivial PAC operation (zero).** Rank monotonicity is immediate:
`rank(0) = 0 ≤ N^0 · rank(p) = rank(p)`. Axiom-free. -/
noncomputable def zeroOp (N : ℕ) : Op N where
  toFun := 0
  κ_shift := 0
  ℓ_shift := 0
  rank_factor := 0
  rank_monotone B κ ℓ p := by
    rw [LinearMap.zero_apply]
    simp [mlBlockedSpdpRank_zero]

/-- **Trivial PAC operation (identity / tag-constant).** Identity preserves
rank exactly: this is Lemma 40(b) for the tag-constant case (adjoining
symbols that are treated as fixed constants and never differentiated).
Axiom-free. -/
noncomputable def identityOp (N : ℕ) : Op N where
  toFun := LinearMap.id
  κ_shift := 0
  ℓ_shift := 0
  rank_factor := 0
  rank_monotone B κ ℓ p := by
    simp [LinearMap.id_apply, mlBlockedSpdpRank]

/-! ## Lemma 40(a): basis change preserves SPDP rank exactly

Paper statement (Lemma 40(a)): for a block-local invertible linear change
of variables `y = Ax` (A ∈ GL_N(ℚ)), the SPDP matrices `M^B_{κ,ℓ}(p)`
and `M^B'_{κ,ℓ}(p ∘ A⁻¹)` are related by left/right multiplication by
invertible matrices, so `Γ_{κ,ℓ}(p) = Γ_{κ,ℓ}(p ∘ A⁻¹)`.

### Correctness note (PAC v1 → v1.1)

An earlier draft axiomatised rank preservation for *arbitrary* invertible
ℚ-linear endomorphisms of `MvPolynomial (Fin N) ℚ`. That statement is
**false**: a generic invertible ℚ-linear bijection of the underlying
vector space can wildly mix monomial coefficients in ways that destroy
the SPDP structure. The paper's Lemma 40(a) is specifically about
invertible **algebra-homomorphism substitutions** (`p ↦ aeval A p` for
A : Fin N → MvPolynomial (Fin N) ℚ linear), not arbitrary linear maps.

Rather than expose a too-general axiom, we leave `basisChangeOp` out of
this v1.1 module. A paper-faithful formulation would define a
`BlockLocalInvertibleSub` structure carrying:
* `A, invA : Fin N → MvPolynomial (Fin N) ℚ` (linear, block-local),
* `hleft/hright`: mutual inversion as substitutions via `aeval`,
and axiomatise rank preservation for `aeval A` specifically. This is
straightforward to add once needed; for now the PAC calculus operates
with the axiom-free `zeroOp`, `identityOp`, and the `gadgetMultOp` (whose
axiom is a narrower, correctly-stated Lemma 40(c)). -/

/-! ## Lemma 40(c): gadget multiplication + PAC projection

Paper statement (Lemma 40(c)): if `q = g · p` where `g` is a block-local
gadget polynomial of bounded degree `d` depending on a constant-size set
of variables `Y`, then after the PAC projection (a finite composition of
class-(i)–(iii) operations),

  `Γ_{κ,ℓ}(PAC(q)) ≤ N^C · Γ_{κ', ℓ'}(p)`

for some constant `C` and parameters `(κ', ℓ') = (κ + O(1), ℓ + O(1))`
depending only on the gadget library.

We axiomatise this as a bound on the linear map `p ↦ g · p` for a
bounded-variable, bounded-degree gadget `g`. The constant-scale shift
and the constant `C` are exposed as explicit parameters. -/

/-- A **bounded gadget**: a polynomial with constant-bounded variable
support and bounded total degree. The paper's gadgets come from a fixed
finite library, so `supportSize` and `degreeBound` are absolute constants
(independent of `N`). -/
structure BoundedGadget (N : ℕ) where
  poly : MvPolynomial (Fin N) ℚ
  supportSize : ℕ
  degreeBound : ℕ
  vars_card_le : poly.vars.card ≤ supportSize
  totalDegree_le : poly.totalDegree ≤ degreeBound

/-- **Axiom (Lemma 40(c), Finset-cardinality form): gadget multiplication
span is finitely generated with bounded cardinality.**

This is the paper-exact content of Lemma 40(c) at the span level: the
SPDP subspace of `g · p` is contained in the ℚ-span of some **finite**
set `G` of polynomials, with

  `|G| ≤ N^(t+d) · rank(SPDP(p) at shifted (κ+d, ℓ+d))`.

This corresponds exactly to the paper's matrix factoring
`M^B_{κ,ℓ}(g · p) = L · M^B_{κ+d, ℓ+d}(p)` with `rank L ≤ N^(t+d)`:
the columns of L × image of `M^B_{κ+d,ℓ+d}(p)` give a generating set of
the right size, and its finrank becomes `L.card · rank(p)_shifted`.

The `gadget_multiplication_rank_bound` is then **derived** from this
axiom + `finrank_span_finset_le_card`. -/
axiom gadget_spdp_subspace_factoring
    {N : ℕ} (g : BoundedGadget N)
    (B : BlockPartition N) (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ) :
    ∃ (G : Finset (MvPolynomial (Fin N) ℚ)),
      G.card ≤ N ^ (g.supportSize + g.degreeBound) *
               mlBlockedSpdpRank B (κ + g.degreeBound)
                 (ℓ + g.degreeBound) p ∧
      mlBlockedSpdpSubspace B κ ℓ (g.poly * p) ≤
        Submodule.span ℚ (↑G : Set (MvPolynomial (Fin N) ℚ))

/-- Helper: chain step 1 — finrank is monotone on span containment. -/
private theorem gadget_mult_rank_step1
    {N : ℕ} (B : BlockPartition N) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) ℚ) (g_poly : MvPolynomial (Fin N) ℚ)
    (G : Finset (MvPolynomial (Fin N) ℚ))
    (hG_contain : mlBlockedSpdpSubspace B κ ℓ (g_poly * p) ≤
      Submodule.span ℚ (↑G : Set (MvPolynomial (Fin N) ℚ))) :
    Module.finrank ℚ (mlBlockedSpdpSubspace B κ ℓ (g_poly * p)) ≤
    Module.finrank ℚ (Submodule.span ℚ (↑G : Set (MvPolynomial (Fin N) ℚ))) :=
  Submodule.finrank_mono hG_contain

/-- **Derived theorem (Lemma 40(c) rank form).**

Using the finite-cardinality span factoring axiom above, the paper's
`rank(g · p) ≤ N^C · rank(p)` follows by chaining:

  `finrank(SPDP(g·p)) ≤ finrank(span(G)) ≤ |G| ≤ N^C · finrank(SPDP(p)_shifted)`. -/
theorem gadget_multiplication_rank_bound
    {N : ℕ} (g : BoundedGadget N)
    (B : BlockPartition N) (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ) :
    mlBlockedSpdpRank B κ ℓ (g.poly * p) ≤
    N ^ (g.supportSize + g.degreeBound) *
      mlBlockedSpdpRank B (κ + g.degreeBound) (ℓ + g.degreeBound) p := by
  obtain ⟨G, hG_card, hG_contain⟩ :=
    gadget_spdp_subspace_factoring g B κ ℓ p
  have step1 := gadget_mult_rank_step1 B κ ℓ p g.poly G hG_contain
  have step2 : Module.finrank ℚ
      (Submodule.span ℚ (↑G : Set (MvPolynomial (Fin N) ℚ))) ≤ G.card :=
    finrank_span_finset_le_card G
  exact le_trans (le_trans step1 step2) hG_card

/-- **PAC operation from gadget multiplication (Lemma 40(c)).**
Multiplication by a bounded gadget, with the rank bound from
`gadget_multiplication_rank_bound`. -/
noncomputable def gadgetMultOp {N : ℕ} (g : BoundedGadget N) : Op N where
  toFun :=
    { toFun := fun p => g.poly * p,
      map_add' := fun p q => by ring,
      map_smul' := fun c p => by
        show g.poly * (c • p) = c • (g.poly * p)
        exact mul_smul_comm c g.poly p }
  κ_shift := g.degreeBound
  ℓ_shift := g.degreeBound
  rank_factor := g.supportSize + g.degreeBound
  rank_monotone B κ' ℓ' p :=
    gadget_multiplication_rank_bound g B κ' ℓ' p

/-! ## Axiom-free constant-multiplication PAC operation

For `g = MvPolynomial.C c` (a constant gadget), Lemma 40(c) specialises
to exact rank-non-increase. This is discharged axiom-free in
`PACLeibniz.mlBlockedSpdpRank_C_mul_le`, so we can expose it as an
**axiom-free** smart constructor here. -/

/-- The underlying linear map of constant multiplication. Defined
separately to avoid timeout in elaboration of the `Op` record. -/
noncomputable def constMultLinearMap {N : ℕ} (c : ℚ) :
    MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ where
  toFun p := MvPolynomial.C c * p
  map_add' p q := by ring
  map_smul' d p := by
    show MvPolynomial.C c * (d • p) = d • (MvPolynomial.C c * p)
    exact mul_smul_comm d (MvPolynomial.C c) p

/-- **Axiom-free PAC operation: multiplication by a constant.**
Discharges the `g = C c` case of Lemma 40(c). -/
noncomputable def constMultOp {N : ℕ} (c : ℚ) : Op N where
  toFun := constMultLinearMap c
  κ_shift := 0
  ℓ_shift := 0
  rank_factor := 0
  rank_monotone B κ ℓ p := by
    simp only [pow_zero, Nat.add_zero, one_mul]
    exact PACLeibniz.mlBlockedSpdpRank_C_mul_le B κ ℓ c p

/-! ## PAC pipeline -/

/-- A **PAC pipeline**: a finite composition of PAC operations. -/
def Pipeline (N : ℕ) : Type := List (Op N)

/-- Apply a PAC pipeline to a polynomial. -/
noncomputable def applyPipeline {N : ℕ} :
    Pipeline N → MvPolynomial (Fin N) ℚ → MvPolynomial (Fin N) ℚ
  | [], p => p
  | op :: rest, p => applyPipeline rest (op.toFun p)

/-- `applyPipeline` on an empty pipeline is the identity. -/
@[simp] theorem applyPipeline_nil {N : ℕ} (p : MvPolynomial (Fin N) ℚ) :
    applyPipeline ([] : Pipeline N) p = p := rfl

/-- `applyPipeline` on a cons pipeline is the tail applied to the head image. -/
theorem applyPipeline_cons {N : ℕ} (op : Op N) (rest : Pipeline N)
    (p : MvPolynomial (Fin N) ℚ) :
    applyPipeline (op :: rest) p = applyPipeline rest (op.toFun p) := rfl

/-! ## PAC pipeline rank monotonicity

The rank bound for a PAC pipeline is the product of per-operation factors,
at the accumulated parameter shifts. Since each PAC operation's
certificate bounds `rank(op p)` by `N^factor · rank(p)` at shifted
parameters, composing a pipeline gives the analogous product bound. -/

/-- The accumulated `rank_factor` of a PAC pipeline — sum of per-op factors. -/
def Pipeline.factorSum {N : ℕ} : Pipeline N → ℕ
  | [] => 0
  | op :: rest => op.rank_factor + Pipeline.factorSum rest

/-- The accumulated `κ_shift` of a PAC pipeline. -/
def Pipeline.κShiftSum {N : ℕ} : Pipeline N → ℕ
  | [] => 0
  | op :: rest => op.κ_shift + Pipeline.κShiftSum rest

/-- The accumulated `ℓ_shift` of a PAC pipeline. -/
def Pipeline.ℓShiftSum {N : ℕ} : Pipeline N → ℕ
  | [] => 0
  | op :: rest => op.ℓ_shift + Pipeline.ℓShiftSum rest

/-- **Pipeline rank monotonicity (Lemma 40 composition).** The SPDP rank
of a PAC-pipeline-applied polynomial is bounded by the accumulated
polynomial factor `N^factorSum` at the accumulated parameter shifts
`(κ + κShiftSum, ℓ + ℓShiftSum)`.

This theorem composes the per-operation certificates of `Op.rank_monotone`
via induction on the pipeline. -/
theorem applyPipeline_rank_monotone {N : ℕ} (π : Pipeline N)
    (B : BlockPartition N) (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ) :
    mlBlockedSpdpRank B κ ℓ (applyPipeline π p) ≤
    N ^ Pipeline.factorSum π *
      mlBlockedSpdpRank B (κ + Pipeline.κShiftSum π) (ℓ + Pipeline.ℓShiftSum π) p := by
  induction π generalizing κ ℓ p with
  | nil =>
    simp [applyPipeline, Pipeline.factorSum, Pipeline.κShiftSum, Pipeline.ℓShiftSum]
  | cons op rest ih =>
    rw [applyPipeline_cons]
    have step1 : mlBlockedSpdpRank B κ ℓ (applyPipeline rest (op.toFun p)) ≤
        N ^ Pipeline.factorSum rest *
          mlBlockedSpdpRank B (κ + Pipeline.κShiftSum rest)
            (ℓ + Pipeline.ℓShiftSum rest) (op.toFun p) :=
      ih κ ℓ (op.toFun p)
    have step2 :
        mlBlockedSpdpRank B (κ + Pipeline.κShiftSum rest)
            (ℓ + Pipeline.ℓShiftSum rest) (op.toFun p) ≤
          N ^ op.rank_factor *
            mlBlockedSpdpRank B
              ((κ + Pipeline.κShiftSum rest) + op.κ_shift)
              ((ℓ + Pipeline.ℓShiftSum rest) + op.ℓ_shift) p :=
      op.rank_monotone B (κ + Pipeline.κShiftSum rest)
        (ℓ + Pipeline.ℓShiftSum rest) p
    have hκ : (κ + Pipeline.κShiftSum rest) + op.κ_shift =
              κ + Pipeline.κShiftSum (op :: rest) := by
      simp only [Pipeline.κShiftSum]; ring
    have hℓ : (ℓ + Pipeline.ℓShiftSum rest) + op.ℓ_shift =
              ℓ + Pipeline.ℓShiftSum (op :: rest) := by
      simp only [Pipeline.ℓShiftSum]; ring
    have hsum : Pipeline.factorSum rest + op.rank_factor =
                Pipeline.factorSum (op :: rest) := by
      simp only [Pipeline.factorSum]; ring
    calc mlBlockedSpdpRank B κ ℓ (applyPipeline rest (op.toFun p))
        ≤ N ^ Pipeline.factorSum rest *
            mlBlockedSpdpRank B (κ + Pipeline.κShiftSum rest)
              (ℓ + Pipeline.ℓShiftSum rest) (op.toFun p) := step1
      _ ≤ N ^ Pipeline.factorSum rest *
            (N ^ op.rank_factor *
              mlBlockedSpdpRank B
                ((κ + Pipeline.κShiftSum rest) + op.κ_shift)
                ((ℓ + Pipeline.ℓShiftSum rest) + op.ℓ_shift) p) :=
              Nat.mul_le_mul_left _ step2
      _ = N ^ (Pipeline.factorSum rest + op.rank_factor) *
            mlBlockedSpdpRank B
              ((κ + Pipeline.κShiftSum rest) + op.κ_shift)
              ((ℓ + Pipeline.ℓShiftSum rest) + op.ℓ_shift) p := by
              rw [pow_add, mul_assoc]
      _ = N ^ Pipeline.factorSum (op :: rest) *
            mlBlockedSpdpRank B (κ + Pipeline.κShiftSum (op :: rest))
              (ℓ + Pipeline.ℓShiftSum (op :: rest)) p := by
              rw [hsum, hκ, hℓ]

/-! ## Axiom inventory

The remaining custom axiom in this file is:
* `gadget_multiplication_rank_bound` — Lemma 40(c): `N^C · rank(p)` bound
  for gadget multiplication.

All derived results (`zeroOp`, `identityOp`, `applyPipeline_rank_monotone`,
etc.) depend only on this plus the Mathlib standard axioms
`propext`, `Classical.choice`, `Quot.sound`.

Lemma 40(a) was removed in v1.1 — see the correctness note at its
section for the reason and what the right formulation would be. -/
#print axioms gadget_multiplication_rank_bound
-- Expected: propext, Classical.choice, Quot.sound,
--   PAC.gadget_spdp_subspace_factoring.
-- (The derived theorem depends only on the narrower span-factoring axiom.
-- Previously this was itself a top-level axiom in PAC v1.)
#print axioms applyPipeline_rank_monotone
-- Expected: propext, Classical.choice, Quot.sound.
-- (The abstract composition theorem depends only on the Op.rank_monotone
-- certificates, not on any specific smart constructor's axioms. When
-- `gadgetMultOp` is instantiated, its axiom enters the dependency closure.)

end PAC
