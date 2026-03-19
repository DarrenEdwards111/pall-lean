/-
  CompiledPoly.lean — Compiled Cook-Levin Polynomial P_{M,n}

  The compiled polynomial is the core object of the paper's separation.
  Given a DTM M and input length n, the Cook-Levin theorem produces
  a CNF formula Φ_{M,n} on N = O(n^c) variables such that:
    M accepts x ⟺ Φ_{M,n}(x, w) is satisfiable

  The polynomial P_{M,n} is the arithmetization of Φ_{M,n}:
  each clause (ℓ₁ ∨ ℓ₂ ∨ ℓ₃) becomes (1 - ℓ̃₁)(1 - ℓ̃₂)(1 - ℓ̃₃)
  where ℓ̃ᵢ = xⱼ or (1 - xⱼ) depending on polarity.
  Then P_{M,n} = ∑ clause polynomials (or ∏, depending on formulation).

  KEY PROPERTY: Block-locality.
  Each clause touches at most 3 variables (width-3 CNF from Cook-Levin).
  This gives the compiled polynomial a block-local structure that the
  profile compression argument (Section 9) exploits.

  The SPDP rank of P_{M,n} is measured at κ = ℓ = Θ(log n) with the
  blocked SPDP matrix from Definition 12.
-/
import PallLean.TuringMachine
import PallLean.SPDPDefs
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace CompiledPoly

open MvPolynomial

/-! ## Cook-Levin Variables

  The computation tableau of a DTM M on input of length n has:
  - T = n^k time steps (for some fixed k depending on M's runtime)
  - S = n^j tape cells
  - At each (time, cell) position: one variable per possible symbol/state

  Total variables N = O(T × S × |Σ|) = O(n^c) for some constant c.
  We abstract this as a flat index space Fin N. -/

/-- The number of compiled variables for a DTM with runtime bound n^k. -/
def compiledVarCount (k : ℕ) (n : ℕ) : ℕ := n ^ (2 * k + 1)

/-- A clause in the Cook-Levin CNF: at most 3 literals on N variables. -/
structure CLClause (N : ℕ) where
  lits : List (Fin N × Bool)  -- (variable index, polarity)
  width_le : lits.length ≤ 3

/-- The Cook-Levin CNF for a DTM on inputs of length n. -/
structure CookLevinCNF (N : ℕ) where
  clauses : List (CLClause N)
  numClauses : ℕ := clauses.length

/-! ## Block-Locality

  The crucial structural property: each clause touches at most 3 variables.
  This induces a natural block partition of the N variables based on which
  clauses reference them. The profile compression argument (Section 9)
  exploits this locality. -/

/-- Variables appearing in a clause. -/
def CLClause.vars {N : ℕ} (c : CLClause N) : Finset (Fin N) :=
  c.lits.toFinset.image Prod.fst

/-- A clause has at most 3 variables. -/
theorem CLClause.vars_card_le {N : ℕ} (c : CLClause N) :
    c.vars.card ≤ 3 := by
  unfold CLClause.vars
  calc Finset.card _ ≤ c.lits.toFinset.card := Finset.card_image_le
    _ ≤ c.lits.length := List.toFinset_card_le c.lits
    _ ≤ 3 := c.width_le

/-! ## Arithmetization

  Each literal ℓ = (xⱼ, true) becomes X j, and (xⱼ, false) becomes (1 - X j).
  Each clause (ℓ₁ ∨ ... ∨ ℓₖ) becomes 1 - ∏(1 - ℓ̃ᵢ),
  which equals 0 on {0,1}^N iff the clause is falsified.

  The compiled polynomial is the product of all clause polynomials:
    P_{M,n} = ∏ clause_poly(cᵢ)
  This equals 1 on {0,1}^N iff all clauses are satisfied. -/

/-- Arithmetize a single literal over F_p. -/
noncomputable def literalPoly {N : ℕ} (p : ℕ) [Fact (Nat.Prime p)]
    (lit : Fin N × Bool) : MvPolynomial (Fin N) (ZMod p) :=
  if lit.2 then X lit.1 else 1 - X lit.1

/-- Arithmetize a clause: 1 - ∏(1 - ℓ̃ᵢ). Equals 1 on {0,1}^N iff clause satisfied. -/
noncomputable def clausePoly {N : ℕ} (p : ℕ) [Fact (Nat.Prime p)]
    (c : CLClause N) : MvPolynomial (Fin N) (ZMod p) :=
  1 - (c.lits.map (fun lit => 1 - literalPoly p lit)).prod

/-- The compiled polynomial: product of all clause polynomials.
    Equals 1 on {0,1}^N iff the full CNF is satisfied. -/
noncomputable def compiledPoly {N : ℕ} (p : ℕ) [Fact (Nat.Prime p)]
    (cnf : CookLevinCNF N) : MvPolynomial (Fin N) (ZMod p) :=
  (cnf.clauses.map (clausePoly p)).prod

/-! ## Block Partition

  The block partition groups variables by their "neighbourhood" in the
  clause-variable incidence graph. Variables that appear in the same
  clause belong to nearby blocks. The width-3 property ensures each
  block involves O(1) variables from each clause.

  For the profile compression argument, the partition satisfies:
  - Each block has bounded size (O(1) from locality)
  - Each clause is "local" to O(1) blocks
  - The partition is determined by the CNF structure, not the function -/

/-- A block partition of Fin N into blocks. -/
structure BlockPartition (N : ℕ) where
  numBlocks : ℕ
  blockOf : Fin N → Fin numBlocks

/-- A clause is local to a partition if all its variables lie in ≤ 3 blocks. -/
def CLClause.isLocal {N : ℕ} (c : CLClause N) (bp : BlockPartition N) : Prop :=
  (c.vars.image bp.blockOf).card ≤ 3

/-- The Cook-Levin CNF has a locality-respecting partition. -/
structure HasLocalPartition {N : ℕ} (cnf : CookLevinCNF N) where
  partition : BlockPartition N
  locality : ∀ c ∈ cnf.clauses, c.isLocal partition
  blockSizeBound : ℕ  -- max variables per block

/-! ## Cook-Levin Theorem (existence of compiled polynomial)

  For any DTM M with polynomial runtime, there exists a Cook-Levin CNF
  on N = O(n^c) variables such that:
  - M accepts x iff Φ(x, w) is satisfiable for some witness w
  - The CNF has width ≤ 3
  - The CNF has a locality-respecting block partition

  We state this as an axiom for now. The full Cook-Levin proof in Lean
  would require substantial TM simulation infrastructure. -/

-- cook_levin axiom removed: not used in P_neq_NP proof chain
-- (Cook-Levin structure is accessed via pside_compiled_collapse and perm_restriction_exists)

/-! ## SPDP on Compiled Polynomials

  The paper's Definition 12 defines the blocked SPDP matrix for a polynomial
  with respect to a block partition. The rank Γ_{κ,ℓ}(P, B) is the rank of
  this matrix, where blocks from the partition constrain which derivative
  sets and shift monomials are "admissible."

  We define this in terms of the existing SPDP infrastructure, extended
  with block-admissibility constraints. -/

/-- Block-admissible derivative set: S touches at most κ blocks. -/
def isBlockAdmissibleDeriv {N : ℕ} (bp : BlockPartition N) (κ : ℕ)
    (S : Finset (Fin N)) : Prop :=
  (S.image bp.blockOf).card ≤ κ

/-- Block-admissible shift monomial: support touches at most ℓ blocks. -/
def isBlockAdmissibleShift {N : ℕ} (bp : BlockPartition N) (ℓ : ℕ)
    (_m : MvPolynomial (Fin N) (ZMod (Nat.succ 1))) -- placeholder field
    (support : Finset (Fin N)) : Prop :=
  (support.image bp.blockOf).card ≤ ℓ

/-- The blocked SPDP rank (Definition 12).
    Generators: m · ∂^S p where:
    - S is a set of κ derivative variables, block-admissible
    - m is a shift monomial of degree ≤ ℓ, block-admissible
    - Entries are coefficients of the product m · ∂^S p -/
noncomputable def blockedSpdpRank {N : ℕ} (p : ℕ) [hp : Fact (Nat.Prime p)]
    (κ ℓ : ℕ) (poly : MvPolynomial (Fin N) (ZMod p))
    (bp : BlockPartition N) : ℕ :=
  Module.finrank (ZMod p) (Submodule.span (ZMod p)
    { q | ∃ (S : List (Fin N)) (m : MvPolynomial (Fin N) (ZMod p)),
        S.length ≤ κ ∧
        m.totalDegree ≤ ℓ ∧
        (S.toFinset.image bp.blockOf).card ≤ κ ∧
        (m.vars.image bp.blockOf).card ≤ ℓ ∧
        q = m * SPDP.iterDerivList S poly })

/-! ## Rational (characteristic 0) variants

  The paper notes (Appendix H.4): "The lower bound is independent of the
  base field F provided char(F) ∤ t!; characteristic 0 suffices for all
  applications in the main text."

  We provide ℚ versions for simplicity. -/

/-- Arithmetize a literal over ℚ. -/
noncomputable def literalPolyQ {N : ℕ}
    (lit : Fin N × Bool) : MvPolynomial (Fin N) ℚ :=
  if lit.2 then X lit.1 else 1 - X lit.1

/-- Arithmetize a clause over ℚ. -/
noncomputable def clausePolyQ {N : ℕ}
    (c : CLClause N) : MvPolynomial (Fin N) ℚ :=
  1 - (c.lits.map (fun lit => 1 - literalPolyQ lit)).prod

/-- Compiled polynomial over ℚ. -/
noncomputable def compiledPolyQ {N : ℕ}
    (cnf : CookLevinCNF N) : MvPolynomial (Fin N) ℚ :=
  (cnf.clauses.map clausePolyQ).prod

/-- Blocked SPDP rank over ℚ. -/
noncomputable def blockedSpdpRankQ {N : ℕ}
    (κ ℓ : ℕ) (poly : MvPolynomial (Fin N) ℚ)
    (bp : BlockPartition N) : ℕ :=
  Module.finrank ℚ (Submodule.span ℚ
    { q | ∃ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
        S.length ≤ κ ∧
        m.totalDegree ≤ ℓ ∧
        (S.toFinset.image bp.blockOf).card ≤ κ ∧
        (m.vars.image bp.blockOf).card ≤ ℓ ∧
        q = m * SPDP.iterDerivList S poly })

end CompiledPoly
