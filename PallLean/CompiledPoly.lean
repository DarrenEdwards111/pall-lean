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

/-- Blocked SPDP rank over ℚ.

    IMPORTANT: Paper Definition 2.3 specifies three conditions we partially
    capture here. The full paper-faithful version requires:

    Paper Definition 2.3 specifies:

    (A) **Multilinear convention**: work mod ⟨x²ᵢ - xᵢ⟩. This means
        coefficient vectors are in the multilinear monomial basis.
        Tautology clauses (x ∨ ¬x) compile to 1 in this basis.
        (Not yet enforced at the polynomial level.)

    (B) **S is block-admissible** (transversal): |S ∩ Bᵢ| ≤ 1 per block.
        Enforced via: image cardinality = toFinset cardinality.

    (C) **m is S-coupled**: every variable in supp(m) lies in a block that
        also contains some element of S. This prevents ambient dimension
        inflation (without it, rank grows as Θ(N^ℓ) for any nonzero poly).
        Enforced via: ∀ v ∈ m.vars, bp.blockOf v ∈ S.toFinset.image bp.blockOf.

    With cell-based partition (poly(n) blocks of O(1) vars each) and
    κ = O(log n), the S-coupling restricts m to O(κ) variables,
    giving the polynomial-rank bound Γ^B ≤ n^O(1).
-/
noncomputable def blockedSpdpRankQ {N : ℕ}
    (κ ℓ : ℕ) (poly : MvPolynomial (Fin N) ℚ)
    (bp : BlockPartition N) : ℕ :=
  Module.finrank ℚ (Submodule.span ℚ
    { q | ∃ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
        S.length ≤ κ ∧
        m.totalDegree ≤ ℓ ∧
        -- S is block-admissible (transversal): distinct blocks
        (S.toFinset.image bp.blockOf).card = S.toFinset.card ∧
        -- m is S-coupled: every variable in m lies in a block touched by S
        -- (Paper Definition 2.3: "each variable in supp(m) lies in a block
        --  that also contains some element of the derivative support")
        (∀ v ∈ m.vars, bp.blockOf v ∈ S.toFinset.image bp.blockOf) ∧
        q = m * SPDP.iterDerivList S poly })

/-- Helper: every SPDP generator m * ∂^S(poly) has total degree bounded by
    ℓ + poly.totalDegree, so the SPDP span lies inside restrictTotalDegree. -/
private theorem spdp_span_le_restrictTotalDegree {N : ℕ}
    (κ ℓ : ℕ) (poly : MvPolynomial (Fin N) ℚ) (bp : BlockPartition N) :
    Submodule.span ℚ
      { q | ∃ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
          S.length ≤ κ ∧
          m.totalDegree ≤ ℓ ∧
          (S.toFinset.image bp.blockOf).card = S.toFinset.card ∧
          (∀ v ∈ m.vars, bp.blockOf v ∈ S.toFinset.image bp.blockOf) ∧
          q = m * SPDP.iterDerivList S poly }
    ≤ MvPolynomial.restrictTotalDegree (Fin N) ℚ (ℓ + poly.totalDegree) := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m, _, hdeg, _, _, hq⟩
  subst hq; rw [SetLike.mem_coe, MvPolynomial.mem_restrictTotalDegree]
  calc (m * SPDP.iterDerivList S poly).totalDegree
      ≤ m.totalDegree + (SPDP.iterDerivList S poly).totalDegree :=
        MvPolynomial.totalDegree_mul m (SPDP.iterDerivList S poly)
    _ ≤ ℓ + poly.totalDegree :=
        Nat.add_le_add hdeg (SPDP.totalDegree_iterDerivList_le S poly)

/-- blockedSpdpRankQ is monotone in both κ and ℓ parameters.
    With the paper-faithful definition (S-coupled shifts), monotonicity
    requires that larger κ admits more transversals, and larger ℓ admits
    more shift monomials. -/
theorem blockedSpdpRankQ_mono_params {N : ℕ}
    (κ₁ ℓ₁ κ₂ ℓ₂ : ℕ) (poly : MvPolynomial (Fin N) ℚ)
    (bp : BlockPartition N) (hκ : κ₁ ≤ κ₂) (hℓ : ℓ₁ ≤ ℓ₂) :
    blockedSpdpRankQ κ₁ ℓ₁ poly bp ≤ blockedSpdpRankQ κ₂ ℓ₂ poly bp := by
  unfold blockedSpdpRankQ
  have h_sub : ({ q | ∃ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
      S.length ≤ κ₁ ∧ m.totalDegree ≤ ℓ₁ ∧
      (S.toFinset.image bp.blockOf).card = S.toFinset.card ∧
      (∀ v ∈ m.vars, bp.blockOf v ∈ S.toFinset.image bp.blockOf) ∧
      q = m * SPDP.iterDerivList S poly } : Set (MvPolynomial (Fin N) ℚ)) ⊆
    { q | ∃ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
      S.length ≤ κ₂ ∧ m.totalDegree ≤ ℓ₂ ∧
      (S.toFinset.image bp.blockOf).card = S.toFinset.card ∧
      (∀ v ∈ m.vars, bp.blockOf v ∈ S.toFinset.image bp.blockOf) ∧
      q = m * SPDP.iterDerivList S poly } := by
    intro q ⟨S, m, hlen, hdeg, hSblk, hmblk, hq⟩
    exact ⟨S, m, le_trans hlen hκ, le_trans hdeg hℓ, hSblk, hmblk, hq⟩
  have hfin : Module.Finite ℚ ↥(Submodule.span ℚ
    { q | ∃ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
      S.length ≤ κ₂ ∧ m.totalDegree ≤ ℓ₂ ∧
      (S.toFinset.image bp.blockOf).card = S.toFinset.card ∧
      (∀ v ∈ m.vars, bp.blockOf v ∈ S.toFinset.image bp.blockOf) ∧
      q = m * SPDP.iterDerivList S poly }) := by
    apply Module.Finite.of_injective
      (Submodule.inclusion (spdp_span_le_restrictTotalDegree κ₂ ℓ₂ poly bp))
      (Submodule.inclusion_injective _)
  exact Submodule.finrank_mono (Submodule.span_mono h_sub)


end CompiledPoly
