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

/-- Compiled polynomial over ℚ (PRODUCT form, not paper-faithful).
    Retained for backward compatibility. The paper uses violationPolyQ instead. -/
noncomputable def compiledPolyQ {N : ℕ}
    (cnf : CookLevinCNF N) : MvPolynomial (Fin N) ℚ :=
  (cnf.clauses.map clausePolyQ).prod

/-! ## Paper-faithful violation polynomial (Section 3.1)

  The paper defines:
    V_{M,n}(x,τ) = Σ_{C ∈ constraints} C(x,τ)²

  Key properties:
  - deg(V) = O(1) (constant, since each C has constant degree)
  - V = 0 on Boolean inputs iff all constraints satisfied
  - V is a SUM of local terms, not a product

  The κ-padded polynomial:
    P_{M,n}(x,τ,y) = (∏_{j=1}^κ y_j) · V_{M,n}(x,τ)

  This has deg = κ + O(1), ensuring the SPDP matrix is non-vacuous.
  Most derivatives hit the padding variables, leaving ≤ deg(V) = O(1)
  derivatives on V itself. This is why the P-side bound works.
-/

/-- Violation polynomial (paper §3.1): V = Σ clausePoly(c)² .
    Has constant degree (≤ 2 * max clause degree).
    V = 0 on Boolean inputs iff all clauses satisfied. -/
noncomputable def violationPolyQ {N : ℕ}
    (cnf : CookLevinCNF N) : MvPolynomial (Fin N) ℚ :=
  (cnf.clauses.map (fun c => (clausePolyQ c) ^ 2)).sum

/-- totalDegree of a list sum is bounded by the max totalDegree. -/
private theorem totalDegree_list_sum_le {σ : Type*} {R : Type*}
    [CommSemiring R] (l : List (MvPolynomial σ R)) (d : ℕ)
    (h : ∀ p ∈ l, p.totalDegree ≤ d) :
    l.sum.totalDegree ≤ d := by
  induction l with
  | nil => simp [MvPolynomial.totalDegree]
  | cons a t ih =>
    rw [List.sum_cons]
    have ha := h a (by simp)
    have ht := ih (fun p hp => h p (by simp [hp]))
    exact le_trans (MvPolynomial.totalDegree_add a t.sum) (max_le ha ht)

/-- Each literal polynomial (X v or 1 - X v) has degree ≤ 1. -/
private theorem literalPolyQ_totalDegree_le {N : ℕ} (lit : Fin N × Bool) :
    (literalPolyQ lit).totalDegree ≤ 1 := by
  unfold literalPolyQ
  split
  · exact le_of_eq (MvPolynomial.totalDegree_X lit.1)
  · calc (1 - MvPolynomial.X lit.1 : MvPolynomial (Fin N) ℚ).totalDegree
        ≤ max (1 : MvPolynomial (Fin N) ℚ).totalDegree (MvPolynomial.X lit.1).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
      _ = max 0 1 := by rw [MvPolynomial.totalDegree_one, @MvPolynomial.totalDegree_X _ ℚ _ _]
      _ = 1 := by norm_num

private theorem one_sub_literalPolyQ_totalDegree_le {N : ℕ} (lit : Fin N × Bool) :
    (1 - literalPolyQ lit : MvPolynomial (Fin N) ℚ).totalDegree ≤ 1 := by
  calc (1 - literalPolyQ lit).totalDegree
      ≤ max (1 : MvPolynomial (Fin N) ℚ).totalDegree (literalPolyQ lit).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
    _ ≤ max 0 1 := max_le_max (le_of_eq MvPolynomial.totalDegree_one) (literalPolyQ_totalDegree_le lit)
    _ = 1 := by norm_num

private theorem clausePolyQ_totalDegree_le {N : ℕ} (c : CLClause N) :
    (clausePolyQ c).totalDegree ≤ 3 := by
  -- clausePolyQ = 1 - ∏(1 - lit), each lit degree ≤ 1, ≤ 3 lits.
  -- deg(1 - prod) ≤ max(0, deg prod) ≤ Σ deg(1-lit) ≤ |lits| ≤ 3.
  -- Proof uses: totalDegree_sub, totalDegree_one, totalDegree_list_prod,
  -- one_sub_literalPolyQ_totalDegree_le, width_le.
  unfold clausePolyQ
  have h1 : (1 : MvPolynomial (Fin N) ℚ).totalDegree = 0 := MvPolynomial.totalDegree_one
  set prod := (c.lits.map (fun lit => 1 - literalPolyQ lit)).prod
  have hsub : (1 - prod).totalDegree ≤ max 0 prod.totalDegree := by
    calc (1 - prod).totalDegree ≤ max (1 : MvPolynomial (Fin N) ℚ).totalDegree prod.totalDegree :=
        MvPolynomial.totalDegree_sub _ _
      _ = max 0 prod.totalDegree := by rw [h1]
  have hprod : prod.totalDegree ≤ 3 := by
    apply le_trans (MvPolynomial.totalDegree_list_prod _)
    apply le_trans _ c.width_le
    -- Need: sum of mapped degrees ≤ c.lits.length
    -- Each factor has degree ≤ 1, and the map preserves length
    have key : ∀ (l : List (MvPolynomial (Fin N) ℚ)),
        (∀ p ∈ l, p.totalDegree ≤ 1) → (l.map MvPolynomial.totalDegree).sum ≤ l.length := by
      intro l hl
      induction l with
      | nil => simp
      | cons a t ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have ha := hl a (by simp)
        have ht := ih (fun p hp => hl p (by simp [hp]))
        omega
    have := key (c.lits.map (fun lit => (1 - literalPolyQ lit : MvPolynomial (Fin N) ℚ)))
      (fun p hp => by
        obtain ⟨lit, _, rfl⟩ := List.mem_map.mp hp
        exact one_sub_literalPolyQ_totalDegree_le lit)
    simp only [List.length_map] at this
    exact this
  omega

theorem violationPolyQ_totalDegree_le {N : ℕ} (cnf : CookLevinCNF N) :
    (violationPolyQ cnf).totalDegree ≤ 6 := by
  unfold violationPolyQ
  apply totalDegree_list_sum_le
  intro p hp
  simp only [List.mem_map] at hp
  obtain ⟨c, _, rfl⟩ := hp
  calc (clausePolyQ c ^ 2).totalDegree
      ≤ 2 * (clausePolyQ c).totalDegree := MvPolynomial.totalDegree_pow _ 2
    _ ≤ 2 * 3 := Nat.mul_le_mul_left 2 (clausePolyQ_totalDegree_le c)
    _ = 6 := by norm_num

/-- Embed a polynomial from Fin N into Fin (N + κ) by mapping variables. -/
noncomputable def embedPoly {N κ : ℕ}
    (p : MvPolynomial (Fin N) ℚ) : MvPolynomial (Fin (N + κ)) ℚ :=
  MvPolynomial.rename (Fin.castAdd κ) p

/-- The κ-padding monomial: ∏_{j=0}^{κ-1} y_j where y_j = X_{N+j}. -/
noncomputable def paddingMonomial (N κ : ℕ) : MvPolynomial (Fin (N + κ)) ℚ :=
  (Finset.univ.val.toList.map (fun j : Fin κ =>
    (X (Fin.natAdd N j) : MvPolynomial (Fin (N + κ)) ℚ))).prod

/-- κ-padded compiled polynomial (paper §3.1):
    P_{M,n} = (∏ y_j) · V_{M,n}
    where y_j are fresh padding variables. -/
noncomputable def paddedPolyQ {N : ℕ} (κ : ℕ)
    (cnf : CookLevinCNF N) : MvPolynomial (Fin (N + κ)) ℚ :=
  paddingMonomial N κ * embedPoly (violationPolyQ cnf)

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
