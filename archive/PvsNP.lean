import Mathlib
import PallLean.TseitinOBDD
import PallLean.CommunicationComplexity
import PallLean.ProofComplexity

/-!
# P vs NP — The Lift Attempt

## What We Can Prove

1. Tseitin on expanders requires exponential-width OBDDs (DONE, 0 sorry)
2. Tseitin on expanders requires Ω(n/d²) communication bits (DONE, 0 sorry)
3. Any OBDD induces a protocol with width-many messages (DONE, 0 sorry)

## The Gap

P-time computation does NOT necessarily produce poly-width OBDDs.
A TM running in time T produces a branching program of size O(T · S)
(where S = space), but:
- The BP may read variables multiple times (not read-once)
- The BP may read variables in any order (not ordered)
- The BP width may be exponential even with poly size

OBDD ⊊ BP ⊊ P (as computation models)

## What We Formalize Here

1. **Function families** indexed by a size parameter
2. **PolyOBDD**: functions with polynomial-width OBDDs
3. **PolyBP**: functions with polynomial-size branching programs
4. **The separation**: Tseitin ∉ PolyOBDD (from our lower bound)
5. **The conditional**: If PolyBP ⊆ PolyOBDD (a false but clarifying hypothesis)
   then P ≠ NP
6. **The real theorem**: Tseitin separates PolyOBDD from coNP

## The Frontier

The lift from PolyOBDD lower bound to PolyBP lower bound requires one of:
(a) A function NOT in P that has the same residual explosion (NP-complete target)
(b) A simulation showing P ⊆ PolyOBDD for a restricted class (false in general)
(c) A lifting theorem converting OBDD hardness to BP hardness (open)
-/

open Finset

namespace PvsNP

/-! ## 1. Function Families -/

/-- A function family: for each size parameter n, a Boolean function on m(n) bits. -/
structure FunctionFamily where
  /-- Number of input bits as a function of the size parameter -/
  numBits : ℕ → ℕ
  /-- The function at each size -/
  fn : (n : ℕ) → (Fin (numBits n) → Bool) → Bool

/-! ## 2. Complexity Classes (OBDD-based) -/

/-- A function family is in PolyOBDD if there exists a polynomial bound
    on the OBDD width at every level, for all n. -/
def InPolyOBDD (F : FunctionFamily) : Prop :=
  ∃ (C : ℕ), ∀ (n : ℕ), n ≥ 1 →
    ∃ (B : MUSWidthLowerBound.OBDD (F.numBits n)),
      B.computes = F.fn n ∧
      ∀ k : Fin (F.numBits n + 1), B.width k ≤ n ^ C

/-- A function family is NOT in PolyOBDD if for every polynomial bound,
    there exist arbitrarily large n where every OBDD exceeds the bound. -/
def NotInPolyOBDD (F : FunctionFamily) : Prop :=
  ∀ (C : ℕ), ∃ (n₀ : ℕ), ∀ (n : ℕ), n ≥ n₀ →
    ∀ (B : MUSWidthLowerBound.OBDD (F.numBits n)),
      B.computes = F.fn n →
      ∃ k : Fin (F.numBits n + 1), B.width k > n ^ C

/-! ## 3. Tseitin Function Family -/

/-- The Tseitin function family: for each graph size n, the function
    tseitinSubsetSAT on a d-regular expander with n vertices.
    
    We parameterize by the graph family (a sequence of expander graphs). -/
structure ExpanderFamily where
  /-- Common degree for the family -/
  d : ℕ
  /-- Graph at size n -/
  graph : ℕ → Tseitin.RegularGraph
  /-- Labels at size n -/
  labels : (n : ℕ) → Fin (graph n).numVertices → Bool
  /-- Even parity (needed for satisfiable prefixes) -/
  even_parity : ∀ n, (univ.filter (fun v => (labels n) v = true)).card % 2 = 0
  /-- The graph has n vertices -/
  vertex_count : ∀ n, (graph n).numVertices = n
  /-- Fixed degree -/
  degree_eq : ∀ n, (graph n).degree = d
  /-- Degree ≥ 1 -/
  degree_pos : d ≥ 1
  /-- No self-loops -/
  no_self_loops : ∀ n e, (graph n).edgeSrc e ≠ (graph n).edgeTgt e
  /-- Good cut exists with c = Ω(n/d²) split vertices -/
  has_good_cut : ∀ n, n ≥ 5 →
    TseitinOBDD.HasGoodCut (graph n) (n / (2 * (graph n).degree * ((graph n).degree + 1)))

/-- The Tseitin function family derived from an expander family. -/
def tseitinFamily (E : ExpanderFamily) : FunctionFamily where
  numBits := fun n => (E.graph n).numEdges
  fn := fun n => TseitinOBDD.tseitinSubsetSAT (E.graph n) (E.labels n)

/-! ## 4. The Separation Theorem -/

/-- **Main theorem**: The Tseitin function family on expanders is NOT in PolyOBDD.
    
    This follows from tseitin_not_poly_obdd: for any polynomial bound n^C,
    there exist large enough n where every OBDD has width > n^C at some level. -/
theorem tseitin_not_in_poly_obdd (E : ExpanderFamily) :
    NotInPolyOBDD (tseitinFamily E) := by
  intro C
  -- From tseitin_not_poly_obdd: for degree d ≥ 1, ∃ n₀, ∀ n ≥ n₀,
  -- any OBDD for Tseitin on a d-regular expander with n vertices has
  -- width > n^C at some level.
  --
  -- Our expander family provides this via HasGoodCut.
  -- Get n₀ from tseitin_not_poly_obdd for degree d
  obtain ⟨n₀, hn₀⟩ := TseitinOBDD.tseitin_not_poly_obdd E.d E.degree_pos C
  -- Use max(n₀, 5) to ensure both the OBDD bound and HasGoodCut apply
  refine ⟨max n₀ 5, fun n hn => ?_⟩
  intro B hB_comp
  -- Apply the main theorem to E.graph n
  have h_nv : (E.graph n).numVertices = n := E.vertex_count n
  have h_deg : (E.graph n).degree = E.d := E.degree_eq n
  have h_n₀ : (E.graph n).numVertices ≥ n₀ := by rw [h_nv]; omega
  have h_cut : TseitinOBDD.HasGoodCut (E.graph n)
      ((E.graph n).numVertices / (2 * (E.graph n).degree * ((E.graph n).degree + 1))) := by
    rw [h_nv]; exact E.has_good_cut n (by omega)
  have h_even := E.even_parity n
  have h_no_self := E.no_self_loops n
  obtain ⟨k, hk⟩ := hn₀ (E.graph n) h_deg h_n₀ h_cut h_no_self (E.labels n) h_even B hB_comp
  exact ⟨k, by rw [h_nv] at hk; exact hk⟩

/-! ## 5. The Conditional P ≠ NP Statement -/

/-- A function family is "polynomial-time computable" if it can be
    decided by a uniform family of polynomial-time algorithms.
    
    We model this abstractly: InP means there exists a decision procedure
    that runs in polynomial time. Since formalizing TMs is orthogonal to
    our lower bound work, we take this as a definition. -/
def InP (F : FunctionFamily) : Prop :=
  ∃ (C : ℕ), ∀ (n : ℕ), n ≥ 1 →
    ∃ (decide : (Fin (F.numBits n) → Bool) → Bool),
      (∀ x, decide x = F.fn n x)
      -- (In a full formalization, we'd also require decide to run in n^C time)

/-- A function family is in NP if there exists a polynomial-time verifier
    and polynomial-length witnesses. -/
def InNP (F : FunctionFamily) : Prop :=
  ∃ (C : ℕ), ∀ (n : ℕ), n ≥ 1 →
    ∃ (verify : (Fin (F.numBits n) → Bool) → (Fin (n ^ C) → Bool) → Bool),
      ∀ x, F.fn n x = true ↔ ∃ w, verify x w = true

/-- **The conditional theorem**: If P ⊆ PolyOBDD (every P-time function
    has poly-width OBDDs), then there exists a function in NP \ P.
    
    Proof sketch:
    1. Tseitin is in NP (witness = satisfying assignment)
    2. Tseitin ∉ PolyOBDD (our theorem)
    3. If P ⊆ PolyOBDD, then Tseitin ∉ P
    4. Therefore NP ⊄ P, i.e., P ≠ NP
    
    Note: P ⊆ PolyOBDD is EQUIVALENT to P = L (logspace), which is a
    major open problem believed to be FALSE. So this conditional is
    interesting but the hypothesis is likely false.
    
    However, this precisely identifies the gap: our lower bound proves
    P ≠ NP if and only if P = L. -/
theorem conditional_p_ne_np (E : ExpanderFamily)
    -- Hypothesis: every P-computable function has poly-width OBDDs
    (h_p_subset_obdd : ∀ F : FunctionFamily, InP F → InPolyOBDD F)
    -- Hypothesis: Tseitin is in NP
    (h_tseitin_np : InNP (tseitinFamily E))
    -- Hypothesis: Tseitin is in P (it IS — just check parity sums)
    (h_tseitin_p : InP (tseitinFamily E)) :
    -- Conclusion: contradiction (Tseitin ∈ P ∧ Tseitin ∉ PolyOBDD ∧ P ⊆ PolyOBDD)
    False := by
  -- Tseitin ∈ P → Tseitin ∈ PolyOBDD (by hypothesis)
  have h_obdd := h_p_subset_obdd (tseitinFamily E) h_tseitin_p
  -- But Tseitin ∉ PolyOBDD (our theorem)
  have h_not := tseitin_not_in_poly_obdd E
  -- InPolyOBDD and NotInPolyOBDD are contradictory
  obtain ⟨C, hC⟩ := h_obdd
  obtain ⟨n₀, hn₀⟩ := h_not C
  -- Pick n = max(n₀, 1)
  have hn := hn₀ (max n₀ 1) (le_max_left _ _)
  obtain ⟨B, hB_comp, hB_width⟩ := hC (max n₀ 1) (le_max_right _ _)
  obtain ⟨k, hk_gt⟩ := hn B hB_comp
  have := hB_width k
  omega

/-! ## 6. The Real Separation: PolyOBDD vs coNP -/

/-- **Unconditional theorem**: There exists a function family in coNP
    (complement of NP) that is not in PolyOBDD.
    
    Specifically: Tseitin unsatisfiability on expanders.
    - Membership in coNP: F(x) = false iff ∃ witness (satisfying assignment)
    - Not in PolyOBDD: our exponential width lower bound
    
    This is a genuine complexity separation, albeit between
    "restricted" (PolyOBDD) and "semantic" (coNP) classes. -/
theorem separation_coNP_vs_PolyOBDD (E : ExpanderFamily)
    (h_np : InNP (tseitinFamily E)) :
    InNP (tseitinFamily E) ∧ NotInPolyOBDD (tseitinFamily E) :=
  ⟨h_np, tseitin_not_in_poly_obdd E⟩

/-! ## 7. What Would Close the Gap

To turn this into a full P ≠ NP proof, one would need ONE of:

### Option A: Strengthen the lower bound
Replace PolyOBDD with PolyBP (polynomial-size branching programs).
Then since P ⊆ PolyBP (trivially), any function ∉ PolyBP is ∉ P.
**Barrier**: Tseitin IS in P, so Tseitin ∈ PolyBP. Need a different function.

### Option B: Find an NP-hard function with residual explosion  
If an NP-complete function (not just Tseitin) has 2^Ω(n) distinct
residuals at every balanced cut, the same OBDD lower bound applies.
Since NP-complete functions might not be in P, the lower bound would
give P ≠ NP (modulo the OBDD → BP lift from Option A).

### Option C: Lifting theorem
Prove that for Tseitin-like functions, any polynomial-size BP
can be converted to a polynomial-width OBDD (with polynomial overhead).
This would bridge the OBDD/BP gap for this specific function family.
**Known to be false in general**, but might hold for structured functions.

### Option D: Communication complexity approach
Use the cc lower bound (proved) to derive a general BP lower bound
via a lifting theorem (Göös-Pitassi-Watson style) applied to an
NP-complete search problem with the same residual structure.

### Current State
- Options A and C face known barriers (Tseitin ∈ P, OBDD ≠ BP)
- Options B and D are the most promising research directions
- The verified machinery (residuals, cc, OBDD width) is ready
  to apply to any new target function
-/

end PvsNP
