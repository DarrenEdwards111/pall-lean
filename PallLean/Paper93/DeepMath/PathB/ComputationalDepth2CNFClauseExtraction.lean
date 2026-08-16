import PallLean.Paper93.DeepMath.PathB.ComputationalDepth2CNFMatchingTransport

/-!
# Extracting endpoints and signs from proper binary clauses

A proper binary clause has exactly two literals on exactly two distinct variables.  Its finite literal set therefore
has canonical `Fin 2` coordinates.  Reading the variable and Boolean target from those two coordinates produces the
signed-pair representation used by the large-matching branch semantics.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoCNFClauseExtraction

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.XorCNFIdentityEmbedding
open PallLean.Paper93.DeepMath.PathB.TwoCNFFinalDispatcher

variable {n : ℕ}

/-- A nondegenerate binary clause: two literals using two distinct variables. -/
structure ProperBinaryClause (n : ℕ) where
  clause : Finset (Literal n)
  literalCard : clause.card = 2
  supportCard : (clauseSupport clause).card = 2

/-- Canonical ordering of the two literals. -/
noncomputable def orderedLiteral (C : ProperBinaryClause n) (side : Fin 2) : Literal n :=
  ((C.clause.equivFinOfCardEq C.literalCard).symm side).1

theorem orderedLiteral_mem (C : ProperBinaryClause n) (side : Fin 2) :
    orderedLiteral C side ∈ C.clause :=
  ((C.clause.equivFinOfCardEq C.literalCard).symm side).2

noncomputable def endpoint (C : ProperBinaryClause n) (side : Fin 2) : Fin n := (orderedLiteral C side).1

noncomputable def sign (C : ProperBinaryClause n) (side : Fin 2) : Bool := (orderedLiteral C side).2

/-- Every literal is one of the two extracted ordered literals. -/
theorem literal_eq_ordered_zero_or_one (C : ProperBinaryClause n)
    {l : Literal n} (hl : l ∈ C.clause) :
    l = orderedLiteral C 0 ∨ l = orderedLiteral C 1 := by
  let q : C.clause := ⟨l, hl⟩
  let side : Fin 2 := C.clause.equivFinOfCardEq C.literalCard q
  have hrecover : orderedLiteral C side = l := by
    exact congrArg Subtype.val ((C.clause.equivFinOfCardEq C.literalCard).symm_apply_apply q)
  have hside : side = 0 ∨ side = 1 := by
    have hle : side.val ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hside with hs | hs
  · left
    rw [← hs]
    exact hrecover.symm
  · right
    rw [← hs]
    exact hrecover.symm

/-- The clause support is precisely the extracted endpoint pair. -/
theorem clauseSupport_eq_endpoints (C : ProperBinaryClause n) :
    clauseSupport C.clause = {endpoint C 0, endpoint C 1} := by
  ext v
  constructor
  · intro hv
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hv
    rcases literal_eq_ordered_zero_or_one C hl with h | h
    · simp [endpoint, h]
    · simp [endpoint, h]
  · intro hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_image.mpr ⟨orderedLiteral C 0, orderedLiteral_mem C 0, rfl⟩
    · exact Finset.mem_image.mpr ⟨orderedLiteral C 1, orderedLiteral_mem C 1, rfl⟩

/-- Properness guarantees the two extracted endpoints are distinct. -/
theorem endpoint_ne (C : ProperBinaryClause n) : endpoint C 0 ≠ endpoint C 1 := by
  intro heq
  have hcard := C.supportCard
  rw [clauseSupport_eq_endpoints C, heq] at hcard
  simp at hcard

/-- Extracted signs as the pair expected by the matching semantics. -/
noncomputable def signPair (C : ProperBinaryClause n) : Bool × Bool := (sign C 0, sign C 1)

/-- **Clause extraction correctness (proved).** -/
theorem evalClause_iff_extracted (C : ProperBinaryClause n) (x : Fin n → Bool) :
    evalClause x C.clause ↔
      x (endpoint C 0) = sign C 0 ∨ x (endpoint C 1) = sign C 1 := by
  constructor
  · rintro ⟨l, hl, hval⟩
    rcases literal_eq_ordered_zero_or_one C hl with h | h
    · left
      simpa [endpoint, sign, h] using hval
    · right
      simpa [endpoint, sign, h] using hval
  · intro h
    rcases h with h | h
    · exact ⟨orderedLiteral C 0, orderedLiteral_mem C 0, by simpa [evalLiteral, endpoint, sign] using h⟩
    · exact ⟨orderedLiteral C 1, orderedLiteral_mem C 1, by simpa [evalLiteral, endpoint, sign] using h⟩

end PallLean.Paper93.DeepMath.PathB.TwoCNFClauseExtraction

#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFClauseExtraction.endpoint_ne
#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFClauseExtraction.evalClause_iff_extracted
