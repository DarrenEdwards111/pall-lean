import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ValuationSparseTheory

/-!
# Route 1 — carry sparse theory: the structure of `⌊s/p⌋` and the carry boundary

The valuation analysis (`…ACC0ValuationSparseTheory`) localised the `ACC⁰[composite]` wall to a single object: the
**down-shift** `s ↦ ⌊s/p⌋`, which is provably non-additive, so the linear-form trick that makes `MOD_p` cheap does not
transfer to the higher conjuncts of `MOD_{p^e}`.  This file dissects that object — the carry — proving exactly how the
non-additivity is structured, where it vanishes, and why it cannot be recovered from the down-shifts alone.

The carry boundary is a **dynamic-boundary** phenomenon: as the modulus refines `MOD_p → MOD_{p^e}`, the observer must
refine from the field residue (mod `p`) to the carry-aware `p`-adic filtration.  The carry is the precise extra datum
that refinement carries.

* **The non-additivity is exactly one carry bit (decomposition + bound).**
  `⌊(a+b)/p⌋ = ⌊a/p⌋ + ⌊b/p⌋ + ⌊(a%p + b%p)/p⌋`, and the defect term `⌊(a%p+b%p)/p⌋ ∈ {0,1}`.  So the down-shift is
  additive *up to a single carry bit* — the entire obstruction is one bit per addition.

* **No-carry regime (restricted positive).**  If `a%p + b%p < p` (no carry) then `⌊(a+b)/p⌋ = ⌊a/p⌋ + ⌊b/p⌋`: the
  down-shift *is* additive.  In a no-carry regime the down-shifted count stays a linear form, so the `MOD_p` test on it
  is again cheap — the sparse representation goes through.  This is the fragment where Route 1 succeeds.

* **The carry obstruction.**  The carry bit is **not a function of the down-shifts** `⌊a/p⌋, ⌊b/p⌋`: the pairs `(0,0)`
  and `(p-1,1)` have identical down-shifts `(0,0)` yet carries `0` and `1`.  So a sparse theory of `⌊s/p⌋` must track the
  *low residues* `a%p, b%p`, not just the down-shifts — the carry lives on the residue boundary the field observer
  already sees, but couples it nonlinearly into the next level.

## What is proved (clean axioms, no `sorry`)

* **`downshift_add_carry_identity`** — `⌊(a+b)/p⌋ = ⌊a/p⌋ + ⌊b/p⌋ + ⌊(a%p+b%p)/p⌋` (exact carry decomposition).
* **`carry_le_one`** — `⌊(a%p+b%p)/p⌋ ≤ 1` (the carry is a single bit).
* **`downshift_additive_no_carry`** — `a%p+b%p < p ⇒ ⌊(a+b)/p⌋ = ⌊a/p⌋ + ⌊b/p⌋` (no-carry additivity).
* **`carry_not_function_of_downshifts`** — `(0,0)` and `(p-1,1)` share down-shifts but differ in carry.

## Honest scope

This is a genuine *structure theory of the carry*, not a representation of it.  It proves the non-additivity is exactly
one carry bit, exhibits the no-carry fragment where Route 1 succeeds, and proves the carry obstruction (carry needs the
residues, not just the down-shifts).  It does **not** produce a sparse/low-degree representation of `⌊s/p⌋` over the
input bits in the general (carry-present) regime — that is the open `ACC⁰[composite]` lower bound.  To prove full
`ACC⁰` one needs either a sparse theory of carries (a low-degree handle on `⌊(∑xᵢ)/p⌋` despite the carries) or a proof
that none exists.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CarrySparseTheory

/-- **Exact carry decomposition (proved): the down-shift's non-additivity is exactly one carry term.**
`⌊(a+b)/p⌋ = ⌊a/p⌋ + ⌊b/p⌋ + ⌊(a%p + b%p)/p⌋`.  The defect from additivity is precisely the carry `⌊(a%p+b%p)/p⌋`
produced by the low residues. -/
theorem downshift_add_carry_identity (p a b : ℕ) (hp : 0 < p) :
    (a + b) / p = a / p + b / p + (a % p + b % p) / p := by
  have ea := Nat.div_add_mod a p
  have eb := Nat.div_add_mod b p
  conv_lhs => rw [show a + b = (a % p + b % p) + p * (a / p + b / p) by rw [Nat.mul_add]; omega]
  rw [Nat.add_mul_div_left _ _ hp]; ring

/-- **The carry is a single bit (proved): `⌊(a%p + b%p)/p⌋ ≤ 1`.**  Each residue is `< p`, so their sum is `< 2p` and
the carry is `0` or `1` — the entire obstruction to additivity is one bit per addition. -/
theorem carry_le_one (p a b : ℕ) (hp : 0 < p) : (a % p + b % p) / p ≤ 1 := by
  have ha := Nat.mod_lt a hp
  have hb := Nat.mod_lt b hp
  have : (a % p + b % p) / p < 2 := by rw [Nat.div_lt_iff_lt_mul hp]; omega
  omega

/-- **No-carry regime — restricted positive (proved): the down-shift is additive when there is no carry.**
If `a%p + b%p < p` then `⌊(a+b)/p⌋ = ⌊a/p⌋ + ⌊b/p⌋`.  In a no-carry regime the down-shifted count remains a linear form,
so the `MOD_p` test on it stays cheap and the sparse representation of `MOD_{p^e}` goes through — the fragment where
Route 1 succeeds. -/
theorem downshift_additive_no_carry (p a b : ℕ) (hp : 0 < p) (h : a % p + b % p < p) :
    (a + b) / p = a / p + b / p := by
  rw [downshift_add_carry_identity p a b hp, Nat.div_eq_of_lt h, Nat.add_zero]

/-- **The carry obstruction (proved): the carry is not a function of the down-shifts.**  The pairs `(0,0)` and
`(p-1,1)` have identical down-shifts `(⌊·/p⌋ = 0, 0)` yet carries `0` and `1`.  So a sparse theory of `⌊s/p⌋` cannot
depend on the down-shifts alone — it must track the low residues `a%p, b%p`.  The carry couples the residue boundary
(which the field observer already sees) nonlinearly into the next `p`-adic level. -/
theorem carry_not_function_of_downshifts (p : ℕ) (hp : 2 ≤ p) :
    ((0 : ℕ) / p = (p - 1) / p) ∧ ((0 : ℕ) / p = 1 / p) ∧
      ((0 % p + 0 % p) / p ≠ ((p - 1) % p + 1 % p) / p) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.zero_div, Nat.div_eq_of_lt (by omega)]
  · rw [Nat.zero_div, Nat.div_eq_of_lt (by omega)]
  · have e1 : (0 % p + 0 % p) / p = 0 := by simp
    have e2 : ((p - 1) % p + 1 % p) / p = 1 := by
      rw [Nat.mod_eq_of_lt (by omega : p - 1 < p), Nat.mod_eq_of_lt (by omega : 1 < p),
          show p - 1 + 1 = p by omega, Nat.div_self (by omega : 0 < p)]
    rw [e1, e2]; omega

end PallLean.Paper93.DeepMath.PathB.ACC0CarrySparseTheory

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarrySparseTheory.downshift_add_carry_identity
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarrySparseTheory.carry_le_one
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarrySparseTheory.downshift_additive_no_carry
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarrySparseTheory.carry_not_function_of_downshifts
