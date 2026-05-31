import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivationTseitin
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFatClauseAveraging

/-!
# Explicit exponential size lower bound for expander Tseitin

The arithmetic corollary of `tseitin_size_lower` (`n^b ≤ (n-d)^b · |L|`).  Two
binomial terms (`bernoulli_pow`) give `n^k ≥ 2·(n-d)^k` whenever `k·d ≥ n-d`;
raising to the `j`-th power gives `n^{kj} ≥ 2^j·(n-d)^{kj}`.  Combined with the
size–width bound at `b = k·j`, this yields the explicit exponential

  `2^j ≤ |L|`

for every refutation, whenever the width budget `w₀ + d + k·j` stays below the
expander lower bound `c·t`.  Choosing `d ≈ √n`, `k ≈ √n`, `j ≈ (c·t)/√n` makes
the exponent `j` a genuine (super-polynomial) function of the parameters.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace LDeriv

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

/-- **Two-term doubling.**  If `k·d ≥ n-d` then `n^k ≥ 2·(n-d)^k` — the first two
binomial terms of `((n-d)+d)^k` already exceed `2·(n-d)^k`. -/
theorem two_mul_pow_le (n d k : ℕ) (hk1 : 1 ≤ k) (hkd : n - d ≤ k * d) (hdn : d ≤ n) :
    2 * (n - d) ^ k ≤ n ^ k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hbern := bernoulli_pow (n - d) d k'
  rw [Nat.sub_add_cancel hdn] at hbern
  have hlow : (n - d) ^ (k' + 1) ≤ (k' + 1) * d * (n - d) ^ k' := by
    calc (n - d) ^ (k' + 1) = (n - d) * (n - d) ^ k' := by rw [pow_succ, mul_comm]
      _ ≤ (k' + 1) * d * (n - d) ^ k' := mul_le_mul_right' hkd ((n - d) ^ k')
  omega

/-- **Iterated doubling.**  Raising the two-term bound to the `j`-th power:
`2^j · (n-d)^{k·j} ≤ n^{k·j}`. -/
theorem two_pow_mul_pow_le (n d k : ℕ) (hk1 : 1 ≤ k) (hkd : n - d ≤ k * d) (hdn : d ≤ n)
    (j : ℕ) : 2 ^ j * (n - d) ^ (k * j) ≤ n ^ (k * j) := by
  have h2 := two_mul_pow_le n d k hk1 hkd hdn
  calc 2 ^ j * (n - d) ^ (k * j)
      = 2 ^ j * ((n - d) ^ k) ^ j := by rw [pow_mul]
    _ = (2 * (n - d) ^ k) ^ j := by rw [mul_pow]
    _ ≤ (n ^ k) ^ j := Nat.pow_le_pow_left h2 j
    _ = n ^ (k * j) := by rw [pow_mul]

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]
  [Nonempty Edge]

/-- **Explicit exponential size lower bound for expander Tseitin.**  Every refutation
of the Tseitin axioms has length `≥ 2^j`, whenever the doubling condition
`n - d ≤ k·d` holds and the width budget `w₀ + d + k·j` stays below the expander
lower bound `c·t`.  (Here `n = |literals|`.) -/
theorem tseitin_size_exp (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (Ax : List (ResolutionClause (TLit Edge)))
    (hAxiom : ∀ C, C ∈ Ax → ∃ v : V, SemanticMeasure.Implies TSat (TConstr G charge) {v} C)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht2 : 2 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V) {w₀ : ℕ} (hw0 : ∀ C ∈ Ax, ResolutionClause.width C ≤ w₀)
    {d k j : ℕ} (hd : 0 < d) (hk1 : 1 ≤ k)
    (hdn : d < Fintype.card (TLit Edge))
    (hkd : Fintype.card (TLit Edge) - d ≤ k * d)
    {L : List (ResolutionClause (TLit Edge))}
    (hLD : LDeriv tcompl (· ∈ Ax) L) (hmt : (∅ : ResolutionClause (TLit Edge)) ∈ L)
    (hsmall : w₀ + d + k * j < c * t) :
    2 ^ j ≤ L.length := by
  set n := Fintype.card (TLit Edge) with hn
  have hsize : n ^ (k * j) ≤ (n - d) ^ (k * j) * L.length :=
    tseitin_size_lower G charge hunsat Ax hAxiom hc hexp ht2 hcard hw0 hd hLD hmt hsmall
  have hpow : 2 ^ j * (n - d) ^ (k * j) ≤ n ^ (k * j) :=
    two_pow_mul_pow_le n d k hk1 hkd (le_of_lt hdn) j
  have hm : 0 < (n - d) ^ (k * j) := pow_pos (by omega) _
  have hkey : 2 ^ j * (n - d) ^ (k * j) ≤ L.length * (n - d) ^ (k * j) := by
    calc 2 ^ j * (n - d) ^ (k * j) ≤ n ^ (k * j) := hpow
      _ ≤ (n - d) ^ (k * j) * L.length := hsize
      _ = L.length * (n - d) ^ (k * j) := by rw [Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_right hkey hm

end LDeriv

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.tseitin_size_exp
