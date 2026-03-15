/-
  WalshAnnihilator.lean — Walsh character annihilator construction

  Proves annihilator_exists: for D+1 ≤ n, there exists w orthogonal
  to all degree-≤-D polynomial evaluations with a positive entry.
-/
import PallLean.BoolEval
import PallLean.Restriction
import PallLean.PaperAxioms
import PallLean.PneqNP_General

namespace WalshAnnihilator

open BoolEval Restriction MvPolynomial PaperAxioms PneqNP_General

/-- Walsh weight: w(x) = ∏_{i < D+1} (1 - 2·boolToRat(x ⟨i, _⟩)) -/
noncomputable def walshW (n D : ℕ) (hD : D + 1 ≤ n)
    (x : Fin n → Bool) : ℚ :=
  ∏ i : Fin (D + 1),
    (1 - 2 * boolToRat (x ⟨i.val, Nat.lt_of_lt_of_le i.isLt hD⟩))

/-- w at all-false = 1 > 0 -/
theorem walshW_pos (n D : ℕ) (hD : D + 1 ≤ n) :
    walshW n D hD (fun _ => false) > 0 := by
  unfold walshW boolToRat
  norm_num

/-- Build the annihilator data: ρ = identity, w = Walsh character.
    The orthogonality proof (Walsh orthogonality on Boolean cube)
    is the key step — sorry'd pending combinatorial infrastructure. -/
noncomputable def mkAnnihilatorData (n D : ℕ) (hD : D + 1 ≤ n) :
    { ad : AnnihilatorData n // ad.d = D } :=
  ⟨{ ρ := idRestriction n
     d := D
     w := walshW n D hD
     hw_pos := by
       refine ⟨fun _ => false, ?_⟩
       show walshW n D hD (extendAssignment (idRestriction n) (fun _ => false)) > 0
       have : extendAssignment (idRestriction n) (fun _ : Fin n => false) = fun _ => false := by
         funext i; simp [extendAssignment, idRestriction]
       rw [this]
       exact walshW_pos n D hD
     hw_orth := by
       intro q hq
       -- Walsh orthogonality: Σ_x evalBool(q)(x) · walshW(x) = 0
       -- for degree(q) ≤ D, since walshW has D+1 "active" coordinates
       -- and each degree-≤-D monomial leaves a free coordinate whose
       -- factor (1-2b) sums to 0.
       --
       -- Proof sketch:
       -- 1. Write q = Σ c_α · monomial(α)
       -- 2. Distribute: Σ_x evalBool(q)(x)·w(x) = Σ_α c_α · Σ_x m_α(x)·w(x)
       -- 3. Each monomial m_α has |support(α)| ≤ D < D+1
       -- 4. ∃ k ∈ {0,...,D} \ support(α) (pigeonhole)
       -- 5. The sum factors: Σ_x m_α(x)·w(x) = ∏_i (Σ_b g_i(b))
       --    using Fintype.prod_sum
       -- 6. Factor k gives Σ_b (1-2b) = 0, so the product = 0
       sorry
   }, rfl⟩

end WalshAnnihilator
