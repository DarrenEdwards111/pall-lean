import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNWYaoPredictor

/-!
# Socket-2 (IKW): the NW ⟷ Yao fusion

Rung 9 gave the NW coordinate-hybrids (`nwHybrid`) whose consecutive pair differs in one coordinate; rung 10 gave Yao's
next-bit identity for an abstract "distinguisher with a plugged bit" `E : Ω → Bool → Bool` and generator bit `g`.  This
file fuses them: it identifies the NW hybrid distinguishing advantage with Yao's `accGen − accUnif`, so Yao's predictor
concretely targets the generator's bit `nwGen f z (poly j)`.

The one genuinely new analytic ingredient is a **marginalisation**: the uniform-side hybrid `nwHybrid f poly j` carries the
target coordinate as one *fresh bit inside the sample*, so its distinguishing probability must be shown equal to Yao's
`accUnif`, which *averages* an independent bit.  We prove this by peeling that coordinate out of the sample space.

  `Prob.expect_bool_marginal` / `Prob.expect_equiv` / `Prob.expect_update_marginal` — **PROVED**: general finite-probability
        infrastructure — expectation over `Ω × Bool` splits as an average; expectation is invariant under a sample-space
        equivalence; and averaging out one coordinate of a function-valued sample (on which the integrand does not depend)
        turns "read that coordinate" into "average the two values".
  `nwE` / `nwG` — the NW distinguisher with coordinate `j` plugged by a bit, and the generator's bit at `j`.
  `distinguish_succ_eq_accGen` / `distinguish_j_eq_accUnif` — **PROVED, the two bridges**: the generator-side hybrid's
        distinguishing probability is Yao's `accGen`, and the uniform-side hybrid's is Yao's `accUnif`.
  `nw_yao_fusion` — **PROVED, the fusion**: a distinguisher separating the two NW hybrids with advantage `≥ ε` yields a
        predictor (or its flip) for `nwGen f z (poly j)` succeeding with probability `≥ 1/2 + ε`.

So the single-coordinate NW distinguishing advantage is now literally a next-bit predictor for the generator's bit — the
predictor whose *other* inputs are the cheap circuits of rung 7.

## Honest scope — the fusion, not the circuit assembly, hardness, or collapse

This identifies the NW hybrid advantage with Yao's and produces the predictor for `nwGen f z (poly j)`.  It does **not**
assemble that predictor as an actual small circuit (wiring rung 7's `< 7·2^k` circuits for the other coordinates into `D`),
nor invoke `f`'s average-case hardness to contradict the predictor's existence, nor the IKW easy-witness collapse.  Those
are the deep `NEXP`-strength content of socket 2, not established here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Prob

variable {Ω : Type*} [Fintype Ω]

/-- **Product marginalisation (proved)**: an expectation over `Ω × Bool` is the expectation over `Ω` of the two-value
average. -/
theorem expect_bool_marginal (F : Ω → Bool → ℝ) :
    expect (fun p : Ω × Bool => F p.1 p.2) = expect (fun ω => (F ω true + F ω false) / 2) := by
  unfold expect
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [Fintype.card_prod, Fintype.card_bool, ← Finset.sum_div]
  push_cast; ring

/-- **Expectation is invariant under a sample-space equivalence (proved)**. -/
theorem expect_equiv {Ω' : Type*} [Fintype Ω'] (e : Ω ≃ Ω') (f : Ω' → ℝ) :
    expect (fun x => f (e x)) = expect f := by
  unfold expect
  rw [Equiv.sum_comp e f, Fintype.card_congr e]

/-- The equivalence peeling coordinate `k` of the function-valued factor out as a separate `Bool`. -/
noncomputable def splitEquiv {A K : Type*} [DecidableEq K] (k : K) :
    (A × (K → Bool)) ≃ ((A × ({i // i ≠ k} → Bool)) × Bool) :=
  (Equiv.prodCongr (Equiv.refl A) (Equiv.piSplitAt k (fun _ => Bool))).trans
    ((Equiv.prodCongr (Equiv.refl A) (Equiv.prodComm Bool _)).trans
      (Equiv.prodAssoc A _ Bool).symm)

/-- **Coordinate marginalisation (proved)**: if `F ω b` does not depend on coordinate `k` of the function-valued factor of
`ω`, then reading that coordinate as the second argument equals averaging over the two values. -/
theorem expect_update_marginal {A K : Type*} [Fintype A] [DecidableEq K] [Fintype K] (k : K)
    (F : (A × (K → Bool)) → Bool → ℝ)
    (hindep : ∀ (z : A) (r : K → Bool) (c b : Bool),
      F (z, Function.update r k c) b = F (z, r) b) :
    expect (fun ω : A × (K → Bool) => F ω (ω.2 k))
      = expect (fun ω => (F ω true + F ω false) / 2) := by
  set e := splitEquiv (A := A) k with he
  have hsymm : ∀ (ω₀ : A × ({i // i ≠ k} → Bool)) (b : Bool),
      e.symm (ω₀, b) = (ω₀.1, (Equiv.piSplitAt k (fun _ => Bool)).symm (b, ω₀.2)) := by
    intro ω₀ b; simp [e, splitEquiv]
  have hcoord : ∀ (ω₀ : A × ({i // i ≠ k} → Bool)) (b : Bool), (e.symm (ω₀, b)).2 k = b := by
    intro ω₀ b; rw [hsymm]; simp [Equiv.piSplitAt]
  have hswap : ∀ (ω₀ : A × ({i // i ≠ k} → Bool)) (x : Bool),
      F (e.symm (ω₀, true)) x = F (e.symm (ω₀, false)) x := by
    intro ω₀ x
    rw [hsymm, hsymm]
    have hup : (Equiv.piSplitAt k (fun _ => Bool)).symm (true, ω₀.2)
        = Function.update ((Equiv.piSplitAt k (fun _ => Bool)).symm (false, ω₀.2)) k true := by
      funext i
      by_cases hi : i = k
      · subst hi; simp [Equiv.piSplitAt]
      · simp [Equiv.piSplitAt, hi]
    rw [hup, hindep]
  have hA : expect (fun ω : A × (K → Bool) => F ω (ω.2 k))
      = expect (fun x : (A × ({i // i ≠ k} → Bool)) × Bool => F (e.symm x) x.2) := by
    rw [← expect_equiv e.symm (fun ω => F ω (ω.2 k))]
    apply expect_congr; intro x
    show F (e.symm x) ((e.symm x).2 k) = F (e.symm x) x.2
    rw [show ((e.symm x).2 k) = x.2 from by rw [← hcoord x.1 x.2]]
  have hB : expect (fun ω : A × (K → Bool) => (F ω true + F ω false) / 2)
      = expect (fun x : (A × ({i // i ≠ k} → Bool)) × Bool =>
          (F (e.symm x) true + F (e.symm x) false) / 2) := by
    rw [← expect_equiv e.symm (fun ω => (F ω true + F ω false) / 2)]
  rw [hA, hB, expect_bool_marginal (fun ω₀ b => F (e.symm (ω₀, b)) b),
    expect_bool_marginal (fun ω₀ b => (F (e.symm (ω₀, b)) true + F (e.symm (ω₀, b)) false) / 2)]
  apply expect_congr; intro ω₀
  rw [hswap ω₀ true, hswap ω₀ false]
  ring

end PallLean.Paper93.DeepMath.PathB.Prob

namespace PallLean.Paper93.DeepMath.PathB.NWDesign

open Polynomial PallLean.Paper93.DeepMath.PathB.Prob

variable {q : ℕ} [Fact q.Prime] {m : ℕ}

/-- The NW distinguisher `D` with the target coordinate `j` *plugged* by a bit `b` (other coordinates from the sample). -/
def nwE (D : (Fin m → Bool) → Bool) (f : (ZMod q → Bool) → Bool) (poly : Fin m → (ZMod q)[X])
    (j : ℕ) (hj : j < m) (ω : NWSample q m) (b : Bool) : Bool :=
  D (Function.update (nwHybrid f poly (j + 1) ω) ⟨j, hj⟩ b)

/-- The generator's bit at coordinate `j`. -/
def nwG (f : (ZMod q → Bool) → Bool) (poly : Fin m → (ZMod q)[X]) (j : ℕ) (hj : j < m)
    (ω : NWSample q m) : Bool := nwGen f ω.1 (poly ⟨j, hj⟩)

/-- The uniform-side hybrid, written as a plug of the fresh coordinate bit. -/
theorem nwHybrid_j_eq_update (f : (ZMod q → Bool) → Bool) (poly : Fin m → (ZMod q)[X])
    (j : ℕ) (hj : j < m) (ω : NWSample q m) :
    nwHybrid f poly j ω = Function.update (nwHybrid f poly (j + 1) ω) ⟨j, hj⟩ (ω.2 ⟨j, hj⟩) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = (⟨j, hj⟩ : Fin m)
  · rw [if_pos hi, hi]; exact (nwHybrid_succ_at f poly j ω hj).1
  · rw [if_neg hi]
    exact nwHybrid_agree_off f poly j ω i (fun hc => hi (Fin.ext hc))

/-- `nwE` does not depend on the fresh coordinate `j` bit of the sample — the independence marginalisation needs. -/
theorem nwE_indep (D : (Fin m → Bool) → Bool) (f : (ZMod q → Bool) → Bool)
    (poly : Fin m → (ZMod q)[X]) (j : ℕ) (hj : j < m) :
    ∀ (z : ZMod q × ZMod q → Bool) (r : Fin m → Bool) (c b : Bool),
      boolToReal (nwE D f poly j hj (z, Function.update r ⟨j, hj⟩ c) b)
        = boolToReal (nwE D f poly j hj (z, r) b) := by
  intro z r c b
  have hstr : nwE D f poly j hj (z, Function.update r ⟨j, hj⟩ c) b
      = nwE D f poly j hj (z, r) b := by
    unfold nwE
    congr 1
    funext i
    rw [Function.update_apply, Function.update_apply]
    by_cases hi : i = (⟨j, hj⟩ : Fin m)
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi]
      dsimp only [nwHybrid]
      by_cases hlt : (i : ℕ) < j + 1
      · simp only [if_pos hlt]
      · simp only [if_neg hlt]
        rw [Function.update_apply, if_neg hi]
  rw [hstr]

/-- **Generator-side bridge (proved)**: the generator-side hybrid's distinguishing probability is Yao's `accGen`. -/
theorem distinguish_succ_eq_accGen (D : (Fin m → Bool) → Bool) (f : (ZMod q → Bool) → Bool)
    (poly : Fin m → (ZMod q)[X]) (j : ℕ) (hj : j < m) :
    distinguish D (nwHybrid f poly (j + 1)) = accGen (nwE D f poly j hj) (nwG f poly j hj) := by
  unfold distinguish accGen prob
  apply expect_congr; intro ω
  congr 1
  show D (nwHybrid f poly (j + 1) ω) = nwE D f poly j hj ω (nwG f poly j hj ω)
  unfold nwE nwG
  rw [← (nwHybrid_succ_at f poly j ω hj).2, Function.update_eq_self]

/-- **Uniform-side bridge (proved)**: the uniform-side hybrid's distinguishing probability is Yao's `accUnif`. -/
theorem distinguish_j_eq_accUnif (D : (Fin m → Bool) → Bool) (f : (ZMod q → Bool) → Bool)
    (poly : Fin m → (ZMod q)[X]) (j : ℕ) (hj : j < m) :
    distinguish D (nwHybrid f poly j) = accUnif (nwE D f poly j hj) := by
  have hstr : ∀ ω, D (nwHybrid f poly j ω) = nwE D f poly j hj ω (ω.2 ⟨j, hj⟩) := by
    intro ω; unfold nwE; rw [nwHybrid_j_eq_update f poly j hj ω]
  unfold distinguish accUnif prob
  rw [show (fun ω => boolToReal (D (nwHybrid f poly j ω)))
        = (fun ω : NWSample q m => boolToReal (nwE D f poly j hj ω (ω.2 ⟨j, hj⟩)))
      from funext (fun ω => by rw [hstr ω])]
  exact expect_update_marginal ⟨j, hj⟩ (fun ω b => boolToReal (nwE D f poly j hj ω b))
    (nwE_indep D f poly j hj)

/-- **The NW ⟷ Yao fusion (proved)**: a distinguisher separating the two consecutive NW hybrids with advantage `≥ ε`
yields a next-bit predictor (or its flip) for the generator's bit `nwGen f z (poly j)` succeeding with probability
`≥ 1/2 + ε`. -/
theorem nw_yao_fusion (f : (ZMod q → Bool) → Bool) (poly : Fin m → (ZMod q)[X])
    (D : (Fin m → Bool) → Bool) (j : ℕ) (hj : j < m) (ε : ℝ)
    (hadv : ε ≤ |distinguish D (nwHybrid f poly j) - distinguish D (nwHybrid f poly (j + 1))|) :
    1 / 2 + ε ≤ predSucc (nwE D f poly j hj) (nwG f poly j hj)
      ∨ 1 / 2 + ε ≤ predSuccFlip (nwE D f poly j hj) (nwG f poly j hj) := by
  apply yao_two_sided
  rw [← distinguish_succ_eq_accGen, ← distinguish_j_eq_accUnif, abs_sub_comm]
  exact hadv

end PallLean.Paper93.DeepMath.PathB.NWDesign

#print axioms PallLean.Paper93.DeepMath.PathB.Prob.expect_update_marginal
#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.distinguish_succ_eq_accGen
#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.distinguish_j_eq_accUnif
#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nw_yao_fusion
