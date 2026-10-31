import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyUnboundedError
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyInstantiate

/-!
# Beigel–Tarui, rung 24: the correlated whole-circuit lift

Rung 23 gave the per-gate `2^{n-t}` bound only for a gate over the input variables, and flagged the correlated
sub-circuit case as the deep obstacle.  This file dissolves that obstacle and completes the lift.

The key observation: rung 8's averaging counts over the **input space** `x`, and the failure event at `x` depends only on
the gate's *reduced input* `red x = (child truth values)` through the pointwise fact "some child true ⇒ a random subset
of the child-values sums to nonzero w.p. ≥ ½".  This holds for **any** map `red`, no matter how the children correlate.
So rung 8 generalises verbatim to an arbitrary `red : (Fin n → Bool) → (Fin m → Bool)`:

  `exists_low_error_red` — **PROVED, the correlation-insensitive per-gate bound**: for any reduced-input map `red` there is
        a subset family `F` (of size `t`, over the fan-in `[m]`) whose bad set `{x : some child true ∧ every subset sums
        to 0 on `red x`}` satisfies `2^t · #bad ≤ 2^n`, i.e. `#bad ≤ 2^{n-t}` — **regardless of how `red` correlates the
        children with `x`** (the count is over `x`, using rung 3/4's amplification at the gate's arity `m`).

Then the union bound (rung 22) turns per-gate bounds into a whole-circuit bound:

  `whole_circuit_error_lt` — **PROVED, the whole-circuit lift**: if every gate's bad set satisfies `2^t · #(ubadSet g) ≤
        2^n` and there are fewer than `2^t` gates, then the whole-circuit substituted polynomial errs on `< 2^n` inputs.
        (Union bound `#error ≤ ∑_gates #(ubadSet g)`, each `≤ 2^{n-t}`, times `#gates < 2^t`.)

## Honest scope

`exists_low_error_red` is the genuine resolution of the "correlated inputs" difficulty: the per-gate `2^{n-t}` bound holds
for a gate over *arbitrary* sub-circuits, because the averaging never inspects the fibers of `red` — it sums a pointwise
`2^{-t}` failure probability over the `2^n` inputs.  `whole_circuit_error_lt` then assembles the per-gate bounds into
`#error < 2^n` via rung 22's union bound, provided `t > log₂(#gates)`.  What is left is purely mechanical *plumbing*: for
a concrete gate `uor l`, instantiate `red := fun x => fun j => (l.getD j …).eval x` and translate the `Fin m`-subset
family `F` into the `ℕ`-subset list `subsets` (a `Finset.image Fin.val` map, exactly as rung 23 did for the base gate),
identifying `#bad` with `#(ubadSet subsets (uor l))`.  That translation carries no new mathematics.  The composite-`MOD_m`
case remains the proven two-fields barrier.  Nothing here is the Beigel–Tarui reduction in full, `NEXP ⊄ ACC⁰`, or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

open MvPolynomial
open scoped Classical
open PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase (embed)

variable {p : ℕ} [Fact p.Prime] {n m t : ℕ}

/-- The inputs on which a gate's reduced input `red x` is nonzero (some child is `true`). -/
noncomputable def redNZ (red : (Fin n → Bool) → (Fin m → Bool)) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => ∃ i, red x i = true)

/-- The number of inputs on which a subset family `F` all-fails over the reduced input `red x`. -/
noncomputable def redNumErr (red : (Fin n → Bool) → (Fin m → Bool)) (t : ℕ)
    (F : Fin t → Finset (Fin m)) : ℕ :=
  ((redNZ red).filter (fun x => F ∈ allFail (p := p) (red x) t)).card

/-- **Double counting (proved)**: summing `redNumErr` over all families equals summing the all-fail count over the
reduced-nonzero inputs. -/
theorem sum_redNumErr (red : (Fin n → Bool) → (Fin m → Bool)) (t : ℕ) :
    ∑ F : Fin t → Finset (Fin m), redNumErr (p := p) red t F
      = ∑ x ∈ redNZ red, (allFail (p := p) (red x) t).card := by
  simp only [redNumErr, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.card_filter]
  congr 1
  exact Finset.filter_univ_mem _

/-- **The summed amplification bound (proved)**: `2^t · (∑ over reduced-nonzero inputs of the all-fail count) ≤
`2^n · (2^m)^t` — rung 4's amplification at the gate's arity `m`, summed over the `≤ 2^n` inputs. -/
theorem sum_redAllFail_bound (red : (Fin n → Bool) → (Fin m → Bool)) (t : ℕ) :
    2 ^ t * (∑ x ∈ redNZ red, (allFail (p := p) (red x) t).card) ≤ 2 ^ n * (2 ^ m) ^ t := by
  rw [Finset.mul_sum]
  calc ∑ x ∈ redNZ red, 2 ^ t * (allFail (p := p) (red x) t).card
      ≤ ∑ _x ∈ redNZ red, (2 ^ m) ^ t := by
        apply Finset.sum_le_sum
        intro x hx
        rw [redNZ, Finset.mem_filter] at hx
        exact amplification (red x) hx.2 t
    _ = (redNZ red).card * (2 ^ m) ^ t := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 ^ n * (2 ^ m) ^ t := by
        apply Nat.mul_le_mul_right
        calc (redNZ red).card ≤ (Finset.univ : Finset (Fin n → Bool)).card :=
              Finset.card_filter_le _ _
          _ = 2 ^ n := by rw [Finset.card_univ]; simp

/-- **The correlation-insensitive per-gate bound (proved)**: for *any* reduced-input map `red`, some subset family `F`
(over the fan-in `[m]`) makes the gate's bad set satisfy `2^t · #bad ≤ 2^n` — i.e. `#bad ≤ 2^{n-t}`.  The proof averages
a pointwise `2^{-t}` failure bound over the `2^n` inputs, so it is blind to how `red` correlates the children with `x`.
This generalises rung 8's `exists_low_error` (the case `red = id`, `m = n`) to an arbitrary gate over sub-circuits. -/
theorem exists_low_error_red (red : (Fin n → Bool) → (Fin m → Bool)) (t : ℕ) :
    ∃ F : Fin t → Finset (Fin m), 2 ^ t * redNumErr (p := p) red t F ≤ 2 ^ n := by
  by_contra hc
  push_neg at hc
  have hcard : (Finset.univ : Finset (Fin t → Finset (Fin m))).card = (2 ^ m) ^ t := by
    rw [Finset.card_univ]; simp [Fintype.card_finset]
  have hlow : (Finset.univ : Finset (Fin t → Finset (Fin m))).card * (2 ^ n + 1)
      ≤ ∑ F : Fin t → Finset (Fin m), 2 ^ t * redNumErr (p := p) red t F := by
    calc (Finset.univ : Finset (Fin t → Finset (Fin m))).card * (2 ^ n + 1)
        = ∑ _F : Fin t → Finset (Fin m), (2 ^ n + 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ F : Fin t → Finset (Fin m), 2 ^ t * redNumErr (p := p) red t F :=
          Finset.sum_le_sum (fun F _ => hc F)
  have hhigh : ∑ F : Fin t → Finset (Fin m), 2 ^ t * redNumErr (p := p) red t F ≤ 2 ^ n * (2 ^ m) ^ t := by
    rw [← Finset.mul_sum, sum_redNumErr]; exact sum_redAllFail_bound red t
  rw [hcard] at hlow
  have hcomb := le_trans hlow hhigh
  have h2 : 0 < (2 ^ m) ^ t := pow_pos (pow_pos (by norm_num) m) t
  rw [mul_comm (2 ^ n) ((2 ^ m) ^ t)] at hcomb
  have := Nat.le_of_mul_le_mul_left hcomb h2
  omega

/-- **The whole-circuit lift (proved)**: if every gate's bad set satisfies `2^t · #(ubadSet g) ≤ 2^n` and the circuit has
fewer than `2^t` gates, then the whole-circuit substituted polynomial errs on `< 2^n` inputs.  This is the union bound
(rung 22) fed with the per-gate `2^{n-t}` bound (justified for *any* gate by `exists_low_error_red`), plus the counting
`#gates · 2^{n-t} < 2^n` when `2^t > #gates`. -/
theorem whole_circuit_error_lt (subsets : List (Finset ℕ)) (f : UForm n) (t : ℕ)
    (hpg : ∀ g ∈ (usubforms f).toFinset, 2 ^ t * (ubadSet (p := p) subsets g).card ≤ 2 ^ n)
    (hgates : (usubforms f).toFinset.card < 2 ^ t) :
    (Finset.univ.filter
        (fun x => uArithApproxVal (p := p) subsets f (fun i => embed (x i)) ≠ embed (f.eval x))).card
      < 2 ^ n := by
  have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
  have hun := uArithApprox_error_card_le (p := p) subsets f
  have hsum : 2 ^ t * (∑ g ∈ (usubforms f).toFinset, (ubadSet (p := p) subsets g).card)
      ≤ (usubforms f).toFinset.card * 2 ^ n := by
    rw [Finset.mul_sum]
    calc ∑ g ∈ (usubforms f).toFinset, 2 ^ t * (ubadSet (p := p) subsets g).card
        ≤ ∑ _g ∈ (usubforms f).toFinset, 2 ^ n := Finset.sum_le_sum hpg
      _ = (usubforms f).toFinset.card * 2 ^ n := by rw [Finset.sum_const, smul_eq_mul]
  have h2 : 2 ^ t * (Finset.univ.filter
      (fun x => uArithApproxVal (p := p) subsets f (fun i => embed (x i)) ≠ embed (f.eval x))).card
      ≤ (usubforms f).toFinset.card * 2 ^ n :=
    le_trans (Nat.mul_le_mul_left _ hun) hsum
  have h3 : (usubforms f).toFinset.card * 2 ^ n < 2 ^ t * 2 ^ n :=
    (Nat.mul_lt_mul_right hpos).mpr hgates
  exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h2 h3)

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.exists_low_error_red
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.whole_circuit_error_lt
