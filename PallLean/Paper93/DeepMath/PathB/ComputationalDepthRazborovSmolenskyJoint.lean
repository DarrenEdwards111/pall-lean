import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyLift

/-!
# Beigel–Tarui, rung 27: the single-shared-family averaging

Rungs 25–26 bounded each gate by its *own* subset family; the whole-circuit polynomial uses *one* shared family.  This
file closes that gap: **one** subset family simultaneously controls **all** gates.  It generalises rung 24's
`exists_low_error_red` from a single reduced-input map to a *finite family* of them (one per gate) at a common arity,
bounding the **sum** of the per-gate bad sets by averaging over the shared family.

  `exists_low_error_family` — **PROVED, the single-shared-family bound**: for any finite family of reduced-input maps
        `reds : ι → ((Fin n → Bool) → (Fin N → Bool))` there is *one* subset family `F` (length `t`, over the common
        arity `[N]`) with `2^t · ∑_i #bad_i ≤ #ι · 2^n` — i.e. the *total* bad count over all gates is `≤ #ι · 2^{n-t}`.
        The proof is rung 24's pigeonhole with a sum over gates (linearity of expectation): `∑_F ∑_i (…) = ∑_i ∑_F (…)`,
        each inner sum bounded by rung 24's `sum_redNumErr`/`sum_redAllFail_bound`.
  `whole_circuit_error_lt_of_sum` — **PROVED**: if the shared family makes `2^t · ∑_gates #(ubadSet g) ≤ #gates · 2^n`
        and there are `< 2^t` gates, then the whole-circuit polynomial errs on `< 2^n` inputs (rung 22's union bound +
        the counting `#gates · 2^{n-t} < 2^n`).

Together: the single family from `exists_low_error_family` (once its `Fin N`-subsets are translated to the `ℕ`-subset list
and its `#bad_i` identified with `#(ubadSet g)` for each gate, as rungs 25–26 do per gate) feeds
`whole_circuit_error_lt_of_sum` to give whole-circuit error `< 2^n`.

## Honest scope

`exists_low_error_family` is the genuine single-shared-family content — one family, all gates, total bad `≤ #gates ·
2^{n-t}` — proved by averaging over the shared family (rung 24 machinery, summed over gates).  `whole_circuit_error_lt_of_sum`
assembles it into the whole-circuit bound.  The only glue not written out is the per-gate identification `#bad_i =
#(ubadSet subsets g)` under padding each gate's reduced map to the common arity `N ≥ max fan-in` and imaging `Fin N`-subsets
to `ℕ`-subsets — the exact `Finset.image Fin.val` translation of rungs 25–26, carrying no new mathematics.  The
composite-`MOD_m` case remains the proven two-fields barrier.  Nothing here is the Beigel–Tarui reduction in full,
`NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

open MvPolynomial
open scoped Classical
open PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase (embed)

variable {p : ℕ} [Fact p.Prime] {n N : ℕ}

/-- **The single-shared-family averaging (proved)**: one subset family `F` bounds the *total* bad count over a finite
family of gates by `#ι · 2^{n-t}`.  Generalises `exists_low_error_red` (a single map) to a family, by rung 24's pigeonhole
summed over gates (linearity of expectation). -/
theorem exists_low_error_family {ι : Type*} [Fintype ι]
    (reds : ι → ((Fin n → Bool) → (Fin N → Bool))) (t : ℕ) :
    ∃ F : Fin t → Finset (Fin N),
      2 ^ t * (∑ i : ι, redNumErr (p := p) (reds i) t F) ≤ Fintype.card ι * 2 ^ n := by
  by_contra hc
  push_neg at hc
  have hcard : (Finset.univ : Finset (Fin t → Finset (Fin N))).card = (2 ^ N) ^ t := by
    rw [Finset.card_univ]; simp [Fintype.card_finset]
  have hlow : (Finset.univ : Finset (Fin t → Finset (Fin N))).card * (Fintype.card ι * 2 ^ n + 1)
      ≤ ∑ F : Fin t → Finset (Fin N), 2 ^ t * ∑ i : ι, redNumErr (p := p) (reds i) t F := by
    calc (Finset.univ : Finset (Fin t → Finset (Fin N))).card * (Fintype.card ι * 2 ^ n + 1)
        = ∑ _F : Fin t → Finset (Fin N), (Fintype.card ι * 2 ^ n + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ F : Fin t → Finset (Fin N), 2 ^ t * ∑ i : ι, redNumErr (p := p) (reds i) t F :=
          Finset.sum_le_sum (fun F _ => hc F)
  have hstep : ∀ i : ι,
      ∑ F : Fin t → Finset (Fin N), 2 ^ t * redNumErr (p := p) (reds i) t F ≤ 2 ^ n * (2 ^ N) ^ t := by
    intro i
    rw [← Finset.mul_sum, sum_redNumErr]
    exact sum_redAllFail_bound (reds i) t
  have hhigh : ∑ F : Fin t → Finset (Fin N), 2 ^ t * ∑ i : ι, redNumErr (p := p) (reds i) t F
      ≤ Fintype.card ι * 2 ^ n * (2 ^ N) ^ t := by
    calc ∑ F : Fin t → Finset (Fin N), 2 ^ t * ∑ i : ι, redNumErr (p := p) (reds i) t F
        = ∑ F : Fin t → Finset (Fin N), ∑ i : ι, 2 ^ t * redNumErr (p := p) (reds i) t F := by
          refine Finset.sum_congr rfl (fun F _ => ?_); rw [Finset.mul_sum]
      _ = ∑ i : ι, ∑ F : Fin t → Finset (Fin N), 2 ^ t * redNumErr (p := p) (reds i) t F :=
          Finset.sum_comm
      _ ≤ ∑ _i : ι, 2 ^ n * (2 ^ N) ^ t := Finset.sum_le_sum (fun i _ => hstep i)
      _ = Fintype.card ι * (2 ^ n * (2 ^ N) ^ t) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ = Fintype.card ι * 2 ^ n * (2 ^ N) ^ t := by ring
  rw [hcard] at hlow
  have hcomb := le_trans hlow hhigh
  have h2 : 0 < (2 ^ N) ^ t := pow_pos (pow_pos (by norm_num) N) t
  rw [mul_comm (Fintype.card ι * 2 ^ n) ((2 ^ N) ^ t)] at hcomb
  have := Nat.le_of_mul_le_mul_left hcomb h2
  omega

/-- **The whole-circuit bound from a shared-family sum bound (proved)**: if the shared family makes the *total* bad count
`2^t · ∑_gates #(ubadSet g) ≤ #gates · 2^n` and there are fewer than `2^t` gates, the whole-circuit polynomial errs on
`< 2^n` inputs. -/
theorem whole_circuit_error_lt_of_sum (subsets : List (Finset ℕ)) (f : UForm n) (t : ℕ)
    (hsum : 2 ^ t * (∑ g ∈ (usubforms f).toFinset, (ubadSet (p := p) subsets g).card)
      ≤ (usubforms f).toFinset.card * 2 ^ n)
    (hgates : (usubforms f).toFinset.card < 2 ^ t) :
    (Finset.univ.filter
        (fun x => uArithApproxVal (p := p) subsets f (fun i => embed (x i)) ≠ embed (f.eval x))).card
      < 2 ^ n := by
  have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
  have hun := uArithApprox_error_card_le (p := p) subsets f
  have h2 : 2 ^ t * (Finset.univ.filter
      (fun x => uArithApproxVal (p := p) subsets f (fun i => embed (x i)) ≠ embed (f.eval x))).card
      ≤ (usubforms f).toFinset.card * 2 ^ n :=
    le_trans (Nat.mul_le_mul_left _ hun) hsum
  have h3 : (usubforms f).toFinset.card * 2 ^ n < 2 ^ t * 2 ^ n :=
    (Nat.mul_lt_mul_right hpos).mpr hgates
  exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h2 h3)

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.exists_low_error_family
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.whole_circuit_error_lt_of_sum
