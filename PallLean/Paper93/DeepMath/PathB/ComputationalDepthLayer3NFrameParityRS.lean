import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Smolensky
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolonomyBalanceFragments

/-!
# Connecting the N-frame holonomy target to the Razborov–Smolensky lower bound

The polynomial-method layer (`…Layer3Smolensky`) proves the full Razborov–Smolensky lower bound for the literal
parity function: any `AC⁰[p]` circuit (`p` odd prime, depth `≤ d`) computing `x ↦ decide(Odd #ones)` on `2m+1`
variables needs `2^{Ω(n^{1/2d})}` subcircuits (`parity_function_lower_bound`).

The N-frame / holonomy correlation layer (`…HolonomyBalanceFragments`) targets `fParity D` — the holonomy parity
`⊕_{i∈D} x_i`.  This file makes the bridge between the two routes explicit: **the N-frame holonomy target on the
full support, `fParity univ`, IS the literal parity function** `decide(Odd #ones)`.  Hence the proved RS size
lower bound applies verbatim to the N-frame target — the first `nframe_target_has_high_rs_degree`-style statement,
fusing the holonomy programme's hard function with the polynomial method's lower bound.

## What is proved (clean axioms, no `sorry`)

* `parityCharge_univ_eq_card` — `parityCharge univ x = (#ones : ZMod 2)`.
* `fParity_univ_eq_parity` — **`fParity univ x = decide(Odd #ones)`**: the holonomy target is the literal parity.
* `nframe_parity_target_size_lower_bound` — **the RS lower bound for the N-frame target**: an `AC⁰[p]` circuit
  computing `fParity univ` (with `MOD` gates of modulus `p`) has `> p^t / 4` subcircuits once `m ≥ 8((p-1)t)^{2d}`.

## Honest scope

This bridges the N-frame holonomy target to the genuine `PARITY ∉ AC⁰[p]` theorem (`p` odd prime, constant depth)
— a real classical lower bound, **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  The hypothesis `hmod` still restricts the
circuit's `MOD` gates to modulus `= p` (the RS field prime); composite / coprime moduli (general `ACC⁰`) are the
hard frontier the polynomial method alone does not reach.  See `ACC_ROADMAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3NFrameParityRS

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments

variable {n : ℕ}

/-- **The full-support holonomy charge is the ones-count mod 2 (proved).** -/
theorem parityCharge_univ_eq_card (x : Fin n → Bool) :
    parityCharge Finset.univ x
      = ((Finset.univ.filter (fun i => x i = true)).card : ZMod 2) := by
  unfold parityCharge
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : x i = true <;> simp [h]

/-- **The N-frame holonomy target on the full support is the literal parity function (proved):**
`fParity univ x = decide(Odd #ones)`. -/
theorem fParity_univ_eq_parity (x : Fin n → Bool) :
    fParity Finset.univ x
      = decide (Odd (Finset.univ.filter (fun i => x i = true)).card) := by
  unfold fParity
  rw [parityCharge_univ_eq_card]
  apply decide_eq_decide.mpr
  set k := (Finset.univ.filter (fun i => x i = true)).card with hk
  have hz2 : ∀ a : ZMod 2, (a = 1) ↔ (a ≠ 0) := by decide
  rw [hz2, ne_eq, CharP.cast_eq_zero_iff (ZMod 2) 2 k, Nat.odd_iff, Nat.dvd_iff_mod_eq_zero]
  omega

/-- **The Razborov–Smolensky size lower bound for the N-frame holonomy target (proved).**  Any `AC⁰[p]` circuit
(`p` odd prime, depth `≤ d`, `MOD` gates of modulus `p`) on `2m+1` variables that computes the N-frame holonomy
parity target `fParity univ` has more than `p^t/4` subcircuits, for every `t ≥ 1` with `m ≥ 8((p-1)t)^{2d}` —
i.e. `2^{Ω(n^{1/2d})}` size at the optimal `t`.  The holonomy target inherits the full RS lower bound. -/
theorem nframe_parity_target_size_lower_bound (p : ℕ) [Fact p.Prime] {m d : ℕ} (hp2 : (2 : ZMod p) ≠ 0)
    (Cir : BoolCircuitSyntax (2 * m + 1)) (hd : Cir.depth ≤ d) (t : ℕ) (ht1 : 1 ≤ t)
    (hnframe : ∀ x : Fin (2 * m + 1) → Bool, Cir.eval x = fParity Finset.univ x)
    (hmod : ∀ q r cs,
      (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax (2 * m + 1)) ∈ subcircuits Cir → q = p)
    (hm : 8 * (((p - 1) * t) ^ d) ^ 2 ≤ m) :
    p ^ t < 4 * (subcircuits Cir).toFinset.card :=
  parity_function_lower_bound p hp2 Cir hd t ht1
    (fun x => by rw [hnframe x, fParity_univ_eq_parity]) hmod hm

end PallLean.Paper93.DeepMath.PathB.Layer3NFrameParityRS

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3NFrameParityRS.fParity_univ_eq_parity
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3NFrameParityRS.nframe_parity_target_size_lower_bound
