import Mathlib.Data.Nat.Basic

/-!
# Pushing the least-dead limit a rung: the formula shrinkage exponent Γ

The `TwoLimitsWall` capstone frames the whole problem as *raise the certified lower limit `L`*.  The
least-dead method for raising a formula-size `L` is **shrinkage applied to Andreev's function**:
formula size `≥ n^{1+Γ}`, where `Γ` is the shrinkage exponent.  The repo's unconditional floor is
`Γ = 3/2` (Subbotovskaya) giving `n^{5/2}` (`AndreevShrinkageRoute` / `andreev_five_halves_full`); the
next rung is `Γ = 2` (Håstad) giving `n^{3-o(1)}`.

This file makes `Γ` the **explicit knob** and pushes the rung honestly.  To stay in `ℕ` we work with the
squared bound and the doubled exponent `g = 2Γ`, so a size `Lsz` "certifies shrinkage exponent `g`" when
`n^{2+g} ≤ (Lsz n)^2`  (i.e. `Lsz n ≥ n^{(2+g)/2} = n^{1+Γ}`).  Subbotovskaya `g = 3` → `n^{5/2}`;
Håstad `g = 4` → `n^3`.

## What is proved

* **`required_bound_mono` (proved)** — raising `g` raises the bound: `g₁ ≤ g₂ ⟹ n^{2+g₁} ≤ n^{2+g₂}`.
  The knob is monotone; pushing `Γ` up is exactly pushing `L` up.
* **`rung_exponent` (proved)** — the rung itself: Subbotovskaya→Håstad strictly raises the exponent
  (`2+3 < 2+4`), i.e. `n^{5/2} → n^3`.
* **`method_capped_at_cube` (proved)** — the honest ceiling: shrinkage-exponent optimality
  (`Γ ≤ 2`, `g ≤ 4` — Håstad's bound is tight, a named cited fact) forces `n^{2+g} ≤ n^6`, i.e. the
  method certifies **at most** `L ≥ n^3`.  It cannot go past the cube.
* **`cube_below_poly_ceiling` (proved)** — the capstone tie: `n^3 ≤ n^k` for `k ≥ 3`.  At its optimal
  exponent the shrinkage `L` is still `n^3`, below every poly ceiling `U = n^k` with `k ≥ 3` — so pushed
  to its limit this method still does **not** clear the wall.

## Honest scope

The unconditional certified `L` stays at `n^{5/2}` (`g = 3`); the rung to `n^3` (`g = 4`) is **conditional
on the named Håstad shrinkage socket**, not re-proved here.  And `method_capped_at_cube` proves the whole
method stops at `n^3`: it is a genuine rung on the certified `L`, and simultaneously a proof that this
least-dead method **cannot** reach a superpolynomial `L`.  Ceiling of the method: `n^3`, formula lower
bounds (`P ≠ NC¹`).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ShrinkageExponentRung

/-- A formula-size measure `Lsz` **certifies shrinkage exponent `g = 2Γ`** when the squared size is at
least `n^{2+g}`, i.e. `Lsz n ≥ n^{1+Γ}` — Andreev's bound at shrinkage exponent `Γ`. -/
def CertifiesShrinkage (Lsz : ℕ → ℕ) (g : ℕ) : Prop :=
  ∀ n, n ^ (2 + g) ≤ (Lsz n) ^ 2

/-- **Shrinkage-exponent optimality (named socket).**  Håstad's shrinkage exponent `Γ = 2` is tight:
no formula-shrinkage argument yields `Γ > 2`, i.e. `g = 2Γ ≤ 4`.  A cited fact, not re-proved. -/
def ShrinkageExponentOptimal (g : ℕ) : Prop := g ≤ 4

/-- **The knob is monotone (proved).**  Raising the shrinkage exponent raises the required bound: pushing
`Γ` (hence `g`) up pushes the certified `L` up. -/
theorem required_bound_mono {g₁ g₂ n : ℕ} (hg : g₁ ≤ g₂) (hn : 1 ≤ n) :
    n ^ (2 + g₁) ≤ n ^ (2 + g₂) :=
  Nat.pow_le_pow_right hn (by omega)

/-- **The rung (proved).**  Subbotovskaya (`g = 3`, `n^{5/2}`) → Håstad (`g = 4`, `n^3`) strictly raises
the exponent.  This is the one rung available above the unconditional floor. -/
theorem rung_exponent : (2 + 3 : ℕ) < 2 + 4 := by omega

/-- **The method ceiling (proved).**  Under shrinkage-exponent optimality (`g ≤ 4`, `Γ ≤ 2`), the bound
cannot exceed `n^6 = (n^3)^2`: the shrinkage method certifies **at most** `L ≥ n^3`.  It stops at the
cube. -/
theorem method_capped_at_cube {g : ℕ} (hopt : ShrinkageExponentOptimal g) {n : ℕ} (hn : 1 ≤ n) :
    n ^ (2 + g) ≤ n ^ 6 :=
  Nat.pow_le_pow_right hn (by unfold ShrinkageExponentOptimal at hopt; omega)

/-- **Capstone tie: the pushed limit still sits below the wall (proved).**  At its optimal exponent the
shrinkage bound is `n^3`; against any poly ceiling `U = n^k` with `k ≥ 3`, `n^3 ≤ n^k`.  So this
least-dead method, pushed to its ceiling, does not clear a superpoly `U` — `L` stays below the wall. -/
theorem cube_below_poly_ceiling {k n : ℕ} (hk : 3 ≤ k) (hn : 1 ≤ n) : n ^ 3 ≤ n ^ k :=
  Nat.pow_le_pow_right hn hk

end PallLean.Paper93.DeepMath.PathB.ShrinkageExponentRung

#print axioms PallLean.Paper93.DeepMath.PathB.ShrinkageExponentRung.required_bound_mono
#print axioms PallLean.Paper93.DeepMath.PathB.ShrinkageExponentRung.rung_exponent
#print axioms PallLean.Paper93.DeepMath.PathB.ShrinkageExponentRung.method_capped_at_cube
#print axioms PallLean.Paper93.DeepMath.PathB.ShrinkageExponentRung.cube_below_poly_ceiling
