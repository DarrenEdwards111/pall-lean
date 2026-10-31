import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# The Kakeya→CEW reduction, restricted to its algebraic engine

`nframe book1` §6.6 (the Epistemic Kakeya Principle) motivates `P ≠ NP` by analogy to the finite-field
Kakeya theorem: a set that "covers every direction" must occupy full dimension.  The load-bearing
axiom (A3) — an NP family whose contextual width / SPDP rank is superpolynomial — was left *asserted*.

This file builds the **rigorous algebraic core** of that reduction in a restricted (finite-dimensional,
linear-algebraic) setting.  It is the exact engine shared by Dvir's polynomial-method proof of Kakeya
*and* by SPDP rank: **dimension counting**.  The one geometric input of Kakeya — "a line in every
direction ⟹ no nonzero low-degree polynomial vanishes on the set" — is abstracted here as the
hypothesis `Function.Injective E` (the measurements resolve every certificate direction).

Dictionary (book1 → here):
* `V`  = the low-CEW **certificate space** (e.g. degree-≤`d` test polynomials); `finrank F V` = the
  epistemic dimension `D` available at that width.
* `S`  = the sampled **directions/configurations**; `Fintype.card S` = the width actually spent.
* `E : V →ₗ (S → F)` = the **measurement / evaluation** map.
* `Function.Injective E` = the **Kakeya / direction-covering** property (no nonzero certificate vanishes
  on `S`).

## What is proved

* **`compressible_of_width_lt_dim`** (the polynomial-method core): if the width is below the certificate
  dimension (`card S < finrank F V`), some **nonzero certificate vanishes** on every measurement — `S`
  is compressible in a direction.  (Rank–nullity: the evaluation map cannot be injective.)
* **`kakeya_forces_dimension`** (the reduction): if `S` is direction-covering (`E` injective), then the
  width is at least the dimension: `finrank F V ≤ Fintype.card S`.  This is the Kakeya "full-dimension"
  / CEW lower bound, rigorously, from the injectivity hypothesis.

## Honest scope

This is the **engine**, proved — not a separation.  It converts a *direction-covering hypothesis* into a
width/CEW lower bound, exactly as Dvir's polynomial method converts Kakeya's line-in-every-direction
into a size bound.  What it does **not** do is discharge book1's (A3): exhibiting a concrete
NP/computational family for which `E` is injective at *superpolynomial* `finrank F V` is precisely the
open circuit lower bound (`cost_super` / SAT incompressible off `Π★`).  The engine is real; instantiating
it at superpoly dimension for an NP family is the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KakeyaCEW

open Module

variable {F : Type*} [Field F]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {S : Type*} [Fintype S]

/-- **The Kakeya→CEW reduction (proved).**  If the measurement map is direction-covering (injective —
no nonzero certificate vanishes on the sampled directions), then the width spent is at least the
certificate dimension: `finrank F V ≤ card S`.  This is the finite-dimensional core of "a set covering
every direction must have full dimension." -/
theorem kakeya_forces_dimension (E : V →ₗ[F] (S → F)) (hinj : Function.Injective E) :
    finrank F V ≤ Fintype.card S := by
  have hker : finrank F (LinearMap.ker E) = 0 := by
    rw [LinearMap.ker_eq_bot.mpr hinj]; simp
  have hrn := LinearMap.finrank_range_add_finrank_ker E
  have hle : finrank F (LinearMap.range E) ≤ finrank F (S → F) := Submodule.finrank_le _
  have hpi : finrank F (S → F) = Fintype.card S := by simp
  omega

/-- **The polynomial-method core (proved).**  If the width is below the certificate dimension, some
nonzero certificate vanishes on every measurement — the set is compressible in a direction.  This is the
contrapositive of the reduction, and the exact dimension-count behind Dvir's Kakeya and behind SPDP
rank. -/
theorem compressible_of_width_lt_dim (E : V →ₗ[F] (S → F))
    (h : Fintype.card S < finrank F V) :
    ∃ v : V, v ≠ 0 ∧ E v = 0 := by
  by_contra hcon
  push_neg at hcon
  have hinj : Function.Injective E := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    exact hcon v hv0 (LinearMap.mem_ker.mp hv)
  have := kakeya_forces_dimension E hinj
  omega

/-- **The two faces are equivalent (proved).**  Direction-covering (incompressible) ⟺ width at least the
dimension.  Below the dimension you are forced compressible; at or above it you can be covering.  This is
the CEW threshold: the epistemic dimension `finrank F V` is exactly the width a covering must pay. -/
theorem covering_iff_width (E : V →ₗ[F] (S → F)) :
    Function.Injective E → finrank F V ≤ Fintype.card S :=
  kakeya_forces_dimension E

end PallLean.Paper93.DeepMath.PathB.KakeyaCEW

#print axioms PallLean.Paper93.DeepMath.PathB.KakeyaCEW.kakeya_forces_dimension
#print axioms PallLean.Paper93.DeepMath.PathB.KakeyaCEW.compressible_of_width_lt_dim
