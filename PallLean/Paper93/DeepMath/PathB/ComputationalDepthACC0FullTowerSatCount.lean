import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FullTowerSat

/-!
# The `#SAT` counting bridge: `#accepting = #{frep-residue 1}` (PROVED)

The counting form of the acceptance characterization — the quantity a `#SAT`-counter computes.  Embedding
Boolean inputs `Fin n → Bool` into `ℤ` (`boolEmbed`), `accept_iff` lifts pointwise to a count equality:

  `accept_count_eq` — `#{x : Bool^n | circuit accepts} = #{x : Bool^n | p^{2^k} ∣ eval x (frep t) − 1}`.

So the circuit's satisfying-count equals the number of Boolean inputs at which the sparse low-degree
polynomial `frep` has residue `1` mod `p^{2^k}` — the exact `#SAT` quantity a `SYM∘AND` counter evaluates.
(This is the counting *object*; the sub-`2^n` algorithm to compute it is the algorithmic half.)

## What is proved (clean axioms, no `sorry`)

* `boolEmbed` — `Fin n → Bool` ↪ `Fin n → ℤ` (`true ↦ 1`, `false ↦ 0`).
* `accept_count_eq` — `#accepting = #{frep-residue 1}` over Boolean inputs.

## Honest scope

The `#SAT` counting object (a `card` equality from `accept_iff`).  The **fast** counter (sub-`2^n` via the
sparse `SYM∘AND` structure) and the `NEXP ⊄ ACC⁰` contradiction are the algorithmic half —
Williams-strength, **not** built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0FullTowerSatCount

open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB.ACC0FullTowerDegree (FTower frep)
open PallLean.Paper93.DeepMath.PathB.ACC0FullTowerEvalBridge (bval)
open PallLean.Paper93.DeepMath.PathB.ACC0FullTowerSat (LeavesBoolAt accept_iff)

variable {n : ℕ}

/-- Embed a Boolean input into `ℤ`: `true ↦ 1`, `false ↦ 0`. -/
def boolEmbed (x : Fin n → Bool) : Fin n → ℤ := fun i => if x i then 1 else 0

/-- **`#SAT` counting bridge (proved): `#accepting = #{frep-residue 1}` over Boolean inputs.**  The
circuit's satisfying-count equals the number of Boolean inputs where the sparse low-degree polynomial
`frep` has residue `1` mod `p^{2^k}`. -/
theorem accept_count_eq (p k : ℕ) [Fact p.Prime] (t : FTower (Fin n))
    (hbool : ∀ x : Fin n → Bool, LeavesBoolAt (boolEmbed x) t) :
    (univ.filter (fun x : Fin n → Bool => bval p (boolEmbed x) t = 1)).card
      = (univ.filter (fun x : Fin n → Bool =>
          (p : ℤ) ^ (2 ^ k) ∣ (eval (boolEmbed x) (frep p k t) - 1))).card := by
  classical
  congr 1
  exact Finset.filter_congr (fun x _ => (accept_iff p k (boolEmbed x) t (hbool x)).symm)

/-!
**`#SAT` counting bridge proved.**  `#accepting = #{frep-residue 1}` — the satisfying-count *is* the count
of Boolean inputs with `frep`-residue `1`, the object a `SYM∘AND` `#SAT`-counter evaluates.  The sub-`2^n`
algorithm and the `NEXP ⊄ ACC⁰` contradiction remain the Williams-strength algorithmic half.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0FullTowerSatCount

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FullTowerSatCount.accept_count_eq
