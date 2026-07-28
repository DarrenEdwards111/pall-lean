import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKakeyaCEWWall
import Mathlib.Data.ZMod.Basic

/-!
# Wiring the approximate-degree method to Razborov–Smolensky: the AC⁰[p] separation, assembled

`ApproxDegreeParity` built the approximate-degree method (a complete real-degree bound for parity); the
honest caveat was that parity is the *wrong* witness over `F₂` (it is degree-1 there) and that the AC⁰[p]
obstruction is `F_p`-approximate degree.  This file states the genuine AC⁰[p] separation with the correct
witness (`MOD_q`, `q` coprime to `p`) as the composition of its two literature halves, proves the
assembly, and proves the *degree-lower-bound direction* concretely over `F_p`.

The two halves (each a real theorem of Razborov–Smolensky):
* **RS approximation** — every AC⁰[p] function has low `F_p`-approximate degree (the switching-lemma /
  probabilistic-polynomial step).  Socketed as the hypothesis `rs`.
* **Degree lower bound** — `MOD_q` does *not* have low `F_p`-approximate degree (Smolensky's spreading /
  counting step).  Socketed as the hypothesis `smolensky`.

## What is proved

* **`lowDeg_proper`** — over `F_p` (`p` prime) the exact degree-`≤ d` class is proper (`d < n`): the top
  monomial is outside it.  The degree-lower-bound *direction* is genuine over `F_p` — proved by reusing
  the multilinear-monomial independence of `KakeyaCEWWall` at `F = ZMod p`.
* **`modq_not_ac0p`** — the assembly: `rs ∧ smolensky ⟹ MOD_q ∉ AC⁰[p]`.

## Honest scope

The assembly is proved and `lowDeg_proper` is real, axiom-clean content.  The two halves are genuine,
established Razborov–Smolensky theorems, socketed here rather than re-proved — the switching lemma and the
`MOD_q` spreading bound are each substantial formalizations (the corpus's RS/ACC layer carries pieces).
This is a **restricted** separation (AC⁰[p], a constant-depth class), the correct home of the
approximate-degree method — **not** `P` vs `NP`, which is unrestricted.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RSWiring

open scoped BigOperators
open PallLean.Paper93.DeepMath.PathB.KakeyaCEWWall

variable {p n q d e : ℕ} [Fact (Nat.Prime p)]

/-- Boolean value embedded into `F_p`. -/
def boolToZMod (b : Bool) : ZMod p := if b then 1 else 0

/-- The `MOD_q` Boolean function: `1` iff the number of true inputs is divisible by `q`. -/
def MODq (q : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((∑ i : Fin n, if x i then 1 else 0) % q = 0)

/-- A Boolean function, viewed over `F_p`. -/
def embed (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → ZMod p := fun x => boolToZMod (f x)

/-- `f` has low `F_p`-approximate degree: it agrees with a degree-`≤ d` polynomial except on at most `e`
inputs. -/
def LowApproxDeg (d e : ℕ) (f : (Fin n → Bool) → ZMod p) : Prop :=
  ∃ g : (Fin n → Bool) → ZMod p, LowDeg d g ∧
    (Finset.univ.filter (fun x => f x ≠ g x)).card ≤ e

/-- **The degree-lower-bound direction is real over `F_p` (proved).**  For `d < n`, the top monomial is
not exactly degree-`≤ d` representable over `ZMod p` — reusing multilinear-monomial independence.  So a
`MOD_q`-style degree lower bound is not vacuous: functions of genuinely high `F_p`-degree exist. -/
theorem lowDeg_proper (hd : d < n) :
    ¬ LowDeg d (monoFn (Finset.univ : Finset (Fin n)) : (Fin n → Bool) → ZMod p) :=
  topMonomial_not_lowDeg hd

/-- **The AC⁰[p] separation, assembled (proved).**  From the RS approximation theorem (`rs`: every AC⁰[p]
function has low `F_p`-approximate degree) and the Smolensky degree lower bound (`smolensky`: `MOD_q` does
not), it follows that `MOD_q ∉ AC⁰[p]`. -/
theorem modq_not_ac0p (AC0p : ((Fin n → Bool) → ZMod p) → Prop)
    (rs : ∀ f, AC0p f → LowApproxDeg d e f)
    (smolensky : ¬ LowApproxDeg d e (embed (MODq q) : (Fin n → Bool) → ZMod p)) :
    ¬ AC0p (embed (MODq q)) :=
  fun h => smolensky (rs _ h)

end PallLean.Paper93.DeepMath.PathB.RSWiring

#print axioms PallLean.Paper93.DeepMath.PathB.RSWiring.lowDeg_proper
#print axioms PallLean.Paper93.DeepMath.PathB.RSWiring.modq_not_ac0p
