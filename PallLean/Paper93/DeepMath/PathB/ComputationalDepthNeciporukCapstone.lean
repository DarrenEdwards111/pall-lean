import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukCountingLemma
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukOptimalBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukSkeletonNoGo

/-!
# Nečiporuk capstone — the `n²/log n` formula-size lower bound, with its ceiling

This file collects, under clean citable names, the **unconditional, `sorry`-free, custom-axiom-free**
Nečiporuk formula-size lower bounds established in the corpus: the general method (`∑ log₂` of per-block
subfunction counts lower-bounds the leaf count), the explicit hard function attaining the classical
`Ω(N²/log N)` rate, and the honest **no-go / ceiling** showing the method tops out there and does not reach
`TC⁰`/`NC¹`/width-5 branching programs.

Each capstone name is verified by `#print axioms` to depend on **only** `propext`, `Classical.choice`,
`Quot.sound` — complete proofs, not conditional shells.

## The capstone theorems (all PROVED, clean-axiom, no `sorry`)

* **`neciporuk_method`** (`= neciporuk_formula_lower_bound`) — the Nečiporuk method: for any partition of
  the variables into disjoint blocks, `∑ᵢ log₂ (#blockResiduals S_i F) ≤ 2·⌈log₂(16+2n+1)⌉·litCount F +
  2·#blocks`, i.e. `litCount F ≥ (∑ᵢ log₂ c_i − 2·#blocks) / (2·⌈log₂(16+2n)⌉)`. No carried hypotheses.
* **`neciporuk_method_opt`** (`= neciporuk_formula_lower_bound_opt`) — the rewired optimal form with a
  *constant* `4` per leaf: `∑ᵢ log₂ (#blockResiduals S_i F) ≤ 4·litCount F + #blocks`.
* **`neciporuk_n2_over_logn`** (`= NecHard.hardF_rate_sq_opt`) — the explicit hard function `hardF` on
  `N = nn b m` variables: any `B₂` (De Morgan) formula computing it has `litCount F ≥ N²/(64·b)` with
  `b ≈ log₂ N`, i.e. `Ω(N²/log N)`.
* **`neciporuk_n2_over_logn_family`** (`= NecHard.hardF_rate_opt_family`) — the headline family form: for
  every `b ≥ 5` there is a block count `m` with the `Ω(N²/log N)` bound on `hardF`.
* **`neciporuk_skeleton_nogo`** (`= freeCount_unbounded_by_leavesIn`) — the honest no-go: the number of
  maximal `S`-free subtrees is *not* bounded by any function of the in-block leaf count, so the naive
  skeleton bound cannot yield a constant-per-leaf subfunction bound. (Records why the method's constant is
  delicate, and — with the corpus's `neciporuk_sum` ceiling analysis — why Nečiporuk tops out at
  `Θ(N²/log N)`.)

## Honest scope

Nečiporuk's method is a **restricted** lower bound — it proves `Ω(N²/log N)` formula-size (De Morgan /
`B₂`) lower bounds for explicit functions, and **provably tops out at `Θ(N²/log N)`**: it does not reach
`TC⁰`, `NC¹`, or width-5 branching programs (the crossing-capacity bridge to those classes is *false*,
recorded in the corpus). It is real classical mathematics, machine-checked, custom-axiom-free — and it is
**not** a super-polynomial bound and **not** `P ≠ NP`. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. See
`NECIPORUK_CAPSTONE.md` and the master ledger `PRIME_ACC0_CAPSTONE.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NeciporukCapstone

/-- The Nečiporuk method (base form, `clog₂` denominator): the summed per-block log-subfunction-count
lower-bounds the leaf count. -/
alias neciporuk_method := PallLean.Paper93.DeepMath.PathB.neciporuk_formula_lower_bound

/-- The Nečiporuk method, optimal rewired form (constant `4` per leaf). -/
alias neciporuk_method_opt := PallLean.Paper93.DeepMath.PathB.neciporuk_formula_lower_bound_opt

/-- Explicit `Ω(N²/log N)` De Morgan formula-size lower bound for `hardF` (per-parameter form). -/
alias neciporuk_n2_over_logn := PallLean.Paper93.DeepMath.PathB.NecHard.hardF_rate_sq_opt

/-- Explicit `Ω(N²/log N)` De Morgan formula-size lower bound for `hardF` (headline family form). -/
alias neciporuk_n2_over_logn_family := PallLean.Paper93.DeepMath.PathB.NecHard.hardF_rate_opt_family

/-- The honest no-go: `freeCount` is not bounded by `leavesIn`, so the naive skeleton bound cannot give a
constant-per-leaf subfunction bound. -/
alias neciporuk_skeleton_nogo := PallLean.Paper93.DeepMath.PathB.freeCount_unbounded_by_leavesIn

end PallLean.Paper93.DeepMath.PathB.NeciporukCapstone

#print axioms PallLean.Paper93.DeepMath.PathB.NeciporukCapstone.neciporuk_method
#print axioms PallLean.Paper93.DeepMath.PathB.NeciporukCapstone.neciporuk_method_opt
#print axioms PallLean.Paper93.DeepMath.PathB.NeciporukCapstone.neciporuk_n2_over_logn
#print axioms PallLean.Paper93.DeepMath.PathB.NeciporukCapstone.neciporuk_n2_over_logn_family
#print axioms PallLean.Paper93.DeepMath.PathB.NeciporukCapstone.neciporuk_skeleton_nogo
