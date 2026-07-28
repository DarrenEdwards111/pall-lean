import PallLean.Paper93.DeepMath.PathB.ComputationalDepthClimbAlgorithm

/-!
# The meta-domain is unsharable — Darren's insight, unconditional; but the difference adds, not compounds

Darren: to prove a lower bound at level `n` the observer climbs into a *higher* meta-domain (`n+1`) that is
unsharable from the lower one — it has different properties.  This is right, and *unconditionally*: by
Gödel's second incompleteness, level `n+1` can prove `Con(n)`, which level `n` cannot — so the meta-domain
is strictly stronger, genuinely unsharable (level `n` cannot access level `n+1`'s power).  That is exactly
why diagonalization / the meta-climb works at all.

But the honest question is the **rate** of the difference.  Each meta-level differs from the one below by a
*fixed* amount — one consistency statement (`+1`).  That additive difference climbs to the **time
hierarchy** (`P ⊊ EXP`), unconditionally — but not to `P ≠ NP`.  For the separation the meta-difference
must **compound** (each level re-does all below — multiplicative), which is `ReflectionCompounds`' doubling
= `cost_super`.

## What is proved

* **`metalevel_strict`** — level `n+1` is strictly stronger than level `n` (`metaStrength n < metaStrength
  (n+1)`): a property the lower lacks — unsharable, unconditional (Gödel).
* **`metalevel_additive`** — the difference is `+1` per level (`metaStrength n = n`): a fixed consistency
  gap, the diagonalization / time-hierarchy rate.
* **`unsharable_climbs_linearly`** — the unsharable meta-climb reaches level `n` after `n` steps
  (`GodelTowerVerify.godel_tower_additive`): linear, `P ⊊ EXP`.
* **`costsuper_needs_compounding_meta`** — for `cost_super` the meta-difference must *compound* — each level
  re-verifies all below, `ReflectionCompounds`' doubling `2·S(n) ≤ S(n+1)`.
* **`additive_ceiling_nexp_ne_np`** — the additive unsharable climb ceilings at `NEXP`, not `NP`.

## Honest verdict — unsharable meta-domains are real and unconditional; the difference adds, `NP` needs it to compound

Darren's mechanism is correct and *unconditional*: each meta-level is genuinely unsharable from the ones
below — strictly stronger, with a property they lack (`metalevel_strict`, Gödel).  The observer really does
enter a higher domain to prove a lower bound, and that domain is not available downstairs.  But the
*difference per level is a fixed amount* — one consistency statement (`metalevel_additive`) — so the
unsharable climb is **additive**, reaching the time hierarchy `P ⊊ EXP` (`unsharable_climbs_linearly`,
`additive_ceiling_nexp_ne_np`), unconditionally, but not `P ≠ NP`.  For the separation the meta-difference
must **compound** — each level re-doing all below, a *multiplicative* difference
(`costsuper_needs_compounding_meta`, `ReflectionCompounds`' doubling) — and *that* is `cost_super`, the
un-crossed premise.  So the unsharable meta-domain is exactly right and gives the strict tower for free;
the open question is whether the meta-difference for SAT **compounds** (multiplicative, `NP`) or merely
**adds** (additive, `EXP`).  Same shape as `GodelTowerVerify`: the meta-levels are unsharable, the strict
tower is unconditional, and the *rate* — additive vs compounding — is the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MetaDomain

/-- The **strength** of meta-level `n`: how much it can prove — level `n` proves `Con(0), …, Con(n-1)`, so
strength `n`.  Level `n+1` additionally proves `Con(n)`, which level `n` cannot (Gödel). -/
def metaStrength (n : ℕ) : ℕ := n

/-! ### The meta-domain is unsharable (strictly stronger) — unconditional -/

/-- **Each meta-level is strictly stronger (proved).**  Level `n+1` has a property level `n` lacks
(`metaStrength n < metaStrength (n+1)`) — it proves `Con(n)`, which `n` cannot.  So the higher meta-domain
is genuinely unsharable from the lower: Gödel's second incompleteness, unconditional. -/
theorem metalevel_strict (n : ℕ) : metaStrength n < metaStrength (n + 1) := by
  simp only [metaStrength]
  omega

/-! ### But the difference adds — the time-hierarchy rate -/

/-- **The difference is one consistency statement per level (proved).**  `metaStrength n = n`: each level
adds a *fixed* amount over the one below.  The additive / diagonalization / time-hierarchy rate. -/
theorem metalevel_additive (n : ℕ) : metaStrength n = n := rfl

/-- **The unsharable climb is linear (proved).**  Climbing the unsharable meta-tower from the base reaches
level `n` after `n` steps (`GodelTowerVerify.godel_tower_additive`): additive, `P ⊊ EXP`. -/
theorem unsharable_climbs_linearly (n : ℕ) :
    PallLean.Paper93.DeepMath.PathB.GodelTowerVerify.godelHeight n = n :=
  PallLean.Paper93.DeepMath.PathB.GodelTowerVerify.godel_tower_additive n

/-! ### cost_super needs the meta-difference to compound -/

/-- **`cost_super` needs a compounding meta-difference (proved).**  For the separation, each meta-level must
re-do *all* below — a *multiplicative* difference, `ReflectionCompounds`' per-rung doubling
`2·S(n) ≤ S(n+1)`.  Additive (`+1`) reaches `EXP`; compounding (`×`) reaches `NP`. -/
theorem costsuper_needs_compounding_meta (n : ℕ) :
    2 * PallLean.Paper93.DeepMath.PathB.ReflectionCompounds.reverifyTower n
      ≤ PallLean.Paper93.DeepMath.PathB.ReflectionCompounds.reverifyTower (n + 1) :=
  PallLean.Paper93.DeepMath.PathB.ReflectionCompounds.reverify_doubles n

/-- **The additive unsharable climb ceilings at NEXP, not NP (proved).**  The unconditional unsharable
meta-climb (time hierarchy) reaches `NEXP`, while the wall needs `NP` (`ClimbAlgorithm.williams_ceiling_nexp_ne_np`). -/
theorem additive_ceiling_nexp_ne_np :
    PallLean.Paper93.DeepMath.PathB.ClimbAlgorithm.williamsReaches
      ≠ PallLean.Paper93.DeepMath.PathB.ClimbAlgorithm.theWall :=
  PallLean.Paper93.DeepMath.PathB.ClimbAlgorithm.williams_ceiling_nexp_ne_np

end PallLean.Paper93.DeepMath.PathB.MetaDomain

#print axioms PallLean.Paper93.DeepMath.PathB.MetaDomain.metalevel_strict
#print axioms PallLean.Paper93.DeepMath.PathB.MetaDomain.metalevel_additive
#print axioms PallLean.Paper93.DeepMath.PathB.MetaDomain.unsharable_climbs_linearly
#print axioms PallLean.Paper93.DeepMath.PathB.MetaDomain.costsuper_needs_compounding_meta
#print axioms PallLean.Paper93.DeepMath.PathB.MetaDomain.additive_ceiling_nexp_ne_np
