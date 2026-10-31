import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LayeredCarryDegree

/-!
# Depth-2 cross-modulus — outer MOD₃ fed by inner MOD₂: staged composition works; flattening is the wall

The smallest depth-2 hard case (entry 248 localized the wall to depth-≥2 nesting): an **outer `MOD_3` gate fed by inner
`MOD_2` outputs**.  The core question: *can the product-observer states compose through the outer `MOD_3` without
representing `MOD_2` over `F_3`?*

**The answer is yes — at the staged level (PROVED).**  Each layer is low-degree over its *own* field, and the outer
gate reads the inner *output bits*:

* **Inner `MOD_2`** is degree `≤ 1` over `F_2` in its inputs (`inner_mod2_deg_le_one`, entry-242 `modpIndicator` at
  `p = 2`).
* **Outer `MOD_3`** is degree `≤ 2` over `F_3` *in the inner bits* (`outer_mod3_deg_le_two`, entry-242 at `p = 3`,
  `p-1 = 2`), and it *reads those bits* via the `F_3` polynomial `1 - (∑ bᵢ)^2` (`outer_mod3_eval` computes
  `[#true inner bits ≡ 0 mod 3]`).

So the outer gate **never arithmetizes `MOD_2` over `F_3`**: it consumes the inner bits (already-computed Boolean
readouts) and applies a degree-2 `F_3` polynomial *to those bits*.  The staged (depth-2) representation is low-degree
*per layer*, over the respective fields — the product observer composes through the outer `MOD_3` with no collapse.

**Where the wall actually is: flattening (socket).**  `MOD_2`-over-`F_3` is forced *only* by **flattening** the depth-2
structure into a *single* `F_3` polynomial in the *original* inputs: substituting `bᵢ = MOD_2(inputs)` into the degree-2
`F_3` polynomial composes degree `2 × deg_{F_3}(MOD_2)`, and `MOD_2` (parity) is high-degree over `F_3` (Smolensky,
entry 244).  So the obstruction is **not** the staged composition (which works); it is the **depth-reduction to a single
`SYM∘AND` over one field** — the Beigel–Tarui flattening — which is exactly the original `ApproxToExactCount` wall.

⚠️ **No crossing.**  The staged per-layer low-degree facts are proved.  Whether a *staged / multi-sorted* fast-SAT
(entry 246, whose counting budget composes) can consume the depth-2 staged observer *without* flattening — thereby
avoiding the Smolensky-blocked single-field representation — is the open `ACC⁰[composite]` core (entry-238
`CarryRefinementCrossing`).  Not built here.

## What is proved (clean axioms, no `sorry`)

* **`inner_mod2_deg_le_one`** (PROVED) — the inner `MOD_2` gate is degree `≤ 1` over `F_2` (entry-242 `modpIndicator`,
  `p = 2`).
* **`outer_mod3_deg_le_two`** (PROVED) — the outer `MOD_3` gate is degree `≤ 2` over `F_3` *in the inner bits*
  (entry-242, `p = 3`).
* **`outer_mod3_reads_inner_bits`** (PROVED) — the outer `MOD_3` polynomial, evaluated on the inner bits over `F_3`,
  computes `[count of true inner bits ≡ 0 mod 3]` (entry-242 `modpIndicator_eval`): it reads the bits, no
  `MOD_2`-over-`F_3`.

## Honest scope

The proved content shows the depth-2 staged representation is low-degree *per layer over its own field*, and the outer
gate reads the inner *bits* — so the product observer **composes through the outer `MOD_3` without representing `MOD_2`
over `F_3`** (the staged route works).  The `MOD_2`-over-`F_3` collapse is forced only by *flattening* to a single-field
`SYM∘AND` (the BT depth-reduction), which is Smolensky-blocked (entry 244) and is the open `ACC⁰[composite]` core.  This
file does not build the staged-fast-SAT-without-flattening crossing.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Depth2CrossModulus

open PallLean.Paper93.DeepMath.PathB.ACC0LayeredCarryDegree

/-- **Inner `MOD_2` is degree `≤ 1` over `F_2` (PROVED).**  The inner gate is low-degree over its own field
(entry-242 `modpIndicator` at `p = 2`, `p - 1 = 1`). -/
theorem inner_mod2_deg_le_one (s : ℕ) :
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    (modpIndicatorPoly s 2).totalDegree ≤ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h := modpIndicator_totalDegree_le s 2
  simpa using h

/-- **Outer `MOD_3` is degree `≤ 2` over `F_3` in the inner bits (PROVED).**  The outer gate is low-degree over its own
field `F_3` *as a function of the inner output bits* (entry-242 at `p = 3`, `p - 1 = 2`) — it does **not** arithmetize
`MOD_2` over `F_3`. -/
theorem outer_mod3_deg_le_two (s : ℕ) :
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    (modpIndicatorPoly s 3).totalDegree ≤ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h := modpIndicator_totalDegree_le s 3
  simpa using h

/-- **The outer `MOD_3` reads the inner bits (PROVED).**  Evaluated on the inner output bits over `F_3`, the outer
polynomial computes `[count of true inner bits ≡ 0 mod 3]` (entry-242 `modpIndicator_eval`): the outer gate consumes the
already-computed inner bits via a degree-2 `F_3` polynomial — no `MOD_2`-over-`F_3` arithmetization. -/
theorem outer_mod3_reads_inner_bits (s : ℕ) (b : Fin s → Bool) :
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    MvPolynomial.eval (fun i => boolToZMod 3 (b i)) (modpIndicatorPoly s 3)
      = if countSum s 3 b = 0 then 1 else 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact modpIndicator_eval s 3 b

/-!
**The flattening socket (named, not proved).**  The staged depth-2 representation above is low-degree per layer (inner
`MOD_2` over `F_2`, outer `MOD_3` over `F_3` reading the inner bits), with no `MOD_2`-over-`F_3`.  The collapse is forced
*only* by flattening to a single `F_3` polynomial in the original inputs (substituting `bᵢ = MOD_2(inputs)`), which
arithmetizes the high-degree `MOD_2` over `F_3` — Smolensky-blocked (entry 244).  Whether a staged / multi-sorted
fast-SAT (entry 246) can consume the depth-2 staged observer *without* flattening is the open `ACC⁰[composite]` core
(entry-238 `CarryRefinementCrossing`).  Not built here.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0Depth2CrossModulus

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Depth2CrossModulus.inner_mod2_deg_le_one
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Depth2CrossModulus.outer_mod3_deg_le_two
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Depth2CrossModulus.outer_mod3_reads_inner_bits
