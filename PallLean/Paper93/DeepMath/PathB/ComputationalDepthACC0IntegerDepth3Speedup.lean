import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0IntegerPolynomialCRT
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Mod6SymAndDepth2

/-!
# Integer route, depth 3: composite `MOD∘MOD∘AND` is exactly SAT-searchable (PROVED)

The integer/CRT route composes past depth 2.  `ACC0ExactQuasipolyModTop` did depth-2 `MOD_M∘AND_w`
(exact + quasipoly + searchable, **composite** `M` via CRT — escaping the Razborov–Smolensky composite
barrier).  The CRT speedup `count_crt_sat_speedup` is **subcircuit-agnostic**: a top `MOD` over *any*
family is searchable in `< 2^n` count-residue cells.  Instantiating it with **depth-2 `MOD∘AND`**
subcircuits gives the depth-3 case:

  `modModAnd_depth3_sat_speedup` — a top `MOD_{∏qs}` gate over `m` subcircuits, each a
  `MOD_{M' j}∘AND` (depth 2), is exactly SAT-searchable over `< 2^n` count-residue cells (once
  `∏qs < 2^n`).

So the exact integer route — unlike the `F_p` polynomial method — reaches depth 3 with a **composite**
top modulus and **no approximation**: the top `MOD` reads the *single integer count* of true depth-2
subcircuits, CRT-decoded.

## What is proved (clean axioms, no `sorry`)

* `modModAnd_depth3_sat_speedup` — the depth-3 composite `MOD∘MOD∘AND` SAT-speedup (`< 2^n` cells).

## Honest scope

This is the **SAT-searchability** (Williams cash-out direction) for the depth-3 `MOD∘MOD∘AND` shape: the
top MOD reads the integer count of true depth-2 subcircuits, decoded by CRT — exact, composite modulus,
`< 2^n` cells.  It does **not** give a single quasipolynomial `SYM∘AND` representation of an *arbitrary*
constant-depth ACC⁰ circuit: that is the front-half wall (`ACC0IntegerPolynomialCRT`: ACC⁰ → exact
low-degree integer polynomial across depth), still open.  The searchability here counts cells of the
*top* gate; the subcircuits are evaluated, not themselves compressed.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0IntegerDepth3Speedup

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0IntegerPolynomialCRT
open PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2 (satCount)

variable {n : ℕ}

/-- **Depth-3 composite `MOD∘MOD∘AND` SAT-speedup (proved).**  A top `MOD_{∏qs}` (pairwise-coprime
`qs`) over `m` depth-2 subcircuits `g j = MOD_{M' j}∘AND` (each `x ↦ [satCount (mono j) x ≡ r j mod
M' j]`) is exactly SAT-searchable: the satisfiability of the count-decision is decided by a search over
the count-residue cells, of which there are `< 2^n` (when `∏qs < 2^n`).  Exact, composite top modulus,
no approximation — the integer route at depth 3. -/
theorem modModAnd_depth3_sat_speedup {m tt : ℕ} (qs : List ℕ) (co : qs.Pairwise Nat.Coprime)
    (hpos : ∀ i : Fin qs.length, 0 < qs.get i) (t : ℕ)
    (mono : Fin m → Fin tt → Finset (Fin n)) (M' : Fin m → ℕ) (r : Fin m → ℕ)
    (hregime : qs.prod < 2 ^ n) :
    ∃ G : ((i : Fin qs.length) → ZMod (qs.get i)) → Bool,
      (Satisfiable
            (modCountDecision qs t (fun j x => decide (satCount (mono j) x % M' j = r j))) ↔
          ∃ v ∈ Finset.univ.image
              (countResVec qs (fun j x => decide (satCount (mono j) x % M' j = r j))), G v = true)
        ∧ (Finset.univ.image
            (countResVec qs (fun j x => decide (satCount (mono j) x % M' j = r j)))).card < 2 ^ n :=
  count_crt_sat_speedup qs co hpos t
    (fun j x => decide (satCount (mono j) x % M' j = r j)) hregime

/-!
**Depth-3 integer-route speedup proved.**  The exact CRT count-decode composes a top composite `MOD`
over depth-2 `MOD∘AND` subcircuits into a `< 2^n`-cell SAT search — exact, composite modulus, no
approximation.  The general quasipoly `SYM∘AND` of an *arbitrary* constant-depth ACC⁰ circuit (the
front-half integer-polynomial-across-depth wall) is untouched.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0IntegerDepth3Speedup

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0IntegerDepth3Speedup.modModAnd_depth3_sat_speedup
