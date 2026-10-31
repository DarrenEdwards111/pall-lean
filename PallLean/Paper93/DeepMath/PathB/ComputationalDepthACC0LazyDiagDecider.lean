import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BoundedAcceptanceDecidable
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LazyDiagonalConstruction

/-!
# Entry 328 — the lazy-diagonal decision procedure, assembled from proved primitives (proved)

Entry 327 reduced the concrete nondeterministic time hierarchy to a single residual: a routing `TMachine` deciding the
lazy diagonal within the bigger bound `f`.  This file **builds the decision procedure itself** — the total computable
function the routing machine must realise — and verifies, against the *proved* primitives, what it computes in each of
its two cases.

**The decider.**  Over a machine enumeration (`machineEquiv : TMachine ≃ ℕ`) and an input encoding `inp : ℕ → List Bool`,
the `g`-clocked enumeration is `enumAccept g inp k m := decAccept (machineEquiv.symm k) (inp m) (g |inp m|)` — manifestly
*total and computable* because `decAccept` (entry 299) is the finite reachable-config search.  The lazy diagonal over it,
`lazyDiagDecide g inp := lazyDiagLang (enumAccept g inp)`, tiles `ℕ` into blocks `{2i, 2i+1}` (entry 302): **copy**
`enumAccept` on the next input at even positions, **complement** it at the odd boundary.

**The two cases, grounded in proved primitives.**

* **Copy (even `n`)** — `lazyDiagDecide g inp n = true ↔ acceptsWithin (toNTM (machine n/2)) (inp (n+1)) (g …)`: a genuine
  *nondeterministic acceptance* (realised by the universal simulation of 296–298, in `NTIME`), via
  `acceptsWithin_iff_decAccept` (entry 299).
* **Boundary (odd `n`)** — `lazyDiagDecide g inp n = true ↔ ¬ acceptsWithin (toNTM (machine n/2)) (inp (n−1)) (g …)`: the
  *decidable bounded complement* (entry 299, `boundary_complement_decidable`) — the one complement lazy diagonalisation
  affords.

## What is proved (clean axioms, no `sorry`)

* **`enumAccept`, `lazyDiagDecide`** — the decidable enumeration and the lazy-diagonal decision procedure (total `Bool`).
* **`lazyDiagDecide_copy`** (PROVED) — the copy case is exactly a nondeterministic acceptance.
* **`lazyDiagDecide_boundary`** (PROVED) — the boundary case is exactly the decidable complement.
* **`lazyDiagDecide_escapes`** (PROVED) — the decision procedure escapes the enumeration (entry 302), so it is the
  correct diagonal.

## Honest scope

This **builds and verifies the lazy-diagonal decision procedure** — the function the routing machine computes — grounding
each case in a proved primitive (copy = nondeterministic acceptance / universal simulation; boundary = the decidable
bounded complement, entry 299) and confirming it is the correct (escaping) diagonal.  What remains for the routing
`TMachine` of entry 327 is purely the **timing-aware compilation**: realising this explicit total function as one
transition table running within `f(|x|)` — the universal-simulation overhead (296–298) for the copy case and the
bounded search for the boundary case, routed by the trivial block arithmetic (`n % 2`, `n / 2`).  That transition-table
assembly is the lone remaining construction, **not built here and not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0LazyDiagDecider

open PallLean.Paper93.DeepMath.PathB.ACC0BoundedAcceptanceDecidable (decAccept acceptsWithin_iff_decAccept)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM machineEquiv)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (acceptsWithin)
open PallLean.Paper93.DeepMath.PathB.ACC0LazyDiagonalConstruction (lazyDiagLang lazyDiagLang_escapes)

/-- **The `g`-clocked decidable enumeration.**  Machine code `k` on the `inp`-encoded input `m`, run for `g |inp m|`
steps, decided by the finite reachable-config search `decAccept` (entry 299) — total and computable. -/
noncomputable def enumAccept (g : ℕ → ℕ) (inp : ℕ → List Bool) (k m : ℕ) : Bool :=
  decAccept (machineEquiv.symm k) (inp m) (g (inp m).length)

/-- **The lazy-diagonal decision procedure.**  The lazy diagonal (entry 302) over the decidable enumeration — a total
`Bool` function: copy on even positions, complement on the odd boundary.  (`noncomputable` only because the *enumeration*
`machineEquiv` is via a classical `TMachine ≃ ℕ`; each value is the decidable bounded search `decAccept`.) -/
noncomputable def lazyDiagDecide (g : ℕ → ℕ) (inp : ℕ → List Bool) : ℕ → Bool :=
  lazyDiagLang (enumAccept g inp)

/-- **The copy case is a nondeterministic acceptance (PROVED).**  At an even position `n`, the decider accepts iff the
`(n/2)`-th machine accepts the next encoded input `inp (n+1)` within `g`-time — realised by the universal simulation
(296–298), in `NTIME`. -/
theorem lazyDiagDecide_copy (g : ℕ → ℕ) (inp : ℕ → List Bool) (n : ℕ) (hn : n % 2 = 0) :
    lazyDiagDecide g inp n = true ↔
      acceptsWithin (toNTM (machineEquiv.symm (n / 2))) (inp (n + 1)) (g (inp (n + 1)).length) := by
  unfold lazyDiagDecide lazyDiagLang enumAccept
  rw [if_pos hn]
  exact (acceptsWithin_iff_decAccept _ _ _).symm

/-- **The boundary case is the decidable complement (PROVED).**  At an odd boundary position `n`, the decider accepts iff
the `(n/2)`-th machine *rejects* the encoded input `inp (n−1)` within `g`-time — the bounded complement decided by the
finite search (entry 299).  This is the single complement lazy diagonalisation affords. -/
theorem lazyDiagDecide_boundary (g : ℕ → ℕ) (inp : ℕ → List Bool) (n : ℕ) (hn : ¬ n % 2 = 0) :
    lazyDiagDecide g inp n = true ↔
      ¬ acceptsWithin (toNTM (machineEquiv.symm (n / 2))) (inp (n - 1)) (g (inp (n - 1)).length) := by
  unfold lazyDiagDecide lazyDiagLang enumAccept
  rw [if_neg hn, acceptsWithin_iff_decAccept]
  cases h : decAccept (machineEquiv.symm (n / 2)) (inp (n - 1)) (g (inp (n - 1)).length) <;> simp

/-- **The decision procedure is the correct diagonal (PROVED).**  `lazyDiagDecide g inp` escapes the enumeration
`enumAccept g inp` (entry 302), so it differs from every enumerated (decidable) language — the verified diagonal. -/
theorem lazyDiagDecide_escapes (g : ℕ → ℕ) (inp : ℕ → List Bool) :
    lazyDiagDecide g inp ∉ Set.range (enumAccept g inp) :=
  lazyDiagLang_escapes (enumAccept g inp)

/-!
**The decision procedure, built and verified.**  `lazyDiagDecide` is a total computable `Bool` function whose copy case
is a nondeterministic acceptance (`lazyDiagDecide_copy`, realised by universal simulation) and whose boundary case is the
decidable bounded complement (`lazyDiagDecide_boundary`, entry 299), and it escapes the enumeration
(`lazyDiagDecide_escapes`, the correct diagonal).  The routing `TMachine` of entry 327 must realise *this* function within
`f(|x|)`: the copy case via the clocked universal simulator (296–298), the boundary via the bounded search (299), routed
by `n % 2` / `n / 2`.  That transition-table compilation is the lone remaining construction.  Not faked, not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0LazyDiagDecider

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LazyDiagDecider.lazyDiagDecide_copy
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LazyDiagDecider.lazyDiagDecide_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LazyDiagDecider.lazyDiagDecide_escapes
