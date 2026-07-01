import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEnumerableNTM

/-!
# A universal machine for the enumerable NTM model — the shift side of `D ∈ NTIME[g]`

The enumerable NTM model (`…EnumerableNTM`) fixed machines as `ℕ` codes under a uniform transition `nsucc`.  This file
builds a **universal machine** for that model: one machine that simulates *any* machine `e` from *any* configuration.
The trick is a `Nat.pair` config encoding — the universal machine carries the simulated machine's code `e` alongside its
configuration `c` and steps via `nsucc e` — so simulation is **faithful with exact overhead `1`** (one universal step per
simulated step).

  `usucc` / `uaccept` — the universal machine's transition and accept predicate: on a config encoding `⟨e, c⟩`, step the
        simulated machine (`nsucc e c`, re-paired with `e`) and accept iff `naccept e c`.
  `usucc_reach` — **PROVED**: the universal machine reaches exactly the simulated configurations —
        `reach (usucc …) u (⟨e,c⟩) k = (reach nsucc e c k).map ⟨e, ·⟩` — for every machine `e`, config `c`, step count `k`.
        Exact overhead `1`.
  `usucc_accepts` — **PROVED**: acceptance is faithful — the universal machine accepts (from `⟨e, c⟩`, within `k`) iff
        machine `e` accepts (from `c`, within `k`).

This is the **shift side** of the lazy diagonaliser's `D ∈ NTIME[g]`: the shift `d(x) = M_e(x+1)` is exactly a universal
simulation of machine `e` on input `x+1`, and this file proves that simulation faithful and overhead-`1`.

## Honest scope

The overhead is `1` because the model's transition `nsucc` is applied *uniformly* — the universal machine gets `nsucc e`
"for free".  A fully concrete NTM with the transition table encoded on the tape would pay the standard per-step
table-lookup overhead (polynomial in the machine encoding) for universal simulation; that constant/polynomial factor is
abstracted here.  With that caveat, this is the universal-simulation-with-overhead the arc was blocked on, for the
nondeterministic model's **shift**.  What remains for the `NondetTimeHierarchy` socket: (i) the **boundary complement**
`d = !(M_e(first))` — the universal machine must exhaustively search all `≤ (branching)^t` paths and complement
(decidable, but it must fit the padded budget); (ii) the **range/padding** function `f` so `NTIME[g]` has room for that
exhaustive boundary complement while `NTIME[f]` does not, giving `NTIME[f] ⊊ NTIME[g]`.  This file supplies the universal
machine and the overhead-`1` shift simulation; the boundary-complement search + padding is the remaining piece.  Nothing
here is `NondetTimeHierarchy`, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.EnumerableNTM

/-- The **universal machine's transition**.  A configuration is a `Nat.pair` `⟨e, c⟩` of a simulated machine code `e` and
its configuration `c`; the universal machine steps the simulated machine (`nsucc e c`) and re-pairs each successor with
`e`. -/
def usucc (nsucc : ℕ → ℕ → List ℕ) (_u p : ℕ) : List ℕ :=
  (nsucc (Nat.unpair p).1 (Nat.unpair p).2).map (Nat.pair (Nat.unpair p).1)

/-- The **universal machine's accept predicate**: accept `⟨e, c⟩` iff machine `e` accepts config `c`. -/
def uaccept (naccept : ℕ → ℕ → Bool) (_u p : ℕ) : Bool :=
  naccept (Nat.unpair p).1 (Nat.unpair p).2

/-- **Faithful universal simulation, exact overhead `1` (proved)**: from the encoded configuration `⟨e, c⟩`, the
universal machine reaches in `k` steps exactly the configurations machine `e` reaches from `c` in `k` steps (re-paired
with `e`). -/
theorem usucc_reach (nsucc : ℕ → ℕ → List ℕ) (u e c k : ℕ) :
    reach (usucc nsucc) u (Nat.pair e c) k = (reach nsucc e c k).map (Nat.pair e) := by
  induction k generalizing c with
  | zero => simp [reach]
  | succ k ih =>
    simp only [reach, ih, List.map_flatMap, List.flatMap_map]
    apply List.flatMap_congr
    intro c' _
    simp [usucc, Nat.unpair_pair]

/-- **Faithful acceptance (proved)**: the universal machine accepts from `⟨e, c⟩` within `k` steps iff machine `e`
accepts from `c` within `k` steps — universal simulation preserves acceptance exactly. -/
theorem usucc_accepts (nsucc : ℕ → ℕ → List ℕ) (naccept : ℕ → ℕ → Bool) (u e c k : ℕ) :
    (reach (usucc nsucc) u (Nat.pair e c) k).any (uaccept naccept u)
      = (reach nsucc e c k).any (naccept e) := by
  rw [usucc_reach, List.any_map]
  congr 1
  funext c'
  simp [Function.comp, uaccept, Nat.unpair_pair]

end PallLean.Paper93.DeepMath.PathB.EnumerableNTM

#print axioms PallLean.Paper93.DeepMath.PathB.EnumerableNTM.usucc_reach
#print axioms PallLean.Paper93.DeepMath.PathB.EnumerableNTM.usucc_accepts
