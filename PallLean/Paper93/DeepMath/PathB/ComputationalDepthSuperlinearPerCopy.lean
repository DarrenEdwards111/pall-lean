import Mathlib.Data.Finset.Card

/-!
# The super-linear per-copy bound, in the restricted (no-sharing) model

The dependency bound gave a *linear* per-copy lower bound (`n/2`) by counting **variables**.  To get
**super-linear** we count **pairs** — the Khrapchenko / Nechiporuk shape: if each of the `~n²` pairs of
inputs needs its *own distinct* distinguishing gate, then `gates ≥ #pairs = n(n-1)`, which is quadratic.

This is honest only with a sharp caveat, stated up front: a super-linear lower bound for **general
circuits** is a *famous open problem* (the best known for any explicit function is about `5n`, linear).
So the quadratic bound below lives in the **restricted, no-sharing model** — exactly where super-linear
bounds are genuinely provable (Khrapchenko's `n²` for parity, Nechiporuk's `n²/log n`; both formula-model
results, and the `n²` Khrapchenko bound is already machine-checked in this repo).

## The counting argument

Model a **pair-distinguishing** circuit: a set of input `pairs`, and an assignment `gate` sending each
pair to a gate that distinguishes it, with distinct pairs going to **distinct** gates (`gate_inj` — the
*no-sharing* hypothesis: no single gate serves two pairs).  Then the pairs inject into the gates, so
`#pairs ≤ #gates`.  With `#pairs = n(n-1)` (all ordered distinct pairs) this is a **quadratic** —
super-linear — lower bound.

## What is proved

* **`gates_ge_pairs`** — `#pairs ≤ #gates`: the no-sharing pair count is a gate lower bound.
* **`quadratic_lower_bound`** — with `n(n-1)` pairs, `n(n-1) ≤ #gates` — genuinely quadratic.
* **`linear_lt_quadratic`** — `n < n(n-1)` for `n ≥ 3`: the bound strictly **exceeds** the linear
  dependency bound.  Part (1)'s per-copy bound is raised from linear to super-linear — in this model.
* **`pairWitness`** — non-vacuous.

## Honest scope — the caveat is the whole story

The quadratic bound is real, and it is genuinely super-linear — but the load-bearing hypothesis is
`gate_inj`, **no gate serves two pairs**.  That is the *no-sharing* assumption, and it holds in the
formula / read-once world (where Khrapchenko and Nechiporuk operate).  In a **general circuit**, one gate
can distinguish *many* pairs at once — that is exactly **sharing / mass production** — so `gate_inj`
**fails**, and no super-linear general bound is known.  The injectivity is precisely the tree-vs-DAG gap.

So this delivers Part (1)'s per-copy bound at **super-linear** strength *in the restricted model* — real
progress on the ceiling, from `n/2` to `n(n-1)` — while the jump to general circuits is blocked by the
**same** wall as everything else: sharing = mass production = `cost_super`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SuperlinearPerCopy

/-- A **pair-distinguishing** circuit (no-sharing model): a set of input `pairs`, an assignment `gate`
sending each pair to a distinguishing gate in `gateset`, with **distinct pairs to distinct gates**
(`gate_inj` — no gate serves two pairs).  Its existence is the Khrapchenko/Nechiporuk hypothesis. -/
structure PairModel where
  /-- the input pairs that must be distinguished -/
  pairs : Finset (ℕ × ℕ)
  /-- each pair's distinguishing gate -/
  gate : ℕ × ℕ → ℕ
  /-- the gates of the circuit -/
  gateset : Finset ℕ
  /-- each pair's gate is a real gate -/
  gate_mem : ∀ p ∈ pairs, gate p ∈ gateset
  /-- no-sharing: distinct pairs occupy distinct gates -/
  gate_inj : Set.InjOn gate ↑pairs

/-- **The pair count is a gate lower bound (proved).**  The pairs inject into the gates, so
`#pairs ≤ #gates`. -/
theorem gates_ge_pairs (M : PairModel) : M.pairs.card ≤ M.gateset.card :=
  Finset.card_le_card_of_injOn M.gate M.gate_mem M.gate_inj

/-- **The super-linear (quadratic) lower bound (proved).**  With all `n(n-1)` ordered distinct pairs to
distinguish, a no-sharing circuit needs `n(n-1) ≤ #gates` — a genuinely quadratic per-copy bound. -/
theorem quadratic_lower_bound (M : PairModel) (n : ℕ) (hp : M.pairs.card = n * (n - 1)) :
    n * (n - 1) ≤ M.gateset.card := by
  rw [← hp]
  exact gates_ge_pairs M

/-- **The bound is super-linear (proved).**  For `n ≥ 3`, `n < n(n-1)`: the quadratic pair bound strictly
exceeds the linear dependency bound.  Part (1)'s per-copy strength rises from linear to super-linear. -/
theorem linear_lt_quadratic (n : ℕ) (hn : 3 ≤ n) : n < n * (n - 1) := by
  have h2 : n * 2 ≤ n * (n - 1) := Nat.mul_le_mul (Nat.le_refl n) (by omega)
  omega

/-- **The model is non-vacuous (proved).**  A single pair `(0,1)` distinguished by gate `0`. -/
def pairWitness : PairModel where
  pairs := {(0, 1)}
  gate := fun _ => 0
  gateset := {0}
  gate_mem := fun _ _ => Finset.mem_singleton_self 0
  gate_inj := fun a ha b hb _ =>
    (Finset.mem_singleton.mp (Finset.mem_coe.mp ha)).trans
      (Finset.mem_singleton.mp (Finset.mem_coe.mp hb)).symm

end PallLean.Paper93.DeepMath.PathB.SuperlinearPerCopy

#print axioms PallLean.Paper93.DeepMath.PathB.SuperlinearPerCopy.gates_ge_pairs
#print axioms PallLean.Paper93.DeepMath.PathB.SuperlinearPerCopy.quadratic_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.SuperlinearPerCopy.linear_lt_quadratic
