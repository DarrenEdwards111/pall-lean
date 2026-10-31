import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEnumerableNTM

/-!
# Enumerable NTM: the boundary-complement cost bound

The nondeterministic time hierarchy (socket 1 for Williams) is built by lazy diagonalisation: the diagonaliser *shifts*
(a clocked simulation, done in `…EnumerableNTMUniversal`) at all but one input, and at the single **boundary** input it
must compute the **complement** `¬(machine e accepts x)` — a co-nondeterministic check, done by *exhaustively* searching
all reachable configurations.  This file bounds that search: with branching factor `≤ B`, machine `e` reaches at most
`B^k` configurations in `k` steps, so the boundary complement costs `≤ B^{tb x}`.

  `length_flatMap_le` — **PROVED**: `|l.flatMap f| ≤ |l|·B` when every `|f x| ≤ B`.
  `reach_length_le` — **PROVED**: with branching `≤ B`, `|reach e c k| ≤ B^k` — the number of configurations reachable in
        `k` steps grows at most geometrically.
  `accept_search_bound` — **PROVED**: the accept decision (hence its complement) examines at most `B^{tb x}` reachable
        configurations at the horizon `tb x`.

## Honest scope — the cost that forces `NTIME[f] ⊊ NTIME[g]`

This quantifies the exhaustive boundary complement: `B^{tb}` configurations.  That is exactly the quantity the padded
outer clock `g` must accommodate (`g ≳ B^{f}`) while the inner clock `f` cannot — the room that makes the lazy diagonal a
*genuine* new language, giving `NTIME[f] ⊊ NTIME[g]`.  What remains for the socket: wiring this cost bound into a concrete
padded clock pair `(f, g)` and realising the boundary complement as an actual machine within budget `g` (the
universal-simulation-with-overhead already supplies the shift).  That final wiring is the remaining piece; it is the same
`≈ Williams' algorithm` universal-machine content the memory flags.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.EnumerableNTM

/-- **`flatMap` length bound (proved)**: if every image list has length `≤ B`, then `|l.flatMap f| ≤ |l|·B`. -/
theorem length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) (B : ℕ)
    (hf : ∀ x, (f x).length ≤ B) : (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul,
      Nat.add_comm (t.length * B) B]
    exact Nat.add_le_add (hf a) ih

/-- **Reachable-configuration count bound (proved)**: with branching factor `≤ B` (every `nsucc e c` has length `≤ B`),
machine `e` reaches at most `B^k` configurations in `k` steps. -/
theorem reach_length_le (nsucc : ℕ → ℕ → List ℕ) (e B : ℕ)
    (hB : ∀ c, (nsucc e c).length ≤ B) (c k : ℕ) :
    (reach nsucc e c k).length ≤ B ^ k := by
  induction k with
  | zero => simp [reach]
  | succ k ih =>
    rw [reach, pow_succ]
    exact le_trans (length_flatMap_le _ _ B hB) (Nat.mul_le_mul ih (le_refl B))

/-- **The boundary-complement search bound (proved)**: computing whether machine `e` accepts `x` within `tb x` steps
(and hence its complement) examines at most `B^{tb x}` reachable configurations — the cost of the single lazy-diagonal
boundary complement. -/
theorem accept_search_bound (nsucc : ℕ → ℕ → List ℕ) (e B : ℕ)
    (hB : ∀ c, (nsucc e c).length ≤ B) (c tbx : ℕ) :
    (reach nsucc e c tbx).length ≤ B ^ tbx :=
  reach_length_le nsucc e B hB c tbx

end PallLean.Paper93.DeepMath.PathB.EnumerableNTM

#print axioms PallLean.Paper93.DeepMath.PathB.EnumerableNTM.length_flatMap_le
#print axioms PallLean.Paper93.DeepMath.PathB.EnumerableNTM.reach_length_le
#print axioms PallLean.Paper93.DeepMath.PathB.EnumerableNTM.accept_search_bound
