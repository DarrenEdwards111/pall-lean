import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDetTimeHierarchyRung3NTM

/-!
# An enumerable nondeterministic machine model — the foundation the lazy construction needs

The repo's `ACC0NTM.NTM` has a per-machine `Config : Type`, so the set of machines is **not enumerable** — and
diagonalisation needs an enumeration.  This file builds a genuinely **enumerable** nondeterministic machine model:
machines are `ℕ` codes under a *uniform* finite-branching transition, with a *decidable* bounded-acceptance predicate, so
each machine's language is a `Bool`-valued function indexed by its code.  It then connects this enumeration to rung 3's
lazy diagonaliser: the lazy diagonaliser **escapes every enumerable NTM's language**.

  `reach nsucc e c k` — the finite `List` of configurations reachable from `c` in exactly `k` steps of machine `e`
        (transition `nsucc e : config → List config`, finite branching → decidable, enumerable).
  `mem_reach_succ` / `reach_add` — **PROVED** model algebra: one-step unfolding, and reachability **composes**
        (`reach (a+b) ↔ ∃ intermediate reachable in a, then b`), the nondeterministic analogue of `ACC0NTM.reachIn_add`,
        now over an *enumerable* model.
  `nLang nsucc ninit naccept tb e x` — machine `e` accepts input `x` within `tb x` steps: a decidable `Bool`, so the
        language family `nLang … : ℕ → ℕ → Bool` is **enumerated by the machine code** `e`.
  `nLang_mono` — **PROVED**: more time only helps (`tb ≤ tb' ⇒ acceptance is preserved`).
  `lazy_diag_escapes_all_ntm` — **PROVED, the payoff**: no enumerable NTM computes the lazy diagonaliser of the
        enumerable-NTM language family — the diagonaliser escapes the whole class (rung 3 applied to this model).

## Honest scope

This supplies the **enumerable model** (machines as `ℕ` codes, uniform finite-branching transition, decidable bounded
acceptance) and the **escapes** direction over it — the property `ACC0NTM.NTM` lacked, now connected to the lazy
diagonaliser.  The transition/initial/accept (`nsucc`, `ninit`, `naccept`) are parameters: fixing a concrete Gödel
encoding of transitions into `nsucc` is routine additional work, and enumerability (machines = `ℕ` codes) holds for any
such encoding.  What is **not** done is the `NondetTimeHierarchy` socket's remaining machine content — the universal NTM
**simulation with overhead**: that the lazy diagonaliser is *itself* an enumerable NTM in `NTIME[g]` (the shift as a
clocked universal simulation of machine `e` on input `x+1`; the boundary complement by exhaustive search within the
padded budget), and the range width grown by a fast-growing padding `f` so `NTIME[f] ⊊ NTIME[g]`.  This file gives the
enumerable model + escapes; the universal-simulation-with-overhead is the remaining piece (the nondeterministic analogue
of the deterministic RAM interpreter, and the same "universal simulator" wall throughout).  Nothing here is
`NondetTimeHierarchy`, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.EnumerableNTM

open PallLean.Paper93.DeepMath.PathB.LazyDiagonalization

/-- Configurations reachable in exactly `k` steps of machine `e`, as a finite `List`.  A machine is a `ℕ` code; its
transition is `nsucc e : config → List config` (finite nondeterministic branching), so reachability is decidable and the
whole model is enumerable by the code `e`. -/
def reach (nsucc : ℕ → ℕ → List ℕ) (e : ℕ) : ℕ → ℕ → List ℕ
  | c, 0 => [c]
  | c, (k + 1) => (reach nsucc e c k).flatMap (nsucc e)

/-- One-step unfolding of reachability. -/
theorem mem_reach_succ (nsucc : ℕ → ℕ → List ℕ) (e c d k : ℕ) :
    d ∈ reach nsucc e c (k + 1) ↔ ∃ c', c' ∈ reach nsucc e c k ∧ d ∈ nsucc e c' := by
  simp [reach, List.mem_flatMap]

/-- **Reachability composes (proved)**: reachable in `a + b` steps iff reachable in `a` steps to some intermediate
configuration, then `b` more — the nondeterministic reachability algebra, over the enumerable model. -/
theorem reach_add (nsucc : ℕ → ℕ → List ℕ) (e c d a b : ℕ) :
    d ∈ reach nsucc e c (a + b) ↔ ∃ m, m ∈ reach nsucc e c a ∧ d ∈ reach nsucc e m b := by
  induction b generalizing d with
  | zero => simp [reach]
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 from rfl]
    simp only [reach, List.mem_flatMap]
    constructor
    · rintro ⟨c', hc', hd⟩
      obtain ⟨m, hm, hc'm⟩ := (ih c').mp hc'
      exact ⟨m, hm, c', hc'm, hd⟩
    · rintro ⟨m, hm, c', hc', hd⟩
      exact ⟨c', (ih c').mpr ⟨m, hm, hc'⟩, hd⟩

/-- The **language** of machine `e`: accept input `x` iff some accepting configuration is reachable within `tb x` steps.
Decidable (finite branching, bounded steps), so `nLang … : ℕ → ℕ → Bool` is a language family **enumerated by the machine
code** `e`.  `nsucc` = transition, `ninit` = initial configuration of the input, `naccept e` = accepting configurations
of machine `e`. -/
def nLang (nsucc : ℕ → ℕ → List ℕ) (ninit : ℕ → ℕ) (naccept : ℕ → ℕ → Bool) (tb : ℕ → ℕ)
    (e x : ℕ) : Bool :=
  (List.range (tb x + 1)).any (fun k => (reach nsucc e (ninit x) k).any (naccept e))

/-- **More time only helps (proved)**: enlarging the time bound preserves acceptance. -/
theorem nLang_mono (nsucc : ℕ → ℕ → List ℕ) (ninit : ℕ → ℕ) (naccept : ℕ → ℕ → Bool)
    (tb tb' : ℕ → ℕ) (h : ∀ x, tb x ≤ tb' x) (e x : ℕ) :
    nLang nsucc ninit naccept tb e x = true → nLang nsucc ninit naccept tb' e x = true := by
  simp only [nLang, List.any_eq_true, List.mem_range]
  rintro ⟨k, hk, hacc⟩
  exact ⟨k, by have := h x; omega, hacc⟩

/-- **The payoff (proved): the lazy diagonaliser escapes every enumerable NTM.**  No machine of the enumerable model
computes the lazy diagonaliser of the enumerable-NTM language family — it is not any enumerable NTM's bounded-acceptance
language.  This is rung 3's lazy diagonalisation applied to the concrete enumerable model. -/
theorem lazy_diag_escapes_all_ntm
    (nsucc : ℕ → ℕ → List ℕ) (ninit : ℕ → ℕ) (naccept : ℕ → ℕ → Bool) (tb : ℕ → ℕ) (L : ℕ) :
    ¬ ∃ e, ∀ x, nLang nsucc ninit naccept tb e x
        = diagonalizer (nLang nsucc ninit naccept tb) L x :=
  diagonalizer_not_enumerated (nLang nsucc ninit naccept tb) L

end PallLean.Paper93.DeepMath.PathB.EnumerableNTM

#print axioms PallLean.Paper93.DeepMath.PathB.EnumerableNTM.reach_add
#print axioms PallLean.Paper93.DeepMath.PathB.EnumerableNTM.nLang_mono
#print axioms PallLean.Paper93.DeepMath.PathB.EnumerableNTM.lazy_diag_escapes_all_ntm
