import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingComplexity

/-!
# The quantitative information-flow bound (capacity side)

Each crossing of boundary `b` carries the control state, i.e. `≤ log|State|` bits.  So the
**crossing sequence** — the states at the crossing times, a list of length `crossingCount(b)` over
`|State|` symbols — takes at most `(|State|+1)^{crossingCount(b)}` distinct values.  That is the
quantitative capacity of the boundary: crossings encode at most `crossingCount · log|State|` bits.

* `crossingSeq` / `crossingSeq_length` — the crossing sequence, whose length is the crossing count.
* `card_le_of_injOn_bounded_lists` — a family with pairwise-distinct length-`≤K` lists over `α` has
  size `≤ (|α|+1)^K` (padding each list to `Fin K → Option α`, which is injective).
* `crossing_info_capacity` — **the capacity bound**: a family of computations with pairwise-distinct
  crossing sequences at `b`, each crossing `b` at most `K` times, has size `≤ (|State|+1)^K`.
  Equivalently, exhibiting `N` distinct crossing behaviours forces some computation to cross `b` at
  least `log_{|State|+1} N` times.

## What this gives, and the honest gap

This is the **capacity** half of `crossingCount(b) ≥ (info across b) / log|State|`.  The other half —
that distinct cut-*behaviours* force distinct crossing *sequences* — is the crossing-sequence
cut-and-paste (Hennie) determinism, supplied here as the injectivity hypothesis rather than proved
(partial machinery exists: `crossing_state_repeat`, `no_rightward_repeat`).  With both halves,
`crossingCount ≥ log_{|State|+1}(distinct behaviours)` — the quantitative single-tape lower bound
that a flattening simulation cannot beat below the information floor.  Whether SAT sits above that
floor for all machines is the open separation.

Nothing here proves a separation or a lower bound for any concrete language.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

variable {M : Machine}

/-- **List capacity.**  A family indexed by `I` whose length-`≤K` lists over a finite type `α` are
pairwise distinct has size at most `(|α|+1)^K` — pad each list to a function `Fin K → Option α`. -/
theorem card_le_of_injOn_bounded_lists {α β : Type} [Fintype α] {I : Finset β}
    (f : β → List α) (K : ℕ)
    (hinj : Set.InjOn f ↑I) (hlen : ∀ i ∈ I, (f i).length ≤ K) :
    I.card ≤ (Fintype.card α + 1) ^ K := by
  classical
  have hle : I.card ≤ (Finset.univ : Finset (Fin K → Option α)).card := by
    apply Finset.card_le_card_of_injOn (fun i => fun j : Fin K => (f i)[j.val]?)
    · intro i _; exact Finset.mem_univ _
    · intro i hi i' hi' heq
      apply hinj hi hi'
      apply List.ext_getElem?
      intro n
      by_cases hn : n < K
      · have h := congrFun heq ⟨n, hn⟩
        simpa using h
      · push_neg at hn
        rw [List.getElem?_eq_none (le_trans (hlen i (Finset.mem_coe.mp hi)) hn),
            List.getElem?_eq_none (le_trans (hlen i' (Finset.mem_coe.mp hi')) hn)]
  calc I.card ≤ (Finset.univ : Finset (Fin K → Option α)).card := hle
    _ = (Fintype.card α + 1) ^ K := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_option, Fintype.card_fin]

/-- The crossing sequence: the control states at the crossing times of `b`, in time order. -/
noncomputable def crossingSeq (M : Machine) (c : Cfg M) (b T : ℕ) : List M.State :=
  ((crossingTimes M c b T).sort (· ≤ ·)).map (fun t => (run M t c).st)

/-- The crossing sequence's length is the crossing count. -/
theorem crossingSeq_length (c : Cfg M) (b T : ℕ) :
    (crossingSeq M c b T).length = crossingCount M c b T := by
  unfold crossingSeq crossingCount
  rw [List.length_map, Finset.length_sort]

/-- **The quantitative information-flow capacity.**  A family of computations with pairwise-distinct
crossing sequences at `b`, each crossing `b` at most `K` times, has size at most `(|State|+1)^K`.  So
`N` distinct crossing behaviours force some computation to cross `b` at least `log_{|State|+1} N`
times — crossings carry at most `log|State|` bits each. -/
theorem crossing_info_capacity (b T K : ℕ) (I : Finset (Cfg M))
    (hinj : Set.InjOn (fun c => crossingSeq M c b T) ↑I)
    (hlen : ∀ c ∈ I, crossingCount M c b T ≤ K) :
    I.card ≤ (Fintype.card M.State + 1) ^ K := by
  refine card_le_of_injOn_bounded_lists (fun c => crossingSeq M c b T) K hinj ?_
  intro c hc
  rw [crossingSeq_length]
  exact hlen c hc

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
