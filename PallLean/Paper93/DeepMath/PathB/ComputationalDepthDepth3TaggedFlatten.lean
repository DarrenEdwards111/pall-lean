import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPathLabel

/-!
# Block-DT model, F-independence step 2: the content-based stream re-encoding (branch `razborov-recoverRho-wip`)

The combinatorial heart of tightening the branching switching label space from the fuel-dependent `(4^w+1)^F`
to the **content-based** `(2·a+1)^k`.  A label stream is a `List (List α)` of **non-empty** blocks; its content
is the flattened length `k`.  We re-encode it by **tagging the first element of each block** `true` and every
other element `false`:

```
  taggedFlatten : List (List α) → List (α × Bool)
```

This map has length `= L.flatten.length` (the content `k`) and is **injective on non-empty-block streams** (the
`true` tags mark exactly the block boundaries, so the blocks are recovered by cutting at the tags).  So a
stream of content `k` injects into the length-`k` tagged lists, hence into `Fin k → Option (α × Bool)`, of
cardinality `(2·|α|+1)^k` — **independent of the number of blocks `F`**.

This is the re-encoding the block decoder needs: its label streams (`descentLabels`) have all-non-empty blocks
(brick 146) and flatten-length `pathLen`, so they inject into a `(2·|α|+1)^{pathLen}` space — `F`-independent,
the shape that (with the weight gain) yields the tight `((2p/(1-p))·O(w))^s` bound.

* `taggedFlatten` / `taggedFlatten_length` / `taggedFlatten_injective` — the re-encoding and its injectivity.
* `nonempty_block_streams_card_le` — content-`k` streams number `≤ (2·|α|+1)^k`, `F`-independently.

## Honest scope

This is the generic content-based re-encoding (`F`-independent cardinality).  Instantiating it at the
`descent`-label streams (`α = Fin w`, term-relative positions) and threading the per-content count through the
weight gain are the next bricks.  This delivers the combinatorial keystone; it is not yet wired to
`descentLabels`/`pweight`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

variable {α : Type*}

/-- Tag the first element of each block `true`, every other element `false`, and flatten.  (An empty block —
which never occurs on the streams we count — contributes nothing.) -/
def taggedFlatten : List (List α) → List (α × Bool)
  | [] => []
  | [] :: L => taggedFlatten L
  | (x :: xs) :: L => (x, true) :: (xs.map (fun a => (a, false)) ++ taggedFlatten L)

/-- The tagged flattening of a stream of **non-empty** blocks has length equal to the content. -/
theorem taggedFlatten_length :
    ∀ (L : List (List α)), (∀ b ∈ L, b ≠ []) →
      (taggedFlatten L).length = L.flatten.length
  | [], _ => rfl
  | [] :: _, h => absurd rfl (h [] (List.mem_cons_self ..))
  | (x :: xs) :: L, h => by
    have hL : ∀ c ∈ L, c ≠ [] := fun c hc => h c (List.mem_cons_of_mem _ hc)
    rw [taggedFlatten, List.flatten_cons, List.length_cons, List.length_append, List.length_append,
      List.length_map, taggedFlatten_length L hL, List.length_cons]
    omega

/-- The tagged flattening never begins with a `false`-tagged element. -/
theorem taggedFlatten_no_false_head :
    ∀ (L : List (List α)), (∀ b ∈ L, b ≠ []) →
      ∀ p ∈ (taggedFlatten L).head?, p.2 = true
  | [], _ => by intro p hp; simp [taggedFlatten] at hp
  | [] :: _, h => absurd rfl (h [] (List.mem_cons_self ..))
  | (x :: xs) :: L, _ => by
    intro p hp
    rw [taggedFlatten] at hp
    simp only [List.head?_cons, Option.mem_some_iff] at hp
    rw [← hp]

/-- Splitting two `false`-prefixed-then-`true` concatenations that agree: the `false` prefixes (the block
tails) and the remainders agree. -/
theorem tail_split (t1 t2 : List α) (r1 r2 : List (α × Bool))
    (hr1 : ∀ p ∈ r1.head?, p.2 = true) (hr2 : ∀ p ∈ r2.head?, p.2 = true)
    (heq : t1.map (fun a => (a, false)) ++ r1 = t2.map (fun a => (a, false)) ++ r2) :
    t1 = t2 ∧ r1 = r2 := by
  induction t1 generalizing t2 with
  | nil =>
    cases t2 with
    | nil => exact ⟨rfl, by simpa using heq⟩
    | cons y ys =>
      exfalso
      simp only [List.map_nil, List.nil_append, List.map_cons, List.cons_append] at heq
      have hh : r1.head? = some (y, false) := by rw [heq]; rfl
      have := hr1 (y, false) (by rw [hh]; rfl)
      simp at this
  | cons x xs ih =>
    cases t2 with
    | nil =>
      exfalso
      simp only [List.map_cons, List.cons_append, List.map_nil, List.nil_append] at heq
      have hh : r2.head? = some (x, false) := by rw [← heq]; rfl
      have := hr2 (x, false) (by rw [hh]; rfl)
      simp at this
    | cons y ys =>
      simp only [List.map_cons, List.cons_append] at heq
      obtain ⟨hxy, hrest⟩ := List.cons.inj heq
      have hxy' : x = y := (Prod.ext_iff.mp hxy).1
      obtain ⟨hts, hr⟩ := ih ys hrest
      exact ⟨by rw [hxy', hts], hr⟩

/-- **`taggedFlatten` is injective on non-empty-block streams.**  The `true` tags mark block boundaries, so the
blocks are recovered from the tagged list. -/
theorem taggedFlatten_injective :
    ∀ (L1 L2 : List (List α)),
      (∀ b ∈ L1, b ≠ []) → (∀ b ∈ L2, b ≠ []) →
      taggedFlatten L1 = taggedFlatten L2 → L1 = L2 := by
  intro L1
  induction L1 with
  | nil =>
    intro L2 _ h2 heq
    cases L2 with
    | nil => rfl
    | cons b2 L2' =>
      have hb2 : b2 ≠ [] := h2 b2 (List.mem_cons_self ..)
      obtain ⟨x2, xs2, rfl⟩ := List.exists_cons_of_ne_nil hb2
      simp [taggedFlatten] at heq
  | cons b1 L1' ih =>
    intro L2 h1 h2 heq
    have hb1 : b1 ≠ [] := h1 b1 (List.mem_cons_self ..)
    obtain ⟨x1, xs1, rfl⟩ := List.exists_cons_of_ne_nil hb1
    have hL1' : ∀ c ∈ L1', c ≠ [] := fun c hc => h1 c (List.mem_cons_of_mem _ hc)
    cases L2 with
    | nil => simp [taggedFlatten] at heq
    | cons b2 L2' =>
      have hb2 : b2 ≠ [] := h2 b2 (List.mem_cons_self ..)
      obtain ⟨x2, xs2, rfl⟩ := List.exists_cons_of_ne_nil hb2
      have hL2' : ∀ c ∈ L2', c ≠ [] := fun c hc => h2 c (List.mem_cons_of_mem _ hc)
      simp only [taggedFlatten] at heq
      obtain ⟨hhd, htl⟩ := List.cons.inj heq
      have hx : x1 = x2 := (Prod.ext_iff.mp hhd).1
      obtain ⟨hxs, hrec⟩ := tail_split xs1 xs2 (taggedFlatten L1') (taggedFlatten L2')
        (taggedFlatten_no_false_head L1' hL1') (taggedFlatten_no_false_head L2' hL2') htl
      rw [hx, hxs, ih L2' hL1' hL2' hrec]

/-- **Content-`k` non-empty-block streams number at most `(2·|α|+1)^k`.**  They inject into
`Fin k → Option (α × Bool)` via `taggedFlatten`'s `getElem?` profile — a bound independent of the number of
blocks. -/
theorem nonempty_block_streams_card_le [Fintype α] [DecidableEq α] (k : ℕ)
    {S : Finset (List (List α))}
    (hne : ∀ L ∈ S, ∀ b ∈ L, b ≠ []) (hlen : ∀ L ∈ S, L.flatten.length = k) :
    S.card ≤ (2 * Fintype.card α + 1) ^ k := by
  classical
  have hcard : Fintype.card (Fin k → Option (α × Bool)) = (2 * Fintype.card α + 1) ^ k := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_option, Fintype.card_prod,
      Fintype.card_bool]
    ring
  rw [← hcard, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn
    (fun L => fun i : Fin k => (taggedFlatten L)[i.1]?)
    (fun _ _ => Finset.mem_univ _) (fun L1 hL1 L2 hL2 heq => ?_)
  have h1 : (taggedFlatten L1).length = k := by
    rw [taggedFlatten_length L1 (hne L1 hL1), hlen L1 hL1]
  have h2 : (taggedFlatten L2).length = k := by
    rw [taggedFlatten_length L2 (hne L2 hL2), hlen L2 hL2]
  have htf : taggedFlatten L1 = taggedFlatten L2 := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < k
    · exact congrFun heq ⟨i, hi⟩
    · rw [List.getElem?_eq_none (by rw [h1]; omega), List.getElem?_eq_none (by rw [h2]; omega)]
  exact taggedFlatten_injective L1 L2 (hne L1 hL1) (hne L2 hL2) htf

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.nonempty_block_streams_card_le
