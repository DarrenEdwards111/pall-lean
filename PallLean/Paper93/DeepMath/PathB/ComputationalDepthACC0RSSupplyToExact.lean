import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SupplyConstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Amplification

/-!
# Plugging the RS supply into the amplification chain — supply ⇒ exact majority representation (proved)

This assembles the BT-side concentration/amplification pipeline (entries 209–215) into a single chain: a **per-input
`3/4` supply of approximant-functions** (the `Uniform34` output of the pointwise RS composition, entry 215) yields,
through the amplification (entry 212) and the majority-vote exactness (entry 206), an **exact** representation of the
target `f` as a majority vote of `2j` approximants — `MajVote g = f`.

The threading.  Take the supply elements to be approximant *functions* via an evaluation `ev : α → (Fin n → Bool) →
Bool`; "approximant `a` correct at input `x`" is `ev a x = f x`.  The entry-212 `exists_good_tuple` (applied to
`corr x a := decide (ev a x = f x)`) produces a tuple `g : Fin (2j) → α` whose majority is correct at every input
(`j < #{i | ev (g i) x = f x}`).  Mapping through `ev`, this is exactly the hypothesis of entry-206 `maj_exact`
(`2j < 2·#{i | (ev ∘ g) i x = f x}`), giving `MajVote (ev ∘ g) = f` — the exact representation.

## What is proved (clean axioms, no `sorry`)

* **`supply_to_exact_majority`** — the assembled chain: given a per-input `3/4` supply (`Uniform34` for the
  agreement-with-`f` predicate, `w ≥ 1`) at `k = 2j`, `j ≥ 3n+1`, there is a tuple `g : Fin (2j) → ((Fin n → Bool) →
  Bool)` of approximants with `MajVote g = f` — an exact representation of `f` as a majority of `2j` approximants.

## Honest scope

This proves the **assembly** completely — supply (entry 212) ∘ majority exactness (entry 206) ⇒ exact majority
representation `MajVote g = f` — in pure `Finset` counting.  Combined with the pointwise RS composition (entry 215,
which *produces* the `Uniform34` supply) and the per-point/gate machinery (209–214), this is the BT-side amplification
realised end to end: an `ACC⁰[p]` circuit `f` has an exact representation as a majority vote of low-degree
(`SYM∘AND`-encodable) approximants.  What this does **not** do: (i) collapse `MajVote g` of `2j` `SYM∘AND`s into a
*single* quasipolynomial `SYM∘AND` (the `MAJ∘SYM∘AND` step — needed for the entry-203 `btQuasipolyCollapse`/depth-collapse,
left as a separate structural step); (ii) it uses the entry-212 `Uniform34` (*exact* `3w`) rather than the genuine
`≥3/4` of entry 215 (the idealisation gap, a minor generalisation of `exists_good_tuple`).  This proves the
supply-to-exact-majority assembly, not the `MAJ∘SYM∘AND` collapse.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RSSupplyToExact

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0SupplyConstruction (Uniform34 exists_good_tuple)
open PallLean.Paper93.DeepMath.PathB.ACC0Amplification (MajVote maj_exact)

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- **Supply ⇒ exact majority representation (PROVED).**  Given a per-input `3/4` supply of approximant-functions
(`ev : α → (Fin n → Bool) → Bool`, with `Uniform34` for the agreement-with-`f` predicate `decide (ev a x = f x)` and
`w ≥ 1`), at `k = 2j` with `j ≥ 3n+1`, there is a tuple `g : Fin (2j) → ((Fin n → Bool) → Bool)` with `MajVote g = f` —
an exact representation of `f` as a majority of `2j` approximants.  The entry-212 `exists_good_tuple` gives a tuple
majority-correct at every input; mapping through `ev` feeds the entry-206 `maj_exact` (the majority of a
pointwise-majority-correct family is exact). -/
theorem supply_to_exact_majority (ev : α → (Fin n → Bool) → Bool) (f : (Fin n → Bool) → Bool)
    (j w : ℕ) (hu : Uniform34 (fun x a => decide (ev a x = f x)) w) (hw : 1 ≤ w)
    (hj : 3 * n + 1 ≤ j) :
    ∃ g : Fin (2 * j) → ((Fin n → Bool) → Bool), MajVote g = f := by
  obtain ⟨g, hg⟩ := exists_good_tuple (fun x a => decide (ev a x = f x)) j w hu hw hj
  refine ⟨fun i => ev (g i), ?_⟩
  apply maj_exact
  intro x
  have hgx := hg x
  have hcount : (Finset.univ.filter (fun i => ev (g i) x = f x)).card
      = (Finset.univ.filter (fun i => decide (ev (g i) x = f x) = true)).card := by
    congr 1
    apply Finset.filter_congr
    intro i _
    simp
  show 2 * j < 2 * (Finset.univ.filter (fun i => ev (g i) x = f x)).card
  omega

end PallLean.Paper93.DeepMath.PathB.ACC0RSSupplyToExact

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RSSupplyToExact.supply_to_exact_majority
