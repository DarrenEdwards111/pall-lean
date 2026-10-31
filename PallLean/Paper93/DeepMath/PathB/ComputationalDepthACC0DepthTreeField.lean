import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SpanMulField

/-!
# A whole bounded-fan-in `AND`/`OR`/`NOT` circuit over `F_{p^k}` lies in the monomial-`AND` span (one theorem)

Packaging the depth recurrence as a *single* structural induction.  An `AndOrTree` is the AC⁰ de Morgan basis —
monomial-`AND` leaves combined by binary `AND`/`OR` and unary `NOT`.  Its degree `deg` adds over children, and its
`F`-evaluation `evalT` lies in the degree-`≤ deg` monomial-`AND` span (`evalT_mem_span`), proved by one induction on
the tree from the composition laws:

* leaf `S` — `sqfEval F S ∈ span(deg ≤ |S|)`;
* `AND` — `sqf_mul_mem_span` (product, degrees add);
* `OR` — De Morgan `1 − (1−a)(1−b)` via `sub_mem` + `sqf_mul_mem_span`;
* `NOT` — `1 − a` via `sub_mem`.

So *any* AC⁰ (de Morgan basis) circuit over the prime-power field `F_{p^k}`, built from `monoAND` leaves, lands in
the `SYM∘AND` bottom layer with degree `≤ deg` (for fan-in `2` and depth `d` with degree-`1` leaves, `deg ≤ 2^d`).
This is the bounded-fan-in BT recurrence as one theorem — the `MOD` gate (and *unbounded* fan-in / composite `MOD`)
are *not* included; that is the barrier.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact

open PallLean.Paper93.DeepMath.PathB.Layer4 (sqfEval)
open PallLean.Paper93.DeepMath.PathB.Layer3 (lowDegMonomials)

/-- A bounded-fan-in AC⁰ (de Morgan basis) circuit: `monoAND` leaves, binary `AND`/`OR`, unary `NOT`. -/
inductive AndOrTree (n : ℕ) where
  | leaf : Finset (Fin n) → AndOrTree n
  | andN : AndOrTree n → AndOrTree n → AndOrTree n
  | orN  : AndOrTree n → AndOrTree n → AndOrTree n
  | notN : AndOrTree n → AndOrTree n

namespace AndOrTree

variable {n : ℕ}

/-- The degree of the tree: leaf `= |S|`, internal nodes add (`NOT` preserves). -/
def deg : AndOrTree n → ℕ
  | leaf S => S.card
  | andN l r => deg l + deg r
  | orN l r => deg l + deg r
  | notN t => deg t

/-- The `F`-evaluation: `monoAND` leaf, product `AND`, De Morgan `OR`, complement `NOT`. -/
noncomputable def evalT (F : Type*) [Field F] : AndOrTree n → (Fin n → Bool) → F
  | leaf S => sqfEval F S
  | andN l r => evalT F l * evalT F r
  | orN l r => 1 - (1 - evalT F l) * (1 - evalT F r)
  | notN t => 1 - evalT F t

/-- **A whole AC⁰ (de Morgan) circuit lies in the degree-`≤ deg` monomial-`AND` span over `F_{p^k}` (proved).**
One structural induction over the tree from the composition laws. -/
theorem evalT_mem_span {F : Type*} [Field F] (t : AndOrTree n) :
    evalT F t ∈ Submodule.span F (sqfGens F n t.deg) := by
  induction t with
  | leaf S =>
    apply Submodule.subset_span
    refine ⟨⟨S, ?_⟩, rfl⟩
    simp [lowDegMonomials, Finset.mem_filter, deg]
  | andN l r ihl ihr => exact sqf_mul_mem_span ihl ihr
  | orN l r ihl ihr =>
    refine Submodule.sub_mem _ (one_mem_sqfSpan' _) (sqf_mul_mem_span ?_ ?_)
    · exact Submodule.sub_mem _ (one_mem_sqfSpan' _) ihl
    · exact Submodule.sub_mem _ (one_mem_sqfSpan' _) ihr
  | notN t iht => exact Submodule.sub_mem _ (one_mem_sqfSpan' _) iht

end AndOrTree

end PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact.AndOrTree.evalT_mem_span
