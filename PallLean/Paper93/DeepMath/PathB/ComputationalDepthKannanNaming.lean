import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSharingModelShannon

/-!
# The Kannan arc, stage 2: from anonymous to NAMED — the first hard function, Π₂ over circuits

Shannon (`SharingModelShannon`) produced an **anonymous** hard function: counting proves existence
and names nothing.  Kannan's move is to *name* one — take the **first** hard function in a fixed
enumeration — and observe that the naming has a *quantifier price*: the defining predicate needs
alternations, which is precisely why Kannan's function lives in the polynomial hierarchy (Σ₂ after
Karp–Lipton) and not below.  This file machine-checks the naming step in the arc's own model.

## What is proved

* **`enc` / `enc_inj`** — a fixed enumeration of all `n`-input Boolean functions (via
  `Fintype.equivFin`), injective.
* **`named_of_exists` / `named_hard_function`** — if any hard function exists (Shannon supplies
  this below the threshold), then there is a **unique** first hard function: `∃! f, IsFirstHard f`.
  The anonymous witness now has a name — *the* least-enumerated function no `L`-gate circuit
  computes.
* **`isFirstHard_pi2`** — the payoff, the **quantifier shape**: `IsFirstHard f` is equivalent to a
  prenex `∀ (c, g) … (… ∨ ∃ c', …)` statement — one universal over circuits and functions, one
  existential over circuits inside.  A genuine Π₂ shape over circuit space, machine-checked: being
  hard is `∀c` (no circuit works), being *first* adds "every earlier `g` has a small circuit" (`∃c'`).
  Naming costs one alternation — that is Kannan's engine.
* **`named_ten`** — concrete: there is a unique first hard 10-input function (needs > 10 gates).

## Honest scope — the naming is proved; the altitude machinery is the remaining arc

This is stage 2 of the Kannan arc (stage 1 = the Shannon counting).  What it does **not** yet give:
the enumeration here is definitional (`Fintype.equivFin`), not algorithmic, and the Π₂ *shape* is
over exponential-size objects (truth tables, circuits).  The remaining stages are the genuinely
open-scale part: (a) uniformize — relate this shape to the faithful machine hierarchy (Σ₂ semantics
over `ComposableMachine`, per-input-length families, an explicit truth-table order); (b) Karp–Lipton
casework to drop the altitude to Σ₂; (c) assembly: Σ₂ escapes size `n^k` for every fixed `k`.  And
the honest ceiling, stated up front: Kannan yields **fixed-polynomial** lower bounds at **Σ₂
altitude** — not superpolynomial, not `P`, not SAT.  It is the true measure of how far self-reference
has ever reached.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KannanNaming

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.SharingModelShannon

/-- `f` is **hard** at size `L`: no circuit of length `≤ L` computes it. -/
def IsHard (n L : ℕ) (f : BF n) : Prop :=
  ∀ c : List (CGate n), computes c f → L < c.length

/-- A fixed enumeration of all `n`-input Boolean functions. -/
noncomputable def enc (n : ℕ) : BF n → ℕ := fun f => ((Fintype.equivFin (BF n)) f).val

/-- The enumeration is injective. -/
theorem enc_inj (n : ℕ) : Function.Injective (enc n) := fun _ _ h =>
  (Fintype.equivFin (BF n)).injective (Fin.val_injective h)

/-- `f` is the **first hard function**: hard, and least in the enumeration among hard functions. -/
def IsFirstHard (n L : ℕ) (f : BF n) : Prop :=
  IsHard n L f ∧ ∀ g : BF n, IsHard n L g → enc n f ≤ enc n g

/-- **Naming (proved).**  If a hard function exists at all, the first hard function exists and is
unique.  The anonymous Shannon witness acquires a name. -/
theorem named_of_exists (n L : ℕ) (hex : ∃ f : BF n, IsHard n L f) :
    ∃! f : BF n, IsFirstHard n L f := by
  classical
  obtain ⟨f₀, hf₀⟩ := hex
  have hne : (Finset.univ.filter (fun f : BF n => IsHard n L f)).Nonempty :=
    ⟨f₀, Finset.mem_filter.mpr ⟨Finset.mem_univ f₀, hf₀⟩⟩
  obtain ⟨f, hf_mem, hf_min⟩ := Finset.exists_min_image _ (enc n) hne
  rw [Finset.mem_filter] at hf_mem
  refine ⟨f, ⟨hf_mem.2, fun g hg => hf_min g (Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg⟩)⟩, ?_⟩
  rintro f' ⟨hf'h, hf'min⟩
  exact enc_inj n (le_antisymm (hf'min f hf_mem.2)
    (hf_min f' (Finset.mem_filter.mpr ⟨Finset.mem_univ f', hf'h⟩)))

/-- **Naming below the Shannon threshold (proved).**  The counting bound supplies the hard function;
naming makes it unique. -/
theorem named_hard_function (n L : ℕ) (hcard : Fintype.card (Code n L) < 2 ^ 2 ^ n) :
    ∃! f : BF n, IsFirstHard n L f :=
  named_of_exists n L (shannon_exists n L hcard)

/-- **The quantifier shape (proved).**  `IsFirstHard` is a Π₂-shaped statement over circuit space:
one universal block (over circuits `c` and functions `g`), one inner existential (a small circuit
`c'` for each earlier `g`).  Hardness is `∀c`; *firstness* costs one more alternation — the price of
the name, and the engine of Kannan's theorem. -/
theorem isFirstHard_pi2 (n L : ℕ) (f : BF n) :
    IsFirstHard n L f ↔
      ∀ (c : List (CGate n)) (g : BF n),
        (computes c f → L < c.length) ∧
        (enc n f ≤ enc n g ∨ ∃ c' : List (CGate n), computes c' g ∧ c'.length ≤ L) := by
  constructor
  · rintro ⟨h1, h2⟩ c g
    refine ⟨h1 c, ?_⟩
    by_cases hg : IsHard n L g
    · exact Or.inl (h2 g hg)
    · right
      unfold IsHard at hg
      push_neg at hg
      exact hg
  · intro h
    constructor
    · intro c hc
      exact (h c f).1 hc
    · intro g hg
      rcases (h [] g).2 with hle | ⟨c', hc', hlen⟩
      · exact hle
      · exact absurd (hg c' hc') (by omega)

/-- **Concrete (proved).**  There is a unique first hard 10-input function — the named function that
no 10-gate circuit computes. -/
theorem named_ten : ∃! f : BF 10, IsFirstHard 10 10 f :=
  named_of_exists 10 10 hard_function_exists_ten

end PallLean.Paper93.DeepMath.PathB.KannanNaming

#print axioms PallLean.Paper93.DeepMath.PathB.KannanNaming.named_of_exists
#print axioms PallLean.Paper93.DeepMath.PathB.KannanNaming.isFirstHard_pi2
#print axioms PallLean.Paper93.DeepMath.PathB.KannanNaming.named_ten
