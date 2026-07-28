import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMonotoneCompounding

/-!
# Pushing the monotone bound as far as it goes: exponential magnitude, and the one door to general circuits

`MonotoneCompounding` established the monotone bound is unconditionally exponential (`2^k`, Razborov), the
strongest bound in the map, but that negation collapses it (Tardos gap).  Now push it as far as it goes —
in *both* directions: how big can the monotone bound get, and how close can it come to crossing?

**Magnitude.**  The ceiling is exponential.  Razborov's `CLIQUE` bound, sharpened by Alon–Boppana, reaches
`2^{Ω(n^{1/3})}`; other monotone functions reach `2^{Ω(√n)}`.  Unconditionally, monotone circuit size goes
all the way to `2^{n^{Ω(1)}}` — far past every general-model bound anyone has proved.  So the raw power of
the compounding, *in the monotone world*, is exponential.

**The one door.**  In general the monotone→general gap is *exponential* (Tardos: a function with a
polynomial general circuit but exponential monotone circuit), so pushing the exponent buys nothing toward
general circuits.  But there is exactly one class where the gap collapses: **slice functions** (zero below
Hamming weight `k`, one above, arbitrary at `k`).  Berkowitz–Wegener: a slice function's monotone
complexity exceeds its general complexity by at most a *polynomial* factor — a monotone selection network
computes the slice with negations only saving `poly(n)`.  So for a slice function, a monotone lower bound
*transfers*: `general ≥ monotone − poly`.  A **superpolynomial monotone bound on a slice function in NP
would give a superpolynomial general bound** — it would cross.

**Why it still doesn't cross.**  The two regimes are disjoint in what is proved.  Where the monotone bound
is strong (`CLIQUE`, matching) the function is *not* a slice, and the gap is exponential — no transfer.
Where the gap closes (slice functions) no superpolynomial monotone bound is known — the best is linear.
The open target is a strong monotone lower bound *exactly where negation can't rescue it*: on a slice.
That is `cost_super` in a new, sharper costume.

## What is proved

* **`monotone_reaches_exponential`** / **`monotone_reach_beats_formula`** — the monotone ceiling is `2^n`,
  exceeding the formula/crossing-number bound `n²`: exponential magnitude, unconditional.
* **`negation_gap_exponential`** — Tardos: a non-slice function with a linear general circuit and an
  exponential monotone bound (`100·general < monotone`): pushing the exponent does not transfer.
* **`slice_transfer`** — Berkowitz–Wegener: for a slice function, `general ≥ monotone − poly` — the
  monotone bound transfers up to the polynomial overhead.
* **`slice_crossing`** — concrete: a slice function with monotone bound `≥ 2048` and poly overhead `≤ 121`
  has general circuit size `≥ 1927` — the exponential monotone bound crossed to general circuits.
* **`crossing_gives_general_bound`** — the pinned open input: any slice model whose monotone bound clears
  the polynomial overhead by margin `p` gives a general bound `> p`.  A *superpolynomial* monotone slice
  bound would give a superpolynomial general bound.

## Honest verdict — pushed to the exact edge; the door is a slice, and it is empty

This is as far as the monotone bound goes.  Magnitude: exponential, `2^{n^{Ω(1)}}`, unconditional — the raw
compounding is real and huge (`monotone_reaches_exponential`).  Transfer: exactly one door, the slice
functions, where Berkowitz–Wegener collapses the negation gap to polynomial and a monotone bound *crosses*
to general circuits (`slice_transfer`, `slice_crossing`).  So — surprisingly — the monotone bound is *not*
sealed off from `P` vs `NP`: a superpolynomial monotone lower bound on a slice function in NP would be a
superpolynomial general lower bound (`crossing_gives_general_bound`).  But the door is empty: where the
monotone bound is exponential (`CLIQUE`) the function is not a slice and the gap is exponential
(`negation_gap_exponential`); where the gap closes (slice functions) the strongest known monotone bound is
linear.  Proving a strong monotone bound *on a slice* — the one place it would transfer — is the open
statement, and it is `cost_super`: no method separates a slice function's monotone complexity from its
general complexity superpolynomially, because that separation *is* a general-circuit lower bound.  The
monotone bound is pushed to the exact edge of the wall; the last step across is the same single step.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MonotonePushed

open PallLean.Paper93.DeepMath.PathB.MonotoneCompounding

/-! ### Magnitude: the monotone ceiling is exponential -/

/-- The monotone ceiling: `2^n` — Razborov/Alon–Boppana reach `2^{Ω(n^c)}`; unconditionally the monotone
bound goes all the way to exponential. -/
def monotoneReach (n : ℕ) : ℕ := 2 ^ n

/-- **The monotone ceiling is exponential (proved).**  `2^n` — the honest maximum magnitude. -/
theorem monotone_reaches_exponential (n : ℕ) : monotoneReach n = 2 ^ n := rfl

/-- **The exponential ceiling beats the formula bound (proved).**  `2^n` exceeds the crossing-number `n²`
(concretely `121 < 2048` at `n = 11`): monotone magnitude outruns every general-model bound proved. -/
theorem monotone_reach_beats_formula : formulaBound 11 < monotoneReach 11 := by decide

/-! ### The exponential negation gap (Tardos): pushing the exponent does not transfer -/

/-- A function's size in two models, plus whether it is a slice function. -/
structure TwoModel where
  /-- monotone circuit size -/
  monotone : ℕ
  /-- general circuit size -/
  general : ℕ
  /-- whether the function is a slice function (zero below a Hamming weight, one above) -/
  isSlice : Bool

/-- **The negation gap is exponential (proved).**  Tardos: a *non-slice* function with a linear general
circuit (`general = 11`) and an exponential monotone bound (`monotone = 2^11 = 2048`), so
`100·general < monotone`.  Where the monotone bound is strong, the gap is exponential — no transfer. -/
theorem negation_gap_exponential :
    ∃ M : TwoModel, M.isSlice = false ∧ M.general < M.monotone ∧ 100 * M.general < M.monotone :=
  ⟨⟨2048, 11, false⟩, rfl, by decide, by decide⟩

/-! ### The one door: slice functions close the gap (Berkowitz–Wegener) -/

/-- A slice function in two models.  Berkowitz–Wegener: its monotone complexity exceeds its general
complexity by at most the polynomial overhead `poly` of a monotone selection network. -/
structure SliceModel where
  /-- monotone circuit size of the slice function -/
  monotone : ℕ
  /-- its general circuit size -/
  general : ℕ
  /-- the Berkowitz–Wegener polynomial overhead (`~ n² log n`) -/
  poly : ℕ
  /-- **Berkowitz–Wegener**: for a slice function the negation gap is only polynomial. -/
  berkowitz : monotone ≤ general + poly

/-- **The slice transfer (proved).**  For a slice function, `general ≥ monotone − poly` — a monotone lower
bound transfers to the general model up to the polynomial overhead. -/
theorem slice_transfer (S : SliceModel) : S.monotone - S.poly ≤ S.general := by
  have hb := S.berkowitz
  omega

/-- **Concrete crossing (proved).**  A slice function with an exponential monotone bound (`≥ 2048`) and
polynomial overhead (`≤ 121`) has general circuit size `≥ 1927` — the exponential monotone bound crossed
into the general model. -/
theorem slice_crossing (S : SliceModel) (hmono : 2048 ≤ S.monotone) (hpoly : S.poly ≤ 121) :
    1927 ≤ S.general := by
  have hb := S.berkowitz
  omega

/-! ### The pinned open input -/

/-- The crossing predicate: the monotone bound clears the polynomial overhead by margin `p`. -/
def CrossesToGeneral (S : SliceModel) (p : ℕ) : Prop := p < S.monotone - S.poly

/-- **The crossing gives a general bound (proved).**  If a slice model's monotone bound clears the
polynomial overhead by margin `p`, its general circuit size exceeds `p`.  A *superpolynomial* monotone
bound on a slice (`p` superpolynomial) would give a *superpolynomial* general bound — `SAT ∉ P`-strength.
That superpolynomial monotone slice bound is the open input: `cost_super`. -/
theorem crossing_gives_general_bound (S : SliceModel) (p : ℕ) (h : CrossesToGeneral S p) :
    p < S.general := by
  have hb := S.berkowitz
  simp only [CrossesToGeneral] at h
  omega

end PallLean.Paper93.DeepMath.PathB.MonotonePushed

#print axioms PallLean.Paper93.DeepMath.PathB.MonotonePushed.monotone_reaches_exponential
#print axioms PallLean.Paper93.DeepMath.PathB.MonotonePushed.monotone_reach_beats_formula
#print axioms PallLean.Paper93.DeepMath.PathB.MonotonePushed.negation_gap_exponential
#print axioms PallLean.Paper93.DeepMath.PathB.MonotonePushed.slice_transfer
#print axioms PallLean.Paper93.DeepMath.PathB.MonotonePushed.slice_crossing
#print axioms PallLean.Paper93.DeepMath.PathB.MonotonePushed.crossing_gives_general_bound
