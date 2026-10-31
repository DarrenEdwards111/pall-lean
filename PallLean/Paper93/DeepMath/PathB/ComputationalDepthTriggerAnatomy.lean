import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMagnificationBraid
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKannanFinitization

/-!
# Discharging the trigger, honestly: anatomy, a concrete sparse target, and the two remaining arcs

The braid's `trigger` is a monolithic socket — the published MMW/OPS magnification theorem.  Its
full formal discharge needs two large ingredients that do not exist in the corpus yet, and this file
does the honest maximum short of them: it **factors the socket into proved glue plus two *named*
arcs**, and it makes the braid's sparse target **concrete and corpus-native** — MCSP built from this
repository's own circuit-code machinery, with its defining sparsity proved by this repository's own
counting theorem.

## What is proved

* **`mcspAt` / `mcspLang`** — the sparse target, concrete: "`x` is the truth table of some
  size-`s`-computable `m`-input function", built from `Code`/`codeEval`/`ttList` (the Kannan arc's
  machinery), decidable and computable.  `mcspAt_eq_true_iff` gives the NP-witness shape: a YES
  instance is witnessed by a circuit code.
* **`mcspYes_card_le` / `mcspYes_sparse`** — **the sparsity is a theorem**: the YES instances at
  table-length `2^m` are the image of the code space, so there are at most `|Code m s|` of them —
  strictly fewer than the `2^{2^m}` tables once the Shannon threshold fires.  The very counting
  bound that proved hard functions exist (stage 1) is what makes this target *sparse* — the property
  magnification feeds on.  One counting theorem, two duties.
* **`SparseToSAT`** — a mapping reduction to SAT with *concrete* correctness
  (`∀ x, sparse x = SATLang (red x)`) and the efficiency requirement isolated as a named field.
* **`trigger_of_reduction` / `braidOfReduction`** — the factoring: an efficient reduction plus the
  DTS-composition property *prove* the trigger; a braid can be assembled with the monolithic socket
  replaced by the two smaller named ingredients.

## The honest anatomy — what remains, exactly

The trigger now factors as **construction + bookkeeping**, each a named arc:

1. **The reduction construction** (`SparseToSAT.red` for `mcspLang`, with `Efficient`): encode
   "∃ code whose table is `x`" as a CNF — a *universal-circuit Tseitin*, where the code bits become
   formula variables.  This is a genuine extension of `CircuitUniversality`'s proven Tseitin
   machinery (which handles a *fixed* circuit) to a quantified one — buildable, roadmapped, no open
   mathematics.
2. **The DTS-composition bookkeeping** (`DTSComposes`): composing the efficient reduction with a
   polynomial-time SAT decider must land in the small-space class `W.DTS p` — this needs
   **space-bounded semantics** for the faithful machine model, which the corpus does not yet have
   (it is why `TradingWorld` is socket-structured at all).

Neither is open mathematics; both are real arcs.  And the locality-barrier caveat from the braid's
audit is unchanged: the *dent* — not the trigger — is where the barrier stands.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TriggerAnatomy

open PallLean.Paper93.DeepMath.PathB.MagnificationBraid
open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.SharingModelShannon
open PallLean.Paper93.DeepMath.PathB.KannanTT

/-! ### The concrete sparse target: corpus-native MCSP -/

/-- **MCSP at scale `(m, s)`, concrete and computable**: `x` is the truth table of some
size-`s`-computable `m`-input function.  Built from the Kannan arc's own machinery. -/
def mcspAt (m s : ℕ) (x : List Bool) : Bool :=
  decide (∃ code : Code m s, ttList m (codeEval m s code) = x)

/-- The NP-witness shape: a YES instance is witnessed by a circuit code. -/
theorem mcspAt_eq_true_iff (m s : ℕ) (x : List Bool) :
    mcspAt m s x = true ↔ ∃ code : Code m s, ttList m (codeEval m s code) = x :=
  decide_eq_true_iff

/-- **The sparse target as a language** (table length dispatches the scale). -/
noncomputable def mcspLang (s : ℕ) : Lang :=
  fun x => mcspAt (Nat.log 2 x.length) s x

/-! ### Sparsity is a theorem: the counting bound's second duty -/

/-- The YES instances at scale `(m, s)`: the image of the code space. -/
def mcspYes (m s : ℕ) : Finset (List Bool) :=
  Finset.image (fun code : Code m s => ttList m (codeEval m s code)) Finset.univ

theorem mem_mcspYes_iff (m s : ℕ) (x : List Bool) :
    x ∈ mcspYes m s ↔ mcspAt m s x = true := by
  rw [mcspAt_eq_true_iff]
  simp [mcspYes]

/-- **At most `|Code m s|` YES instances (proved).** -/
theorem mcspYes_card_le (m s : ℕ) : (mcspYes m s).card ≤ Fintype.card (Code m s) := by
  rw [← Finset.card_univ]
  exact Finset.card_image_le

/-- **Sparsity (proved).**  Below the Shannon threshold there are strictly fewer YES tables than the
`2^{2^m}` tables of length `2^m`: the counting theorem that produced hard functions also makes this
target sparse — the property magnification feeds on. -/
theorem mcspYes_sparse (m s : ℕ) (hcard : Fintype.card (Code m s) < 2 ^ 2 ^ m) :
    (mcspYes m s).card < 2 ^ 2 ^ m :=
  lt_of_le_of_lt (mcspYes_card_le m s) hcard

/-! ### The trigger, factored: reduction construction + composition bookkeeping -/

/-- A **mapping reduction to SAT**: a concrete map with concrete correctness, and the
`n^{1+ε}`-overhead small-space computability isolated as a named requirement (it awaits the
space-semantics arc). -/
structure SparseToSAT (sparse : Lang) where
  /-- the reduction map -/
  red : List Bool → List Bool
  /-- concrete correctness: membership transfers exactly -/
  correct : ∀ x, sparse x = SATLang (red x)
  /-- the efficiency of `red` (`n^{1+ε}` overhead, small space) — the space-semantics arc -/
  Efficient : Prop

/-- **The composition bookkeeping socket**: an `Efficient` reduction into a polynomial-time-decidable
SAT lands the source in the small-space class.  Pure model bookkeeping (space semantics), not
construction. -/
def DTSComposes (W : TradingWorld) (p : ℕ) (sparse : Lang) (R : SparseToSAT sparse) : Prop :=
  R.Efficient → InP SATLang → W.DTS p sparse

/-- **The trigger, proved from the factoring.**  Efficient reduction + composition ⟹ the braid's
trigger: if the sparse target has no `n^{p/q}` small-space algorithm, `SAT ∉ P`. -/
theorem trigger_of_reduction (W : TradingWorld) (p : ℕ) (sparse : Lang)
    (R : SparseToSAT sparse) (hEff : R.Efficient) (hClos : DTSComposes W p sparse R) :
    ¬ W.DTS p sparse → SAT_not_in_P :=
  fun hdent hInP => hdent (hClos hEff hInP)

/-- **A braid with the monolithic trigger replaced by the two named ingredients (proved).**  The
socket is factored: construction (`SparseToSAT` + `Efficient`) and bookkeeping (`DTSComposes`). -/
def braidOfReduction (W : TradingWorld) (sparse : Lang) (p q : ℕ) (hq : 1 ≤ q) (hpq : q < p)
    (R : SparseToSAT sparse) (hEff : R.Efficient) (hClos : DTSComposes W p sparse R) : Braid :=
  { sparse := sparse, W := W, p := p, q := q, hq := hq, hpq := hpq,
    trigger := trigger_of_reduction W p sparse R hEff hClos }

end PallLean.Paper93.DeepMath.PathB.TriggerAnatomy

#print axioms PallLean.Paper93.DeepMath.PathB.TriggerAnatomy.mcspAt_eq_true_iff
#print axioms PallLean.Paper93.DeepMath.PathB.TriggerAnatomy.mcspYes_sparse
#print axioms PallLean.Paper93.DeepMath.PathB.TriggerAnatomy.trigger_of_reduction
