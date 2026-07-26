import Mathlib.Data.Nat.Basic

/-!
# Two observer interfaces meet: verify vs find — and the answer is hidden between them

Darren's reframe: a bounded observer can **verify** the God (verify NP), but can't **see** the proof — the
witness is too thermodynamically expensive to find.  This is the right structure — it is exactly the
verify/find asymmetry that *defines* NP.  But made precise it shows why the thermodynamic argument can't
cross: the two visible quantities (verify cost, brute-force cost) do **not** determine the answer.

## The two interfaces, and the hidden third quantity

Three costs meet here:

* **`verify`** — check a witness.  Cheap, in P.  The bounded observer can do this.
* **`bruteForce`** — find a witness by exhaustive search.  The God's search — *exponential*.
* **`minFind`** — the cost of the *best* algorithm, over all of them, clever ones included.  **This is the
  answer** (`cbudget`): P vs NP is whether it is polynomial.

The thermodynamic argument establishes exactly `verify ≤ minFind ≤ bruteForce`: verifying is cheap,
brute-force is expensive.  That is `NP ⊆ EXP` — **trivial and known**, true whether or not P = NP.

## What is proved

* **`thermo_data_undecided`** — two worlds with *identical* thermodynamic data (`verify` cheap,
  `bruteForce` expensive) but *different* answers: one with `minFind = verify` (a cheap clever finder — a
  `P = NP`-like world), one with `minFind = bruteForce` (no clever finder — a `P ≠ NP` world).  The
  visible costs do not decide `minFind`.

## Honest scope — the energy bounds the dumb algorithm, not the smart one

"Too thermodynamically expensive to find" is true of **brute-force** search — the *dumb* algorithm.  But P
vs NP is whether the expense is *necessary*, i.e. whether `minFind` (the best over *all* algorithms) is
large.  A clever polynomial finder, if it exists, uses *little* energy (it is polynomial) — so the
thermodynamic argument, which only bounds brute force, says **nothing** about it.  `minFind` sits hidden
between the two visible interfaces, and it *is* `cost_super`.

At the meta level the same shape recurs: the God's *proof that P ≠ NP* (the separating measure `Π★`) exists
at the unbounded altitude, but a bounded observer cannot efficiently construct or verify it — that is the
**natural-proofs barrier** (`DischargePiStar`: an efficiently-verifiable separating certificate would be a
natural property and break crypto).  "We can't see the proof" is that barrier — a real obstruction, not a
resolution.  So the verify/find reframe correctly names the *structure* (NP), and correctly names *why* it
is hard (the answer is the hidden `minFind`), but it does not cross: `minFind = cost_super`.  Nothing here
is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.VerifyFindGap

/-- A **search world**: the cost to `verify` a witness, the cost `minFind` of the best finder (the answer,
`cbudget`), and the `bruteForce` cost.  Always `verify ≤ minFind ≤ bruteForce` — verifying is no harder
than the best find, which is no harder than brute force. -/
structure SearchWorld where
  /-- cost to verify a witness (cheap, in P) -/
  verify : ℕ
  /-- cost of the best algorithm over all — the answer, `cbudget` -/
  minFind : ℕ
  /-- cost of exhaustive search (the God's search, exponential) -/
  bruteForce : ℕ
  /-- verifying is no harder than finding -/
  h1 : verify ≤ minFind
  /-- the best finder is no harder than brute force -/
  h2 : minFind ≤ bruteForce

/-- A `P = NP`-like world: a clever finder as cheap as verification (`minFind = verify`). -/
def easyWorld (v e : ℕ) (h : v ≤ e) : SearchWorld := ⟨v, v, e, Nat.le_refl v, h⟩

/-- A `P ≠ NP` world: no clever finder — the best is brute force (`minFind = bruteForce`). -/
def hardWorld (v e : ℕ) (h : v ≤ e) : SearchWorld := ⟨v, e, e, h, Nat.le_refl e⟩

/-- **The thermodynamic data does not decide the answer (proved).**  With `v < e`, `easyWorld` and
`hardWorld` have *identical* visible costs — same `verify`, same `bruteForce` (the two observer interfaces)
— yet *different* `minFind` (the answer).  So knowing "verify cheap, brute-force expensive" (`NP ⊆ EXP`)
leaves `minFind` — the P vs NP question — completely open. -/
theorem thermo_data_undecided (v e : ℕ) (h : v < e) :
    (easyWorld v e (Nat.le_of_lt h)).verify = (hardWorld v e (Nat.le_of_lt h)).verify ∧
    (easyWorld v e (Nat.le_of_lt h)).bruteForce = (hardWorld v e (Nat.le_of_lt h)).bruteForce ∧
    (easyWorld v e (Nat.le_of_lt h)).minFind ≠ (hardWorld v e (Nat.le_of_lt h)).minFind := by
  refine ⟨rfl, rfl, ?_⟩
  show v ≠ e
  omega

end PallLean.Paper93.DeepMath.PathB.VerifyFindGap

#print axioms PallLean.Paper93.DeepMath.PathB.VerifyFindGap.thermo_data_undecided
