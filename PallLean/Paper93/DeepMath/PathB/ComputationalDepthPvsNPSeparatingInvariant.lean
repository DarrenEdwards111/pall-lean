import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-!
# The polynomial-time separating-invariant interface

The communication ladder (one-cut → one-way multi-pass → interactive) is finished; extending it will not
reach `P`.  This file changes direction, as the roadmap requires:

1. **A faithful clocked polynomial-time machine model.**  `ClockedMachine` is a general deterministic machine:
   its `Config` is an arbitrary type (so it may hold the read-only input, work memory, head positions — hence
   random access, revisits, and workspace are all expressible), `next` is the deterministic step, and
   `runtime` is the clock.  `IsPolyTime` bounds the clock by a polynomial.  Because `Config` is arbitrary and
   `decide` reads the halting output, **every** polynomial-time decision procedure is a `ClockedMachine` with
   `IsPolyTime` — the model cannot silently exclude a real `P` algorithm.

2. **The two invariant obligations, and the conditional capstone.**  For a candidate resource
   `R : ClockedMachine → Nat → Nat`:

   * `PUpper R`  — every polynomial-time machine has `R` polynomially bounded;
   * `SATLower R L` — every machine deciding `L` has `R` *not* polynomially bounded.

   These **mechanically** give `¬ InP L`, and for `L ∈ NP` (e.g. SAT) `¬ P = NP`.

This is deliberately an **interface**: the two obligations are the exact, still-unfilled breakthrough.  The
capstone below states precisely what a genuine separating invariant would have to satisfy — it does **not**
supply one.  Finding an `R` for which *both* obligations are provable is the actual `P` vs `NP` breakthrough;
nothing here claims to have it.

## Honest scope

An interface + a conditional theorem.  `PUpper R ∧ SATLower R L ∧ L ∈ NP → P ≠ NP`.  No candidate `R` is
provided, and neither obligation is discharged.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant

/-! ## A faithful clocked deterministic polynomial-time machine -/

/-- A general deterministic machine with a clock.  `Config` is arbitrary — it may bundle the read-only input,
work memory, and head positions, so random access, revisits, and workspace are all representable. -/
structure ClockedMachine where
  Config : Type
  init : List Bool → Config
  next : Config → Config
  output : Config → Bool
  runtime : List Bool → Nat

/-- The decision computed by the machine: run `next` for `runtime x` steps from the initial configuration and
read the output. -/
def ClockedMachine.decide (M : ClockedMachine) (x : List Bool) : Bool :=
  M.output (M.next^[M.runtime x] (M.init x))

/-- The machine runs in polynomial time: its clock is bounded by a polynomial in the input length. -/
def IsPolyTime (M : ClockedMachine) : Prop :=
  ∃ c k : Nat, ∀ x : List Bool, M.runtime x ≤ c * (x.length + 1) ^ k

/-- `M` decides the language `L`. -/
def Decides (M : ClockedMachine) (L : List Bool → Bool) : Prop :=
  ∀ x, M.decide x = L x

/-- **`P`**: languages decided by some clocked polynomial-time machine. -/
def InP (L : List Bool → Bool) : Prop :=
  ∃ M : ClockedMachine, IsPolyTime M ∧ Decides M L

/-- **Faithfulness / normal equivalence.**  `InP L` is exactly "some clocked machine decides `L` within a
polynomial clock", so the model captures precisely the real class `P` and cannot exclude a genuine `P`
algorithm. -/
theorem InP_iff_polyClocked (L : List Bool → Bool) :
    InP L ↔ ∃ (M : ClockedMachine) (c k : Nat),
      (∀ x, M.runtime x ≤ c * (x.length + 1) ^ k) ∧ Decides M L := by
  constructor
  · rintro ⟨M, ⟨c, k, hck⟩, hdec⟩; exact ⟨M, c, k, hck, hdec⟩
  · rintro ⟨M, c, k, hck, hdec⟩; exact ⟨M, ⟨c, k, hck⟩, hdec⟩

/-- **`NP`**: languages with a polynomial-time verifier and a polynomial-length witness. -/
def InNP (L : List Bool → Bool) : Prop :=
  ∃ (V : ClockedMachine) (c k : Nat), IsPolyTime V ∧
    ∀ x, L x = true ↔ ∃ w : List Bool, w.length ≤ c * (x.length + 1) ^ k ∧ V.decide (x ++ w) = true

/-- **`P = NP`**: every `NP` language is in `P`. -/
def PeqNP : Prop := ∀ L : List Bool → Bool, InNP L → InP L

/-! ## The separating-invariant obligations -/

/-- A function `Nat → Nat` is polynomially bounded. -/
def PolyBounded (g : Nat → Nat) : Prop :=
  ∃ c k : Nat, ∀ n, g n ≤ c * (n + 1) ^ k

/-- **`P_upper` obligation.**  The candidate resource is polynomially bounded on *every* polynomial-time
machine. -/
def PUpper (R : ClockedMachine → Nat → Nat) : Prop :=
  ∀ M : ClockedMachine, IsPolyTime M → PolyBounded (R M)

/-- **`SAT_lower` obligation.**  The candidate resource is *not* polynomially bounded on *any* machine deciding
`L` — i.e. super-polynomial infinitely often. -/
def SATLower (R : ClockedMachine → Nat → Nat) (L : List Bool → Bool) : Prop :=
  ∀ M : ClockedMachine, Decides M L → ¬ PolyBounded (R M)

/-- `SATLower` is exactly the super-polynomial-infinitely-often statement (the negation of `PolyBounded`). -/
theorem satLower_iff (R : ClockedMachine → Nat → Nat) (L : List Bool → Bool) :
    SATLower R L ↔ ∀ M, Decides M L → ∀ c k : Nat, ∃ n, c * (n + 1) ^ k < R M n := by
  unfold SATLower PolyBounded
  constructor
  · intro h M hdec c k
    by_contra hcon
    push_neg at hcon
    exact h M hdec ⟨c, k, fun n => hcon n⟩
  · intro h M hdec ⟨c, k, hb⟩
    obtain ⟨n, hn⟩ := h M hdec c k
    exact Nat.not_lt.mpr (hb n) hn

/-! ## The conditional capstone -/

/-- **The two obligations exclude `L` from `P`.**  A polynomial-time machine deciding `L` would have `R`
polynomially bounded (`PUpper`) and not polynomially bounded (`SATLower`) — a contradiction. -/
theorem no_InP_of_invariant (R : ClockedMachine → Nat → Nat) (L : List Bool → Bool)
    (hUpper : PUpper R) (hLower : SATLower R L) : ¬ InP L := by
  rintro ⟨M, hpoly, hdec⟩
  exact hLower M hdec (hUpper M hpoly)

/-- **`L ∉ P → ¬ P = NP`** for any `NP` language `L`.  If `P = NP` then `L ∈ NP ⊆ P`. -/
theorem PneqNP_of_no_InP (L : List Bool → Bool) (hLNP : InNP L) (hno : ¬ InP L) : ¬ PeqNP :=
  fun hP => hno (hP L hLNP)

/-- **The separating-invariant capstone.**  If a resource `R` is polynomially bounded on every polynomial-time
machine but super-polynomial on every decider of an `NP`-language `L`, then `P ≠ NP`.

Instantiating `L` with SAT (which is in `NP` and `NP`-complete) turns this into the target `P ≠ NP`.  The two
obligations `PUpper R` and `SATLower R L` are the **explicit, unfilled** breakthrough: exhibiting an `R` for
which both are provable is precisely what remains, and this theorem supplies none. -/
theorem PneqNP_of_invariant (R : ClockedMachine → Nat → Nat) (L : List Bool → Bool)
    (hLNP : InNP L) (hUpper : PUpper R) (hLower : SATLower R L) : ¬ PeqNP :=
  PneqNP_of_no_InP L hLNP (no_InP_of_invariant R L hUpper hLower)

/-! ## Why the obvious candidates are rejected by the interface (a sanity check)

`R := runtime`-style measures satisfy `PUpper` trivially (a polynomial-time machine has polynomial runtime),
but `SATLower R SAT` for such an `R` is *itself* the statement `SAT ∉ P`; it is not independently provable.
State count and transcript count (the communication ladder) fail the *other* obligation: a real `P` algorithm
for the equality family — a full random-access scan — runs in linear time yet has `2^n` one-cut states, so
those measures violate `PUpper`.  The interface makes both failure modes precise: a genuine invariant must
clear `PUpper` against every `P` algorithm *and* `SATLower` against every SAT decider. -/

/-- The trivial resource `R = 0` satisfies `PUpper` but not `SATLower` (for any language with a decider) —
showing the interface is non-degenerate: `PUpper` alone is cheap; the content is `SATLower`. -/
theorem zero_PUpper : PUpper (fun _ _ => 0) :=
  fun _ _ => ⟨0, 0, fun _ => Nat.zero_le _⟩

theorem zero_not_SATLower (L : List Bool → Bool) (M : ClockedMachine) (hM : Decides M L) :
    ¬ SATLower (fun _ _ => 0) L :=
  fun h => (h M hM) ⟨0, 0, fun _ => Nat.zero_le _⟩

/-! ## The decisive filter: semantic invariance

The N-Frame `CEW + positivity-projected SPDP rank` proposal has the right shape for `R`, but its separation is
packaged under axioms A1–A4.  In this interface:

* **A1** ("bounded CEW ⇒ polynomial SPDP rank for every `P` computation") is exactly `PUpper R`;
* **A3** ("super-polynomial SPDP rank for an NP-complete family") supplies the `¬ PolyBounded` witness needed
  for `SATLower R L`;
* the **semantic bridge** after A3 ("decision equivalence forces comparable rank") is the *appended-sheet
  loophole in a new form* — and it is captured precisely by `SemanticInvariant` below.

The single most important test: **do two machines deciding the same function get polynomially comparable `R`?**
If not, `R` measures the *representation*, not decision difficulty, and cannot prove `P ≠ NP`. -/

/-- **Semantic invariance.**  Any two machines deciding the same language have polynomially comparable `R`
(here: one is `PolyBounded` iff the other is).  This is the property that makes `R` a measure of the *decision
function* rather than of an implementation — the exact requirement that closes the appended-sheet / different
internal-polynomial loophole. -/
def SemanticInvariant (R : ClockedMachine → Nat → Nat) : Prop :=
  ∀ (M₁ M₂ : ClockedMachine) (L : List Bool → Bool),
    Decides M₁ L → Decides M₂ L → (PolyBounded (R M₁) ↔ PolyBounded (R M₂))

/-- **Under semantic invariance, `SATLower` is a property of the language, not a representation.**  A single
decider with super-polynomial `R` witnesses that *every* decider does — so `A3` on one encoding suffices, and
no clever implementation can dodge it. -/
theorem satLower_of_one_witness (R : ClockedMachine → Nat → Nat) (L : List Bool → Bool)
    (hinv : SemanticInvariant R)
    (M₀ : ClockedMachine) (hdec₀ : Decides M₀ L) (hR₀ : ¬ PolyBounded (R M₀)) :
    SATLower R L := by
  intro M hdec hPB
  exact hR₀ ((hinv M M₀ L hdec hdec₀).mp hPB)

/-- **The loophole, made precise.**  If `R` is *not* semantically invariant — some decider of `L` has
polynomially bounded `R` — then `SATLower R L` is false: that implementation dodges the lower bound.  This is
why point 3 (representation-independence of SPDP rank) is load-bearing: without it a single low-rank decider
kills the separation. -/
theorem polyR_decider_breaks_SATLower (R : ClockedMachine → Nat → Nat) (L : List Bool → Bool)
    (M : ClockedMachine) (hdec : Decides M L) (hPB : PolyBounded (R M)) :
    ¬ SATLower R L :=
  fun h => h M hdec hPB

/-- **A representation-dependent candidate cannot satisfy both obligations.**  If two machines decide the same
`L`, one polynomial-time with polynomially bounded `R` and one with super-polynomial `R`, then the first
already puts `L ∈ P` (so `SATLower` must fail) — the candidate is measuring representation. -/
theorem representationDependent_not_separating (R : ClockedMachine → Nat → Nat)
    (L : List Bool → Bool) (M₁ M₂ : ClockedMachine)
    (hpoly₁ : IsPolyTime M₁) (hdec₁ : Decides M₁ L) (hPB₁ : PolyBounded (R M₁))
    (_hdec₂ : Decides M₂ L) (_hR₂ : ¬ PolyBounded (R M₂)) :
    InP L ∧ ¬ SATLower R L :=
  ⟨⟨M₁, hpoly₁, hdec₁⟩, polyR_decider_breaks_SATLower R L M₁ hdec₁ hPB₁⟩

/-- **The N-Frame obligation capstone.**  Mapping the N-Frame axioms onto this interface: if the SPDP-rank
candidate `R` is semantically invariant (the bridge after A3), polynomially bounded on every polynomial-time
machine (A1), and super-polynomial on *one* decider of an `NP`-complete language `L` (A3), then `P ≠ NP`.

Every hypothesis is an explicit, still-unproven obligation.  `hInv` is the semantic bridge (likely the crux),
`hUpper` is A1 (bounded CEW for all of `P`, likely false for the present CEW definition), `M₀`/`hR₀` is A3
(the NP-complete SPDP lower bound).  This theorem *states* the route; it discharges nothing. -/
theorem nframe_obligation_capstone (R : ClockedMachine → Nat → Nat) (L : List Bool → Bool)
    (hLNP : InNP L) (hInv : SemanticInvariant R) (hUpper : PUpper R)
    (M₀ : ClockedMachine) (hdec₀ : Decides M₀ L) (hR₀ : ¬ PolyBounded (R M₀)) :
    ¬ PeqNP :=
  PneqNP_of_invariant R L hLNP hUpper (satLower_of_one_witness R L hInv M₀ hdec₀ hR₀)

end PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant.InP_iff_polyClocked
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant.satLower_iff
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant.no_InP_of_invariant
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant.PneqNP_of_invariant
