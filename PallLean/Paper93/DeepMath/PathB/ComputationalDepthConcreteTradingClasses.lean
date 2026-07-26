import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniformityGapDiagonal
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthIndirectDiagonalization

/-!
# Concrete trading classes: the braid's sockets, stated against the real machine

The `TradingWorld` ingredients and the braid's trigger were abstract fields — honest sockets,
but sockets over abstract `Prop`-families of classes.  This file performs the first, genuinely
dischargeable stage of "discharge the sockets": it DEFINES the three uniform classes concretely
over the faithful `ComposableMachine`, proves the structural lemmas that are provable today,
and assembles a concrete `TradingWorld` from the four ingredients — so that from here on, each
ingredient is a NAMED OPEN LEMMA about actual machines, not a field over abstract classes.
A statement about real machines cannot be vacuously instantiated; this is the same trap-closing
move as concretizing `Universal`.

## The classes (all over the faithful model, scaled exponents as in the engine)

* **`NTIME a L`** — a verifier machine: `L x = true ↔ ∃ witness w`, the machine accepts the
  self-delimiting pairing `encPair x w` within clock `c·(n+1)^a`.  (Witness length is not
  separately bounded — the clock already caps what can be read; this keeps monotonicity
  honest.)
* **`DTS a L`** — a decider within clock `c·(n+1)^a` whose tape never grows more than
  polylog(`|x|`) beyond the input: space = tape growth in this one-tape model (the forced
  initializer copies the input, so raw tape length is ≥ `|x|` always; growth is the honest
  space notion here).  Translating to the literature's RO-input multitape TISP is part of the
  ingredient mountains, stated not hidden.
* **`Sigma2 a L`** — `∃ w₁ ∀ w₂` around a clocked deterministic check.

## What is proved / what remains

PROVED here: exponent-monotonicity for all three classes (`ntime_mono`, `dts_mono`,
`sigma2_mono`), non-vacuity for all three (the constant-true language, via `trivialTrue`), the
assembly `mkWorld : Padding → Speedup → Slowdown → Hierarchy → TradingWorld`, and the engine
running on the concrete classes (`concrete_engine`).

REMAINING (the four mountains, now well-posed): `ConcretePadding` (padding/translation — needs
a pad-stripping transducer), `ConcreteSpeedup` (Nepomnjaščiĭ — needs configuration-midpoint
guessing), `ConcreteSlowdown` (completeness + simulation), `ConcreteHierarchy` (nondeterministic
time hierarchy — needs a universal machine; the largest).  Each is a published theorem;
formalization labor, not open mathematics — unlike the braid's dent.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.UniformityGapDiagonal
open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization

/-- Self-delimiting pairing: each input bit is tagged `[true, b]`, then a `false` separator,
then the witness.  (Decoding lemmas deferred to the padding mountain; the definition is
prefix-free by construction.) -/
def encPair (x w : List Bool) : List Bool :=
  (x.map (fun b => [true, b])).flatten ++ [false] ++ w

/-- The clock discipline: `T` is within `c·(n+1)^a`. -/
def ClockLe (a c : ℕ) (T : ℕ → ℕ) : Prop :=
  ∀ n, T n ≤ c * (n + 1) ^ a

/-- Space discipline: the tape never grows more than `S` beyond the input (the forced
initializer copies the input, so growth is the honest one-tape space notion). -/
def SpaceGrowthLe (M : Machine) (x : List Bool) (S : ℕ) : Prop :=
  ∀ t, (run M t (init M x)).tp.length ≤ x.length + S

/-- Polylog space budget. -/
def polylogBound (c n : ℕ) : ℕ := c * (Nat.log 2 (n + 1) + 1) ^ c

/-- **Concrete `NTIME(n^a)`**: a clocked verifier over the self-delimiting pairing. -/
def NTIME (a : ℕ) (L : Lang) : Prop :=
  ∃ (M : Machine) (T : ℕ → ℕ) (c : ℕ), ClockLe a c T ∧
    ∀ x, (L x = true ↔ ∃ w : List Bool,
      HaltsBy M (encPair x w) (T (encPair x w).length) ∧
      decideOut M (encPair x w) (T (encPair x w).length) = true)

/-- **Concrete `DTS(n^a)`**: a clocked decider with polylog tape growth. -/
def DTS (a : ℕ) (L : Lang) : Prop :=
  ∃ (M : Machine) (T : ℕ → ℕ) (c : ℕ), ClockLe a c T ∧ Decides M L T ∧
    ∀ x, SpaceGrowthLe M x (polylogBound c x.length)

/-- **Concrete `Σ₂TIME(n^a)`**: `∃ w₁ ∀ w₂` around a clocked check. -/
def Sigma2 (a : ℕ) (L : Lang) : Prop :=
  ∃ (M : Machine) (T : ℕ → ℕ) (c : ℕ), ClockLe a c T ∧
    ∀ x, (L x = true ↔ ∃ w₁ : List Bool, ∀ w₂ : List Bool,
      HaltsBy M (encPair x (encPair w₁ w₂)) (T (encPair x (encPair w₁ w₂)).length) ∧
      decideOut M (encPair x (encPair w₁ w₂)) (T (encPair x (encPair w₁ w₂)).length) = true)

/-- Clock relaxation: a `ClockLe a` clock is a `ClockLe a'` clock for `a ≤ a'`. -/
theorem clockLe_mono {a a' c : ℕ} (h : a ≤ a') {T : ℕ → ℕ} (hT : ClockLe a c T) :
    ClockLe a' c T := fun n =>
  le_trans (hT n) (Nat.mul_le_mul_left c (Nat.pow_le_pow_right (by omega) h))

/-- **Monotonicity (proved).**  Bigger exponent, bigger class. -/
theorem ntime_mono {a a' : ℕ} (h : a ≤ a') {L : Lang} (hL : NTIME a L) : NTIME a' L := by
  obtain ⟨M, T, c, hclock, hspec⟩ := hL
  exact ⟨M, T, c, clockLe_mono h hclock, hspec⟩

theorem dts_mono {a a' : ℕ} (h : a ≤ a') {L : Lang} (hL : DTS a L) : DTS a' L := by
  obtain ⟨M, T, c, hclock, hdec, hspace⟩ := hL
  exact ⟨M, T, c, clockLe_mono h hclock, hdec, hspace⟩

theorem sigma2_mono {a a' : ℕ} (h : a ≤ a') {L : Lang} (hL : Sigma2 a L) : Sigma2 a' L := by
  obtain ⟨M, T, c, hclock, hspec⟩ := hL
  exact ⟨M, T, c, clockLe_mono h hclock, hspec⟩

/-- **Non-vacuity (proved).**  The constant-true language is in every class (the one-state
immediate-accept machine; its tape never grows). -/
theorem dts_nonvacuous (a : ℕ) : DTS a (fun _ => true) := by
  refine ⟨trivialTrue, fun _ => 0, 1, fun n => by positivity, fun x => ⟨rfl, rfl⟩, ?_⟩
  intro x t
  have hh : trivialTrue.halt (init trivialTrue x).st = true := rfl
  rw [run_of_halted trivialTrue hh]
  show x.length ≤ x.length + polylogBound 1 x.length
  omega

theorem ntime_nonvacuous (a : ℕ) : NTIME a (fun _ => true) := by
  refine ⟨trivialTrue, fun _ => 0, 1, fun n => by positivity, fun x => ?_⟩
  constructor
  · intro _
    exact ⟨[], rfl, rfl⟩
  · intro _
    rfl

theorem sigma2_nonvacuous (a : ℕ) : Sigma2 a (fun _ => true) := by
  refine ⟨trivialTrue, fun _ => 0, 1, fun n => by positivity, fun x => ?_⟩
  constructor
  · intro _
    exact ⟨[], fun _ => ⟨rfl, rfl⟩⟩
  · intro _
    rfl

/-! ### The four ingredients, now NAMED OPEN LEMMAS about real machines -/

/-- **Padding/translation (OPEN — mountain 1).**  Needs a pad-stripping transducer. -/
def ConcretePadding : Prop :=
  ∀ p q, (∀ L, NTIME q L → DTS p L) → ∀ m, 1 ≤ m → ∀ L, NTIME (m * q) L → DTS (m * p) L

/-- **Nepomnjaščiĭ speedup (OPEN — mountain 2).**  Needs configuration-midpoint guessing. -/
def ConcreteSpeedup : Prop :=
  ∀ b, 1 ≤ b → ∀ L, DTS (2 * b) L → Sigma2 b L

/-- **Slowdown (OPEN — mountain 3).**  Needs completeness + simulation under the assumption. -/
def ConcreteSlowdown : Prop :=
  ∀ p q, 1 ≤ q → (∀ L, NTIME q L → DTS p L) →
    ∀ a, 1 ≤ a → ∀ L, Sigma2 (a * q) L → NTIME (a * p) L

/-- **Nondeterministic time hierarchy (OPEN — mountain 4, the largest).**  Needs a universal
machine and delayed diagonalization. -/
def ConcreteHierarchy : Prop :=
  ∀ a b, 1 ≤ b → b < a → ¬ (∀ L, NTIME a L → NTIME b L)

/-- **The assembly (proved).**  The four concrete ingredients yield a `TradingWorld` over the
real classes — the abstract sockets are now exactly these four named statements. -/
def mkWorld (hp : ConcretePadding) (hs : ConcreteSpeedup)
    (hd : ConcreteSlowdown) (hh : ConcreteHierarchy) : TradingWorld where
  NTIME := NTIME
  DTS := DTS
  Sig2 := Sigma2
  padding := hp
  speedup := hs
  slowdown := hd
  hierarchy := hh

/-- **The engine on the real classes (proved).**  Given the four ingredients, no uniform
small-space simulation of nondeterministic time below `√2` exists — for the CONCRETE machine
classes. -/
theorem concrete_engine (hp : ConcretePadding) (hs : ConcreteSpeedup)
    (hd : ConcreteSlowdown) (hh : ConcreteHierarchy)
    (p q : ℕ) (hq : 1 ≤ q) (hqp : q ≤ p) (hlt : p * p < 2 * (q * q)) :
    ¬ (∀ L, NTIME q L → DTS p L) :=
  lipton_viglas_engine (mkWorld hp hs hd hh) p q hq hqp hlt

end PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses

#print axioms PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses.ntime_mono
#print axioms PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses.dts_nonvacuous
#print axioms PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses.ntime_nonvacuous
#print axioms PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses.sigma2_nonvacuous
#print axioms PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses.concrete_engine
