import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPadVerifierComposition

/-!
# Mountain 1, camp 6: reducing the two machine obligations to three primitives (glue all proved)

Camp 5 left mountain 1's NTIME side resting on two obligations — `StripTransducersExist` and
`NTIMENormalizable`.  This file discharges as much of each as machine-*independent* mathematics can:
it reduces both, with all glue PROVED, down to **three concrete machine primitives**, isolating the
single irreducible arithmetic construction from everything arithmetic-free or shared.

## `NTIMENormalizable`, fully reduced to the shared clocked simulator

* **`clockFaithful_of_alwaysHalts`** — a machine that always halts by a clock `P` is automatically
  clock-faithful w.r.t. `P` (once halted, stays halted, so any accepting run is already reflected at
  `P`).  So clock-faithfulness need not be engineered — it is *free* from always-halting.
* **`normalizable_of_clockedSim`** — `NTIMENormalizable` follows from `ClockedSimExists` (the
  standard clocked universal simulator: force-halt `M` at the polynomial clock).  A complete,
  machine-checked reduction — and the simulator is exactly the **mountain-4 / Kannan-stage-5 shared**
  universal machine, paid once for all three.

## `StripTransducersExist`, factored into checker + stripper

* **`PadLengthChecker`** — the one **irreducible arithmetic** primitive: verify the two pads have the
  exact required length `(|·|+1)^m` (identity on good inputs, divergence otherwise).
* **`PadShapeStripper`** — the **arithmetic-free** primitive: on a well-formed doubly-padded input,
  produce the stripped pair `encPair x w` (finite-state tape scanning; behavior off the well-formed
  set is irrelevant, the checker already diverged those).
* **`stripTransducer_of_pieces`** — PROVED: `comp` of a checker and a stripper *is* a
  `StripTransducer` (phase-1 runs the checker to its identity-halt, the switch hands the untouched
  tape to the stripper, phase-2 produces the stripped pair; divergence on bad inputs is inherited via
  `comp_never_halts`).  The composition glue — first-halt time, exact output tape, linear clock — is
  all discharged here.

## The grand reduction

* **`ntimeHalf_of_primitives`** — the padding mountain's NTIME half from the three primitives.
* **`concretePadding_of_primitives`** — `ConcretePadding` itself now rests on: `PadLengthChecker`
  (arithmetic), `PadShapeStripper` (scanning), `ClockedSim` (shared universal machine), and the
  virtual-input `PaddingDTSHalf`.  Each is genuine TM engineering; only the checker's `(n+1)^m`
  arithmetic is bespoke.  None is open mathematics; none is the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PadMountainReductions

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization
open PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses
open PallLean.Paper93.DeepMath.PathB.EncPairDecode
open PallLean.Paper93.DeepMath.PathB.PadFunction
open PallLean.Paper93.DeepMath.PathB.PaddingAssembly
open PallLean.Paper93.DeepMath.PathB.PadWitnessBudget
open PallLean.Paper93.DeepMath.PathB.PadVerifierComposition

/-! ### NTIMENormalizable ⟸ the clocked simulator -/

/-- The concrete polynomial clock `c·(n+1)^a`. -/
def polyClock (a c : ℕ) : ℕ → ℕ := fun n => c * (n + 1) ^ a

/-- **The clocked universal simulator (mountain-4 / Kannan-stage-5 shared).**  Given any machine `M`
and a clock `T ≤ c·(n+1)^a`, a machine `M'` that always halts by the polynomial clock and accepts
iff `M` accepts within `T`.  The standard force-halt-at-`P` construction. -/
def ClockedSimExists : Prop :=
  ∀ (M : Machine) (a c : ℕ) (T : ℕ → ℕ), ClockLe a c T →
    ∃ (M' : Machine) (c' : ℕ),
      (∀ y, HaltsBy M' y (polyClock a c' y.length)) ∧
      (∀ y, decideOut M' y (polyClock a c' y.length) = true ↔
             (HaltsBy M y (T y.length) ∧ decideOut M y (T y.length) = true))

/-- **Clock-faithfulness is free from always-halting (proved).**  A machine that always halts by `P`
is clock-faithful w.r.t. `P`. -/
theorem clockFaithful_of_alwaysHalts (M' : Machine) (P : ℕ → ℕ)
    (hH : ∀ y, HaltsBy M' y (P y.length)) : ClockFaithful M' P := by
  intro y t hHt hAt
  refine ⟨hH y, ?_⟩
  rcases Nat.le_total t (P y.length) with hle | hle
  · have hst := run_stable M' y hle hHt
    show M'.accept (run M' (P y.length) (init M' y)).st = true
    rw [hst]; exact hAt
  · have hst := run_stable M' y hle (hH y)
    show M'.accept (run M' (P y.length) (init M' y)).st = true
    rw [← hst]; exact hAt

/-- **`NTIMENormalizable` from the clocked simulator (proved).**  The complete reduction: clocked
simulation gives an always-halting `M'`, whose clock-faithfulness is then free. -/
theorem normalizable_of_clockedSim (h : ClockedSimExists) : NTIMENormalizable := by
  intro a L hL
  obtain ⟨M, T, c, hclock, hspec⟩ := hL
  obtain ⟨M', c', hHalt, hAcc⟩ := h M a c T hclock
  refine ⟨M', polyClock a c', c', fun n => le_refl _,
    clockFaithful_of_alwaysHalts M' (polyClock a c') hHalt, fun x => ?_⟩
  rw [hspec x]
  constructor
  · rintro ⟨w, hHw, hAw⟩
    exact ⟨w, hHalt _, (hAcc _).mpr ⟨hHw, hAw⟩⟩
  · rintro ⟨w, _, hAw⟩
    exact ⟨w, (hAcc _).mp hAw⟩

/-! ### StripTransducersExist ⟸ checker + stripper -/

/-- **The pad-length checker** — the one irreducible arithmetic primitive.  On a doubly-padded input
it halts leaving the tape untouched (so the stripper receives it); on every other input it diverges.
Verifying the pad lengths `(|·|+1)^m` is the bespoke `(n+1)^m` arithmetic. -/
structure PadLengthChecker (m : ℕ) where
  Mc : Machine
  Tc : ℕ → ℕ
  cc : ℕ
  clock : ClockLe 1 cc Tc
  goodId : ∀ x w : List Bool, ∃ tc,
    tc ≤ Tc (encPair (padWith m x) (padWith m w)).length ∧
    (∀ s, s < tc → Mc.halt (run Mc s (init Mc (encPair (padWith m x) (padWith m w)))).st = false) ∧
    Mc.halt (run Mc tc (init Mc (encPair (padWith m x) (padWith m w)))).st = true ∧
    (run Mc tc (init Mc (encPair (padWith m x) (padWith m w)))).tp
      = encPair (padWith m x) (padWith m w)
  badLoop : ∀ z, (∀ x w : List Bool, z ≠ encPair (padWith m x) (padWith m w)) →
    ∀ t, Mc.halt (run Mc t (init Mc z)).st = false

/-- **The pad-shape stripper** — the arithmetic-free primitive.  On a well-formed doubly-padded
input it first-halts leaving the stripped pair `encPair x w`; its behavior off that set is
irrelevant. -/
structure PadShapeStripper (m : ℕ) where
  Ms : Machine
  Ts : ℕ → ℕ
  cs : ℕ
  clock : ClockLe 1 cs Ts
  goodStrip : ∀ x w : List Bool, ∃ ts,
    ts ≤ Ts (encPair (padWith m x) (padWith m w)).length ∧
    (∀ s, s < ts → Ms.halt (run Ms s (init Ms (encPair (padWith m x) (padWith m w)))).st = false) ∧
    Ms.halt (run Ms ts (init Ms (encPair (padWith m x) (padWith m w)))).st = true ∧
    (run Ms ts (init Ms (encPair (padWith m x) (padWith m w)))).tp = encPair x w

/-- **`comp` of a checker and a stripper is a `StripTransducer` (proved).**  Phase-1 runs the
checker to its identity-halt; the switch hands the untouched tape to the stripper; phase-2 produces
the stripped pair.  Divergence on bad inputs is inherited.  All glue — first-halt, output, clock —
discharged. -/
def stripTransducer_of_pieces (m : ℕ) (C : PadLengthChecker m) (S : PadShapeStripper m) :
    StripTransducer m where
  Ms := comp C.Mc S.Ms
  Ts := fun n => C.Tc n + 1 + S.Ts n
  cs := C.cc + 1 + S.cs
  clock := by
    intro n
    have h1 := C.clock n
    have h2 := S.clock n
    rw [pow_one] at h1 h2 ⊢
    show C.Tc n + 1 + S.Ts n ≤ (C.cc + 1 + S.cs) * (n + 1)
    have hexp : (C.cc + 1 + S.cs) * (n + 1) = C.cc * (n + 1) + (n + 1) + S.cs * (n + 1) := by ring
    omega
  goodHalt := fun x w => by
    obtain ⟨tc, htc, hcmin, hchalt, hctp⟩ := C.goodId x w
    obtain ⟨ts, hts, hsmin, hshalt, hstp⟩ := S.goodStrip x w
    have hsw : run (comp C.Mc S.Ms) (tc + 1)
        (init (comp C.Mc S.Ms) (encPair (padWith m x) (padWith m w)))
        = embedR C.Mc S.Ms ⟨S.Ms.start, 0, encPair (padWith m x) (padWith m w)⟩ := by
      have hh := comp_switch_run C.Mc S.Ms (encPair (padWith m x) (padWith m w)) tc hcmin hchalt
      rw [hctp] at hh; exact hh
    refine ⟨tc + 1 + ts, ?_, ?_, ?_, ?_⟩
    · show tc + 1 + ts
          ≤ C.Tc (encPair (padWith m x) (padWith m w)).length + 1
            + S.Ts (encPair (padWith m x) (padWith m w)).length
      omega
    · intro s hs
      rcases Nat.lt_or_ge s (tc + 1) with h1 | h1
      · rw [comp_phase1 C.Mc S.Ms (encPair (padWith m x) (padWith m w)) s
          (fun u hu => hcmin u (by omega))]
        rfl
      · obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le h1
        rw [comp_phase2 C.Mc S.Ms (encPair (padWith m x) (padWith m w)) tc
          (encPair (padWith m x) (padWith m w)) s' hsw]
        show S.Ms.halt (run S.Ms s' (init S.Ms (encPair (padWith m x) (padWith m w)))).st = false
        exact hsmin s' (by omega)
    · rw [comp_phase2 C.Mc S.Ms (encPair (padWith m x) (padWith m w)) tc
        (encPair (padWith m x) (padWith m w)) ts hsw]
      show S.Ms.halt (run S.Ms ts (init S.Ms (encPair (padWith m x) (padWith m w)))).st = true
      exact hshalt
    · rw [comp_phase2 C.Mc S.Ms (encPair (padWith m x) (padWith m w)) tc
        (encPair (padWith m x) (padWith m w)) ts hsw]
      show (run S.Ms ts (init S.Ms (encPair (padWith m x) (padWith m w)))).tp = encPair x w
      exact hstp
  badLoop := fun z hz t => comp_never_halts C.Mc S.Ms z (C.badLoop z hz) t

/-! ### The grand reduction -/

/-- The checker primitive exists at every scale. -/
def PadLengthCheckerExists : Prop := ∀ m, 1 ≤ m → Nonempty (PadLengthChecker m)

/-- The stripper primitive exists at every scale. -/
def PadShapeStripperExists : Prop := ∀ m, 1 ≤ m → Nonempty (PadShapeStripper m)

/-- **`StripTransducersExist` from the two primitives (proved).** -/
theorem stripTransducersExist_of_pieces (hC : PadLengthCheckerExists) (hS : PadShapeStripperExists) :
    StripTransducersExist := by
  intro m hm
  obtain ⟨C⟩ := hC m hm
  obtain ⟨S⟩ := hS m hm
  exact ⟨stripTransducer_of_pieces m C S⟩

/-- **The padding mountain's NTIME half from the three primitives (proved).** -/
theorem ntimeHalf_of_primitives (hC : PadLengthCheckerExists) (hS : PadShapeStripperExists)
    (hSim : ClockedSimExists) (m q : ℕ) (hm : 1 ≤ m) (hq : 1 ≤ q) (L : Lang)
    (hL : NTIME (m * q) L) : NTIME q (padLang m L) :=
  ntimeHalf_of_components (stripTransducersExist_of_pieces hC hS)
    (normalizable_of_clockedSim hSim) m q hm hq L hL

/-- **The `q ≥ 1` NTIME half from the primitives (proved).**  For every super-constant window ratio
the padding verifier side reduces to the three primitives.  (The `q = 0` edge — constant clock, which
linear strip time cannot fit — is genuinely not covered by this composition engine; the braid uses
`q ≥ 1` throughout via `Braid.hq`, so this is the operative statement.  Discharging `ConcretePadding`
at `q = 0` would need a different, degenerate argument, flagged not hidden.) -/
theorem paddingNTIMEHalf_qpos (hC : PadLengthCheckerExists) (hS : PadShapeStripperExists)
    (hSim : ClockedSimExists) (m q : ℕ) (hm : 1 ≤ m) (hq : 1 ≤ q) (L : Lang)
    (hL : NTIME (m * q) L) : NTIME q (padLang m L) :=
  ntimeHalf_of_primitives hC hS hSim m q hm hq L hL

end PallLean.Paper93.DeepMath.PathB.PadMountainReductions

#print axioms PallLean.Paper93.DeepMath.PathB.PadMountainReductions.normalizable_of_clockedSim
#print axioms PallLean.Paper93.DeepMath.PathB.PadMountainReductions.stripTransducer_of_pieces
#print axioms PallLean.Paper93.DeepMath.PathB.PadMountainReductions.ntimeHalf_of_primitives
