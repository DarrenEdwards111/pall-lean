import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPadWitnessBudget

/-!
# Mountain 1, camp 5: the composition engine — `comp` of a strip transducer IS a `PadVerifier2`

Camp 5 builds the machine — as far as machine-*independent* mathematics can carry it, which turns
out to be all the way to the composition.  The construction `Mv := comp Ms M` (strip transducer,
then the original verifier) is here PROVED to satisfy the fixed interface `PadVerifier2`, given two
exactly-specified inputs.  A third honest catch surfaced on the way and is baked into the spec:

**The catch (the `T`-computability gap).**  `PadVerifier2`'s `good` is an *iff*: the composed
machine must accept **exactly** when `M` accepts *within its clock `T`*.  But a machine cannot cut
off a simulation at `T` steps for an arbitrary (possibly uncomputable) `T : ℕ → ℕ` — and a
late-accepting `M` (halting after `T` but within the composed budget) would break the iff.  The
repair is the classical one: require the verifier to be **clock-faithful** (`ClockFaithful M T` — if
it ever halts-accepting, it already did so within `T`).  Every standard verifier is normalizable to
this form by clocked simulation — that normalization (`NTIMENormalizable`) is exactly
mountain-4-shared infrastructure, named here, not hidden.

## What is proved

* **`comp_never_halts` / `comp_switch_run`** — the two missing simulation lemmas: a diverging
  transducer keeps the composition in phase 1 forever (the reject path is *free*: no halt, no
  accept), and the exact switch configuration after the transducer's first halt.
* **`padVerifier2_of_strip`** — THE ENGINE: a `StripTransducer` (linear-clock, first-halt with tape
  `encPair x w` on good inputs, divergence on bad inputs) plus a clock-faithful verifier yields a
  `PadVerifier2` — `good` both ways (phase-1/switch/phase-2 simulation, `run_stable` lift,
  `pad_clock_transfer2` paying the clock), `badY`/`badW` via pairing injectivity + divergence.
* **`ntimeHalf_of_components`** — the assembly: strip transducers + clock-faithful normalization
  give the NTIME half for `q ≥ 1`.

## What remains, exactly

1. **`StripTransducersExist`** — the concrete transducer: decode the outer pair, check *both* pads
   exact, re-tag, halt with `encPair x w` on the tape; diverge otherwise.  A pure transducer with a
   fully concrete spec — no `M`, no `T`, no computability subtleties.  Machine engineering.
2. **`NTIMENormalizable`** — clocked simulation (every `NTIME` witness has a clock-faithful form).
   Universal-machine-flavored: mountain-4-shared, paid once for both.
3. The `q = 0` edge of the half is *not* covered by this engine (the linear strip time cannot be
   absorbed into a constant clock); the braid instantiates `q ≥ 1` throughout (`Braid.hq`), and the
   degenerate case is flagged to the tracker as a design question for `ConcretePadding`'s statement.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PadVerifierComposition

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization
open PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses
open PallLean.Paper93.DeepMath.PathB.EncPairDecode
open PallLean.Paper93.DeepMath.PathB.PadFunction
open PallLean.Paper93.DeepMath.PathB.PaddingAssembly
open PallLean.Paper93.DeepMath.PathB.PadWitnessBudget

/-- **The strip transducer** — camp 6's concrete construction target, specified exactly: linear
clock; on good inputs (`encPair (padWith m x) (padWith m w)`) a first halt within clock with the
stripped pair `encPair x w` on the tape; on every other input, divergence (which makes the reject
path free: a never-halting run is never accepted). -/
structure StripTransducer (m : ℕ) where
  /-- the transducer machine -/
  Ms : Machine
  /-- its clock -/
  Ts : ℕ → ℕ
  /-- its clock constant -/
  cs : ℕ
  /-- the clock is linear -/
  clock : ClockLe 1 cs Ts
  /-- on good inputs: first halt within clock, with the stripped pair on the tape -/
  goodHalt : ∀ x w : List Bool, ∃ tf,
    tf ≤ Ts (encPair (padWith m x) (padWith m w)).length ∧
    (∀ s, s < tf →
      Ms.halt (run Ms s (init Ms (encPair (padWith m x) (padWith m w)))).st = false) ∧
    Ms.halt (run Ms tf (init Ms (encPair (padWith m x) (padWith m w)))).st = true ∧
    (run Ms tf (init Ms (encPair (padWith m x) (padWith m w)))).tp = encPair x w
  /-- on every other input: divergence -/
  badLoop : ∀ z, (∀ x w : List Bool, z ≠ encPair (padWith m x) (padWith m w)) →
    ∀ t, Ms.halt (run Ms t (init Ms z)).st = false

/-- **Clock faithfulness**: if the verifier ever halts-accepting, it already did so within its
clock.  The classical normal form; `NTIMENormalizable` (mountain-4-shared) supplies it. -/
def ClockFaithful (M : Machine) (T : ℕ → ℕ) : Prop :=
  ∀ y t, HaltsBy M y t → decideOut M y t = true →
    HaltsBy M y (T y.length) ∧ decideOut M y (T y.length) = true

/-- A diverging transducer keeps the composition in phase 1 forever: no halt, ever. -/
theorem comp_never_halts (Mf Mg : Machine) (z : List Bool)
    (h : ∀ t, Mf.halt (run Mf t (init Mf z)).st = false) (t : ℕ) :
    (comp Mf Mg).halt (run (comp Mf Mg) t (init (comp Mf Mg) z)).st = false := by
  rw [comp_phase1 Mf Mg z t (fun s _ => h s)]
  rfl

/-- The exact configuration one step after the transducer's first halt: `Mg`'s start, head reset,
the transducer's tape. -/
theorem comp_switch_run (Mf Mg : Machine) (z : List Bool) (tf : ℕ)
    (hmin : ∀ s, s < tf → Mf.halt (run Mf s (init Mf z)).st = false)
    (hhalt : Mf.halt (run Mf tf (init Mf z)).st = true) :
    run (comp Mf Mg) (tf + 1) (init (comp Mf Mg) z)
      = embedR Mf Mg ⟨Mg.start, 0, (run Mf tf (init Mf z)).tp⟩ := by
  rw [run_succ, comp_phase1 Mf Mg z tf hmin, comp_step_switch Mf Mg _ hhalt]

/-- **THE COMPOSITION ENGINE (proved).**  A strip transducer plus a clock-faithful verifier at
exponent `m·q` compose (via `comp`) into a `PadVerifier2` at exponent `q` — the machine obligation
of the padding mountain's NTIME half, discharged down to the transducer. -/
def padVerifier2_of_strip (m q : ℕ) (hq : 1 ≤ q) (S : StripTransducer m)
    (M : Machine) (T : ℕ → ℕ) (c : ℕ) (hclock : ClockLe (m * q) c T)
    (hfaith : ClockFaithful M T) : PadVerifier2 m q M T where
  Mv := comp S.Ms M
  Tv := fun n => S.Ts n + 1 + c * 3 ^ (m * q) * (n + 1) ^ q
  cv := S.cs + 1 + c * 3 ^ (m * q)
  clock := by
    intro n
    have hA1 : n + 1 ≤ (n + 1) ^ q := by
      calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ (n + 1) ^ q := Nat.pow_le_pow_right (by omega) hq
    have h1 : S.Ts n ≤ S.cs * (n + 1) ^ q := by
      have h0 := S.clock n
      rw [pow_one] at h0
      exact le_trans h0 (Nat.mul_le_mul_left _ hA1)
    have h2 : 1 ≤ (n + 1) ^ q := Nat.one_le_pow _ _ (by omega)
    show S.Ts n + 1 + c * 3 ^ (m * q) * (n + 1) ^ q
        ≤ (S.cs + 1 + c * 3 ^ (m * q)) * (n + 1) ^ q
    calc S.Ts n + 1 + c * 3 ^ (m * q) * (n + 1) ^ q
        ≤ S.cs * (n + 1) ^ q + (n + 1) ^ q + c * 3 ^ (m * q) * (n + 1) ^ q := by omega
      _ = (S.cs + 1 + c * 3 ^ (m * q)) * (n + 1) ^ q := by ring
  good := fun x w => by
    obtain ⟨tf, htf, hmin, hhalt, htp⟩ := S.goodHalt x w
    have hsw := comp_switch_run S.Ms M (encPair (padWith m x) (padWith m w)) tf hmin hhalt
    rw [htp] at hsw
    constructor
    · rintro ⟨hH, hA⟩
      by_cases hcase : S.Ts (encPair (padWith m x) (padWith m w)).length + 1
          + c * 3 ^ (m * q) * ((encPair (padWith m x) (padWith m w)).length + 1) ^ q ≤ tf
      · exfalso
        have hph := comp_phase1 S.Ms M (encPair (padWith m x) (padWith m w)) _
          (fun s hs => hmin s (lt_of_lt_of_le hs hcase))
        have hH' : (comp S.Ms M).halt
            (run (comp S.Ms M) _ (init (comp S.Ms M) (encPair (padWith m x) (padWith m w)))).st
            = true := hH
        rw [hph] at hH'
        exact absurd hH' (by simp [embedL, comp])
      · push_neg at hcase
        obtain ⟨s', hs'⟩ := Nat.exists_eq_add_of_le
          (show tf + 1 ≤ S.Ts (encPair (padWith m x) (padWith m w)).length + 1
              + c * 3 ^ (m * q) * ((encPair (padWith m x) (padWith m w)).length + 1) ^ q
            from by omega)
        have hrun := comp_phase2 S.Ms M (encPair (padWith m x) (padWith m w)) tf
          (encPair x w) s' hsw
        rw [← hs'] at hrun
        have hH' : (comp S.Ms M).halt
            (run (comp S.Ms M) _ (init (comp S.Ms M) (encPair (padWith m x) (padWith m w)))).st
            = true := hH
        have hA' : (comp S.Ms M).accept
            (run (comp S.Ms M) _ (init (comp S.Ms M) (encPair (padWith m x) (padWith m w)))).st
            = true := hA
        rw [hrun] at hH' hA'
        have hMH : M.halt (run M s' (init M (encPair x w))).st = true := hH'
        have hMA : M.accept (run M s' (init M (encPair x w))).st = true := hA'
        exact hfaith (encPair x w) s' hMH hMA
    · rintro ⟨hMH, hMA⟩
      have hrun := comp_phase2 S.Ms M (encPair (padWith m x) (padWith m w)) tf
        (encPair x w) (T (encPair x w).length) hsw
      have hcompH : (comp S.Ms M).halt
          (run (comp S.Ms M) (tf + 1 + T (encPair x w).length)
            (init (comp S.Ms M) (encPair (padWith m x) (padWith m w)))).st = true := by
        rw [hrun]; exact hMH
      have hle : tf + 1 + T (encPair x w).length
          ≤ S.Ts (encPair (padWith m x) (padWith m w)).length + 1
            + c * 3 ^ (m * q) * ((encPair (padWith m x) (padWith m w)).length + 1) ^ q := by
        have h1 : T (encPair x w).length ≤ c * ((encPair x w).length + 1) ^ (m * q) :=
          hclock (encPair x w).length
        have h2 := pad_clock_transfer2 m q c x w
        have h3 : T (encPair x w).length
            ≤ c * 3 ^ (m * q) * ((encPair (padWith m x) (padWith m w)).length + 1) ^ q :=
          le_trans h1 h2
        omega
      have hstab := run_stable (comp S.Ms M) (encPair (padWith m x) (padWith m w)) hle hcompH
      constructor
      · show (comp S.Ms M).halt
            (run (comp S.Ms M) _ (init (comp S.Ms M) (encPair (padWith m x) (padWith m w)))).st
            = true
        rw [hstab, hrun]
        exact hMH
      · show (comp S.Ms M).accept
            (run (comp S.Ms M) _ (init (comp S.Ms M) (encPair (padWith m x) (padWith m w)))).st
            = true
        rw [hstab, hrun]
        exact hMA
  badY := fun y hy w'' => by
    rintro ⟨hH, _⟩
    have hbad : ∀ x w : List Bool, encPair y w'' ≠ encPair (padWith m x) (padWith m w) := by
      intro x w heq
      exact hy x (encPair_injective heq).1
    have hnever := comp_never_halts S.Ms M (encPair y w'') (S.badLoop _ hbad)
    have hH' : (comp S.Ms M).halt
        (run (comp S.Ms M) _ (init (comp S.Ms M) (encPair y w''))).st = true := hH
    rw [hnever] at hH'
    exact Bool.noConfusion hH'
  badW := fun x w'' hw => by
    rintro ⟨hH, _⟩
    have hbad : ∀ x' w : List Bool,
        encPair (padWith m x) w'' ≠ encPair (padWith m x') (padWith m w) := by
      intro x' w heq
      exact hw w (encPair_injective heq).2
    have hnever := comp_never_halts S.Ms M (encPair (padWith m x) w'') (S.badLoop _ hbad)
    have hH' : (comp S.Ms M).halt
        (run (comp S.Ms M) _ (init (comp S.Ms M) (encPair (padWith m x) w''))).st = true := hH
    rw [hnever] at hH'
    exact Bool.noConfusion hH'

/-! ### The assembly: the NTIME half from the two named components -/

/-- **The concrete transducer obligation (camp 6).**  Pure machine engineering, fully concrete. -/
def StripTransducersExist : Prop := ∀ m, 1 ≤ m → Nonempty (StripTransducer m)

/-- **The normalization obligation (mountain-4-shared).**  Every `NTIME` witness has a
clock-faithful form — clocked simulation. -/
def NTIMENormalizable : Prop :=
  ∀ a L, NTIME a L → ∃ (M : Machine) (T : ℕ → ℕ) (c : ℕ), ClockLe a c T ∧ ClockFaithful M T ∧
    ∀ x, (L x = true ↔ ∃ w : List Bool,
      HaltsBy M (encPair x w) (T (encPair x w).length) ∧
      decideOut M (encPair x w) (T (encPair x w).length) = true)

/-- **The NTIME half from the two components (proved), for `q ≥ 1`.**  Strip transducers plus
clock-faithful normalization give the padding mountain's verifier side. -/
theorem ntimeHalf_of_components (hS : StripTransducersExist) (hN : NTIMENormalizable)
    (m q : ℕ) (hm : 1 ≤ m) (hq : 1 ≤ q) (L : Lang) (hL : NTIME (m * q) L) :
    NTIME q (padLang m L) := by
  obtain ⟨M, T, c, hclock, hfaith, hspec⟩ := hN (m * q) L hL
  obtain ⟨S⟩ := hS m hm
  exact ntime_pad2 m q L M T hspec (padVerifier2_of_strip m q hq S M T c hclock hfaith)

end PallLean.Paper93.DeepMath.PathB.PadVerifierComposition

#print axioms PallLean.Paper93.DeepMath.PathB.PadVerifierComposition.comp_never_halts
#print axioms PallLean.Paper93.DeepMath.PathB.PadVerifierComposition.comp_switch_run
#print axioms PallLean.Paper93.DeepMath.PathB.PadVerifierComposition.padVerifier2_of_strip
#print axioms PallLean.Paper93.DeepMath.PathB.PadVerifierComposition.ntimeHalf_of_components
