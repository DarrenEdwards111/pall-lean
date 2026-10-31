import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniformityGapDiagonal
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHierarchyDiagonalSkeleton

/-!
# Discharging the enumerability socket — for the canonical-clock class, with an audit finding

The hierarchy skeleton left two sockets; `NTIMEEnumerable b` was the tractable one.  Attacking it
surfaces a genuine defect in the class definition, and then discharges the fixed version.

## The audit finding

`NTIME b` quantifies the clock over an ARBITRARY `T : ℕ → ℕ` with `ClockLe b c T`.  There are
uncountably many such `T` (any function bounded by `c·(n+1)^b`), and a NON-COMPUTABLE sub-clock
yields a non-computable language that is still in `NTIME b` by the definition.  So `NTIME b` is not
countable, and `NTIMEEnumerable b` — as stated over the arbitrary-clock class — is FALSE.  This is
why the tractable socket cannot be discharged as-is: the obstruction is the definition, not the
proof.  (Standard complexity fixes this by attaching the clock to the machine — running exactly
`c·(n+1)^b` steps — which is the canonical class below.)

## The fix and the discharge

`NTIMEcanon b` fixes the clock to the canonical `c·(n+1)^b` and parametrises by a FINITE-state
machine (`FinMachineData`) plus the constant `c` — a countable parameter space.

* **`NTIMEcanon_sub_NTIME`** (proved) — the canonical class is a sub-class: `NTIMEcanon b L → NTIME
  b L`.
* **`ntimecanon_enumerable`** (proved) — `NTIMEcanon b` IS enumerable: the parameter space
  `Σ k, FinMachineData k × ℕ` is countable, so a surjection `ℕ → params` gives an enumeration
  covering every canonical language.  The tractable socket, discharged for the fixed-clock class.

## Consequence for the hierarchy

With the clock canonicalised in the class definition, `ntimecanon_enumerable` discharges the
hierarchy's first socket, leaving only `DiagonalInNTIME` (universal machine + lazy diagonalisation).
The recommendation is concrete: the engine's `NTIME`/`DTS`/`Σ₂` should attach the clock to the
machine (canonical form) — a definitional refinement that costs nothing downstream (the engine and
audits are clock-agnostic) and makes the hierarchy ingredient closable.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NTIMEEnumerable

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization
open PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses
open PallLean.Paper93.DeepMath.PathB.UniformityGapDiagonal

/-- The canonical clock `c·(n+1)^b`. -/
def canonClock (b c n : ℕ) : ℕ := c * (n + 1) ^ b

/-- The language of a canonical-clock finite-state verifier `(data, c)`: accept `x` iff some witness
`w` makes `ofData data` halt-and-accept on `encPair x w` within the canonical clock.  (Classical: the
witness existential is over all strings.) -/
noncomputable def canonLang (b : ℕ) (k : ℕ) (data : FinMachineData k) (c : ℕ) : Lang := fun x =>
  if (∃ w : List Bool,
      HaltsBy (ofData data) (encPair x w) (canonClock b c (encPair x w).length) ∧
      decideOut (ofData data) (encPair x w) (canonClock b c (encPair x w).length) = true)
    then true else false

/-- The canonical-clock nondeterministic class: parametrised by a finite-state machine and clock
constant only. -/
def NTIMEcanon (b : ℕ) (L : Lang) : Prop :=
  ∃ (k : ℕ) (data : FinMachineData k) (c : ℕ), L = canonLang b k data c

/-- Acceptance of the canonical language is exactly the witness existential. -/
theorem canonLang_true_iff (b k : ℕ) (data : FinMachineData k) (c : ℕ) (x : List Bool) :
    canonLang b k data c x = true ↔
      (∃ w : List Bool,
        HaltsBy (ofData data) (encPair x w) (canonClock b c (encPair x w).length) ∧
        decideOut (ofData data) (encPair x w) (canonClock b c (encPair x w).length) = true) := by
  unfold canonLang
  split <;> simp_all

/-- **The canonical class is a sub-class of `NTIME` (proved).**  The canonical clock `c·(n+1)^b`
satisfies `ClockLe b c`, so a canonical verifier is an `NTIME(b)` verifier. -/
theorem NTIMEcanon_sub_NTIME (b : ℕ) (L : Lang) (h : NTIMEcanon b L) : NTIME b L := by
  obtain ⟨k, data, c, rfl⟩ := h
  exact ⟨ofData data, fun n => canonClock b c n, c, fun n => le_of_eq rfl,
    fun x => canonLang_true_iff b k data c x⟩

/-- A nonempty parameter (a one-state machine). -/
instance : Nonempty (Σ k, FinMachineData k × ℕ) :=
  ⟨⟨1, (⟨0, fun _ => false, fun s _ => (s, none, 2), fun _ => false⟩, 0)⟩⟩

/-- **The enumerability socket, discharged for the canonical class (proved).**  `NTIMEcanon b` is
enumerable: `Σ k, FinMachineData k × ℕ` is countable, so a surjection `ℕ → params` yields an
enumeration `ℕ → Lang` covering every canonical-clock language. -/
theorem ntimecanon_enumerable (b : ℕ) :
    ∃ enum : ℕ → Lang, ∀ L, NTIMEcanon b L → ∃ i, L = enum i := by
  obtain ⟨e, he⟩ := exists_surjective_nat (Σ k, FinMachineData k × ℕ)
  refine ⟨fun i => canonLang b (e i).1 (e i).2.1 (e i).2.2, ?_⟩
  rintro L ⟨k, data, c, rfl⟩
  obtain ⟨i, hi⟩ := he ⟨k, data, c⟩
  exact ⟨i, by dsimp only; rw [hi]⟩

end PallLean.Paper93.DeepMath.PathB.NTIMEEnumerable

#print axioms PallLean.Paper93.DeepMath.PathB.NTIMEEnumerable.NTIMEcanon_sub_NTIME
#print axioms PallLean.Paper93.DeepMath.PathB.NTIMEEnumerable.ntimecanon_enumerable
