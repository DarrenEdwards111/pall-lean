import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ConcreteNTM
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TimeHierarchyDiagonal

/-!
# Universal simulation (interpreter level) — `enum_covers` discharged, the overhead socket isolated

With machines now encodable (`…ACC0ConcreteNTM.machineEquiv : TMachine ≃ ℕ`), the **interpreter-level** universal
simulation is provable: a single step-relation `univStep code`, decoding `code` to a machine and applying its step,
simulates *any* machine (when `code = ⟨M⟩`) — exactly, with no overhead at the relation level.  The overhead only
appears when this interpreter is compiled into a *physical* machine; that physical-overhead bound is the one part still
socketed.

The payoff: the concrete time class `cNTIME f` (over encodable `TMachine`s) is **enumerable**, so the hierarchy socket
`enum_covers` is now a *theorem* — and the nondeterministic time hierarchy reduces to the single remaining socket
`diag_in_big` (the diagonal decidable within the bigger time bound, i.e. simulation within the time budget — where the
physical overhead matters).

## What is proved (clean axioms, no `sorry`)

* **`univStep`, `univStep_correct`, `univStep_eq`** — the universal interpreter: `univStep (⟨M⟩) = concreteStep M`.
* **`cNTIME`** — concrete nondeterministic time over encodable machines; **`enum`** — its machine enumeration.
* **`enum_covers`** — **proved**: `cNTIME f ⊆ Set.range (enum f)` (every concrete-`NTIME` language is some enumerated
  machine's language, via `machineEquiv`).  *This discharges a hierarchy socket.*
* **`diag_not_mem_cNTIME`** — the diagonal language is **not** in `cNTIME g` (Cantor + `enum_covers`).
* **`cTime_hierarchy`** — given the single remaining socket `diag_in_big` (`diagLang ∈ cNTIME f`),
  `¬ (cNTIME f ⊆ cNTIME g)` — the concrete nondeterministic time hierarchy.

## Honest scope

`enum_covers` is genuinely *proved* (machine enumerability), discharging one of the two hierarchy sockets; the diagonal
argument is now complete down to `diag_in_big` alone.  But `diag_in_big` — that the diagonal language is *decidable
within the bigger time bound* — needs a **physical universal machine with a verified overhead bound** (simulate
`g`-time machines within `f`-time, `f ≫ g`).  Building that physical machine and proving its overhead is the remaining
deep step; the interpreter-level simulation here has no overhead and so cannot supply it.  This does **not** prove the
hierarchy outright.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalNTM

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (Lang CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (acceptsWithin)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine CConfig concreteStep toNTM machineEquiv)
open PallLean.Paper93.DeepMath.PathB.ACC0TimeHierarchyDiagonal (diagLang diag_not_mem_range idxEquiv)

/-- **The universal interpreter step**: decode `code` to a machine and apply its step relation. -/
def univStep (code : ℕ) (c d : CConfig) : Prop :=
  concreteStep (machineEquiv.symm code) c d

/-- **Universal simulation, interpreter level (proved): `univStep ⟨M⟩` simulates `M` exactly.** -/
theorem univStep_correct (M : TMachine) (c d : CConfig) :
    univStep (machineEquiv M) c d ↔ concreteStep M c d := by
  unfold univStep
  rw [Equiv.symm_apply_apply]

theorem univStep_eq (M : TMachine) : univStep (machineEquiv M) = concreteStep M := by
  funext c d
  exact propext (univStep_correct M c d)

/-- Concrete nondeterministic time over encodable machines. -/
def cNTIME (f : ℕ → ℕ) : CClass :=
  { L : Lang | ∃ M : TMachine, ∀ x, L x ↔ acceptsWithin (toNTM M) x (f x.length) }

/-- The language a machine `M` decides within the bound `f`. -/
def langOf (M : TMachine) (f : ℕ → ℕ) : Lang :=
  fun x => acceptsWithin (toNTM M) x (f x.length)

/-- The enumeration of `cNTIME f` languages, indexed by machine code. -/
noncomputable def enum (f : ℕ → ℕ) (k : ℕ) : Lang :=
  langOf (machineEquiv.symm k) f

/-- **`enum_covers` is a theorem (proved): every concrete-`NTIME` language is enumerated.**  A language `L ∈ cNTIME f`
is decided by some machine `M`; then `L = enum f ⟨M⟩` via `machineEquiv`.  This discharges a hierarchy socket. -/
theorem enum_covers (f : ℕ → ℕ) : cNTIME f ⊆ Set.range (enum f) := by
  rintro L ⟨M, hM⟩
  refine ⟨machineEquiv M, ?_⟩
  funext x
  simp only [enum, langOf, Equiv.symm_apply_apply]
  exact propext (hM x).symm

/-- **The diagonal language is not in `cNTIME g` (proved).**  Cantor (`diag_not_mem_range`) plus `enum_covers`. -/
theorem diag_not_mem_cNTIME (g : ℕ → ℕ) :
    diagLang (enum g) idxEquiv ∉ cNTIME g := by
  intro hmem
  exact diag_not_mem_range (enum g) idxEquiv (enum_covers g hmem)

/-- The concrete nondeterministic time hierarchy statement. -/
def cConcreteHierarchy (f g : ℕ → ℕ) : Prop := ¬ (cNTIME f ⊆ cNTIME g)

/-- **The concrete time hierarchy, down to one socket (proved).**  With `enum_covers` discharged, the hierarchy
`¬ (cNTIME f ⊆ cNTIME g)` follows from the single remaining socket `diag_in_big`: the diagonal language is decidable
within the bigger bound `f` (the physical universal simulator with overhead). -/
theorem cTime_hierarchy (f g : ℕ → ℕ)
    (diag_in_big : diagLang (enum g) idxEquiv ∈ cNTIME f) :
    cConcreteHierarchy f g := by
  intro hsub
  exact diag_not_mem_cNTIME g (hsub diag_in_big)

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalNTM

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalNTM.univStep_correct
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalNTM.enum_covers
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalNTM.diag_not_mem_cNTIME
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalNTM.cTime_hierarchy
