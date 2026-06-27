import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMUSim
import Mathlib.Tactic

/-!
# RAM lazy diagonal decider — the diagonal wrap skeleton (PROVED, with named sockets) — step 2, brick 4

Bricks 1–3 built the decider as a real RAM program: decode → dispatch → clock → **simulate inside the clock**.
This brick performs the **diagonal wrap**: the decider, on input `x`, simulates machine `x` on `x` (its
self-application) within the clock budget and outputs the **complement** of the simulated bit.  The classical
diagonal argument then gives: the decider's function differs from every machine in the simulated class.

This is the honest *skeleton* of the (lazy) diagonalisation.  Two facts are load-bearing and are **named
sockets, not proved here** — they are exactly the separation-strength classical content:

* `FaithfulOnDiagonal` — the clocked simulator reproduces the class value on every self-application.  This holds
  precisely when the clock budget **dominates** each machine's running time, i.e. membership in the clocked
  class.  For `ACC⁰` this is the Beigel–Tarui `SYM∘AND` quasipoly normal form plus the Williams fast-`SAT`
  speed-up — *not* proved here.
* the decider's own **efficiency** (`Big (ramDiag sim)`, e.g. the decider lies in `NEXP`) — needs the clocked
  simulation of every class member to fit the bigger class's budget; again the Williams fast-`SAT` content.

What *is* proved here is the diagonalisation core and its RAM realisation: the decider's complement branch
genuinely computes the diagonal function (`ramDiag_realized_by_clockedDecider`), and from the two sockets the
class separation follows (`class_separation`).  Discharging the sockets **is** the theorem `NEXP ⊄ ACC⁰`; this
file does not do that and does not claim to.  It lays the diagonal skeleton onto which the classical bridges
plug.
-/

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-! ### The diagonalisation core (PROVED, unconditional) -/

/-- The diagonal function: complement of machine `x`'s simulated self-application bit.  (Boolean bits are
`0/1`; `1 - ·` is the flip.)  This is what the decider's complement branch computes. -/
def ramDiag (sim : ℕ → ℕ → ℕ) (x : ℕ) : ℕ := 1 - sim x x

/-- **The diagonal value disagrees with the machine it diagonalises against.**  On a Boolean self-application,
`ramDiag sim e ≠ sim e e`. -/
theorem ramDiag_ne (sim : ℕ → ℕ → ℕ) (e : ℕ) (hbit : sim e e ≤ 1) :
    ramDiag sim e ≠ sim e e := by
  simp only [ramDiag]; omega

/-- **No machine of the class computes the diagonal function.**  If every class machine is Boolean on its own
diagonal, then there is no index `e` whose row equals `ramDiag sim` — the diagonal escapes the class.  This is
the unconditional diagonalisation core. -/
theorem ramDiag_not_mem (sim : ℕ → ℕ → ℕ) (hbit : ∀ e, sim e e ≤ 1) :
    ¬ ∃ e, ∀ x, sim e x = ramDiag sim x := by
  rintro ⟨e, he⟩
  have h := he e
  have hb := hbit e
  simp only [ramDiag] at h
  omega

/-! ### RAM realisation (PROVED): the decider's complement branch computes the diagonal -/

/-- **The RAM decider realises the diagonal flip.**  `clockedDecider`'s complement branch outputs `1 - inp`;
with the input cell `mem[12]` holding the simulated self-value `sim x x`, the decider's result cell `mem[3]`
holds `1 - sim x x = ramDiag sim x`.  So the actual RAM program genuinely computes the diagonal function — the
abstract `ramDiag` is not a fiction, it is what brick 2's complement branch does. -/
theorem ramDiag_realized_by_clockedDecider (sim : ℕ → ℕ → ℕ) (x : ℕ) (m : Mem) (acc : ℕ)
    (hmode : m 11 ≠ 0) (hinp : m 12 = sim x x) :
    (run clockedDecider ⟨m, acc, 0, false⟩ 12).mem 3 = ramDiag sim x := by
  have h := (clockedDecider_complement m acc hmode).2
  simp only [ramDiag, h, hinp]

/-! ### The named sockets and the separation skeleton -/

/-- **SOCKET 1 (faithful clocked simulation = budget domination = class membership).**  The clocked simulator
reproduces the class value on every self-application.  This is the load-bearing bridge: it holds exactly when
the clock budget dominates each machine `e`'s running time.  For `ACC⁰` it is the Beigel–Tarui `SYM∘AND`
quasipoly form + the Williams fast-`SAT` speed-up — separation-strength, **not proved here**. -/
def FaithfulOnDiagonal (C sim : ℕ → ℕ → ℕ) : Prop := ∀ e, sim e e = C e e

/-- **Diagonal separation skeleton.**  Given faithful clocked simulation on the diagonal (Socket 1) and a
Boolean class, the decider's diagonal function `ramDiag sim` differs from every machine of the class `C`: no
index `e` has `C e = ramDiag sim`.  This is the honest core; the only nontrivial input is Socket 1. -/
theorem diagonal_separation_skeleton (C sim : ℕ → ℕ → ℕ)
    (hfaith : FaithfulOnDiagonal C sim) (hbit : ∀ e, C e e ≤ 1) :
    ¬ ∃ e, ∀ x, C e x = ramDiag sim x := by
  rintro ⟨e, he⟩
  have h1 : C e e = ramDiag sim e := he e
  have h2 : sim e e = C e e := hfaith e
  have hb := hbit e
  simp only [ramDiag] at h1
  omega

/-- **Class separation (skeleton).**  The decider lies in the bigger class `Big` (Socket 2 — decider
efficiency, the Williams fast-`SAT` content) **and** is not in the class `C` (from Socket 1 via the diagonal
core).  This is the shape of `C ⊊ Big`; instantiating `C := ACC⁰`, `Big := NEXP` and discharging the two
sockets **is** `NEXP ⊄ ACC⁰`.  The sockets are not discharged here. -/
theorem class_separation (C sim : ℕ → ℕ → ℕ) (Big : (ℕ → ℕ) → Prop)
    (hfaith : FaithfulOnDiagonal C sim) (hbit : ∀ e, C e e ≤ 1)
    (hbig : Big (ramDiag sim)) :
    Big (ramDiag sim) ∧ ¬ ∃ e, ∀ x, C e x = ramDiag sim x :=
  ⟨hbig, diagonal_separation_skeleton C sim hfaith hbit⟩

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.ramDiag_not_mem
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.ramDiag_realized_by_clockedDecider
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.diagonal_separation_skeleton
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.class_separation
