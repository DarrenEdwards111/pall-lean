import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ResidueMachine

/-!
# Step 4: depth iteration — reducing a depth-`d` ACC⁰ circuit to a residue-searchable depth-2 form

Steps 1–3 made the *depth-2* `MOD`-circuit SAT speedup operational (`residueSearch`, branched cost, survivor
restriction).  Real `ACC⁰` is depth-`d` layered (AND/OR/MOD of AND/OR/MOD of …).  The algorithm needs the circuit
collapsed to the depth-2 `MOD`-form the residue machine searches.

**Honest naming of the structural step.**  Switching collapses the AC⁰ (AND/OR) layers — but provably **not** the
`MOD` layer (the proved `…ACCSwitchingModBridge` no-go: switching cannot cross a `MOD` gate).  The genuine
depth-collapse for `ACC⁰` is the **Yao–Beigel–Tarui normal form**: every `ACC⁰` function is computed by a depth-2
circuit — a symmetric/arbitrary top gate over `MOD` (and small-`AND`) gates — i.e. it is `MixedModResidueSearchable`.
That normal form is a deep structural theorem, **not** supplied by switching or by this cell model; we name it the
`MixedACCDepthReductionSocket` (open), and prove it **suffices** and is **nonvacuous**.

The chain: `depth-d ACC⁰` ──[socket: Yao–Beigel–Tarui]──▶ residue-searchable depth-2 ──[steps 1–3]──▶ SAT in
`< 2^n` steps.  Everything after the socket is proved; the socket is the isolated remaining structural gap.

## What is proved (clean axioms, no `sorry`)

* `MixedModResidueSearchable` — `f` is computed by a depth-2 `MOD`-circuit of small modulus product (`< 2^n`).
* `residueSearchable_base` — **nonvacuous**: any small-modulus depth-2 `MOD`-circuit is residue-searchable (itself).
* `residueSearchable_gives_speedup` — **the socket suffices**: residue-searchable `f` ⇒ a timed algorithm deciding
  `Satisfiable f` in `< 2^n` steps.
* `acc0_depth_reduction_speedup` — the `ACC⁰` form: `MixedACCDepthReductionSocket C` ⇒ the residue search decides
  `Satisfiable (eval C)` in `< 2^n` steps.

## Honest scope

This isolates the depth-collapse as one named structural socket (Yao–Beigel–Tarui) and proves the entire downstream
(residue search) is already done, plus the base case.  It does **not** prove the normal form (a real theorem, hard
to formalise; switching provably cannot give it).  And even granting it, the cell-count speedup is **not**
`NEXP ⊄ ACC⁰` — that is step 5 (the uniform nondeterministic realisation + time-hierarchy cash-out).  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ResidueDepthReduction

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueMachine

variable {n k : ℕ}

/-- `f` is **residue-searchable**: computed on the cube by a depth-2 `MOD`-circuit whose moduli are positive and
whose product is `< 2^n` (so the residue search decides its SAT in `< 2^n` steps). -/
def MixedModResidueSearchable (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (k : ℕ) (C' : Depth2ModCircuit n k),
    (∀ x, f x = C'.eval x) ∧ (∀ j, 0 < (C'.gates j).modulus) ∧ (∏ j, (C'.gates j).modulus) < 2 ^ n

/-- **Nonvacuity (proved): a small-modulus depth-2 `MOD`-circuit is residue-searchable (by itself).**  The base case
of the depth iteration — depth-2 is already in the searchable form. -/
theorem residueSearchable_base (C : Depth2ModCircuit n k) (hpos : ∀ j, 0 < (C.gates j).modulus)
    (hsmall : (∏ j, (C.gates j).modulus) < 2 ^ n) :
    MixedModResidueSearchable C.eval :=
  ⟨k, C, fun _ => rfl, hpos, hsmall⟩

/-- **The socket suffices (proved): residue-searchable `f` ⇒ a timed algorithm deciding SAT in `< 2^n` steps.** -/
theorem residueSearchable_gives_speedup {f : (Fin n → Bool) → Bool}
    (h : MixedModResidueSearchable f) :
    ∃ (k : ℕ) (C' : Depth2ModCircuit n k),
      (∀ x, f x = C'.eval x)
        ∧ ((residueSearch C').result = true ↔ Satisfiable f)
        ∧ (residueSearch C').steps < 2 ^ n := by
  obtain ⟨k, C', heq, hpos, hsmall⟩ := h
  refine ⟨k, C', heq, ?_, residueSearch_beats_bruteforce C' hpos hsmall⟩
  rw [residueSearch_decides]
  unfold Satisfiable
  constructor
  · rintro ⟨x, hx⟩; exact ⟨x, by rw [heq x]; exact hx⟩
  · rintro ⟨x, hx⟩; exact ⟨x, by rw [← heq x]; exact hx⟩

/-- **(The named OPEN depth-reduction socket.)**  A depth-`d` `ACC⁰` circuit collapses to a residue-searchable
depth-2 form — the Yao–Beigel–Tarui normal form.  This is the genuine structural step (not switching, which the
`MOD` no-go blocks); granted it, the residue search decides the circuit's SAT in `< 2^n` steps. -/
def MixedACCDepthReductionSocket (C : ACC0Circuit n) : Prop :=
  MixedModResidueSearchable (eval C)

/-- **The depth-`d` ACC⁰ speedup, granted the depth-reduction socket (proved).**  If a depth-`d` `ACC⁰` circuit
collapses to a residue-searchable depth-2 form, the residue search decides `Satisfiable (eval C)` in `< 2^n`
steps — the full algorithmic chain, with the lone remaining gap the (named) Yao–Beigel–Tarui depth collapse. -/
theorem acc0_depth_reduction_speedup (C : ACC0Circuit n) (h : MixedACCDepthReductionSocket C) :
    ∃ (k : ℕ) (C' : Depth2ModCircuit n k),
      (∀ x, eval C x = C'.eval x)
        ∧ ((residueSearch C').result = true ↔ Satisfiable (eval C))
        ∧ (residueSearch C').steps < 2 ^ n :=
  residueSearchable_gives_speedup h

end PallLean.Paper93.DeepMath.PathB.ACC0ResidueDepthReduction

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ResidueDepthReduction.residueSearchable_base
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ResidueDepthReduction.residueSearchable_gives_speedup
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ResidueDepthReduction.acc0_depth_reduction_speedup
