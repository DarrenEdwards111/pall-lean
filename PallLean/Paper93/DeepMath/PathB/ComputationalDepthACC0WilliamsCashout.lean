import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ResidueDepthReduction

/-!
# Step 5: the Williams cash-out interface — residue speedup ⇒ `NEXP ⊄ ACC⁰` (conditional)

Steps 1–4 built the residue SAT-speedup chain: granted the depth-reduction socket
(`MixedACCDepthReductionSocket`, Yao–Beigel–Tarui), a depth-`d` `ACC⁰` circuit has its SAT decided by `residueSearch`
in `< 2^n` steps.  This file assembles the **cash-out interface** to Williams' algorithmic method — as an honest
interface layer over named sockets, **not** a from-scratch proof of the separation.

The architecture (each arrow a socket or a proved step):

```
∀ ACC⁰ C : MixedACCDepthReductionSocket C          -- socket 1 (Beigel–Tarui depth-2 normal form)
        │  mixedACC_speedup_of_depthReduction  (PROVED — steps 1–4 end to end)
        ▼
∀ n : MixedACCResidueSatSpeedup n                  -- residue SAT decided in < 2^n (cell model)
        │  uniform realization                      -- socket 2 (TM encoding / enumeration / poly overhead)
        ▼
UniformACC0SatSpeedup                              -- genuine 2^{n−n^ε} nondeterministic ACC⁰-SAT algorithm
        │  Williams algorithmic method              -- socket 3 (nondeterministic time hierarchy + witness compression)
        ▼
NEXP ⊄ ACC⁰
```

`UniformACC0SatSpeedup` and `NEXPnotACC0` are abstract `Prop` parameters: this file does **not** define `NTIME`,
`2^{n−n^ε}`, `NEXP`, or `ACC⁰`-as-a-class.  The only *proved* link is `mixedACC_speedup_of_depthReduction` (the
residue chain); the realization and Williams steps are sockets.

## What is proved (clean axioms, no `sorry`)

* `mixedACC_speedup_of_depthReduction` — **the proved link**: depth-reduction socket ⇒ residue SAT speedup for all
  `ACC⁰`.
* `residue_cashout_to_NEXP_not_ACC0` — **the master interface (modus ponens)**: depth socket + uniform-realization
  socket + Williams socket ⇒ `NEXP ⊄ ACC⁰`.
* `residue_cashout_bundled` — the headline 2-socket form: depth socket + `UniformWilliamsRealizationSocket` ⇒ `NEXP ⊄
  ACC⁰`.
* `williams_socket_iff_separation`, `realization_socket_iff_separation` — **the self-audit**: each cash-out socket,
  once the prior stage is established, is *logically equivalent to the separation* — so it carries the entire
  `NEXP ⊄ ACC⁰` difficulty and the conditional reduces nothing.

## Honest scope

The honest **anatomy** of the Williams route: one proved link (the residue chain) and two named, open,
separation-strength sockets (depth normal form; uniform realization + algorithmic method).  The self-audit theorems
make explicit that the cash-out sockets *are* the separation — a conditional `_of_*` theorem here is architecture,
**not** progress on `NEXP ⊄ ACC⁰`, which is an undefined abstract `Prop`.  Proves nothing about `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashout

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueMachine
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueDepthReduction

/-- The `ACC⁰`-SAT speedup in the residue cell model on `n` variables: **every** `ACC⁰` circuit has its SAT decided
by a residue search in `< 2^n` steps. -/
def MixedACCResidueSatSpeedup (n : ℕ) : Prop :=
  ∀ C : ACC0Circuit n,
    ∃ (k : ℕ) (C' : Depth2ModCircuit n k),
      (∀ x, eval C x = C'.eval x)
        ∧ ((residueSearch C').result = true ↔ Satisfiable (eval C))
        ∧ (residueSearch C').steps < 2 ^ n

/-- **The proved link (modulo the depth-reduction socket): the residue chain delivers the `ACC⁰`-SAT speedup.**
Steps 1–4 end to end: if every `ACC⁰` circuit collapses to a residue-searchable depth-2 form, every one has its SAT
decided in `< 2^n` steps. -/
theorem mixedACC_speedup_of_depthReduction (n : ℕ)
    (h : ∀ C : ACC0Circuit n, MixedACCDepthReductionSocket C) :
    MixedACCResidueSatSpeedup n :=
  fun C => acc0_depth_reduction_speedup C (h C)

/-- **The master cash-out interface (proved, modus ponens): three sockets ⇒ the separation.**  Given
(1) the depth-reduction socket for all `ACC⁰` circuits, (2) the uniform-realization socket turning the residue cell
speedup into a genuine `2^{n−n^ε}` nondeterministic `ACC⁰`-SAT algorithm, and (3) the Williams algorithmic-method
socket turning that algorithm into the separation — `NEXP ⊄ ACC⁰` follows.  This is the *architecture*; all content
is in the three (open) hypotheses. -/
theorem residue_cashout_to_NEXP_not_ACC0 {UniformACC0SatSpeedup NEXPnotACC0 : Prop}
    (hdepth : ∀ (n : ℕ) (C : ACC0Circuit n), MixedACCDepthReductionSocket C)
    (hrealize : (∀ n, MixedACCResidueSatSpeedup n) → UniformACC0SatSpeedup)
    (hwilliams : UniformACC0SatSpeedup → NEXPnotACC0) :
    NEXPnotACC0 :=
  hwilliams (hrealize (fun n => mixedACC_speedup_of_depthReduction n (hdepth n)))

/-- The bundled cash-out socket: the residue cell speedup (for all `ACC⁰`) realizes, via uniform encoding and
Williams' method, the separation. -/
def UniformWilliamsRealizationSocket (NEXPnotACC0 : Prop) : Prop :=
  (∀ n, MixedACCResidueSatSpeedup n) → NEXPnotACC0

/-- **The headline (proved): two sockets cash out the residue chain to `NEXP ⊄ ACC⁰`.**  If the depth-reduction
socket and the uniform-Williams-realization socket both hold, the residue-speedup chain (steps 1–4) cashes out to
`NEXP ⊄ ACC⁰`.  The architecture is closed; the two sockets are the entire remaining content. -/
theorem residue_cashout_bundled {NEXPnotACC0 : Prop}
    (hdepth : ∀ (n : ℕ) (C : ACC0Circuit n), MixedACCDepthReductionSocket C)
    (hrealize : UniformWilliamsRealizationSocket NEXPnotACC0) :
    NEXPnotACC0 :=
  hrealize (fun n => mixedACC_speedup_of_depthReduction n (hdepth n))

/-- **Self-audit (proved): the Williams socket is equivalent to the separation.**  Once a genuine uniform `ACC⁰`-SAT
speedup is established, the Williams algorithmic-method hypothesis `(UniformACC0SatSpeedup → separation)` is
*logically equivalent* to `NEXP ⊄ ACC⁰` itself — it carries the whole difficulty, the conditional reduces nothing. -/
theorem williams_socket_iff_separation {UniformACC0SatSpeedup NEXPnotACC0 : Prop}
    (huniform : UniformACC0SatSpeedup) :
    (UniformACC0SatSpeedup → NEXPnotACC0) ↔ NEXPnotACC0 :=
  ⟨fun h => h huniform, fun h _ => h⟩

/-- **Self-audit (proved): the bundled realization socket is equivalent to the separation.**  Once the residue
speedup is established (depth-reduction socket), `UniformWilliamsRealizationSocket` is *logically equivalent* to
`NEXP ⊄ ACC⁰` — the cash-out parks the entire separation difficulty in this one socket. -/
theorem realization_socket_iff_separation {NEXPnotACC0 : Prop}
    (hspeedup : ∀ n, MixedACCResidueSatSpeedup n) :
    UniformWilliamsRealizationSocket NEXPnotACC0 ↔ NEXPnotACC0 :=
  ⟨fun h => h hspeedup, fun h _ => h⟩

end PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashout

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashout.mixedACC_speedup_of_depthReduction
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashout.residue_cashout_to_NEXP_not_ACC0
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashout.residue_cashout_bundled
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashout.williams_socket_iff_separation
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashout.realization_socket_iff_separation
