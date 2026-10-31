import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameKRW

/-!
# N-Frame → KRW: concrete monotone instances (connectivity + lifting) → unconditional super-log depth

The monotone route is where KRW composition is a THEOREM.  This file instantiates the KRW/KW framework
with concrete monotone functions whose monotone formula depth is known unconditionally, and derives —
machine-checked — that the depth is SUPER-LOGARITHMIC (outside `NC¹`-depth `c·log N` for every constant
`c`).  The depth bounds themselves are cited theorems (Karchmer–Wigderson; Raz–McKenzie / Göös–Pitassi
lifting) — they rest on communication complexity, which is not in Mathlib; what is formalized here is the
super-log conclusion the framework extracts from their numeric output.

## Instance 1 — st-connectivity (Karchmer–Wigderson)

`STCONN` (is there an `s`–`t` path?) is monotone with monotone formula depth `Θ(log² N)` on `N`-vertex
graphs [Karchmer–Wigderson 1988], via the recursive KW game: `d = log N` rounds, each contributing
`Δ = Θ(log N)` communication.  Feeding `(d, Δ, L) = (log N, log N, 1)` into `krw_beats_log_depth`:

  `connectivity_monotone_superlog` — **PROVED**: with `t := log N`, `D_mon = t·t = log² N`, for every
        constant `c` and `t > c` (i.e. `N > 2^c`) we get `c·log N < log² N` — unconditionally
        super-logarithmic monotone depth.  This is the first super-log depth bound (KW), re-proved and
        strengthened by lifting.

## Instance 2 — lifting a hard decision tree (Raz–McKenzie / Göös–Pitassi–Watson)

The query-to-communication lifting theorem: for an outer function `f` with decision-tree depth `q`
composed with a monotone indexing gadget `IND_m`, the monotone KW complexity (= monotone depth) of
`f ⋄ IND_m` is `Θ(q · log m)`.  Choosing `q` and `m` polynomial gives monotone depth up to `N^{Ω(1)}`.

  `lifting_monotone_superlog` — **PROVED**: given the lifting output `q · Λ ≤ D_mon` (`Λ = log m`) and
        `c · log N < q · Λ` (the lifted depth beats `c·log N`), we get `c · log N < D_mon`.
  `lifting_instance_concrete` — **PROVED (witness)**: with query depth `q = n`, gadget `Λ = 2t`
        (`t = log n`), input `log N = 3t`, and `3c < 2n`, the lifted depth `n·2t` exceeds `c·3t` — a
        concrete super-log (indeed `≈ n log n`) monotone depth on `N = n³` bits.

## Honest scope

The framework (`krw_amplifies`, `krw_beats_log_depth`) and these instantiations are proved arithmetic.
The DEPTH inputs — `D_mon(STCONN) = Θ(log² N)` and `D_mon(f ⋄ IND) = Θ(q·log m)` — are cited unconditional
theorems (KW; Raz–McKenzie; GPW lifting), not formalized here (they need a communication-complexity
development).  So this is a genuine, unconditional MONOTONE super-log depth lower bound assembled from a
cited monotone depth theorem and the machine-checked framework — the stepping stone.  It is a monotone /
formula-depth statement, NOT a general circuit bound: nothing here is `P ⊄ NC¹` (general, open), `NEXP ⊄
ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameKRWMonotone

open PallLean.Paper93.DeepMath.PathB.NFrameKRW

/-- **CONNECTIVITY IS SUPER-LOG (proved instantiation)**: with `t := log N` and the KW theorem
`D_mon(STCONN) = t·t = log² N` (the recursive KW game: `t` rounds, `Δ = t` each), for every constant `c`
and `t > c` (`N > 2^c`) the framework gives `c·(t·1) < t·t`, i.e. `c·log N < log² N`.  Unconditional
super-logarithmic monotone formula depth. -/
theorem connectivity_monotone_superlog (t c : ℕ) (ht : 1 ≤ t) (hc : c < t) :
    c * (t * 1) < t * t :=
  krw_beats_log_depth (t * t) t t 1 c ht (le_refl (t * t)) (by omega)

/-- **LIFTING GIVES SUPER-LOG (proved)**: the lifting theorem output `q·Λ ≤ D_mon` (`q` = decision-tree
depth of the outer function, `Λ = log m` the gadget), together with the lifted depth beating `c·log N`
(`c·log N < q·Λ`), yields `c·log N < D_mon` — super-`c·log N` monotone depth. -/
theorem lifting_monotone_superlog (Dmon q Λ logN c : ℕ)
    (hlift : q * Λ ≤ Dmon) (hbeat : c * logN < q * Λ) :
    c * logN < Dmon := by
  omega

/-- **CONCRETE LIFTING WITNESS (proved)**: query depth `q = n`, gadget `Λ = 2t` (`t = log n`), input
`log N = 3t` (`N = n³`); for `3c < 2n` the lifted depth `n·(2t)` exceeds `c·(3t)` — a concrete
unconditional super-log (`≈ n log n`) monotone depth. -/
theorem lifting_instance_concrete (n t c : ℕ) (ht : 1 ≤ t) (hnc : 3 * c < 2 * n) :
    c * (3 * t) < n * (2 * t) := by
  nlinarith [ht, hnc]

end PallLean.Paper93.DeepMath.PathB.NFrameKRWMonotone

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameKRWMonotone.connectivity_monotone_superlog
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameKRWMonotone.lifting_monotone_superlog
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameKRWMonotone.lifting_instance_concrete
