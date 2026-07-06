import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCutRigid

/-!
# N-Frame: the ε-biased attempt — the detection matrix is `M`, and why ε-biased fails

Attempt to prove that an explicit ε-biased `M` gives a weak every-cut `F₂`-rank bound.  The
detection-matrix bridge is frozen in Lean; the ε-biased bound itself is worked on paper, with
an HONEST negative outcome: ε-biasedness is the wrong tool.

  `bilinSym_units` — **PROVED, THE DETECTION MATRIX**: `bilinSym A (e_a) (e_b) = A_{ab} + A_{ba}`,
        the `(a,b)` entry of `M = A + Aᵀ`.  So evaluating `qform`'s detection on the unit
        directions RECONSTRUCTS `M`: the cut-rank of `qform A` across `(S, Sᶜ)` is exactly
        `rank_{F₂}(M_{S,Sᶜ})`, and an induced cross-matching of size `r` (rows `a_1..a_r ∈ S`,
        cols `b_1..b_r ∈ Sᶜ` with `M_{a_k,b_l} = [k=l]`) gives `r` independent detectable
        directions, so `cut-rank ≥ r`.

## Honest scope — ε-biased does NOT give a provable every-cut bound

The every-cut requirement `rank_{F₂}(M_{S,Sᶜ}) ≥ r` for ALL `2^N` balanced cuts is the
obstruction, and it defeats the ε-biased approach:

- **What DOES work (non-explicit): a RANDOM `M`.**  For a fixed cut, `Pr[corank ≥ t] ≈ 2^{-t²}`
  (each rank deficiency costs `~2^{-2t+1}`); union over the `≤ 2^N` balanced cuts needs
  `2^{-t²} < 2^{-N}`, i.e. `t > √N`.  So a random `M` has `rank_{F₂}(M_{S,Sᶜ}) ≥ N/2 − O(√N) =
  Θ(N)` at EVERY balanced cut, whp.  The target is achievable — just not explicitly.

- **Why ε-biased FAILS.**  An ε-biased distribution over the entries controls LINEAR tests: for
  `r` independent tests, `|Pr[all zero] − 2^{-r}| < ε`.  The first-moment bound on `t`-dim
  kernels gives `E[#t-dim kernels] ≤ 2^{tN/2}·(2^{-tN/2} + ε) = 1 + ε·2^{tN/2}`, so to force
  corank `< t` at even ONE cut needs `ε < 2^{-tN/2}`; with the union over `2^N` cuts,
  `ε ≤ 2^{-Θ(N^{1.5})}` — seed length `Θ(N^{1.5})`, no better than a truly random matrix.  A
  standard small-bias set (`ε = 1/poly(N)`, seed `O(log N)`) does NOT survive: ε-biasedness is a
  "few linear tests" tool, and the every-cut kernel analysis has `2^{Θ(N)}` events.  **The
  union bound over exponentially many cuts is the barrier, and ε-biasedness cannot pay for it.**

So the honest answer is that ε-biased `M` does NOT provably give a weak every-cut bound — not
because the bound is false (random `M` has it) but because the ε-biased CERTIFICATE (linear-test
bias) is the wrong certificate for an every-cut (exponentially-many-events) property.  The gap
between "random works" and "ε-biased fails" IS the explicit-rigidity barrier, now located
sharply at the union-bound-over-cuts step.  A provable EXPLICIT every-cut bound needs a
certificate that is not per-cut (e.g. an algebraic every-cut induced-matching guarantee), which
is the open problem.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameEpsBias

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameQuadForm
open PallLean.Paper93.DeepMath.PathB.NFrameCutRigid

variable {N : ℕ}

/-- **THE DETECTION MATRIX (proved)**: evaluating the polarization on the unit directions
`e_a, e_b` returns the `(a,b)` entry of `M = A + Aᵀ`.  So the detection matrix of `qform A`
is exactly `M`, and the cut-rank is `rank_{F₂}(M_{S,Sᶜ})`. -/
theorem bilinSym_units (A : Fin N → Fin N → ZMod 2) (a b : Fin N) :
    bilinSym A (fun i => if i = a then 1 else 0) (fun i => if i = b then 1 else 0)
      = A a b + A b a := by
  rw [bilinSym_eq]
  rw [Finset.sum_eq_single a
    (fun i _ hia => by
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg hia, zero_mul, mul_zero])
    (fun h => absurd (Finset.mem_univ a) h)]
  rw [Finset.sum_eq_single b
    (fun j _ hjb => by rw [if_neg hjb, mul_zero, mul_zero])
    (fun h => absurd (Finset.mem_univ b) h)]
  rw [if_pos rfl, if_pos rfl, mul_one, mul_one]

/-- **The induced-matching detection (proved)**: for a matched pair `(a, b)` off the diagonal
with `M_{ab} = 1` (an edge) and `M`'s symmetric entry, the unit direction `e_b` is detected at
`e_a` iff `(a,b)` is an edge — the atom of the cut-rank = induced-matching bound. -/
theorem bilinSym_edge (A : Fin N → Fin N → ZMod 2) (a b : Fin N)
    (hedge : A a b + A b a = 1) :
    bilinSym A (fun i => if i = a then 1 else 0) (fun i => if i = b then 1 else 0) = 1 := by
  rw [bilinSym_units]; exact hedge

end PallLean.Paper93.DeepMath.PathB.NFrameEpsBias

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameEpsBias.bilinSym_units
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameEpsBias.bilinSym_edge
