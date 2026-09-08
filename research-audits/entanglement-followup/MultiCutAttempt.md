# Attempt: sum dynamic rank across observer cuts

2026-09-09. Elementary derivation and finite enumeration; not Lean verified. No separation.

## Candidate

For q qubits, define E(psi) as the sum of log2 Schmidt rank over all unordered nontrivial bipartitions. This tests whether many observer perspectives amplify a small single-cut cost into a superpolynomial one.

## Exact example

Start with |+> on qubit 0 and |0> on every other qubit. Every cut has Schmidt rank one, so E=0. Apply CNOT from qubit 0 to qubit 1. Now those two qubits form a Bell pair, with all others unentangled.

Each cut separating qubits 0 and 1 has log2 rank one; every other cut has log2 rank zero. Count each unordered cut by choosing the side containing qubit 0. Qubit 1 must be outside, and the other q-2 qubits may be assigned freely. Exactly 2^(q-2) cuts contribute. Thus ONE gate changes E by 2^(q-2). Applying that same gate again removes this entire cost.

Consequently the maximum additive per-step reduction r for this gate model is at least 2^(q-2). For this example E_initial/r <= 1 on the disentangling run. Exponentially many perspectives do not yield independent charges automatically.

## Weighted repair

For fixed nonnegative weights w_C, a two-qubit gate on a,b changes each cut's log rank by at most two, and changes it by zero when a,b are on the same side. Therefore

 |delta E| <= 2 SUM_{C separating a,b} w_C.

This is a triangle-inequality upper bound, not asserted tight. Choosing weights to limit each gate's summed change also limits the amplification attributed to that gate. If weights vary with time, additional weight-change terms must be included; they cannot be silently omitted.

A normalized average avoids the exponential duplication but each cut's log rank is <= q/2, so the average is <= q/2. This does not rule out a superpolynomial accumulated path-cost lower bound, but such necessity is not established by counting cuts.

## Applicability to separate P and NP observers

The many cuts in this experiment are candidate mathematical perspectives, not assumed physical copies of the system or the repository's exact observer construction. If a particular physical boundary prohibits the gate, this example is not an allowed operation at that boundary. A universal SAT lower bound still requires a faithful simulation theorem for the allowed operations. No such theorem is supplied here.

## Reproduction

Run: python3 research-audits/entanglement-followup/multi-cut-check.py
Compare the emitted JSON with multi-cut-results.json. The script checks the combinatorial count for q=2..12. The quantum-state/rank argument is given above, not simulated numerically.
