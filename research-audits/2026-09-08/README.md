# Research audit and dynamic-rank experiments — 8 September 2026

These artifacts document checked restricted/conditional results and unsuccessful
separation attempts. **No P ≠ NP proof is claimed.**

- [Dynamic kinetic-rank experiment](dynamic-lagrangian/REPORT.md): configuration-dependent matrix rank, with proved space/time bounds.
- [Full-action extraction](dynamic-lagrangian/FULL-ACTION-STATUS.md): exact coefficient identity, not a machine-derived gauge.
- [Holographic reconstruction audit](dynamic-lagrangian/HolographicBoundaryBulkAudit.md): boundary/bulk semantics and the remaining necessity gap.
- [Separate P/NP observer audit](dynamic-lagrangian/SeparateObserverBoundaryAudit.md): independent boundaries are already present; the execution-derived cost gap remains unproved.
- [Continuation necessity](dynamic-lagrangian/ReconstructionNecessity.lean): distinguishability and conditional runtime capacity.
- [SAT specialization](dynamic-lagrangian/SATReconstructionNecessity.lean): equality-CNF one-way boundary needs n bits; this bound is attained. No unrestricted SAT lower bound is claimed.
- [Curiosity search](curiosity-profile-search/REPORT.md): five generated proposals and mathematical review.
- [Concrete easy-machine refutation](curiosity-profile-search/EASY-MACHINE-FINDING.md): the old unprojected profile target fails even for an accept-all machine.
- [Paper audit](p-vs-np1-paper-audit-2026-09-08.md): identified gaps in the supplied manuscript.
- [Initial separation audit](pall-separation-2026-09-08.md): status of the direct-sum/crossing-energy route.

The standalone Lean files were individually checked using this repository's
Lean v4.28.0 Lake environment. They are research artifacts, not additions to
the default capstone. The repeated-observation reuse lemma is also included
under `PallLean/Paper93/DeepMath/PathB/`.

Generated JSON retains the original heuristic labels; these are NOT proof
certificates. The reports explain the subsequent rejections. The runtime
SQLite archive is not committed; model inputs, outputs and review summaries
are included as text. Generation scripts require the separate Mikoshi Curiosity
package and a local Ollama qwen2:7b installation; running them creates a new
local archive. No credentials or model weights are included.
