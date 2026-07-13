# SCOPE: formalizing an actually-best-partition-hard function

A **best-partition-hard** function has high Schmidt rank (tensor bond) across *every* balanced partition of its
variables — unlike `eqFun`/`IP`, which are high-rank only across one partition and collapse under a good ordering.
This is the genuine tensor-network-hardness object.  This scopes formalizing one.  **Verdict: the reduction is
proved (`BestPartitionReduction.chi_subset_finrank`), but the function itself reduces to explicit matrix rigidity —
a famous open problem (Valiant) — so no clean explicit construction is formalizable; a probabilistic existence is
available but needs a separate substantial counting build.**

## 1. The construction template and the exact rank formula

Take the quadratic form `Q_M(z) = Σ_{i<j} M_{ij} zᵢ zⱼ` over `𝔽₂` for a symmetric zero-diagonal `M`.  Across a
partition `(S, Sᶜ)`, `Q_M = Q_S(z_S) ⊕ Q_{Sᶜ}(z_{Sᶜ}) ⊕ z_Sᵀ M_{S,Sᶜ} z_{Sᶜ}`, so the `±1` communication matrix
factors as `D₁ · H · D₂` with `D₁, D₂` diagonal `±1` (the two local terms) and `H[a][b] = (-1)^{aᵀ M_{S,Sᶜ} b}`.
Diagonal `±1` scaling preserves rank, and the rows of `H` are the characters `χ_{M_{S,Sᶜ}ᵀ a}` — of which there are
`|image(M_{S,Sᶜ}ᵀ)| = 2^{rank_{𝔽₂}(M_{S,Sᶜ})}` distinct ones, each independent. Hence:

> **communication rank of `Q_M` across `(S, Sᶜ)` = `2^{rank_{𝔽₂}(M_{S,Sᶜ})}`.**

The engine — *distinct characters are always linearly independent* — is proved: `chi_subset_finrank` (any set `T`
of characters spans dimension `|T|`). Inner product is the case `M_{S,Sᶜ} = I` (`chi_finrank`, `= 2^N`).

So **`Q_M` is best-partition-hard ⟺ `M` is rank-rigid**: every balanced off-diagonal block `M_{S,Sᶜ}` has `𝔽₂`-rank
`Ω(n)`.

## 2. The remaining piece is matrix rigidity — Valiant's open problem

"Every balanced off-diagonal block has high rank" is exactly the **matrix rigidity** property. Explicit
constructions matching what random matrices achieve are a famous *open* problem (Valiant, 1977) — and one already on
this project's list of live barriers. And it is not for want of trying natural matrices:

| explicit `𝔽₂` matrix `M` | off-diagonal block rank | verdict |
|---|---|---|
| Sylvester `M_{ij} = ⟨i,j⟩` (`i,j ∈ 𝔽₂^k`, `n = 2^k`) | `≤ k = log n` (`M = PᵀP`) | low rank — fails |
| all-ones `J − I` | `1` | fails |
| cycle / matching graphs | `O(1)` for a contiguous / aligned cut | low cut — fails |
| Cauchy (every submatrix nonsingular) | full | **impossible over `𝔽₂`** (only 2 elements) |

Every clean algebraic candidate is either low-rank or has a low-rank block under an adversarial partition. High rank
under *every* balanced partition is inherently random-like — which is precisely why explicit rigidity is open. So
there is **no clean explicit best-partition-hard function to formalize**; producing one would resolve explicit
matrix rigidity.

## 3. The probabilistic existence — engine built (`LowRankCount`), assembly is mechanical

A *random* symmetric `M` is rank-rigid with high probability, so a best-partition-hard function **exists**. Sketch:
a fixed balanced off-diagonal block is an `h × h` `𝔽₂` matrix (`h = n/2`); `#{h×h : rank ≤ s} ≤ 2^{2hs}` (rank
factorization `M = A·B`, inner dimension `s`, counted by the domain `(A,B)`); the bad count per partition is
`≤ 2^{2hs}·2^{N²−h²}` (block low-rank, complement free); union over `≤ 2^n` partitions is `< 2^{N²}` once
`2r < h`. So some `M` has every balanced off-diagonal block of rank `≥ h/2 ≈ n/4`, giving best-partition rank
`≥ 2^{Ω(n)}`.

**The engine is now built and committed** (`ComputationalDepthLowRankCount.lean`, clean-axiom, no sorry):

* `exists_span_of_finrank_le` — spanning family of size `s` from `finrank ≤ s`;
* `rank_factor` — **the crux, absent from Mathlib**: `rank M ≤ s ⟹ M = A·B` (inner dimension `s`);
* `card_lowRank_le` — `#{h×h 𝔽₂ matrices of rank ≤ s} ≤ 2^{2hs}` (via `rank_factor` + `(A,B) ↦ A·B`);
* `exists_avoiding` — the probabilistic-method pigeonhole: `Σ_test |Bad test| < |Ω| ⟹` some object avoids every bad
  set.

**The assembly is now built too** (`ComputationalDepthBestPartitionExistence.lean`, clean-axiom, no sorry):
`exists_best_partition_hard` — for `2r + 2 < h`, there is an `𝔽₂` matrix `M` on `2h` variables whose off-diagonal
block at **every** balanced partition has rank `≥ r ≈ n/4`. The block `blk S M` is `M.submatrix (orderEmbOfFin S)
(orderEmbOfFin Sᶜ)`; the per-partition bad set injects via `M ↦ (blk S M, M|_complement)` (`blk_restOf_injective`),
giving `|Bad_S| ≤ 2^{2hr}·2^{N²−h²}` (`fiber_bound`); the union over `≤ 2^n` partitions is `< 2^{N²}` by the
arithmetic `2hr + 2h < h²`, and `exists_avoiding` produces the rigid `M`.

So the entire chain is complete: `𝔽₂` rank factorization (`rank_factor`) → low-rank count (`card_lowRank_le`) →
pigeonhole (`exists_avoiding`) → **a best-partition-hard matrix exists** (`exists_best_partition_hard`), and via the
reduction (`chi_subset_finrank`) a best-partition-hard function exists — all clean-axiom, no sorry.

## 4. Verdict

* **Proved:** the reduction and its engine — the communication rank of `Q_M` across any partition is
  `2^{rank(off-diagonal block)}`, resting on `chi_subset_finrank` (distinct characters are full rank). This is the
  correct, complete characterization of when the template is best-partition-hard.
* **Blocked (explicit):** an *explicit* best-partition-hard function requires an explicit rank-rigid matrix =
  explicit matrix rigidity = Valiant's open problem. No clean construction exists; the natural algebraic ones
  provably fail (§2).
* **Built (existential):** a *random* `M` works, so a best-partition-hard function **exists** — now formalized end
  to end (`exists_best_partition_hard`, §3), clean-axiom and no sorry.

So the corpus now contains an actual best-partition-hard object, obtained the only way available: the probabilistic
method (a random matrix), since explicit rank-rigid matrices are Valiant-open. The full chain — `rank_factor` (the
`𝔽₂` rank factorization, new to the corpus and absent from Mathlib) → `card_lowRank_le` → `exists_avoiding` →
`exists_best_partition_hard`, with `chi_subset_finrank` as the rank engine — is complete. Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
