# SCOPE: the bond-dimension-to-tensor-cost connection

This assesses the natural next step for the tensor-network line: turning the *bond-dimension* lower bounds
(`TensorEntanglementLowerBound` and its instantiations) into *representation-cost* lower bounds — the cost of the
whole tensor network (MPS/MERA), not just the rank at one cut. It is a **map**, not a build. **Verdict: the
fixed-ordering connection is real and buildable (cost `≥ bond² ≥ rank²`), and gives genuine *restricted* results —
but the deep content is already proved, the build is mostly framing, and the *representation-invariant* version
(min over orderings) collapses for the flagship family (equality) and is at best a restricted tensor-network bound
for the others. It does not reach a separation.**

## 1. The connection, precisely

A matrix-product state (MPS) writes `f(x) = v^T · A₁(x₁) · A₂(x₂) · ⋯ · Aₙ(xₙ) · w`, where `Aᵢ(xᵢ)` is a
`χᵢ₋₁ × χᵢ` matrix and `χᵢ` is the **bond dimension** on the edge between sites `i` and `i+1`. The representation
**cost** is the total number of tensor entries, `Σᵢ 2·χᵢ₋₁·χᵢ ≥ 2·(maxᵢ χᵢ)²`.

At any *prefix* cut (site `j`), the MPS factors as a bond-`χⱼ` decomposition:

```text
  left_a(x_{≤j})  = (v^T · A₁(x₁)⋯Aⱼ(xⱼ))_a ,   right_a(x_{>j}) = (Aⱼ₊₁(xⱼ₊₁)⋯Aₙ(xₙ)·w)_a ,
  f(x) = Σ_{a<χⱼ} left_a · right_a .
```

That is exactly a `TensorFactorization` with bond `χⱼ`. So `finrank_residualSpan_le_bond` gives immediately

> **`χⱼ ≥ ` cross-cut rank at cut `j` = the residual-span dimension** (the standard "MPS bond = Schmidt rank").

Combining: `cost ≥ 2·(maxⱼ χⱼ)² ≥ 2·(maxⱼ rankⱼ)²`. For a variable ordering that puts an address block as a
contiguous prefix, `TensorEntanglementHardF` gives `rank ≥ 2^b − 1`, so **`cost ≥ 2·(2^b − 1)²`** — exponential.

## 2. What is buildable, and what it costs

Buildable, cleanly:

* an MPS model (`Aᵢ : Bool → Matrix (Fin χ) (Fin χ) K`, boundary vectors, `f = v ⬝ ∏Aᵢ(xᵢ) ⬝ w`);
* `mps_cut_factorization` — an MPS induces a `TensorFactorization` at each prefix cut (bond = `χⱼ`), via matrix-
  product associativity;
* `mps_bond_ge_rank` — hence `χⱼ ≥ rank` (immediate from `finrank_residualSpan_le_bond`);
* `mps_cost_ge` — `cost ≥ bond² ≥ rank²`, and the instantiation `hardF_mps_cost_ge : cost ≥ 2·(2^b−1)²`.

Effort: **moderate (~150–200 lines)**, dominated by the matrix-product machinery. But note: the *deep* content —
`bond ≥ rank` — is **already done** (`finrank_residualSpan_le_bond`). The MPS layer is **framing**: it packages the
already-proved rank bound into the standard cost language. Genuine, but not new mathematics.

## 3. The decisive caveat — min over orderings collapses (this is the ceiling)

Every cost bound in §1–2 is for a **fixed** variable ordering with the block as a contiguous prefix — exactly the
contiguity restriction of the branching-program width bound. For a *cost* measure to witness hardness it must hold
for the **best** ordering (min over orderings / min over tensor networks). And there the story changes:

* **Equality collapses.** `EQ(x,y) = ∏ᵢ [xᵢ = yᵢ]` is a *product* of local checks. Order the sites so each pair
  `(xᵢ, yᵢ)` is adjacent, and equality has an **`O(1)`-bond MPS** (carry the running AND plus the pending `xᵢ`).
  So `min over orderings` of the bond is `O(1)` — equality is *easy* for tensor networks, and its `2^k` bond
  (proved across the all-`x`/all-`y` cut) is an artifact of a *bad* ordering, not intrinsic hardness. The
  `eqFun` bound of `TensorEntanglementLowerBound` is a fixed-cut statement; it does not survive re-ordering.

* **The addressing families are unclear — and at best restricted.** For `hardF`/`orMux`/`edFun` the dynamic
  addressing is non-local (the addressed cell is not statically adjacent to the address bits), so the bond may
  stay high under *many* orderings. But whether it stays high under *every* ordering — i.e. whether these families
  are genuinely hard for tensor networks — is an open tensor-network-complexity question, not something the rank
  argument settles. And even a positive answer is a **restricted** bound: `hardF ∈ P`, tensor networks are a
  restricted model (a P function can have exponential MPS cost), so "hard for tensor networks" separates the
  family from *low-bond MPS*, not `P` from `NP`.

* **The representation-invariant version is the same wall.** "High bond under every ordering / every tensor
  network" is the min-over-representations quantifier — the identical representation-invariance that made the
  observer boundary collapse (`unrestricted_min_trivial`) and that the machine-completeness bridge could not
  discharge. The equality collapse above is a concrete instance of it: minimizing over orderings kills the bound.

## 4. Verdict and recommendation

* **Buildable and genuine:** the *fixed-ordering* cost bound `cost ≥ 2·(rank)²` — e.g. `hardF` needs an MPS of
  cost `≥ 2·(2^b−1)²` when its address block is read as a contiguous prefix. A real restricted tensor-network cost
  lower bound, in the same clean-axiom species as the rest of the matrix. Mostly framing over
  `finrank_residualSpan_le_bond`.
* **Not a separation:** the min-over-orderings cost collapses for equality (`O(1)`-bond MPS), and for the addressing
  families it is at best a *restricted* (tensor-network) bound, whose representation-invariant form is the same
  collapse/machine-completeness wall every route meets.

Recommendation: **build the fixed-ordering cost connection if a clean cost-language statement is wanted** — it is a
legitimate restricted result and rounds out the tensor line — but present it as fixed-ordering, and do **not**
pursue the min-over-orderings/representation-invariant version as a route to `P ≠ NP`. The interesting *open* (and
non-separation) question it exposes is a restricted one: are the addressing families `hardF`/`orMux`/`edFun`
genuinely hard for tensor networks (high bond under every ordering)? That is a real tensor-network-complexity
question, worth a focused attack on its own terms — but it is not `P` vs `NP`. Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
