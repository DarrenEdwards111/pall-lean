# ATTACK: are the addressing families hard for tensor networks?

The open question left by `SCOPE_TENSOR_COST_CONNECTION`: is the bond dimension of `hardF`/`orMux`/`edFun` high
under **every** variable ordering (min over orderings), i.e. are they genuinely hard for tensor networks? This
attacks it. **Verdict: no — not as a clean unconditional TN-hardness result, and the best-partition question stays
open.** The fixed-cut bonds are only linear in the input size, a bounded number of pointers is TN-*easy*, and the
many-pointer regime realizes inner product — which (correcting an earlier draft of this doc) is itself
best-partition-*easy*, so it gives no tensor-network hardness. What the attack *does* yield, both proved: the
tightness/reframing fact `finrank_residualSpan_le_two_pow_card` (rank `≤ 2^{|S|}`), and the fixed-partition
inner-product full-rank bound `InnerProductCommRank.chi_finrank` (the canonical communication-matrix rank, honestly
labelled fixed-partition).

## 1. Reframing: the bonds are exponential in the block length, not the input size

The new upper bound `finrank_residualSpan_le_two_pow_card` proves the Schmidt bound `rank ≤ 2^{|S|}` (every residual
depends only on the `S`-coordinates, so factors through the restriction `(ι → Bool) → ({i ∈ S} → Bool)`). This
makes the lower bounds **tight**, and separates two very different situations:

| family | cut `|S|` | input size `n` | bond | in terms of `n` |
|---|---|---|---|---|
| `eqFun` | `k` | `2k` (unpadded) | `2^k` | `2^{n/2}` — **super-poly** |
| `hardF`/`orMux`/`edFun` | `b` | `≥ 2^b` (padded by `2^b` data cells) | `2^b` | `≤ n` — **linear** |

So the "exponential bond" of the addressing families is exponential in the *block length* `b = O(log n)`, hence
`2^b ≤ n` — only **linear in the input size**. The single genuinely super-polynomial-in-`n` bond among the four is
`eqFun`'s (because it is unpadded, `n = 2k`), and that one collapses under reordering (`EQ = ∏[xᵢ = yᵢ]`, pairs
adjacent → `O(1)` bond). So *no* family gives a super-poly-in-`n` bond that survives reordering. This already
answers most of the question: at their fixed cut, the addressing families are linear-bond, so nothing there forces
tensor-network hardness.

## 2. A bounded number of pointers is TN-easy

`hardF` with `m` blocks has an MPS of bond `≤ 2^{m·b} = n^{O(m)}` under the **addresses-first** ordering
(`addr₁, …, addr_m, data₀, …, data_{2^b−1}`): read the `m` addresses into the bond state (`2^{mb}` states remember
all `m` addresses), then sweep the data cells, XOR-ing in the addressed ones. So:

* `m = 1` (the multiplexer / storage-access function): bond `≤ 2^b = Θ(n)` — **polynomial**. A single dynamic
  pointer is *not* TN-hard. (Matches the fixed-cut `Θ(2^b)` from §1: MUX is linear-bond both ways.)
* `m = O(1)`: bond `≤ n^{O(1)}` — still **polynomial**.

So tensor-network hardness, if it exists, needs `m = ω(1)` pointers — the *number* of pointers, not the addressing
itself, is the source.

## 3. The many-pointer regime is inner product — but that does NOT give TN-hardness

Write `hardF(addr, data) = ⟨p(addr), data⟩` over `𝔽₂`, where `p(addr)_c = (#\{k : addr_k = c\}) mod 2` is the
parity-address-count vector. For `m ≥ 2^b` the map `addr ↦ p` is onto `{0,1}^{2^b}`, so `hardF` **realizes the
inner-product function** `IP` on `2^b`-bit vectors (the `p`-side encoded by the addresses, the `data`-side direct).

**Correction (an earlier version of this section was wrong): `IP` is NOT best-partition-hard.** Its `±1`
communication matrix is full rank `2^{2^b}` only across the **fixed `p | data` partition** (that Hadamard full-rank
fact is now formalized: `InnerProductCommRank.chi_finrank`). But under the partition that keeps each pair
`(p_c, data_c)` on the *same* side, `IP = A_local ⊕ B_local` — a XOR of two local sums, **rank 2**. So `IP`, like
equality, *collapses* under a good ordering; it is a fixed-partition example, not a best-partition one. Realizing
`IP` therefore does **not** establish tensor-network hardness.

Two things follow:

* The `IP` connection gives `hardF` a *fixed-partition* high-rank cut, not a min-over-orderings bound. It does not
  resolve the best-partition question either way.
* Whether many-pointer `hardF` is genuinely best-partition-hard (over its real address+data variables — note `p` is
  *derived* from the addresses, so the `p | data` split is not itself a variable partition) is **still open**, and
  the rank/entanglement machinery here only ever produces fixed-partition bounds. This is the recurring
  min-over-orderings wall, now confirmed to bite even in the many-pointer regime.

## 4. Verdict

* **Not a clean unconditional TN-hardness result** for the addressing families: the fixed-cut bonds are linear in
  `n` (§1), a bounded number of pointers is outright TN-easy (§2), and the many-pointer regime realizes `IP` — which
  is itself best-partition-*easy* (§3), so the connection gives no TN-hardness.
* **The best-partition question is genuinely open** for `m = ω(1)`, and the rank machinery cannot reach it: every
  bound it yields (including `IP`'s) is fixed-partition, and the min-over-orderings quantifier — the recurring
  representation-invariance wall — is exactly what separates fixed-partition from best-partition.
* **No new provable unconditional sub-fact toward TN-hardness this round.** What the attack *did* produce, both
  clean and proved: the tightness bound `finrank_residualSpan_le_two_pow_card` (rank `≤ 2^{|S|}`, making §1
  rigorous), and — correcting the earlier over-claim — the fixed-partition `IP` full-rank bound
  `InnerProductCommRank.chi_finrank` (the canonical communication-matrix rank `= 2^N`, honestly labelled as
  fixed-partition, in the same species as `eqFun`).

Recommendation: there is **no known best-partition-hard family** hiding in the addressing functions to formalize —
`IP` is not it. A genuine tensor-network (best-partition) lower bound would require an actually-best-partition-hard
function, which is a specialized and much harder object; that is the honest edge of this line. Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
