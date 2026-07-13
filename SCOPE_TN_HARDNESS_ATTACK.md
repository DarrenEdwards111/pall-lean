# ATTACK: are the addressing families hard for tensor networks?

The open question left by `SCOPE_TENSOR_COST_CONNECTION`: is the bond dimension of `hardF`/`orMux`/`edFun` high
under **every** variable ordering (min over orderings), i.e. are they genuinely hard for tensor networks? This
attacks it. **Verdict: no — not as a clean unconditional TN-hardness result.** The fixed-cut bonds are only linear
in the input size, a bounded number of pointers is TN-*easy*, and the genuine hardness appears only in the
many-pointer regime, where it *is* the inner-product best-partition lower bound — a known-hard, separate result,
still gated by the min-over-orderings quantifier. What the attack *does* yield is a clean tightness/reframing
fact, now proved (`finrank_residualSpan_le_two_pow_card`).

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

## 3. The many-pointer regime is inner product

Write `hardF(addr, data) = ⟨p(addr), data⟩` over `𝔽₂`, where `p(addr)_c = (#\{k : addr_k = c\}) mod 2` is the
parity-address-count vector. For `m ≥ 2^b` the map `addr ↦ p` is onto `{0,1}^{2^b}`, so `hardF` **realizes the
inner-product function** `IP` on `2^b`-bit vectors (the `p`-side encoded by the addresses, the `data`-side direct).

`IP` is the textbook best-partition-hard function: its `2^b × 2^b` communication matrix is (`±1`) Hadamard, full
rank, so under **every** balanced partition into a `p`-half and a `data`-half the rank is `2^{Ω(2^b)}`. That is
genuine tensor-network hardness — high bond under every ordering. So the many-pointer `hardF` **is** plausibly
TN-hard, but:

* the hardness is *inherited from* `IP`, not produced by the rank argument of the entanglement matrix;
* proving it rigorously is the inner-product best-partition lower bound plus the `addr ↦ p` reduction — a real,
  known-in-communication-complexity result, but a substantial formalization not currently in the corpus;
* it is still gated by the **min-over-orderings / best-partition quantifier** — the same representation-invariance
  that collapses `eqFun` and that every separation route in this project has met. `IP` happens to survive that
  quantifier (that is exactly why `IP` is the canonical example), but establishing survival *is* the work, and it
  is a statement about `IP`, not about `P` vs `NP`.

## 4. Verdict

* **Not a clean unconditional TN-hardness result** for the addressing families as defined: the fixed-cut bonds are
  linear in `n` (§1), and a bounded number of pointers is outright TN-easy (§2).
* **The genuine hardness is inner product** (§3): it appears only for `m = ω(1)` pointers, where `hardF` realizes
  `IP`, and it is the inner-product best-partition lower bound — a known-hard, separate result, not something the
  entanglement/rank machinery delivers, and still behind the min-over-orderings quantifier.
* **No new provable unconditional sub-fact toward TN-hardness this round.** The barrier is the min-over-orderings
  quantifier (the recurring representation-invariance wall), and the honest reduction is "TN-hardness of many-pointer
  `hardF` ⟺ best-partition hardness of `IP`". The one genuinely new, proved fact extracted is the tightness bound
  `finrank_residualSpan_le_two_pow_card` (rank `≤ 2^{|S|}`), which is what makes the §1 reframing rigorous.

Recommendation: do **not** pursue many-pointer `hardF` as a fresh TN-hardness theorem — it is the inner-product
lower bound in disguise. If a genuine tensor-network lower bound is wanted, formalize `IP`'s best-partition rank
directly (clean, self-contained, and honestly labelled as a communication/tensor-network bound). Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
