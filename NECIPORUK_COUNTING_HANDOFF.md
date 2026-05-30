# Codex handoff: Nečiporuk counting lemma (card bound + bridge)

**Goal:** finish the last rung of the concrete Nečiporuk formula lower bound — bound
the number of distinct subfunctions a formula exposes on a block, and feed it into
the additive combiner. Everything *below* this rung is already proved and clean
(`[propext]` / `[propext, Classical.choice, Quot.sound]`, no sorry).

Branch `n-frame-route-chain`, dir `PallLean/Paper93/DeepMath/PathB/`.
Create a new file `ComputationalDepthNeciporukCountingLemma.lean`.

## Already-proved interfaces you build on (do NOT re-prove)

From `ComputationalDepthFormulaLeafSemantics.lean` (namespace `…PathB`, `BFormula` ns):
- `BFormula n` : `lit (Fin n) Bool | cst Bool | un (Bool→Bool) … | bin (Bool→Bool→Bool) … …`
- `BFormula.eval`, `BFormula.litCount`, `BFormula.leavesIn (S : Finset (Fin n))`
- `BFormula.block_realization (S α F) : ∃ G, litCount G ≤ leavesIn S F ∧ ∀ x, eval G x = eval F (fun i => if i ∈ S then x i else α i)`
- `BFormula.sum_leavesIn_of_partition` : `∑ i ∈ blocks, leavesIn (S i) F = litCount F` (disjoint cover)

From `ComputationalDepthFormulaNormalForm.lean`:
- `NF n` : `leaf (Fin n) Bool | node (Bool→Bool→Bool) (NF n) (NF n)`
- `NF.eval`, `NF.leaves`, `NF.seval : Bool ⊕ NF n → …`
- `norm : BFormula n → Bool ⊕ NF n`
- `seval_norm (F x) : NF.seval (norm F) x = BFormula.eval F x`
- `leaves_norm_le (F) {t} (h : norm F = Sum.inr t) : NF.leaves t ≤ BFormula.litCount F`

From `ComputationalDepthNeciporukSummation.lean`:
- `neciporuk_sum_lower_bound (blocks) (c b : ι→ℕ) (B) (hbudget : B = ∑ b_i) (hperblock : ∀ i∈blocks, c i ≤ 2^(b i)) : ∑ Nat.log 2 (c i) ≤ B`

## Step 1 — countable encoding of `NF` (the hard part)

```
inductive Tok (n) | g : (Bool→Bool→Bool) → Tok n | lf : Fin n → Bool → Tok n
deriving DecidableEq, Fintype   -- Bool→Bool→Bool is a Fintype ⇒ Tok n is
```
`encode : NF n → List (Tok n)` : `leaf i b ↦ [lf i b]`, `node g l r ↦ g g :: encode l ++ encode r`.

`decode : List (Tok n) → Option (NF n × List (Tok n))` parsing one tree off the front
(well-founded on list length; use `termination_by l => l.length` with a
`decreasing_by` that uses a `decode_length_le : decode l = some (t, r) → r.length ≤ l.length`
helper, or thread fuel = `l.length`).

**Key lemma (round-trip):** `decode (encode t ++ rest) = some (t, rest)` by induction on `t`
(needs `List.append_assoc`). ⇒ `encode_injective : Function.Injective encode`.

## Step 2 — card bound

`encode t` has length `2 * NF.leaves t - 1`. For `leaves t ≤ k`, length `< 2k`.
Inject `NF`-with-`≤k`-leaves into `Fin (2*k) → Option (Tok n)` via
`fun i => (encode t).get? i` (canonical none-padding; injective by `encode_injective`
+ length bound). Hence
```
nfCard_le : (#{t : NF n | NF.leaves t ≤ k}.toFinset) ≤ (Fintype.card (Tok n) + 1) ^ (2*k)
```
with `Fintype.card (Tok n) = 16 + 2*n`. (Use `Fintype.card_fun`, `Fintype.card_option`.)
Looseness vs. the optimal `(c·|S|)^k` is fine — `2^{O(k log n)}` still yields a
superlinear bound (`n²/log² n`), which is genuine.

## Step 3 — subfunction count on a block

Define `blockSubfns (S F) : Finset ((Fin n→Bool)→Bool) :=` image over `α` of
`fun x => eval F (override S α x)` (needs `DecidableEq` of the function type via `Fintype`).
Using `block_realization` + `seval_norm` + `leaves_norm_le`: every element of
`blockSubfns S F` is either a constant (≤ 2) or `NF.eval t` with `leaves t ≤ leavesIn S F`.
Map each to its witnessing `t` (or `inl c`); injectivity of the *value* lets you bound
`(blockSubfns S F).card ≤ 2 + nfCard(leavesIn S F)`.
⇒ `subfn_count_le : (blockSubfns S F).card ≤ 2 + (16+2n+1)^(2 * leavesIn S F)`.
Hence `(blockSubfns S F).card ≤ 2 ^ (2 * leavesIn S F * Nat.log 2 (16+2n+1) + 1)` (loosen).

## Step 4 — assemble the concrete lower bound

With `b i := 2 * leavesIn (S i) F * Nat.log 2 (16+2n+1) + 1`, `c i := (blockSubfns (S i) F).card`:
- `hperblock` from Step 3, `hbudget` from `sum_leavesIn_of_partition` (× the constant; adjust the `+1` per block).
- Conclude `∑ i ∈ blocks, Nat.log 2 (c i) ≤ (2 Nat.log 2 (16+2n+1)) * litCount F + #blocks`,
  i.e. `litCount F ≥ (∑ log c_i − #blocks) / (2 log₂(16+2n+1))`.

State the final theorem `neciporuk_formula_lower_bound` and a `#print axioms` trace.
Acceptance: `lake build` clean, **no sorry/admit/custom axiom**.

## Honest scope (keep in the docstring)
Real restricted formula bound (`B₂` formulas over the full binary basis). Nečiporuk
provably tops out at `Θ(n²/log n)`; this does **NOT** reach TC⁰/NC¹/width-5 BP.
Not a P vs NP bridge.
