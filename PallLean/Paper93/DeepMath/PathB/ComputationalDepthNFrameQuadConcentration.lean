import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameQuadPair

/-!
# N-Frame: the concentration analysis — the drag's block-count ceiling (Route H gate)

Route H, the open gate: at a real balanced cut, is the priced mass `|V|` ever `Θ(N)`?  Attacked
honestly, the answer is NO for the drag as built — and the reason is a structural cap
independent of the witness-rank cap Route H removed.

The discharged drag (`gParity_quad_drag`) requires ONE priced position per block (`hVone`) and
prices each block's quadratic monomial with that block's tautology/scaffold on the opposite
side of the cut.  Two consequences bound `|V|`:

  `priced_card_le_blocks` — **PROVED**: with one priced position per block, `|V| ≤ m` (the
        block count).  The map `q ↦ q.1` is injective on `V`, so `V` embeds in `Fin m`.

Combined with `gParity_quad_drag` (`|V| ≤ jj ≤ coneExcess + 1`), the drag can prove at most
`coneExcess ≥ |V| − 1 ≥ m − 1`.  Since `N = m · L` and a block needs `L ≥ ⌈log(menu)⌉ = Ω(log v)`
selector bits to address a nontrivial literal menu over `F₂^v`, we have `m = N / L = O(N / log N)`.

  `priced_card_le_ratio` — **PROVED**: `L · |V| ≤ N` — the priced mass times the per-block
        codebook length is at most the input size, so `|V| ≤ N / L`.

## Honest scope — the finding (Route H concentration gate, RESOLVED)

The concentration analysis does NOT yield `Θ(N)`.  The drag's priced mass is capped at the
BLOCK COUNT `m = N/L`, and `L ≥ Ω(log v)` (menu addressing), so `|V| ≤ O(N/log N)` and the drag
proves at most `coneExcess = O(N/log N)`, i.e. `cbudget ≤ (2 + o(1))N` by this method.  This
CONFIRMS the Route G ceiling from the drag side: Route H removed the witness-RANK cap
(detection rank `Θ(N)` per cut is available), but the BINDING cap is the per-cut block count
`m`, not the per-block detection rank.  Constant `c` in `(2+c)N` is blocked by the SAME
`L ≥ log v` addressing cost as Route G.  To exceed it the family would need `m = Θ(N)` blocks,
i.e. `L = O(1)` selector bits per block — impossible for a block addressing a `v`-spanning
literal menu.  Whether the drag ACHIEVES `Θ(N/log N)` (vs less) is the residual spread-forcing
question; the CEILING is `N/log N`, so `(2 + Ω(1))N` is out of reach for the drag method.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameQuadConcentration

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout

variable {v m L N : ℕ}

/-- **THE BLOCK-COUNT CAP (proved)**: with one priced position per block, the priced mass is
at most the number of blocks. -/
theorem priced_card_le_blocks (V : Finset (Fin m × Fin L))
    (hVone : ∀ q ∈ V, ∀ q' ∈ V, q.1 = q'.1 → q = q') :
    V.card ≤ m := by
  classical
  have h := Finset.card_le_card_of_injOn (s := V) (t := (Finset.univ : Finset (Fin m)))
    (fun q => q.1) (fun q _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    (fun q hq q' hq' hqq => hVone q (Finset.mem_coe.mp hq) q' (Finset.mem_coe.mp hq') hqq)
  simpa using h

/-- **THE RATIO CAP (proved)**: the priced mass times the per-block codebook length is at most
the input size — so `|V| ≤ N / L`.  (The block grid `m · L` fits in `N`.) -/
theorem priced_card_le_ratio (hfit : m * L ≤ N) (V : Finset (Fin m × Fin L))
    (hVone : ∀ q ∈ V, ∀ q' ∈ V, q.1 = q'.1 → q = q') :
    L * V.card ≤ N := by
  have hbl := priced_card_le_blocks V hVone
  calc L * V.card ≤ L * m := Nat.mul_le_mul_left L hbl
    _ = m * L := Nat.mul_comm L m
    _ ≤ N := hfit

end PallLean.Paper93.DeepMath.PathB.NFrameQuadConcentration

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadConcentration.priced_card_le_blocks
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadConcentration.priced_card_le_ratio
