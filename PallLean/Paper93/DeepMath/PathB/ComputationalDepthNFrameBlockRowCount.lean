import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCutFactorization

/-!
# N-Frame: the block-exclusive row count — a fixed-partition interface lower bound

The semantic input to accumulation, at its **honest** strength.  The subfunction machinery
(`sat3_block_subfunctions_distinct`) produces `2^k` pairwise-distinct rows for **one** partition: the
*block-exclusive* cut, whose free side is exactly one designated block's coordinates.  Feeding that family
to the row-capacity engine gives an interface lower bound for that partition.

  `blockCoords` — the coordinate set of block `c` (`i.val / D = c.val`).
  `sat3_block_row_distinct` — **PROVED**: `2^k` pin contexts give pairwise-distinct rows over `blockCoords`.
  `sat3_block_exclusive_interface` — **PROVED, the count**: any factorization `f = op (g|_A, h|_B)` whose
        exclusive-left side is exactly block `c` (`A \ B = blockCoords c`) has shared interface
        `|A ∩ B| ≥ k − 1`.

## Honest scope — the adversarial gap, stated

This is a **fixed**-partition bound: it constrains only factorizations that place a full designated block
on the exclusive-left side.  The circuit's own top cut is **adversarial** — it need not make `A \ B` a
full block, and if it splits every block across the cut, this family says nothing.  Bounding the row count
across *every* balanced partition (so the circuit cannot dodge) is a **formula/communication lower bound**
in the Nečiporuk regime — capped at `n²/log n`, and genuinely `P`-vs-`NP`-adjacent past that.  So the
accumulation chain has its structural half (`frontier_val_agree`, `coneExcess_ge_multiReader`) and its
information-theoretic half (`shared_split_row_capacity`, and this count for one partition) as theorems, and
its **adversarial-partition** link as the open mountain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The coordinate set of block `c`. -/
def blockCoords (N : ℕ) (c : Fin (sat3M N)) : Finset (Fin N) :=
  Finset.univ.filter (fun i => i.val / sat3D N = c.val)

/-- `mixOn blockCoords` is exactly `sat3Patch`. -/
theorem mixOn_blockCoords_eq_patch (N : ℕ) (c : Fin (sat3M N)) (x y : Fin N → Bool) :
    mixOn (blockCoords N c) x y = sat3Patch N c y x := by
  funext i
  show (if i ∈ blockCoords N c then x i else y i)
    = (if i.val / sat3D N = c.val then x i else y i)
  have hmem : i ∈ blockCoords N c ↔ i.val / sat3D N = c.val := by
    rw [blockCoords, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ i, h⟩⟩
  by_cases hi : i.val / sat3D N = c.val
  · rw [if_pos (hmem.mpr hi), if_pos hi]
  · rw [if_neg (fun hm => hi (hmem.mp hm)), if_neg hi]

/-- The pin-context map is injective — distinct subfunctions come from distinct context points. -/
theorem sat3Context_injective (N : ℕ) (hv : 1 ≤ sat3V N) {k : ℕ}
    (hk : k + 1 ≤ sat3M N) (hkv : k ≤ sat3V N) (c : Fin (sat3M N)) :
    Function.Injective (fun bvec : Fin k → Bool => sat3Context N c hk bvec) := by
  intro b b' heq
  by_contra hne
  obtain ⟨uu, huu⟩ := sat3_block_subfunctions_distinct N hv hk hkv c b b' hne
  apply huu
  show sat3Family N (sat3Patch N c (sat3Context N c hk b) uu)
    = sat3Family N (sat3Patch N c (sat3Context N c hk b') uu)
  rw [(by exact heq : sat3Context N c hk b = sat3Context N c hk b')]

/-- **THE BLOCK-EXCLUSIVE INTERFACE COUNT (proved)**: a factorization whose exclusive-left side is exactly
block `c` has shared interface `≥ k − 1`. -/
theorem sat3_block_exclusive_interface (N : ℕ) (hv : 1 ≤ sat3V N) {k : ℕ}
    (hk : k + 1 ≤ sat3M N) (hkv : k ≤ sat3V N) (hk2 : 2 ≤ k) (c : Fin (sat3M N))
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool)
    (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (hAB : A \ B = blockCoords N c) :
    k ≤ (A ∩ B).card + 1 := by
  classical
  set Y : Finset (Fin N → Bool) :=
    Finset.univ.image (fun bvec : Fin k → Bool => sat3Context N c hk bvec) with hY
  have hcard : Y.card = 2 ^ k := by
    rw [hY, Finset.card_image_of_injective _ (sat3Context_injective N hv hk hkv c),
      Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hmix : ∀ (b : Fin k → Bool) (uu : Fin N → Bool),
      sat3Family N (mixOn (A \ B) uu (sat3Context N c hk b))
        = sat3Family N (sat3Patch N c (sat3Context N c hk b) uu) := by
    intro b uu
    rw [hAB, mixOn_blockCoords_eq_patch]
  have hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' →
      ∃ x, sat3Family N (mixOn (A \ B) x y)
        ≠ sat3Family N (mixOn (A \ B) x y') := by
    intro y hy y' hy' hyne
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hy
    obtain ⟨b', -, hb'⟩ := Finset.mem_image.mp hy'
    have hbeq : sat3Context N c hk b = y := hb
    have hb'eq : sat3Context N c hk b' = y' := hb'
    subst hbeq
    subst hb'eq
    have hbne : b ≠ b' := fun hh' => hyne (by rw [hh'])
    obtain ⟨uu, huu⟩ := sat3_block_subfunctions_distinct N hv hk hkv c b b' hbne
    refine ⟨uu, ?_⟩
    rw [hmix b uu, hmix b' uu]
    exact huu
  have hlt : 2 ^ ((k - 2) + 1) < Y.card := by
    rw [hcard]
    apply Nat.pow_lt_pow_right (by omega : 1 < 2)
    omega
  have h := rows_force_interface (sat3Family N) A B op g h hg hh hf Y hdist (k - 2) hlt
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3Context_injective
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_block_exclusive_interface
