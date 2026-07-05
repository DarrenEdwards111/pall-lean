import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameStackedBands

/-!
# N-Frame: the multi-block patch — plumbing for the additive drag

Rung 1 of the multi-block additive-drag arc (patch → eval → drag → rebuilt window).  The
single-block `sat3Patch` overrides one block; the additive drag needs several data blocks
overridden at once, each with its own content.  This file is the plumbing, engineered for the
eval induction:

  `sat3PatchMulti` — override every block in a set `C`, block `c` by `us c`.
  `sat3PatchMulti_empty` / `sat3PatchMulti_insert` — the induction interface: the empty patch is
        the context, and patching `insert c C` is a single-block patch of `c` over the `C`-patch
        (unconditionally — no freshness hypothesis needed).
  `sat3PatchMulti_singleton` — the bridge: the one-block multi-patch IS `sat3Patch`, so the
        entire existing single-block eval corpus applies verbatim to the base case.
  `sat3PatchMulti_own` / `sat3PatchMulti_out_block` / `sat3PatchMulti_out` — the read lemmas.
  `sat3PatchMulti_congr` — only the overrides of blocks in `C` matter.
  `sat3PatchMulti_single_eval` — sanity: the multi-selector eval replayed through the new
        interface at a singleton, exercising the bridge.

## Honest scope

Pure plumbing — no lower-bound content.  The remaining rungs of the arc: the multi-block
context (pin enumeration avoiding a set of designated blocks), the multi-block eval (per-block
reading with slot-1 kits neutralizing the other data blocks), the additive drag
(`j ≥ Σ_c d_c`), and the rebuilt window.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- Override every block in `C`: a bit of block `c ∈ C` reads `us c`, all other bits read `y`. -/
def sat3PatchMulti (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (us : Fin (sat3M N) → Fin N → Bool) : Fin N → Bool :=
  fun b =>
    if h : b.val / sat3D N < sat3M N then
      if (⟨b.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ C then us ⟨b.val / sat3D N, h⟩ b
      else y b
    else y b

theorem sat3PatchMulti_empty (N : ℕ) (y : Fin N → Bool)
    (us : Fin (sat3M N) → Fin N → Bool) :
    sat3PatchMulti N ∅ y us = y := by
  funext b
  show (if h : b.val / sat3D N < sat3M N then
      if (⟨b.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ (∅ : Finset (Fin (sat3M N)))
      then us ⟨b.val / sat3D N, h⟩ b
      else y b
    else y b) = y b
  by_cases h : b.val / sat3D N < sat3M N
  · rw [dif_pos h, if_neg (Finset.notMem_empty _)]
  · rw [dif_neg h]

/-- Reading a layout bit of a patched block. -/
theorem sat3PatchMulti_own (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (us : Fin (sat3M N) → Fin N → Bool) (c : Fin (sat3M N)) (hc : c ∈ C)
    (t : Fin 3) (f : ℕ) (hf : f < sat3V N + 1) :
    sat3PatchMulti N C y us (sat3Bit N c t f hf) = us c (sat3Bit N c t f hf) := by
  have hdiv : (sat3Bit N c t f hf).val / sat3D N = c.val := sat3Bit_clause N c t f hf
  have hlt : (sat3Bit N c t f hf).val / sat3D N < sat3M N := by
    rw [hdiv]
    exact c.isLt
  have hfin : (⟨(sat3Bit N c t f hf).val / sat3D N, hlt⟩ : Fin (sat3M N)) = c :=
    Fin.ext hdiv
  show (if h : (sat3Bit N c t f hf).val / sat3D N < sat3M N then
      if (⟨(sat3Bit N c t f hf).val / sat3D N, h⟩ : Fin (sat3M N)) ∈ C
      then us ⟨(sat3Bit N c t f hf).val / sat3D N, h⟩ (sat3Bit N c t f hf)
      else y (sat3Bit N c t f hf)
    else y (sat3Bit N c t f hf)) = us c (sat3Bit N c t f hf)
  rw [dif_pos hlt]
  by_cases hmem : (⟨(sat3Bit N c t f hf).val / sat3D N, hlt⟩ : Fin (sat3M N)) ∈ C
  · rw [if_pos hmem]
    exact congrArg (fun z => us z (sat3Bit N c t f hf)) hfin
  · exfalso
    apply hmem
    rw [hfin]
    exact hc

/-- Reading any bit whose block is not patched (including tail bits). -/
theorem sat3PatchMulti_out (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (us : Fin (sat3M N) → Fin N → Bool) (b : Fin N)
    (hout : ∀ h : b.val / sat3D N < sat3M N,
      (⟨b.val / sat3D N, h⟩ : Fin (sat3M N)) ∉ C) :
    sat3PatchMulti N C y us b = y b := by
  show (if h : b.val / sat3D N < sat3M N then
      if (⟨b.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ C then us ⟨b.val / sat3D N, h⟩ b
      else y b
    else y b) = y b
  by_cases h : b.val / sat3D N < sat3M N
  · rw [dif_pos h, if_neg (hout h)]
  · rw [dif_neg h]

/-- Reading a layout bit of an unpatched block. -/
theorem sat3PatchMulti_out_block (N : ℕ) (C : Finset (Fin (sat3M N)))
    (y : Fin N → Bool) (us : Fin (sat3M N) → Fin N → Bool)
    (c : Fin (sat3M N)) (hc : c ∉ C) (t : Fin 3) (f : ℕ) (hf : f < sat3V N + 1) :
    sat3PatchMulti N C y us (sat3Bit N c t f hf) = y (sat3Bit N c t f hf) := by
  apply sat3PatchMulti_out
  intro h
  have hfin : (⟨(sat3Bit N c t f hf).val / sat3D N, h⟩ : Fin (sat3M N)) = c :=
    Fin.ext (sat3Bit_clause N c t f hf)
  rw [hfin]
  exact hc

/-- **THE BRIDGE (proved)**: the one-block multi-patch is the single-block patch — the whole
existing eval corpus applies to the base case verbatim. -/
theorem sat3PatchMulti_singleton (N : ℕ) (c : Fin (sat3M N)) (y : Fin N → Bool)
    (us : Fin (sat3M N) → Fin N → Bool) :
    sat3PatchMulti N {c} y us = sat3Patch N c y (us c) := by
  funext b
  show (if h : b.val / sat3D N < sat3M N then
      if (⟨b.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ ({c} : Finset (Fin (sat3M N)))
      then us ⟨b.val / sat3D N, h⟩ b
      else y b
    else y b) = (if b.val / sat3D N = c.val then us c b else y b)
  by_cases hdiv : b.val / sat3D N = c.val
  · have hlt : b.val / sat3D N < sat3M N := by
      rw [hdiv]
      exact c.isLt
    have hfin : (⟨b.val / sat3D N, hlt⟩ : Fin (sat3M N)) = c := Fin.ext hdiv
    rw [dif_pos hlt, if_pos (Finset.mem_singleton.mpr hfin), if_pos hdiv]
    exact congrArg (fun z => us z b) hfin
  · rw [if_neg hdiv]
    by_cases h : b.val / sat3D N < sat3M N
    · have hnmem : (⟨b.val / sat3D N, h⟩ : Fin (sat3M N))
          ∉ ({c} : Finset (Fin (sat3M N))) := by
        intro hmem
        exact hdiv (congrArg Fin.val (Finset.mem_singleton.mp hmem))
      rw [dif_pos h, if_neg hnmem]
    · rw [dif_neg h]

/-- **THE INDUCTION STEP (proved)**: patching `insert c C` is a single-block patch of `c` over
the `C`-patch — unconditionally. -/
theorem sat3PatchMulti_insert (N : ℕ) (C : Finset (Fin (sat3M N))) (c : Fin (sat3M N))
    (y : Fin N → Bool) (us : Fin (sat3M N) → Fin N → Bool) :
    sat3PatchMulti N (insert c C) y us
      = sat3Patch N c (sat3PatchMulti N C y us) (us c) := by
  funext b
  show (if h : b.val / sat3D N < sat3M N then
      if (⟨b.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ insert c C
      then us ⟨b.val / sat3D N, h⟩ b
      else y b
    else y b)
    = (if b.val / sat3D N = c.val then us c b else sat3PatchMulti N C y us b)
  by_cases hdiv : b.val / sat3D N = c.val
  · have hlt : b.val / sat3D N < sat3M N := by
      rw [hdiv]
      exact c.isLt
    have hfin : (⟨b.val / sat3D N, hlt⟩ : Fin (sat3M N)) = c := Fin.ext hdiv
    rw [dif_pos hlt, if_pos (by rw [hfin]; exact Finset.mem_insert_self c C),
      if_pos hdiv]
    exact congrArg (fun z => us z b) hfin
  · rw [if_neg hdiv]
    show _ = (if h : b.val / sat3D N < sat3M N then
      if (⟨b.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ C then us ⟨b.val / sat3D N, h⟩ b
      else y b
    else y b)
    by_cases h : b.val / sat3D N < sat3M N
    · rw [dif_pos h, dif_pos h]
      by_cases hmem : (⟨b.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ C
      · rw [if_pos (Finset.mem_insert_of_mem hmem), if_pos hmem]
      · have hni : (⟨b.val / sat3D N, h⟩ : Fin (sat3M N)) ∉ insert c C := by
          intro hins
          rcases Finset.mem_insert.mp hins with heq | hmm
          · exact hdiv (congrArg Fin.val heq)
          · exact hmem hmm
        rw [if_neg hni, if_neg hmem]
    · rw [dif_neg h, dif_neg h]

/-- Only the overrides of patched blocks matter. -/
theorem sat3PatchMulti_congr (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (us us' : Fin (sat3M N) → Fin N → Bool)
    (h : ∀ c ∈ C, ∀ b : Fin N, us c b = us' c b) :
    sat3PatchMulti N C y us = sat3PatchMulti N C y us' := by
  funext b
  show (if hlt : b.val / sat3D N < sat3M N then
      if (⟨b.val / sat3D N, hlt⟩ : Fin (sat3M N)) ∈ C
      then us ⟨b.val / sat3D N, hlt⟩ b
      else y b
    else y b)
    = (if hlt : b.val / sat3D N < sat3M N then
      if (⟨b.val / sat3D N, hlt⟩ : Fin (sat3M N)) ∈ C
      then us' ⟨b.val / sat3D N, hlt⟩ b
      else y b
    else y b)
  by_cases hlt : b.val / sat3D N < sat3M N
  · rw [dif_pos hlt, dif_pos hlt]
    by_cases hmem : (⟨b.val / sat3D N, hlt⟩ : Fin (sat3M N)) ∈ C
    · rw [if_pos hmem, if_pos hmem]
      exact h _ hmem b
    · rw [if_neg hmem, if_neg hmem]
  · rw [dif_neg hlt, dif_neg hlt]

/-- **THE SANITY EVAL (proved)**: the multi-selector eval replayed through the multi-patch
interface at a singleton — the base case of the future eval induction. -/
theorem sat3PatchMulti_single_eval (N : ℕ) (hv : 1 ≤ sat3V N) {k : ℕ}
    (hk : k + 1 ≤ sat3M N) (hkv : k ≤ sat3V N) (c : Fin (sat3M N))
    (α : Fin k → Fin (sat3V N)) (hα : Function.Injective α)
    (bvec : Fin k → Bool) (T : Finset (Fin (sat3V N)))
    (hcov : ∀ w ∈ T, ∃ j : Fin k, α j = w)
    (us : Fin (sat3M N) → Fin N → Bool)
    (hus : us c = fun bit => decide (∃ w ∈ T, bit.val % sat3D N = w.val)) :
    sat3Family N (sat3PatchMulti N {c} (sat3ContextG N c hk α bvec) us)
      = decide (∃ j : Fin k, α j ∈ T ∧ bvec j = true) := by
  rw [sat3PatchMulti_singleton, hus]
  exact sat3ContextG_multi_probe_eval N hv hk hkv c α hα bvec T hcov

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3PatchMulti_singleton
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3PatchMulti_insert
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3PatchMulti_single_eval
