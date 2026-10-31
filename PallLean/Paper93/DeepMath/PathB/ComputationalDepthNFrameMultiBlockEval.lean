import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockContext

/-!
# N-Frame: the multi-block eval — independent reading of designated data blocks

Rung 3 of the multi-block additive-drag arc (patch → context → **eval** → drag/window).  The
single-block workhorses read ONE designated block; sat3's conjunction otherwise collapses several
data blocks to their intersection.  The repair is the slot-1 kit: in reading mode `(c*, w*)`,
every data block other than `c*` gets a slot-1 clause `{w*}` — satisfied by the pin-forced
`a (w*) = true` — so the instance value isolates the target block's pattern.  Staged:

  `sat3KitM` — the kit contents: slot-0 selector pattern `T c` on every data block, slot-1 kit
        clause `{w*}` on the data blocks other than `c*`.
  `sat3MultiEval_pin_*` / `sat3MultiEval_taut_*` — stage 1a: the pin/tautology context reads
        through the multi-patch (those blocks are outside `C`, so the patch passes them through).
  `sat3KitM_read_*` — stage 1b: the eight data-block reads of the kit through the multi-patch.
  `sat3_multi_pin_clause_iff` — stage 2: a pin clause is satisfied iff `a (α p) ⊕ sign` fires.
  `sat3_multi_taut_clause_sat` — stage 2: a tautology block is satisfied by every assignment.
  `sat3_multi_data_clause_iff` — stage 3, **the designated-block eval**: a data block `c ∈ C` is
        satisfied iff `(∃ w ∈ T c, a w) ∨ (c ≠ c* ∧ a w*)`.
  `sat3_multi_kit_neutralized` — stage 4: a non-designated data block is satisfied outright once
        `a w* = true` — the kit neutralizes it regardless of its pattern `T c`.
  `sat3_multi_kit_eval` — stage 5, **PROVED, the workhorse**: with data blocks `C`, patterns
        `T c` on slot 0 (covered by pins), pin vector forcing exactly `a (w*) = true`, and the
        slot-1 kits `{w*}` on `C \ {c*}`:
        `sat3Family (patchMulti C (contextM, sat3KitM)) = decide (w* ∈ T c*)`.

Reading mode `(c*, w*)` recovers the target block's pattern bit by bit while every other data
block is neutralized — the AND-collapse is gone.  This is the engine of additivity: the drag
rung indexes rows by the full tuple `(T c)_{c ∈ C}` and reads any two tuples apart at some
`(c*, w*)`, giving `2^{Σ_c d_c}` rows.

The staging (read lemmas → clause lemmas → block evals → family theorem) keeps each elaboration
unit small; a monolithic proof of the eval exhausts elaborator memory.

## Honest scope

The eval alone proves no lower bound.  Remaining rungs: the additive drag (`j ≥ Σ_c d_c` over a
cut factorization, with the side-location bookkeeping for `S`), then the rebuilt window
(`m·j → j`) toward `coneExcess = Ω(N)`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The kit -/

/-- **The slot-1 kit contents**: data block `c` carries its selector pattern `T c` on slot 0;
every data block other than `cstar` additionally carries the slot-1 kit clause `{wstar}`
(slot-1 selector at position `wstar`, positive sign — satisfied by the pin-forced
`a wstar = true`). -/
def sat3KitM (N : ℕ) (T : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (cstar : Fin (sat3M N)) (wstar : Fin (sat3V N)) :
    Fin (sat3M N) → Fin N → Bool :=
  fun c => fun bit => decide ((∃ w ∈ T c, bit.val % sat3D N = w.val)
    ∨ (c ≠ cstar ∧ bit.val % sat3D N = (sat3V N + 1) + wstar.val))

/-! ### Stage 1a: pin-block reads through the multi-patch -/

theorem sat3MultiEval_pin_sel (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (us : Fin (sat3M N) → Fin N → Bool) (p : Fin k) :
    sat3PatchMulti N C (sat3ContextM N C hk α b) us
      (sat3Bit N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ (α p).val
        (by have := (α p).isLt; omega)) = true := by
  rw [sat3PatchMulti_out_block N C (sat3ContextM N C hk α b) us _
    (sat3PinClauseM_not_mem N C hk p)]
  exact sat3ContextM_pin_sel N C hk α b p

theorem sat3MultiEval_pin_miss (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (us : Fin (sat3M N) → Fin N → Bool) (p : Fin k)
    (i : Fin (sat3V N)) (hi : i ≠ α p) :
    sat3PatchMulti N C (sat3ContextM N C hk α b) us
      (sat3Bit N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ i.val
        (by have := i.isLt; omega)) = false := by
  rw [sat3PatchMulti_out_block N C (sat3ContextM N C hk α b) us _
    (sat3PinClauseM_not_mem N C hk p)]
  exact sat3ContextM_pin_miss N C hk α b p i hi

theorem sat3MultiEval_pin_dead (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (us : Fin (sat3M N) → Fin N → Bool) (p : Fin k)
    (t : Fin 3) (ht : 1 ≤ t.val) (i : Fin (sat3V N)) :
    sat3PatchMulti N C (sat3ContextM N C hk α b) us
      (sat3Bit N (sat3PinClauseM N C hk p) t i.val
        (by have := i.isLt; omega)) = false := by
  rw [sat3PatchMulti_out_block N C (sat3ContextM N C hk α b) us _
    (sat3PinClauseM_not_mem N C hk p)]
  exact sat3ContextM_pin_dead N C hk α b p t ht i

theorem sat3MultiEval_pin_sign (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (us : Fin (sat3M N) → Fin N → Bool) (p : Fin k) :
    sat3PatchMulti N C (sat3ContextM N C hk α b) us
      (sat3Bit N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ (sat3V N) (by omega))
      = decide (b p = false) := by
  rw [sat3PatchMulti_out_block N C (sat3ContextM N C hk α b) us _
    (sat3PinClauseM_not_mem N C hk p)]
  exact sat3ContextM_pin_sign N C hk α b p

/-! ### Stage 1a: tautology-block reads through the multi-patch -/

theorem sat3MultiEval_taut_sel0 (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (us : Fin (sat3M N) → Fin N → Bool)
    (cl : Fin (sat3M N)) (h1 : cl ∉ C)
    (h2 : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val) :
    sat3PatchMulti N C (sat3ContextM N C hk α b) us
      (sat3Bit N cl ⟨0, by omega⟩ 0 (by omega)) = true := by
  rw [sat3PatchMulti_out_block N C (sat3ContextM N C hk α b) us cl h1]
  exact sat3ContextM_taut_sel0 N C hk α b cl h1 h2

theorem sat3MultiEval_taut_miss0 (N : ℕ) (hv : 1 ≤ sat3V N)
    (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (us : Fin (sat3M N) → Fin N → Bool)
    (cl : Fin (sat3M N)) (h1 : cl ∉ C)
    (h2 : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val)
    (i : Fin (sat3V N)) (hi : i ≠ (⟨0, hv⟩ : Fin (sat3V N))) :
    sat3PatchMulti N C (sat3ContextM N C hk α b) us
      (sat3Bit N cl ⟨0, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
  rw [sat3PatchMulti_out_block N C (sat3ContextM N C hk α b) us cl h1]
  exact sat3ContextM_taut_miss0 N hv C hk α b cl h1 h2 i hi

theorem sat3MultiEval_taut_sign0 (N : ℕ) (hv : 1 ≤ sat3V N)
    (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (us : Fin (sat3M N) → Fin N → Bool)
    (cl : Fin (sat3M N)) (h1 : cl ∉ C)
    (h2 : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val) :
    sat3PatchMulti N C (sat3ContextM N C hk α b) us
      (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)) = false := by
  rw [sat3PatchMulti_out_block N C (sat3ContextM N C hk α b) us cl h1]
  exact sat3ContextM_taut_sign0 N hv C hk α b cl h1 h2

theorem sat3MultiEval_taut_sel1 (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (us : Fin (sat3M N) → Fin N → Bool)
    (cl : Fin (sat3M N)) (h1 : cl ∉ C)
    (h2 : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val) :
    sat3PatchMulti N C (sat3ContextM N C hk α b) us
      (sat3Bit N cl ⟨1, by omega⟩ 0 (by omega)) = true := by
  rw [sat3PatchMulti_out_block N C (sat3ContextM N C hk α b) us cl h1]
  exact sat3ContextM_taut_sel1 N C hk α b cl h1 h2

theorem sat3MultiEval_taut_miss1 (N : ℕ) (hv : 1 ≤ sat3V N)
    (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (us : Fin (sat3M N) → Fin N → Bool)
    (cl : Fin (sat3M N)) (h1 : cl ∉ C)
    (h2 : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val)
    (i : Fin (sat3V N)) (hi : i ≠ (⟨0, hv⟩ : Fin (sat3V N))) :
    sat3PatchMulti N C (sat3ContextM N C hk α b) us
      (sat3Bit N cl ⟨1, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
  rw [sat3PatchMulti_out_block N C (sat3ContextM N C hk α b) us cl h1]
  exact sat3ContextM_taut_miss1 N hv C hk α b cl h1 h2 i hi

theorem sat3MultiEval_taut_sign1 (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (us : Fin (sat3M N) → Fin N → Bool)
    (cl : Fin (sat3M N)) (h1 : cl ∉ C)
    (h2 : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val) :
    sat3PatchMulti N C (sat3ContextM N C hk α b) us
      (sat3Bit N cl ⟨1, by omega⟩ (sat3V N) (by omega)) = true := by
  rw [sat3PatchMulti_out_block N C (sat3ContextM N C hk α b) us cl h1]
  exact sat3ContextM_taut_sign1 N C hk α b cl h1 h2

/-! ### Stage 1b: data-block reads of the kit through the multi-patch -/

theorem sat3KitM_read_sel_in (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (cstar : Fin (sat3M N)) (wstar : Fin (sat3V N))
    (c : Fin (sat3M N)) (hc : c ∈ C) (w : Fin (sat3V N)) (hw : w ∈ T c) :
    sat3PatchMulti N C y (sat3KitM N T cstar wstar)
      (sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega)) = true := by
  rw [sat3PatchMulti_own N C y (sat3KitM N T cstar wstar) c hc]
  show decide _ = true
  rw [decide_eq_true_eq]
  left
  refine ⟨w, hw, ?_⟩
  rw [sat3Bit_rem]
  show (0 : ℕ) * (sat3V N + 1) + w.val = w.val
  omega

theorem sat3KitM_read_sel_out (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (cstar : Fin (sat3M N)) (wstar : Fin (sat3V N))
    (c : Fin (sat3M N)) (hc : c ∈ C) (i : Fin (sat3V N)) (hi : i ∉ T c) :
    sat3PatchMulti N C y (sat3KitM N T cstar wstar)
      (sat3Bit N c ⟨0, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
  rw [sat3PatchMulti_own N C y (sat3KitM N T cstar wstar) c hc]
  have hr : (sat3Bit N c ⟨0, by omega⟩ i.val
      (by have := i.isLt; omega)).val % sat3D N = i.val := by
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + i.val = i.val
    omega
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨w, hw, hrem⟩ | ⟨-, hrem⟩)
  · rw [hr] at hrem
    rw [show i = w from Fin.ext hrem] at hi
    exact hi hw
  · rw [hr] at hrem
    have := i.isLt
    omega

theorem sat3KitM_read_sign0 (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (cstar : Fin (sat3M N)) (wstar : Fin (sat3V N))
    (c : Fin (sat3M N)) (hc : c ∈ C) :
    sat3PatchMulti N C y (sat3KitM N T cstar wstar)
      (sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega)) = false := by
  rw [sat3PatchMulti_own N C y (sat3KitM N T cstar wstar) c hc]
  have hr : (sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega)).val % sat3D N
      = sat3V N := by
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
    omega
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨w, -, hrem⟩ | ⟨-, hrem⟩)
  · rw [hr] at hrem
    have := w.isLt
    omega
  · rw [hr] at hrem
    have := wstar.isLt
    omega

theorem sat3KitM_read_sel1_kit (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (cstar : Fin (sat3M N)) (wstar : Fin (sat3V N))
    (c : Fin (sat3M N)) (hc : c ∈ C) (hne : c ≠ cstar) :
    sat3PatchMulti N C y (sat3KitM N T cstar wstar)
      (sat3Bit N c ⟨1, by omega⟩ wstar.val
        (by have := wstar.isLt; omega)) = true := by
  rw [sat3PatchMulti_own N C y (sat3KitM N T cstar wstar) c hc]
  show decide _ = true
  rw [decide_eq_true_eq]
  right
  refine ⟨hne, ?_⟩
  rw [sat3Bit_rem]
  show (1 : ℕ) * (sat3V N + 1) + wstar.val = sat3V N + 1 + wstar.val
  omega

theorem sat3KitM_read_sel1_miss (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (cstar : Fin (sat3M N)) (wstar : Fin (sat3V N))
    (c : Fin (sat3M N)) (hc : c ∈ C) (i : Fin (sat3V N)) (hi : i ≠ wstar) :
    sat3PatchMulti N C y (sat3KitM N T cstar wstar)
      (sat3Bit N c ⟨1, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
  rw [sat3PatchMulti_own N C y (sat3KitM N T cstar wstar) c hc]
  have hr : (sat3Bit N c ⟨1, by omega⟩ i.val
      (by have := i.isLt; omega)).val % sat3D N = sat3V N + 1 + i.val := by
    rw [sat3Bit_rem]
    show (1 : ℕ) * (sat3V N + 1) + i.val = sat3V N + 1 + i.val
    omega
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨w, -, hrem⟩ | ⟨-, hrem⟩)
  · rw [hr] at hrem
    have := w.isLt
    omega
  · rw [hr] at hrem
    have hiw : i.val = wstar.val := by omega
    exact hi (Fin.ext hiw)

theorem sat3KitM_read_sel1_cstar (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (cstar : Fin (sat3M N)) (hcstar : cstar ∈ C) (wstar : Fin (sat3V N))
    (i : Fin (sat3V N)) :
    sat3PatchMulti N C y (sat3KitM N T cstar wstar)
      (sat3Bit N cstar ⟨1, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
  rw [sat3PatchMulti_own N C y (sat3KitM N T cstar wstar) cstar hcstar]
  have hr : (sat3Bit N cstar ⟨1, by omega⟩ i.val
      (by have := i.isLt; omega)).val % sat3D N = sat3V N + 1 + i.val := by
    rw [sat3Bit_rem]
    show (1 : ℕ) * (sat3V N + 1) + i.val = sat3V N + 1 + i.val
    omega
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨w, -, hrem⟩ | ⟨hne, -⟩)
  · rw [hr] at hrem
    have := w.isLt
    omega
  · exact hne rfl

theorem sat3KitM_read_sign1 (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (cstar : Fin (sat3M N)) (wstar : Fin (sat3V N))
    (c : Fin (sat3M N)) (hc : c ∈ C) :
    sat3PatchMulti N C y (sat3KitM N T cstar wstar)
      (sat3Bit N c ⟨1, by omega⟩ (sat3V N) (by omega)) = false := by
  rw [sat3PatchMulti_own N C y (sat3KitM N T cstar wstar) c hc]
  have hr : (sat3Bit N c ⟨1, by omega⟩ (sat3V N) (by omega)).val % sat3D N
      = sat3V N + 1 + sat3V N := by
    rw [sat3Bit_rem]
    show (1 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N + 1 + sat3V N
    omega
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨w, -, hrem⟩ | ⟨-, hrem⟩)
  · rw [hr] at hrem
    have := w.isLt
    omega
  · rw [hr] at hrem
    have := wstar.isLt
    omega

theorem sat3KitM_read_slot2 (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (cstar : Fin (sat3M N)) (wstar : Fin (sat3V N))
    (c : Fin (sat3M N)) (hc : c ∈ C) (i : Fin (sat3V N)) :
    sat3PatchMulti N C y (sat3KitM N T cstar wstar)
      (sat3Bit N c ⟨2, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
  rw [sat3PatchMulti_own N C y (sat3KitM N T cstar wstar) c hc]
  have hr : (sat3Bit N c ⟨2, by omega⟩ i.val
      (by have := i.isLt; omega)).val % sat3D N
      = 2 * (sat3V N + 1) + i.val := by
    rw [sat3Bit_rem]
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨w, -, hrem⟩ | ⟨-, hrem⟩)
  · rw [hr] at hrem
    have := w.isLt
    omega
  · rw [hr] at hrem
    have := wstar.isLt
    omega

/-! ### Stage 2: clause-level analysis of the pin and tautology blocks -/

set_option maxHeartbeats 800000 in
/-- A pin clause of the multi-patched instance is satisfied iff the pinned literal
`a (α p) ⊕ sign(b p)` fires — for ANY kit contents `us` (pin blocks are outside `C`). -/
theorem sat3_multi_pin_clause_iff (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (us : Fin (sat3M N) → Fin N → Bool) (a : Fin (sat3V N) → Bool) (p : Fin k) :
    (∃ t, sat3Lit N (sat3PatchMulti N C (sat3ContextM N C hk α b) us) a
        (sat3PinClauseM N C hk p) t = true) ↔
      xor (a (α p)) (decide (b p = false)) = true := by
  have hiff := sat3Clause_single_iff N
    (sat3PatchMulti N C (sat3ContextM N C hk α b) us) a
    (sat3PinClauseM N C hk p) (α p)
    (sat3MultiEval_pin_sel N C hk α b us p)
    (fun i hi => sat3MultiEval_pin_miss N C hk α b us p i hi)
    (sat3MultiEval_pin_dead N C hk α b us p ⟨1, by omega⟩ (by show (1 : ℕ) ≤ 1; omega))
    (sat3MultiEval_pin_dead N C hk α b us p ⟨2, by omega⟩ (by show (1 : ℕ) ≤ 2; omega))
  rw [sat3MultiEval_pin_sign N C hk α b us p] at hiff
  exact hiff

set_option maxHeartbeats 800000 in
/-- A tautology block of the multi-patched instance is satisfied by every assignment —
for ANY kit contents `us` (tautology blocks are outside `C`). -/
theorem sat3_multi_taut_clause_sat (N : ℕ) (hv : 1 ≤ sat3V N)
    (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (us : Fin (sat3M N) → Fin N → Bool) (a : Fin (sat3V N) → Bool)
    (cl : Fin (sat3M N)) (h1 : cl ∉ C)
    (h2 : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val) :
    ∃ t, sat3Lit N (sat3PatchMulti N C (sat3ContextM N C hk α b) us) a cl t = true := by
  cases ha : a ⟨0, hv⟩
  · refine ⟨⟨1, by omega⟩, ?_⟩
    rw [sat3Lit_single N (sat3PatchMulti N C (sat3ContextM N C hk α b) us) a cl
        ⟨1, by omega⟩ ⟨0, hv⟩
        (sat3MultiEval_taut_sel1 N C hk α b us cl h1 h2)
        (sat3MultiEval_taut_miss1 N hv C hk α b us cl h1 h2),
      sat3MultiEval_taut_sign1 N C hk α b us cl h1 h2, Bool.xor_true, ha]
    rfl
  · refine ⟨⟨0, by omega⟩, ?_⟩
    rw [sat3Lit_single N (sat3PatchMulti N C (sat3ContextM N C hk α b) us) a cl
        ⟨0, by omega⟩ ⟨0, hv⟩
        (sat3MultiEval_taut_sel0 N C hk α b us cl h1 h2)
        (sat3MultiEval_taut_miss0 N hv C hk α b us cl h1 h2),
      sat3MultiEval_taut_sign0 N hv C hk α b us cl h1 h2, Bool.xor_false, ha]

/-! ### Stage 3: the designated-block eval -/

set_option maxHeartbeats 1600000 in
/-- **The designated-block eval**: a data block `c ∈ C` of the multi-patched instance is
satisfied iff its slot-0 pattern fires (`∃ w ∈ T c, a w`) or its slot-1 kit fires
(`c ≠ cstar ∧ a wstar`) — for ANY context `y` (data blocks read the kit through the patch). -/
theorem sat3_multi_data_clause_iff (N : ℕ) (C : Finset (Fin (sat3M N)))
    (y : Fin N → Bool) (T : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (cstar : Fin (sat3M N)) (wstar : Fin (sat3V N)) (a : Fin (sat3V N) → Bool)
    (c : Fin (sat3M N)) (hc : c ∈ C) :
    (∃ t, sat3Lit N (sat3PatchMulti N C y (sat3KitM N T cstar wstar)) a c t = true) ↔
      ((∃ w ∈ T c, a w = true) ∨ (c ≠ cstar ∧ a wstar = true)) := by
  constructor
  · rintro ⟨t, ht⟩
    rcases t with ⟨tv, htv⟩
    interval_cases tv
    · unfold sat3Lit at ht
      obtain ⟨i, -, hi⟩ := List.any_eq_true.mp ht
      rw [Bool.and_eq_true] at hi
      obtain ⟨hisel, hilit⟩ := hi
      have hiT : i ∈ T c := by
        by_contra hniT
        rw [sat3KitM_read_sel_out N C y T cstar wstar c hc i hniT] at hisel
        exact Bool.noConfusion hisel
      rw [sat3KitM_read_sign0 N C y T cstar wstar c hc] at hilit
      refine Or.inl ⟨i, hiT, ?_⟩
      cases hai : a i
      · rw [hai] at hilit
        exact Bool.noConfusion hilit
      · rfl
    · unfold sat3Lit at ht
      obtain ⟨i, -, hi⟩ := List.any_eq_true.mp ht
      rw [Bool.and_eq_true] at hi
      obtain ⟨hisel, hilit⟩ := hi
      by_cases hcs : c = cstar
      · exfalso
        rw [hcs] at hisel hc
        rw [sat3KitM_read_sel1_cstar N C y T cstar hc wstar i] at hisel
        exact Bool.noConfusion hisel
      · by_cases hiw : i = wstar
        · subst hiw
          rw [sat3KitM_read_sign1 N C y T cstar i c hc] at hilit
          refine Or.inr ⟨hcs, ?_⟩
          cases hai : a i
          · rw [hai] at hilit
            exact Bool.noConfusion hilit
          · rfl
        · exfalso
          rw [sat3KitM_read_sel1_miss N C y T cstar wstar c hc i hiw] at hisel
          exact Bool.noConfusion hisel
    · exfalso
      rw [sat3Lit_false_of_empty N (sat3PatchMulti N C y (sat3KitM N T cstar wstar))
        a c ⟨2, htv⟩
        (fun i => sat3KitM_read_slot2 N C y T cstar wstar c hc i)] at ht
      exact Bool.noConfusion ht
  · rintro (⟨w, hwT, haw⟩ | ⟨hne, haw⟩)
    · refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N
        (sat3PatchMulti N C y (sat3KitM N T cstar wstar)) a c ⟨0, by omega⟩ w
        (sat3KitM_read_sel_in N C y T cstar wstar c hc w hwT) ?_⟩
      rw [sat3KitM_read_sign0 N C y T cstar wstar c hc, haw]
      rfl
    · refine ⟨⟨1, by omega⟩, sat3Lit_true_of_selected N
        (sat3PatchMulti N C y (sat3KitM N T cstar wstar)) a c ⟨1, by omega⟩ wstar
        (sat3KitM_read_sel1_kit N C y T cstar wstar c hc hne) ?_⟩
      rw [sat3KitM_read_sign1 N C y T cstar wstar c hc, haw]
      rfl

/-! ### Stage 4: the neutralization corollary -/

/-- **Neutralization**: a non-designated data block is satisfied outright once the pin-forced
`a wstar = true` holds — its slot-1 kit clause fires regardless of its pattern `T c`.  This is
what removes the AND-collapse across data blocks. -/
theorem sat3_multi_kit_neutralized (N : ℕ) (C : Finset (Fin (sat3M N)))
    (y : Fin N → Bool) (T : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (cstar : Fin (sat3M N)) (wstar : Fin (sat3V N)) (a : Fin (sat3V N) → Bool)
    (c : Fin (sat3M N)) (hc : c ∈ C) (hne : c ≠ cstar) (haw : a wstar = true) :
    ∃ t, sat3Lit N (sat3PatchMulti N C y (sat3KitM N T cstar wstar)) a c t = true :=
  (sat3_multi_data_clause_iff N C y T cstar wstar a c hc).mpr (Or.inr ⟨hne, haw⟩)

/-! ### Stage 5: the family theorem -/

set_option maxHeartbeats 1600000 in
/-- **THE MULTI-BLOCK KIT EVAL (proved)**: in reading mode `(c*, w*)`, the instance value is the
target block's pattern bit `decide (w* ∈ T c*)` — every other data block is neutralized by its
slot-1 kit. -/
theorem sat3_multi_kit_eval (N : ℕ) (hv : 1 ≤ sat3V N)
    (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (hα : Function.Injective α)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (hcov : ∀ c ∈ C, ∀ w ∈ T c, ∃ p : Fin k, α p = w)
    (cstar : Fin (sat3M N)) (hcstar : cstar ∈ C)
    (wstar : Fin (sat3V N)) (pstar : Fin k) (hpstar : α pstar = wstar) :
    sat3Family N (sat3PatchMulti N C
      (sat3ContextM N C hk α (fun p => decide (α p = wstar)))
      (sat3KitM N T cstar wstar))
      = decide (wstar ∈ T cstar) := by
  classical
  set bvec : Fin k → Bool := fun p => decide (α p = wstar) with hbvec
  set x : Fin N → Bool :=
    sat3PatchMulti N C (sat3ContextM N C hk α bvec) (sat3KitM N T cstar wstar) with hx
  by_cases hsat : wstar ∈ T cstar
  · rw [decide_eq_true hsat]
    set awit : Fin (sat3V N) → Bool :=
      fun i => if h : ∃ p : Fin k, α p = i then bvec (Classical.choose h) else true
      with hawit
    have hawit_at : ∀ p : Fin k, awit (α p) = bvec p := by
      intro p
      show (if h : ∃ p' : Fin k, α p' = α p then bvec (Classical.choose h) else true)
        = bvec p
      have hex : ∃ p' : Fin k, α p' = α p := ⟨p, rfl⟩
      rw [dif_pos hex]
      exact congrArg bvec (hα (Classical.choose_spec hex))
    have hawit_wstar : awit wstar = true := by
      rw [← hpstar, hawit_at pstar]
      exact decide_eq_true hpstar
    rw [sat3Family_iff]
    refine ⟨awit, sat3Eval_true_of_all N x awit ?_⟩
    intro cl
    by_cases hclC : cl ∈ C
    · by_cases hclstar : cl = cstar
      · refine (sat3_multi_data_clause_iff N C (sat3ContextM N C hk α bvec) T cstar
          wstar awit cl hclC).mpr (Or.inl ⟨wstar, ?_, hawit_wstar⟩)
        rw [hclstar]
        exact hsat
      · exact sat3_multi_kit_neutralized N C (sat3ContextM N C hk α bvec) T cstar
          wstar awit cl hclC hclstar hawit_wstar
    · by_cases hpin : ∃ p : Fin k, sat3PinClauseM N C hk p = cl
      · obtain ⟨p, rfl⟩ := hpin
        refine (sat3_multi_pin_clause_iff N C hk α bvec (sat3KitM N T cstar wstar)
          awit p).mpr ?_
        rw [hawit_at p]
        cases bvec p <;> rfl
      · exact sat3_multi_taut_clause_sat N hv C hk α bvec (sat3KitM N T cstar wstar)
          awit cl hclC (fun p h => hpin ⟨p, Fin.ext h.symm⟩)
  · rw [decide_eq_false hsat]
    apply decide_eq_false
    rintro ⟨A, hA⟩
    have hforce : ∀ p : Fin k, A (α p) = bvec p := by
      intro p
      exact xor_decide_eq _ _
        ((sat3_multi_pin_clause_iff N C hk α bvec (sat3KitM N T cstar wstar) A p).mp
          (sat3Eval_clause_true N x A hA (sat3PinClauseM N C hk p)))
    rcases (sat3_multi_data_clause_iff N C (sat3ContextM N C hk α bvec) T cstar wstar
        A cstar hcstar).mp (sat3Eval_clause_true N x A hA cstar)
      with ⟨w, hwT, hAw⟩ | ⟨hne, -⟩
    · obtain ⟨p, hp⟩ := hcov cstar hcstar w hwT
      have h1 : bvec p = true := by
        rw [← hforce p, hp]
        exact hAw
      have h1' : decide (α p = wstar) = true := h1
      have hww : w = wstar := by
        rw [← hp]
        exact of_decide_eq_true h1'
      rw [hww] at hwT
      exact hsat hwT
    · exact hne rfl

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_data_clause_iff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_kit_neutralized
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_kit_eval
