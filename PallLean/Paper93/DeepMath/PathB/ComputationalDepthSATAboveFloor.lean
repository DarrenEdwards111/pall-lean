import PallLean.Paper93.DeepMath.PathB.ComputationalDepthROTExtraction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATSlackTransfer

/-!
# SAT above the cone floor: `2·deps ≤ cbudget (SATFamily N)` at every length

The first above-floor fact on the actual target family.  The cone floor
(`cone_bound`) gives `2·deps − 1 ≤ cbudget` for every function; the dense-floor
file fills `deps` to `N − 22` on the SAT slices.  This file beats the floor:

* **`SATLang_se_append` (proved)** — the three-sign gadget's satisfiability is
  padding-transparent: trailing garbage after the encoded word never changes it;
* **`word_triple` (proved)** — the triple-update of the padded base completion at
  the sign positions `9, 15, 21` is exactly the encoded gadget word plus padding;
* **`SATFamily_not_ROT` (proved)** — no read-once tree computes any SAT slice of
  length `≥ 22`: the embedded `AllEqual₃` refuses every split (`rot_split` vs
  `allEq3_no_split_a/b/c`);
* **`SATFamily_above_floor` (proved)** — hence floor attainment is impossible
  (`floor_realizes_ROT` would deliver a read-once tree), so
  `2·(depSet (SATFamily N)).card ≤ cbudget (SATFamily N)`;
* **`cbudget_SATFamily_two_n_plus` (proved)** — readable form
  `2N ≤ cbudget (SATFamily N) + 44`, one past the dense floor's `45`.

## Honest scope

This is `+1` over the cone floor on the exact target family, at every length —
the seed the slack program demanded, now unconditional on SAT itself.  It is NOT
superlinear: the open campaign is making the excess grow (the `AEm` analogue
grew it to `+m` via the kill-chain; transferring that analysis to the codec
function is the genuine open work).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor

/-- The padded base completion: the three-clause base word, `false` beyond it. -/
def zBase (N : ℕ) : Fin N → Bool := fun k => sBase.getD k.val false

/-- **Padding-transparent gadget satisfiability (proved)**: the encoded three-sign
word followed by any garbage decides exactly `AllEqual₃` of the signs. -/
theorem SATLang_se_append (t₁ t₂ t₃ : Bool) (rest : List Bool) :
    SATLang (encodeFormula' (se t₁ t₂ t₃) ++ rest) = allEq3 t₁ t₂ t₃ := by
  cases t₁ <;> cases t₂ <;> cases t₃
  · rw [SATLang_append_sat _ _ ⟨fun _ => false, by decide⟩]; rfl
  · rw [SATLang_append_unsat _ _ (unsat_of_conflict _ (by decide) (by decide))]; rfl
  · rw [SATLang_append_unsat _ _ (unsat_of_conflict _ (by decide) (by decide))]; rfl
  · rw [SATLang_append_unsat _ _ (unsat_of_conflict _ (by decide) (by decide))]; rfl
  · rw [SATLang_append_unsat _ _ (unsat_of_conflict _ (by decide) (by decide))]; rfl
  · rw [SATLang_append_unsat _ _ (unsat_of_conflict _ (by decide) (by decide))]; rfl
  · rw [SATLang_append_unsat _ _ (unsat_of_conflict _ (by decide) (by decide))]; rfl
  · rw [SATLang_append_sat _ _ ⟨fun _ => true, by decide⟩]; rfl

/-- **The word identity (proved)**: updating the padded base completion at the three
sign positions produces the encoded gadget word plus `false`-padding. -/
theorem word_triple (N : ℕ) (hN : 22 ≤ N) (h9 : 9 < N) (h15 : 15 < N) (h21 : 21 < N)
    (a b c : Bool) :
    wordOfFin (Function.update (Function.update (Function.update (zBase N)
        ⟨9, h9⟩ a) ⟨15, h15⟩ b) ⟨21, h21⟩ c)
      = encodeFormula' (se a b c) ++ List.replicate (N - 22) false := by
  rw [se_concrete]
  apply List.ext_getElem
  · simp only [wordOfFin_length, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    omega
  · intro k h1 h2
    have hkN : k < N := by rw [wordOfFin_length] at h1; exact h1
    rw [wordOfFin_getElem _ k h1 hkN]
    by_cases hk22 : k < 22
    · interval_cases k <;> rfl
    · push_neg at hk22
      have hne21 : (⟨k, hkN⟩ : Fin N) ≠ ⟨21, h21⟩ := by
        intro he; rw [Fin.mk.injEq] at he; omega
      have hne15 : (⟨k, hkN⟩ : Fin N) ≠ ⟨15, h15⟩ := by
        intro he; rw [Fin.mk.injEq] at he; omega
      have hne9 : (⟨k, hkN⟩ : Fin N) ≠ ⟨9, h9⟩ := by
        intro he; rw [Fin.mk.injEq] at he; omega
      rw [Function.update_of_ne hne21, Function.update_of_ne hne15,
        Function.update_of_ne hne9]
      have hzb : zBase N ⟨k, hkN⟩ = false := by
        show sBase.getD k false = false
        have hlen : sBase.length ≤ k := by
          simp only [sBase, List.length_cons, List.length_nil]
          omega
        rw [List.getD_eq_default _ _ hlen]
      rw [hzb]
      have hlen22 : ([true, true, true, false,
          true, false, false, false, false, a,
          true, false, false, false, false, b,
          true, false, false, false, false, c] : List Bool).length ≤ k := by
        simp only [List.length_cons, List.length_nil]
        omega
      rw [List.getElem_append_right hlen22]
      rw [List.getElem_replicate]

/-- **No SAT slice is read-once realizable (proved)**: the codec's embedded
`AllEqual₃` refuses every split. -/
theorem SATFamily_not_ROT (N : ℕ) (hN : 22 ≤ N) :
    ¬ ∃ t : ROT N, ROT.ReadOnce t ∧ t.eval = SATFamily N := by
  rintro ⟨t, hro, hev⟩
  have h9 : (9 : ℕ) < N := by omega
  have h15 : (15 : ℕ) < N := by omega
  have h21 : (21 : ℕ) < N := by omega
  have hsp := rot_split t hro ⟨9, h9⟩ ⟨15, h15⟩ ⟨21, h21⟩
    (by intro he; rw [Fin.mk.injEq] at he; omega)
    (by intro he; rw [Fin.mk.injEq] at he; omega)
    (by intro he; rw [Fin.mk.injEq] at he; omega) (zBase N)
  have heq : (fun a b c => t.eval (Function.update (Function.update
      (Function.update (zBase N) ⟨9, h9⟩ a) ⟨15, h15⟩ b) ⟨21, h21⟩ c))
      = allEq3 := by
    funext a b c
    rw [hev]
    show SATFamily N _ = allEq3 a b c
    rw [SATFamily_apply, word_triple N hN h9 h15 h21 a b c, SATLang_se_append]
  rw [heq] at hsp
  rcases hsp with h | h | h
  · exact allEq3_no_split_a h
  · exact allEq3_no_split_b h
  · exact allEq3_no_split_c h

/-- **SAT BEATS ITS CONE FLOOR (proved)**: at every slice length `≥ 22`,
`2·deps ≤ cbudget (SATFamily N)` — one above the universal floor `2·deps − 1`,
unconditionally, via the read-once extraction. -/
theorem SATFamily_above_floor (N : ℕ) (hN : 22 ≤ N) :
    2 * (depSet (SATFamily N)).card ≤ cbudget (SATFamily N) := by
  rcases Nat.lt_or_ge (cbudget (SATFamily N)) (2 * (depSet (SATFamily N)).card)
    with h | h
  · exfalso
    obtain ⟨c, hcomp, hclen⟩ := Nat.sInf_mem (cbudget_set_nonempty (SATFamily N))
    have hclen' : c.length = cbudget (SATFamily N) := hclen
    have hfloor := cone_bound (SATFamily N)
    have hlen : c.length + 1 = 2 * (depSet (SATFamily N)).card := by omega
    exact SATFamily_not_ROT N hN
      (floor_realizes_ROT N (SATFamily N) c hcomp hlen)
  · exact h

/-- **Readable form (proved)**: `2N ≤ cbudget (SATFamily N) + 44` — one past the
dense floor's `45`. -/
theorem cbudget_SATFamily_two_n_plus (N : ℕ) (hN : 22 ≤ N) :
    2 * N ≤ cbudget (SATFamily N) + 44 := by
  have h1 := depSet_card_ge_dense N
  have h2 := SATFamily_above_floor N hN
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.SATFamily_not_ROT
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.SATFamily_above_floor
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_SATFamily_two_n_plus
