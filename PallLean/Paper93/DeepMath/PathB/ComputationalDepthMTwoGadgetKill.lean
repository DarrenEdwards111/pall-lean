import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShapeTreeExtract

/-!
# Brick 4a of the `SlackComposes` m = 2 attack: the shared subtree hits both gadgets

The missing-gadget kill, assembled: if the shared wire's subtree misses a gadget,
that gadget's triple has all leaf counts 1 in the extracted read-twice tree
(`shape_tree_cnt`), so `rot_split_cnt` splits its `allEq3` restriction — refuted
by `allEq3_no_split`:

* **`AEm_gadget2_allEq3` (proved)** — gadget 1 under the all-true completion is
  `AllEqual₃` (the coordinate-3,4,5 mirror of `AEm_gadget_allEq3`);
* **`shape_S_hits` (proved)** — in a 12-gate circuit for `AEm 2`, the shared
  subtree contains a variable of *each* gadget.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- Gadget 1 under the all-true completion is exactly `AllEqual₃`. -/
theorem AEm_gadget2_allEq3 (h3 : (3:ℕ) < 3 * 2) (h4 : (4:ℕ) < 3 * 2)
    (h5 : (5:ℕ) < 3 * 2) :
    (fun a b c => AEm 2 (Function.update (Function.update (Function.update
        (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ b) ⟨5, h5⟩ c))
      = allEq3 := by
  funext a b c
  cases a <;> cases b <;> cases c <;> rfl

/-- **The shared subtree hits both gadgets (proved).** -/
theorem shape_S_hits (c : List (CGate (3 * 2))) {s r₁ r₂ : ℕ}
    (hsh : TwelveShape c s r₁ r₂) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) :
    (∃ i : Fin (3 * 2), i.val < 3 ∧ Reach c s (varPos c i))
    ∧ (∃ i : Fin (3 * 2), 3 ≤ i.val ∧ Reach c s (varPos c i)) := by
  obtain ⟨t, hev, hcnt⟩ := shape_tree_cnt c hsh hcomp hlen
  constructor
  · by_contra hno
    push_neg at hno
    have h0 : (0:ℕ) < 3 * 2 := by omega
    have h1 : (1:ℕ) < 3 * 2 := by omega
    have h2 : (2:ℕ) < 3 * 2 := by omega
    have hsp := rot_split_cnt t ⟨0, h0⟩ ⟨1, h1⟩ ⟨2, h2⟩
      (by intro he; simp at he) (by intro he; simp at he) (by intro he; simp at he)
      (fun _ => true)
      (hcnt ⟨0, h0⟩ (hno ⟨0, h0⟩ (by show (0:ℕ) < 3; omega)))
      (hcnt ⟨1, h1⟩ (hno ⟨1, h1⟩ (by show (1:ℕ) < 3; omega)))
      (hcnt ⟨2, h2⟩ (hno ⟨2, h2⟩ (by show (2:ℕ) < 3; omega)))
    rw [hev] at hsp
    rw [AEm_gadget_allEq3 2 h0 h1 h2] at hsp
    rcases hsp with h | h | h
    · exact allEq3_no_split_a h
    · exact allEq3_no_split_b h
    · exact allEq3_no_split_c h
  · by_contra hno
    push_neg at hno
    have h3 : (3:ℕ) < 3 * 2 := by omega
    have h4 : (4:ℕ) < 3 * 2 := by omega
    have h5 : (5:ℕ) < 3 * 2 := by omega
    have hsp := rot_split_cnt t ⟨3, h3⟩ ⟨4, h4⟩ ⟨5, h5⟩
      (by intro he; simp at he) (by intro he; simp at he) (by intro he; simp at he)
      (fun _ => true)
      (hcnt ⟨3, h3⟩ (hno ⟨3, h3⟩ (by show (3:ℕ) ≤ 3; omega)))
      (hcnt ⟨4, h4⟩ (hno ⟨4, h4⟩ (by show (3:ℕ) ≤ 4; omega)))
      (hcnt ⟨5, h5⟩ (hno ⟨5, h5⟩ (by show (3:ℕ) ≤ 5; omega)))
    rw [hev] at hsp
    rw [AEm_gadget2_allEq3 h3 h4 h5] at hsp
    rcases hsp with h | h | h
    · exact allEq3_no_split_a h
    · exact allEq3_no_split_b h
    · exact allEq3_no_split_c h

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.shape_S_hits
