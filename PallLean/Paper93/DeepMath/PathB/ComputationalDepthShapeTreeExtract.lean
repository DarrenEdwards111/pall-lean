import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTwelveFanout
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthROTCountSplit

/-!
# Brick 3b of the `SlackComposes` m = 2 attack: the read-twice tree extraction

From the `TwelveShape` anatomy, extract a tree computing `AEm 2` in which every
variable whose var gate is *not* reachable from the shared wire `s` occurs in
exactly one leaf:

* `reach_cases` / `reach_var_stuck` — first-step inversion of `Reach`;
* `varPos` — the unique var-gate position of each variable (bijectivity);
* **`shape_reach_not_both` (proved)** — away from `s`, reader chains are
  deterministic: the two sources of a binary gate cannot both reach a position
  outside the shared subtree (the avoidance invariant `Reach q q₀` is carried
  down the recursion, so every chain position stays ≠ `s`);
* **`shape_extract_spec` (proved)** — the fuel-indexed extraction computes the
  wire, and for every variable outside the shared subtree the leaf count of the
  extracted tree is exactly [position reachable];
* **`shape_tree_cnt` (proved)** — a 12-gate circuit for `AEm 2` yields a tree
  `t` with `t.eval = AEm 2` and `t.cnt i = 1` for every variable `i` outside
  the shared subtree.

With `rot_split_cnt`, any such tree splits on a gadget triple disjoint from the
shared subtree — brick 4 turns this into the missing-gadget kill.  Nothing here
is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-! ### Reach inversions -/

/-- First-step inversion: a reached position is the start or lies below a read. -/
theorem reach_cases {n : ℕ} {c : List (CGate n)} {w q : ℕ} (h : Reach c w q) :
    q = w ∨ ∃ t, t ∈ gateReads (c.getD w (.cst false)) ∧ t < w ∧ Reach c t q := by
  induction h with
  | refl => exact Or.inl rfl
  | step hp hq hlt ih =>
    rcases ih with he | ⟨t, ht, htw, hres⟩
    · subst he
      exact Or.inr ⟨_, hq, hlt, Reach.refl _⟩
    · exact Or.inr ⟨t, ht, htw, Reach.step hres hq hlt⟩

/-- A var gate reaches only itself. -/
theorem reach_var_stuck {n : ℕ} {c : List (CGate n)} {w : ℕ} {i : Fin n}
    (hg : c.getD w (.cst false) = CGate.var i) {q : ℕ} (h : Reach c w q) : q = w := by
  rcases reach_cases h with he | ⟨t, ht, -, -⟩
  · exact he
  · rw [hg] at ht
    exact absurd ht (by simp [gateReads])

/-- The cone is exactly downward reachability from the root. -/
theorem inCone_reach_root {n : ℕ} {c : List (CGate n)} {q : ℕ} (h : InCone c q) :
    Reach c (c.length - 1) q := by
  induction h with
  | root => exact Reach.refl _
  | step hw hj hlt ih => exact Reach.step ih hj hlt

/-! ### The unique var position -/

open Classical in
/-- The (unique) var-gate position of a variable. -/
noncomputable def varPos (c : List (CGate (3 * 2))) (i : Fin (3 * 2)) : ℕ :=
  if h : ∃ p, p ∈ cone c ∧ c.getD p (.cst false) = CGate.var i then Classical.choose h
  else 0

theorem varPos_mem (c : List (CGate (3 * 2))) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) (i : Fin (3 * 2)) :
    varPos c i ∈ cone c ∧ c.getD (varPos c i) (.cst false) = CGate.var i := by
  have hi : i ∈ depSet (AEm 2) := by
    rw [depSet_AEm]
    exact Finset.mem_univ _
  have hex := var_position_exists (AEm 2) c hcomp (by omega) i hi
  rw [varPos, dif_pos hex]
  exact Classical.choose_spec hex

theorem varPos_lt (c : List (CGate (3 * 2))) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) (i : Fin (3 * 2)) : varPos c i < 12 := by
  have := (mem_cone.mp (varPos_mem c hcomp hlen i).1).1
  omega

theorem varPos_gate (c : List (CGate (3 * 2))) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) (i : Fin (3 * 2)) :
    c.getD (varPos c i) (.cst false) = CGate.var i :=
  (varPos_mem c hcomp hlen i).2

/-! ### Chain determinism away from the shared wire -/

/-- **Reader-chain disjointness away from `s` (proved)**: the two sources of a
binary gate cannot both reach a position outside the shared subtree. -/
theorem shape_reach_not_both (c : List (CGate (3 * 2))) {s r₁ r₂ : ℕ}
    (hsh : TwelveShape c s r₁ r₂) (hlen : c.length = 12)
    {w j k : ℕ} (hw12 : w < 12)
    (hj : j ∈ gateReads (c.getD w (.cst false))) (hjw : j < w)
    (hk : k ∈ gateReads (c.getD w (.cst false))) (hkw : k < w)
    (hjk : j ≠ k) {q₀ : ℕ} (hq₀s : ¬ Reach c s q₀) :
    ∀ (m q : ℕ), 12 - q ≤ m → Reach c j q → Reach c k q → Reach c q q₀ → False := by
  intro m
  induction m with
  | zero =>
    intro q hq hrj _ _
    have := reach_le hrj
    omega
  | succ m ih =>
    intro q hq hrj hrk hrq₀
    have hqs : q ≠ s := fun he => hq₀s (he ▸ hrq₀)
    by_cases hqj : q = j
    · subst hqj
      obtain ⟨p, hpk, hqp, hqlt⟩ := reach_last hrk hjk
      have hple := reach_le hpk
      have hpw : p = w :=
        hsh.others_one q (by omega) hqs p w (by omega) hw12 hqp hj
      rw [hpw] at hpk
      have := reach_le hpk
      omega
    · by_cases hqk : q = k
      · subst hqk
        obtain ⟨p, hpj, hqp, hqlt⟩ := reach_last hrj (Ne.symm hjk)
        have hple := reach_le hpj
        have hpw : p = w :=
          hsh.others_one q (by omega) hqs p w (by omega) hw12 hqp hk
        rw [hpw] at hpj
        have := reach_le hpj
        omega
      · obtain ⟨p₁, hp₁, hqr₁, hql₁⟩ := reach_last hrj hqj
        obtain ⟨p₂, hp₂, hqr₂, hql₂⟩ := reach_last hrk hqk
        have hp₁le := reach_le hp₁
        have hp₂le := reach_le hp₂
        have h12' : p₁ = p₂ :=
          hsh.others_one q (by omega) hqs p₁ p₂ (by omega) (by omega) hqr₁ hqr₂
        rw [← h12'] at hp₂
        exact ih p₁ (by omega) hp₁ hp₂
          (reach_trans (Reach.step (Reach.refl p₁) hqr₁ hql₁) hrq₀)

/-! ### The extraction with counts -/

/-- **The read-twice extraction (proved)**: from every position, the extracted
tree computes the wire; for variables outside the shared subtree, the leaf count
is exactly [var position reachable]. -/
theorem shape_extract_spec (c : List (CGate (3 * 2))) {s r₁ r₂ : ℕ}
    (hsh : TwelveShape c s r₁ r₂) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) (i₀ : Fin (3 * 2)) :
    ∀ (fuel w : ℕ), w < fuel → w < 12 →
      (∀ x, (extractT c i₀ fuel w).eval x = wire c x w)
      ∧ ∀ i : Fin (3 * 2), ¬ Reach c s (varPos c i) →
          ((Reach c w (varPos c i) → (extractT c i₀ fuel w).cnt i = 1)
           ∧ (¬ Reach c w (varPos c i) → (extractT c i₀ fuel w).cnt i = 0)) := by
  intro fuel
  induction fuel with
  | zero => intro w hw _; exact absurd hw (Nat.not_lt_zero w)
  | succ fuel ih =>
    intro w hw hw12
    have hwlt : w < c.length := by omega
    rcases hsh.dichotomy w hw12 with ⟨i', hg⟩ | ⟨op, j, k, hg, hj, hk, hjk⟩
    · -- var gate
      rw [extractT_var hg]
      constructor
      · intro x
        rw [wire_eq c x hwlt, hg]
        rfl
      · intro i his
        by_cases hii : i' = i
        · subst hii
          have hvp : w = varPos c i' :=
            hsh.var_inj w (varPos c i') i' hw12 (varPos_lt c hcomp hlen i') hg
              (varPos_gate c hcomp hlen i')
          constructor
          · intro _
            show (if i' = i' then 1 else 0) = 1
            rw [if_pos rfl]
          · intro hnr
            exact absurd (by rw [← hvp]; exact Reach.refl w) hnr
        · have hnr : ¬ Reach c w (varPos c i) := by
            intro hr
            have hq := reach_var_stuck hg hr
            have hgi := varPos_gate c hcomp hlen i
            rw [hq, hg] at hgi
            exact hii (CGate.var.inj hgi)
          constructor
          · intro hr
            exact absurd hr hnr
          · intro _
            show (if i' = i then 1 else 0) = 0
            rw [if_neg hii]
    · -- genuine binary gate
      have hjm : j ∈ gateReads (c.getD w (.cst false)) := by
        rw [hg]
        exact Finset.mem_insert_self j {k}
      have hkm : k ∈ gateReads (c.getD w (.cst false)) := by
        rw [hg]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self k)
      rw [extractT_bin hg]
      obtain ⟨hevj, hcntj⟩ := ih j (by omega) (by omega)
      obtain ⟨hevk, hcntk⟩ := ih k (by omega) (by omega)
      constructor
      · intro x
        show op ((extractT c i₀ fuel j).eval x) ((extractT c i₀ fuel k).eval x)
          = wire c x w
        rw [wire_eq c x hwlt, hg]
        show op ((extractT c i₀ fuel j).eval x) ((extractT c i₀ fuel k).eval x)
          = op ((runFrom x [] (c.take w)).getD j false)
            ((runFrom x [] (c.take w)).getD k false)
        rw [wire_prefix c x hj (le_of_lt hwlt),
          wire_prefix c x hk (le_of_lt hwlt), hevj x, hevk x]
      · intro i his
        obtain ⟨hcj1, hcj0⟩ := hcntj i his
        obtain ⟨hck1, hck0⟩ := hcntk i his
        constructor
        · intro hr
          show (extractT c i₀ fuel j).cnt i + (extractT c i₀ fuel k).cnt i = 1
          rcases reach_cases hr with he | ⟨t, ht, htw, hres⟩
          · exfalso
            have hgi := varPos_gate c hcomp hlen i
            rw [he, hg] at hgi
            simp at hgi
          · have ht' : t = j ∨ t = k := by
              rw [hg] at ht
              rcases Finset.mem_insert.mp ht with h | h
              · exact Or.inl h
              · exact Or.inr (Finset.mem_singleton.mp h)
            rcases ht' with heq | heq
            · subst heq
              have hnk : ¬ Reach c k (varPos c i) := by
                intro hrk
                exact shape_reach_not_both c hsh hlen hw12 hjm hj hkm hk hjk his
                  12 (varPos c i) (by omega) hres hrk (Reach.refl _)
              rw [hcj1 hres, hck0 hnk]
            · subst heq
              have hnj : ¬ Reach c j (varPos c i) := by
                intro hrj
                exact shape_reach_not_both c hsh hlen hw12 hjm hj hkm hk hjk his
                  12 (varPos c i) (by omega) hrj hres (Reach.refl _)
              rw [hcj0 hnj, hck1 hres]
        · intro hnr
          show (extractT c i₀ fuel j).cnt i + (extractT c i₀ fuel k).cnt i = 0
          have hnj : ¬ Reach c j (varPos c i) := fun hr =>
            hnr (reach_trans (Reach.step (Reach.refl w) hjm hj) hr)
          have hnk : ¬ Reach c k (varPos c i) := fun hr =>
            hnr (reach_trans (Reach.step (Reach.refl w) hkm hk) hr)
          rw [hcj0 hnj, hck0 hnk]

/-- **THE READ-TWICE TREE (proved)**: a 12-gate circuit for `AEm 2` yields a tree
computing `AEm 2` in which every variable outside the shared subtree occurs in
exactly one leaf. -/
theorem shape_tree_cnt (c : List (CGate (3 * 2))) {s r₁ r₂ : ℕ}
    (hsh : TwelveShape c s r₁ r₂) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) :
    ∃ t : ROT (3 * 2), t.eval = AEm 2 ∧
      ∀ i : Fin (3 * 2), ¬ Reach c s (varPos c i) → t.cnt i = 1 := by
  have hspec := shape_extract_spec c hsh hcomp hlen ⟨0, by omega⟩ 12 11
    (by omega) (by omega)
  refine ⟨extractT c ⟨0, by omega⟩ 12 11, ?_, ?_⟩
  · funext x
    rw [hspec.1 x]
    have hw : wire c x 11 = output c x := by
      rw [output_eq_wire]
      have h11 : c.length - 1 = 11 := by omega
      rw [h11]
    rw [hw]
    exact hcomp x
  · intro i his
    refine (hspec.2 i his).1 ?_
    have hm := varPos_mem c hcomp hlen i
    have hic : InCone c (varPos c i) := (mem_cone.mp hm.1).2
    have hrr := inCone_reach_root hic
    have h11 : c.length - 1 = 11 := by omega
    rw [h11] at hrr
    exact hrr

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.shape_reach_not_both
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.shape_tree_cnt
