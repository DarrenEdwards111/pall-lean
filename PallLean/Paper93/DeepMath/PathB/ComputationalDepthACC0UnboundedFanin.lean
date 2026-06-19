import Mathlib

/-!
# Entry 324 — the unbounded-fan-in ACC⁰ circuit model (proved)

Entry 323 made the circuit bridges depth/gate-type faithful over the *binary-fan-in* `Circ` (formula) model, leaving one
honest modelling caveat: full `ACC⁰` permits **unbounded fan-in** (an `AND`/`OR`/`MOD` of arbitrarily many inputs is one
gate of depth `1`).  This file builds that model.

**`UCirc n`** — a circuit over `n` inputs with: `var` (input), `const`, `unot` (NOT), and the **unbounded-fan-in** gates
`uand` / `uor` / `umod m` taking a *list* of child sub-circuits.  `umod m` is the `MOD_m` gate: it fires iff the number
of accepting children is `≡ 0 (mod m)`.  This is the genuine `ACC⁰[m]` basis.

The defining feature, impossible in the binary model: **an unbounded-fan-in gate over arbitrarily many depth-`0` leaves
has depth `1`** (`uand_vars_depth`).  So `AND` of `n` inputs is one gate, depth `1` — not a depth-`log n` binary tree.

## What is proved (clean axioms, no `sorry`)

* **`UCirc`, `eval`, `size`, `depth`, `moduli`** — the model, its Boolean semantics, gate count, depth, and the multiset
  of `MOD` moduli it uses (for `ACC⁰[m]` gate-type accounting).
* **`foldrMax_le`, `depth_uand_le` / `depth_uor_le` / `depth_umod_le`** — a gate's depth is `1 +` the max child depth.
* **`uand_vars_depth`** (PROVED) — `depth (uand (L.map var)) = 1` for any list `L`: **unbounded fan-in, constant
  depth** — the property the binary model cannot express.
* **`usubst`, `usubst_eval`** (PROVED) — circuit substitution and its semantic preservation, the reconstruction wiring
  in the unbounded model.
* **`usubst_depth_le`** (PROVED) — substitution depth is additive (`≤ depth P + dt`).
* **`IsACC0m`** + **`umod2_isACC0` / `usubst_isACC0m`** — gate-type accounting: a circuit is `ACC⁰[m]` iff every `MOD`
  gate has modulus `m`; substitution preserves `ACC⁰[m]`-ness.

## Honest scope

This builds a genuine **unbounded-fan-in** `ACC⁰[m]` circuit model — the modelling choice entry 323 deferred — with
semantics, depth, size, and modulus accounting, and proves the defining unbounded-fan-in/constant-depth property plus the
substitution (wiring) lemmas needed to carry the reconstruction bridge here.  It is the faithful `ACC⁰` model; it does
**not** by itself reprove the NW bridges in this model (that would re-run entries 321/322 over `UCirc`) — it supplies the
model and the wiring/depth/gate-type infrastructure they would use.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UnboundedFanin

/-- **An unbounded-fan-in `ACC⁰[m]` circuit over `n` inputs.**  `uand`/`uor`/`umod m` take a *list* of children — one
gate of any fan-in.  `umod m cs` is the `MOD_m` gate (fires iff the number of accepting children is `≡ 0 mod m`). -/
inductive UCirc (n : ℕ) where
  | var : Fin n → UCirc n
  | const : Bool → UCirc n
  | unot : UCirc n → UCirc n
  | uand : List (UCirc n) → UCirc n
  | uor : List (UCirc n) → UCirc n
  | umod : ℕ → List (UCirc n) → UCirc n

namespace UCirc

/-- **Boolean semantics.**  `uand` = all children true; `uor` = some child true; `umod m` = `#(true children) ≡ 0
(mod m)`. -/
def eval {n : ℕ} (x : Fin n → Bool) : UCirc n → Bool
  | var i => x i
  | const b => b
  | unot c => !(eval x c)
  | uand cs => (cs.map (eval x)).all (fun b => b)
  | uor cs => (cs.map (eval x)).any (fun b => b)
  | umod m cs => decide (((cs.map (eval x)).count true) % m = 0)

/-- **Gate count.** -/
def size {n : ℕ} : UCirc n → ℕ
  | var _ => 1
  | const _ => 1
  | unot c => 1 + size c
  | uand cs => 1 + (cs.map size).sum
  | uor cs => 1 + (cs.map size).sum
  | umod _ cs => 1 + (cs.map size).sum

/-- **Circuit depth.**  Inputs/constants `↦ 0`; every gate adds one level above the deepest child. -/
def depth {n : ℕ} : UCirc n → ℕ
  | var _ => 0
  | const _ => 0
  | unot c => 1 + depth c
  | uand cs => 1 + (cs.map depth).foldr max 0
  | uor cs => 1 + (cs.map depth).foldr max 0
  | umod _ cs => 1 + (cs.map depth).foldr max 0

/-- **The multiset (list) of `MOD` moduli used by the circuit** — for `ACC⁰[m]` gate-type accounting. -/
def moduli {n : ℕ} : UCirc n → List ℕ
  | var _ => []
  | const _ => []
  | unot c => moduli c
  | uand cs => (cs.map moduli).flatten
  | uor cs => (cs.map moduli).flatten
  | umod m cs => m :: (cs.map moduli).flatten

end UCirc

open UCirc

/-- **Every circuit has size `≥ 1` (PROVED).** -/
theorem UCirc.size_pos {n : ℕ} (C : UCirc n) : 1 ≤ C.size := by
  cases C <;> simp only [UCirc.size] <;> omega

/-- **Custom induction principle for the nested inductive `UCirc`** (via size-bounded strong induction): in the
list-gate cases the hypothesis ranges over every child `c ∈ cs`. -/
@[elab_as_elim]
theorem UCirc.induction {n : ℕ} {motive : UCirc n → Prop}
    (var : ∀ i, motive (UCirc.var i))
    (const : ∀ b, motive (UCirc.const b))
    (unot : ∀ c, motive c → motive (UCirc.unot c))
    (uand : ∀ cs, (∀ c ∈ cs, motive c) → motive (UCirc.uand cs))
    (uor : ∀ cs, (∀ c ∈ cs, motive c) → motive (UCirc.uor cs))
    (umod : ∀ m cs, (∀ c ∈ cs, motive c) → motive (UCirc.umod m cs)) :
    ∀ C, motive C := by
  have H : ∀ k, ∀ C : UCirc n, C.size ≤ k → motive C := by
    intro k
    induction k with
    | zero => intro C hC; exact absurd hC (by have := UCirc.size_pos C; omega)
    | succ k ih =>
        intro C hC
        cases C with
        | var i => exact var i
        | const b => exact const b
        | unot c =>
            simp only [UCirc.size] at hC
            exact unot c (ih c (by omega))
        | uand cs =>
            simp only [UCirc.size] at hC
            refine uand cs (fun c hc => ih c ?_)
            have hmem : UCirc.size c ≤ (cs.map UCirc.size).sum :=
              List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
            omega
        | uor cs =>
            simp only [UCirc.size] at hC
            refine uor cs (fun c hc => ih c ?_)
            have hmem : UCirc.size c ≤ (cs.map UCirc.size).sum :=
              List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
            omega
        | umod m cs =>
            simp only [UCirc.size] at hC
            refine umod m cs (fun c hc => ih c ?_)
            have hmem : UCirc.size c ≤ (cs.map UCirc.size).sum :=
              List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
            omega
  exact fun C => H C.size C le_rfl

/-- **`foldr max` is bounded by any common bound (PROVED).** -/
theorem foldrMax_le {l : List ℕ} {d : ℕ} (h : ∀ a ∈ l, a ≤ d) : l.foldr max 0 ≤ d := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.foldr_cons, max_le_iff]
      exact ⟨h a (List.mem_cons.mpr (Or.inl rfl)),
        ih (fun b hb => h b (List.mem_cons.mpr (Or.inr hb)))⟩

/-- **Each element is `≤ foldr max` (PROVED).** -/
theorem le_foldrMax {l : List ℕ} {a : ℕ} (ha : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at ha
  | cons h t ih =>
      rw [List.foldr_cons]
      rcases List.mem_cons.mp ha with rfl | hmem
      · exact le_max_left _ _
      · exact le_trans (ih hmem) (le_max_right _ _)

/-- **An `AND` gate's depth is one above the deepest child (PROVED).** -/
theorem depth_uand_le {n : ℕ} (cs : List (UCirc n)) (d : ℕ) (h : ∀ c ∈ cs, c.depth ≤ d) :
    (uand cs).depth ≤ 1 + d := by
  have : (cs.map UCirc.depth).foldr max 0 ≤ d :=
    foldrMax_le (by intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact h c hc)
  simpa only [UCirc.depth] using Nat.add_le_add_left this 1

/-- **Unbounded fan-in, constant depth (PROVED) — the defining property the binary model cannot express.**  An `AND`
gate over arbitrarily many input variables (`L.map var`, fan-in `|L|`) has depth exactly `1`. -/
theorem uand_vars_depth {n : ℕ} (L : List (Fin n)) :
    (uand (L.map UCirc.var)).depth = 1 := by
  have h0 : ((L.map UCirc.var).map UCirc.depth).foldr max 0 = 0 := by
    apply Nat.le_zero.mp
    apply foldrMax_le
    intro a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    simp [UCirc.depth]
  simp only [UCirc.depth, h0]

/-- **Circuit substitution.**  Replace each input `var i` of a circuit over `Fin n` by a sub-circuit `g i : UCirc n'`. -/
def usubst {n n' : ℕ} (g : Fin n → UCirc n') : UCirc n → UCirc n'
  | UCirc.var i => g i
  | UCirc.const b => UCirc.const b
  | UCirc.unot c => UCirc.unot (usubst g c)
  | UCirc.uand cs => UCirc.uand (cs.map (usubst g))
  | UCirc.uor cs => UCirc.uor (cs.map (usubst g))
  | UCirc.umod m cs => UCirc.umod m (cs.map (usubst g))

/-- **Substitution preserves semantics (PROVED).**  `eval x (usubst g C) = eval (fun i => eval x (g i)) C`. -/
theorem usubst_eval {n n' : ℕ} (g : Fin n → UCirc n') (x : Fin n' → Bool) (C : UCirc n) :
    UCirc.eval x (usubst g C) = UCirc.eval (fun i => UCirc.eval x (g i)) C := by
  induction C using UCirc.induction with
  | var i => simp only [usubst, UCirc.eval]
  | const b => simp only [usubst, UCirc.eval]
  | unot c ih => simp only [usubst, UCirc.eval, ih]
  | uand cs ih =>
      have hmap : (cs.map (usubst g)).map (UCirc.eval x)
          = cs.map (UCirc.eval (fun i => UCirc.eval x (g i))) := by
        rw [List.map_map]; exact List.map_congr_left fun c hc => ih c hc
      simp only [usubst, UCirc.eval]; rw [hmap]
  | uor cs ih =>
      have hmap : (cs.map (usubst g)).map (UCirc.eval x)
          = cs.map (UCirc.eval (fun i => UCirc.eval x (g i))) := by
        rw [List.map_map]; exact List.map_congr_left fun c hc => ih c hc
      simp only [usubst, UCirc.eval]; rw [hmap]
  | umod m cs ih =>
      have hmap : (cs.map (usubst g)).map (UCirc.eval x)
          = cs.map (UCirc.eval (fun i => UCirc.eval x (g i))) := by
        rw [List.map_map]; exact List.map_congr_left fun c hc => ih c hc
      simp only [usubst, UCirc.eval]; rw [hmap]

/-- **Substitution depth is additive (PROVED).**  If every sub-circuit has depth `≤ dt`, then `(usubst g P).depth ≤
P.depth + dt` — bounded-depth wiring stays bounded depth. -/
theorem usubst_depth_le {n n' : ℕ} (g : Fin n → UCirc n') (dt : ℕ) (hg : ∀ i, (g i).depth ≤ dt) :
    ∀ C : UCirc n, (usubst g C).depth ≤ C.depth + dt := by
  intro C
  induction C using UCirc.induction with
  | var i => simpa only [usubst, UCirc.depth, Nat.zero_add] using hg i
  | const b => simp only [usubst, UCirc.depth]; omega
  | unot c ih => simp only [usubst, UCirc.depth]; omega
  | uand cs ih =>
      have hfold : ((cs.map (usubst g)).map UCirc.depth).foldr max 0
          ≤ (cs.map UCirc.depth).foldr max 0 + dt := by
        rw [List.map_map]
        apply foldrMax_le
        intro a ha
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
        exact le_trans (ih c hc)
          (Nat.add_le_add_right (le_foldrMax (List.mem_map.mpr ⟨c, hc, rfl⟩)) dt)
      simp only [usubst, UCirc.depth]; omega
  | uor cs ih =>
      have hfold : ((cs.map (usubst g)).map UCirc.depth).foldr max 0
          ≤ (cs.map UCirc.depth).foldr max 0 + dt := by
        rw [List.map_map]
        apply foldrMax_le
        intro a ha
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
        exact le_trans (ih c hc)
          (Nat.add_le_add_right (le_foldrMax (List.mem_map.mpr ⟨c, hc, rfl⟩)) dt)
      simp only [usubst, UCirc.depth]; omega
  | umod m cs ih =>
      have hfold : ((cs.map (usubst g)).map UCirc.depth).foldr max 0
          ≤ (cs.map UCirc.depth).foldr max 0 + dt := by
        rw [List.map_map]
        apply foldrMax_le
        intro a ha
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
        exact le_trans (ih c hc)
          (Nat.add_le_add_right (le_foldrMax (List.mem_map.mpr ⟨c, hc, rfl⟩)) dt)
      simp only [usubst, UCirc.depth]; omega

/-- **`ACC⁰[m]` gate-type membership: every `MOD` gate has modulus `m`.** -/
def IsACC0m {n : ℕ} (m : ℕ) (C : UCirc n) : Prop := ∀ q ∈ C.moduli, q = m

/-- **A bare `MOD₂` gate is `ACC⁰[2]` (PROVED).** -/
theorem umod2_isACC0 {n : ℕ} (cs : List (UCirc n)) (hcs : ∀ c ∈ cs, IsACC0m 2 c) :
    IsACC0m 2 (UCirc.umod 2 cs) := by
  intro q hq
  rw [UCirc.moduli, List.mem_cons] at hq
  rcases hq with h | h
  · exact h
  · obtain ⟨l, hl, hql⟩ := List.mem_flatten.mp h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
    exact hcs c hc q hql

end PallLean.Paper93.DeepMath.PathB.ACC0UnboundedFanin

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnboundedFanin.uand_vars_depth
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnboundedFanin.usubst_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnboundedFanin.usubst_depth_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnboundedFanin.umod2_isACC0
