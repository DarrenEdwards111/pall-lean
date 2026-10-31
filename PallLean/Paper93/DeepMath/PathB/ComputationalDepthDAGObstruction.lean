import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKhrMethodCeiling
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDAGWireSurgery

/-!
# The DAG obstruction: composition is LINEAR in the circuit measure

The machine-checked record of why the multiplicative engine had to leave the
DAG measure: block composition with a fixed gadget has a linear `cbudget`
ceiling — compute each gadget copy once, then the outer circuit on the
outputs:

* `relocG`/`topG` — gate relocation (variables re-indexed / replaced by
  wire reads; internal reads shifted);
* **`runFrom_relocG`/`runFrom_topG` (proved)** — a relocated circuit run on
  top of any prefix reproduces its own run, appended;
* **`comp_circuit` (proved)** — `m` gadget copies plus the relocated outer
  circuit compute `f ∘ g^m`;
* **`cbudget_comp_le` (proved)** —
  `cbudget (f ∘ g^m) ≤ m·(cbudget g + 1) + (cbudget f + 1)`.

Iterating a fixed gadget can therefore never produce a superlinear DAG bound:
the multiplicative recurrence lives in the tree measure, by necessity.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor

/-! ### Relocation -/

/-- Relocate a gadget circuit: re-index variables, shift internal reads. -/
def relocG {b N : ℕ} (ρ : Fin b → Fin N) (δ : ℕ) : CGate b → CGate N
  | .var i => .var (ρ i)
  | .cst v => .cst v
  | .un op j => .un op (j + δ)
  | .bin op j k => .bin op (j + δ) (k + δ)

/-- Relocate the outer circuit: variables become wire reads, reads shift. -/
def topG {m N : ℕ} (out : Fin m → ℕ) (δ : ℕ) : CGate m → CGate N
  | .var i => .un (fun v => v) (out i)
  | .cst v => .cst v
  | .un op j => .un op (j + δ)
  | .bin op j k => .bin op (j + δ) (k + δ)

theorem evalGate_relocG {b N : ℕ} (ρ : Fin b → Fin N) (x : Fin N → Bool)
    (V U : List Bool) (g : CGate b) :
    evalGate x (V ++ U) (relocG ρ V.length g)
      = evalGate (fun i => x (ρ i)) U g := by
  cases g with
  | var i => rfl
  | cst v => rfl
  | un op j =>
    have e1 : (V ++ U).getD (j + V.length) false = U.getD j false := by
      rw [List.getD_append_right V U false (j + V.length) (by omega)]
      congr 1
      omega
    show op ((V ++ U).getD (j + V.length) false) = op (U.getD j false)
    rw [e1]
  | bin op j k =>
    have e1 : (V ++ U).getD (j + V.length) false = U.getD j false := by
      rw [List.getD_append_right V U false (j + V.length) (by omega)]
      congr 1
      omega
    have e2 : (V ++ U).getD (k + V.length) false = U.getD k false := by
      rw [List.getD_append_right V U false (k + V.length) (by omega)]
      congr 1
      omega
    show op ((V ++ U).getD (j + V.length) false)
        ((V ++ U).getD (k + V.length) false)
      = op (U.getD j false) (U.getD k false)
    rw [e1, e2]

theorem evalGate_topG {m N : ℕ} (out : Fin m → ℕ) (x : Fin N → Bool)
    (y : Fin m → Bool) (V U : List Bool)
    (hout : ∀ i, V.getD (out i) false = y i)
    (hlt : ∀ i, out i < V.length) (g : CGate m) :
    evalGate x (V ++ U) (topG out V.length g) = evalGate y U g := by
  cases g with
  | var i =>
    show (V ++ U).getD (out i) false = y i
    rw [List.getD_append V U false (out i) (hlt i)]
    exact hout i
  | cst v => rfl
  | un op j =>
    have e1 : (V ++ U).getD (j + V.length) false = U.getD j false := by
      rw [List.getD_append_right V U false (j + V.length) (by omega)]
      congr 1
      omega
    show op ((V ++ U).getD (j + V.length) false) = op (U.getD j false)
    rw [e1]
  | bin op j k =>
    have e1 : (V ++ U).getD (j + V.length) false = U.getD j false := by
      rw [List.getD_append_right V U false (j + V.length) (by omega)]
      congr 1
      omega
    have e2 : (V ++ U).getD (k + V.length) false = U.getD k false := by
      rw [List.getD_append_right V U false (k + V.length) (by omega)]
      congr 1
      omega
    show op ((V ++ U).getD (j + V.length) false)
        ((V ++ U).getD (k + V.length) false)
      = op (U.getD j false) (U.getD k false)
    rw [e1, e2]

/-- **Relocated runs reproduce the original, appended (proved).** -/
theorem runFrom_relocG {b N : ℕ} (ρ : Fin b → Fin N) (x : Fin N → Bool)
    (c : List (CGate b)) :
    ∀ (V U : List Bool), runFrom x (V ++ U) (c.map (relocG ρ V.length))
      = V ++ runFrom (fun i => x (ρ i)) U c := by
  induction c with
  | nil => intro V U; rfl
  | cons g gs ih =>
    intro V U
    show runFrom x ((V ++ U) ++ [evalGate x (V ++ U) (relocG ρ V.length g)])
        (gs.map (relocG ρ V.length))
      = V ++ runFrom (fun i => x (ρ i))
          (U ++ [evalGate (fun i => x (ρ i)) U g]) gs
    rw [evalGate_relocG, List.append_assoc]
    exact ih V (U ++ [evalGate (fun i => x (ρ i)) U g])

/-- **The relocated outer run reads the copy outputs (proved).** -/
theorem runFrom_topG {m N : ℕ} (out : Fin m → ℕ) (x : Fin N → Bool)
    (y : Fin m → Bool) (c : List (CGate m)) :
    ∀ (V U : List Bool), (∀ i, V.getD (out i) false = y i) →
      (∀ i, out i < V.length) →
      runFrom x (V ++ U) (c.map (topG out V.length)) = V ++ runFrom y U c := by
  induction c with
  | nil => intro V U _ _; rfl
  | cons g gs ih =>
    intro V U hout hlt
    show runFrom x ((V ++ U) ++ [evalGate x (V ++ U) (topG out V.length g)])
        (gs.map (topG out V.length))
      = V ++ runFrom y (U ++ [evalGate y U g]) gs
    rw [evalGate_topG out x y V U hout hlt, List.append_assoc]
    exact ih V (U ++ [evalGate y U g]) hout hlt

/-! ### The copies -/

/-- The block-variable map of copy `k` (junk beyond `m`, never used). -/
def blockRho {m b : ℕ} (hm : 0 < m) (hb : 0 < b) (k : ℕ) :
    Fin b → Fin (m * b) :=
  if h : k < m then emb hb ⟨k, h⟩ else emb hb ⟨0, hm⟩

/-- The first `k` relocated gadget copies. -/
def gCopies {m b : ℕ} (hm : 0 < m) (hb : 0 < b) (cg : List (CGate b)) :
    ℕ → List (CGate (m * b))
  | 0 => []
  | k + 1 => gCopies hm hb cg k
      ++ (cg.map (relocG (blockRho hm hb k) (k * cg.length)))

theorem gCopies_length {m b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (cg : List (CGate b)) : ∀ k, (gCopies hm hb cg k).length = k * cg.length := by
  intro k
  induction k with
  | zero => simp [gCopies]
  | succ k ih =>
    show (gCopies hm hb cg k
        ++ cg.map (relocG (blockRho hm hb k) (k * cg.length))).length = _
    rw [List.length_append, ih, List.length_map]
    have e : (k + 1) * cg.length = k * cg.length + cg.length := by ring
    omega

/-- **The copies compute the gadget on each block (proved).** -/
theorem gCopies_run {m b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (cg : List (CGate b)) (hLg : 0 < cg.length) (x : Fin (m * b) → Bool) :
    ∀ k, (runFrom x [] (gCopies hm hb cg k)).length = k * cg.length
      ∧ ∀ j, j < k →
        (runFrom x [] (gCopies hm hb cg k)).getD
            (j * cg.length + (cg.length - 1)) false
          = output cg (fun i => x (blockRho hm hb j i)) := by
  intro k
  induction k with
  | zero =>
    constructor
    · simp [gCopies, runFrom]
    · intro j hj
      exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    obtain ⟨ihl, ihv⟩ := ih
    have hrun : runFrom x [] (gCopies hm hb cg (k + 1))
        = runFrom x [] (gCopies hm hb cg k)
          ++ runFrom (fun i => x (blockRho hm hb k i)) [] cg := by
      show runFrom x [] (gCopies hm hb cg k
          ++ cg.map (relocG (blockRho hm hb k) (k * cg.length))) = _
      rw [runFrom_append, ← ihl]
      have h := runFrom_relocG (blockRho hm hb k) x cg
        (runFrom x [] (gCopies hm hb cg k)) []
      rw [List.append_nil] at h
      exact h
    constructor
    · rw [hrun, List.length_append, ihl, CbudgetConeBound.runFrom_length]
      have e : (k + 1) * cg.length = k * cg.length + cg.length := by ring
      simp only [List.length_nil]
      omega
    · intro j hj
      rw [hrun]
      by_cases hjk : j < k
      · rw [List.getD_append _ _ false _ (by
          rw [ihl]
          have h1 : (j + 1) * cg.length ≤ k * cg.length :=
            Nat.mul_le_mul_right cg.length hjk
          have h2 : (j + 1) * cg.length = j * cg.length + cg.length := by ring
          omega)]
        exact ihv j hjk
      · have hjeq : j = k := by omega
        subst hjeq
        rw [List.getD_append_right _ _ false _ (by rw [ihl]; omega)]
        rw [ihl]
        have e : j * cg.length + (cg.length - 1) - j * cg.length
            = cg.length - 1 := by omega
        rw [e]
        rfl

/-! ### The assembly -/

/-- **The composed circuit computes `f ∘ g^m` (proved).** -/
theorem comp_circuit {m b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (f : (Fin m → Bool) → Bool) (g : (Fin b → Bool) → Bool)
    (cg : List (CGate b)) (cf : List (CGate m))
    (hgc : computes cg g) (hfc : computes cf f)
    (hLg : 0 < cg.length) (hLf : 0 < cf.length) :
    computes (gCopies hm hb cg m
        ++ cf.map (topG (fun i : Fin m => i.val * cg.length + (cg.length - 1))
          (m * cg.length)))
      (comp hb f g) := by
  intro x
  obtain ⟨hVl, hVv⟩ := gCopies_run hm hb cg hLg x m
  have hout : ∀ i : Fin m,
      (runFrom x [] (gCopies hm hb cg m)).getD
          (i.val * cg.length + (cg.length - 1)) false
        = (fun j : Fin m => g (fun i' => x (emb hb j i'))) i := by
    intro i
    have h1 := hVv i.val i.isLt
    rw [h1, hgc]
    show g (fun i' => x (blockRho hm hb i.val i'))
      = g (fun i' => x (emb hb i i'))
    congr 1
    funext i'
    congr 1
    show blockRho hm hb i.val i' = emb hb i i'
    rw [blockRho, dif_pos i.isLt, Fin.eta]
  have hlt : ∀ i : Fin m, i.val * cg.length + (cg.length - 1)
      < (runFrom x [] (gCopies hm hb cg m)).length := by
    intro i
    rw [hVl]
    have h1 : (i.val + 1) * cg.length ≤ m * cg.length :=
      Nat.mul_le_mul_right cg.length i.isLt
    have h2 : (i.val + 1) * cg.length = i.val * cg.length + cg.length := by ring
    omega
  have htop := runFrom_topG
    (fun i : Fin m => i.val * cg.length + (cg.length - 1)) x
    (fun j : Fin m => g (fun i' => x (emb hb j i'))) cf
    (runFrom x [] (gCopies hm hb cg m)) [] hout hlt
  rw [List.append_nil] at htop
  show (runFrom x [] (gCopies hm hb cg m
      ++ cf.map (topG (fun i : Fin m => i.val * cg.length + (cg.length - 1))
        (m * cg.length)))).getD
      ((gCopies hm hb cg m
      ++ cf.map (topG (fun i : Fin m => i.val * cg.length + (cg.length - 1))
        (m * cg.length))).length - 1) false
    = comp hb f g x
  rw [runFrom_append, List.length_append, gCopies_length, List.length_map,
    ← hVl, htop]
  rw [List.getD_append_right _ _ false _ (by omega)]
  have e : (runFrom x [] (gCopies hm hb cg m)).length + cf.length - 1
      - (runFrom x [] (gCopies hm hb cg m)).length = cf.length - 1 := by
    omega
  rw [e]
  have hfin : (runFrom (fun j : Fin m => g (fun i' => x (emb hb j i'))) [] cf).getD
      (cf.length - 1) false
      = f (fun j : Fin m => g (fun i' => x (emb hb j i'))) :=
    hfc (fun j : Fin m => g (fun i' => x (emb hb j i')))
  rw [hfin]
  rfl

/-- **THE DAG OBSTRUCTION (proved)**: block composition is LINEAR in the
circuit measure — the multiplicative engine cannot live in `cbudget`. -/
theorem cbudget_comp_le {m b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (f : (Fin m → Bool) → Bool) (g : (Fin b → Bool) → Bool) :
    cbudget (comp hb f g) ≤ m * (cbudget g + 1) + (cbudget f + 1) := by
  classical
  obtain ⟨cg, hgc, hgl⟩ := Nat.sInf_mem (cbudget_set_nonempty g)
  obtain ⟨cf, hfc, hfl⟩ := Nat.sInf_mem (cbudget_set_nonempty f)
  have hgl' : cg.length = cbudget g := hgl
  have hfl' : cf.length = cbudget f := hfl
  have hpadg : ∃ cg', computes cg' g ∧ 0 < cg'.length
      ∧ cg'.length ≤ cbudget g + 1 := by
    by_cases h0 : cg.length = 0
    · refine ⟨[CGate.cst false], ?_, by simp,
        by simp only [List.length_singleton]; omega⟩
      intro x
      have h1 := hgc x
      have hce : cg = [] := List.eq_nil_of_length_eq_zero h0
      rw [hce] at h1
      have h3 : output [CGate.cst false] x = false := rfl
      have h2 : output ([] : List (CGate b)) x = false := rfl
      rw [h3, ← h2]
      exact h1
    · exact ⟨cg, hgc, by omega, by omega⟩
  have hpadf : ∃ cf', computes cf' f ∧ 0 < cf'.length
      ∧ cf'.length ≤ cbudget f + 1 := by
    by_cases h0 : cf.length = 0
    · refine ⟨[CGate.cst false], ?_, by simp,
        by simp only [List.length_singleton]; omega⟩
      intro x
      have h1 := hfc x
      have hce : cf = [] := List.eq_nil_of_length_eq_zero h0
      rw [hce] at h1
      have h3 : output [CGate.cst false] x = false := rfl
      have h2 : output ([] : List (CGate m)) x = false := rfl
      rw [h3, ← h2]
      exact h1
    · exact ⟨cf, hfc, by omega, by omega⟩
  obtain ⟨cg', hgc', hLg, hgle⟩ := hpadg
  obtain ⟨cf', hfc', hLf, hfle⟩ := hpadf
  have hcomp := comp_circuit hm hb f g cg' cf' hgc' hfc' hLg hLf
  have hlen : (gCopies hm hb cg' m
      ++ cf'.map (topG (fun i : Fin m => i.val * cg'.length + (cg'.length - 1))
        (m * cg'.length))).length = m * cg'.length + cf'.length := by
    rw [List.length_append, gCopies_length, List.length_map]
  have hin : cbudget (comp hb f g) ≤ m * cg'.length + cf'.length :=
    Nat.sInf_le ⟨_, hcomp, hlen⟩
  have hmono : m * cg'.length ≤ m * (cbudget g + 1) :=
    Nat.mul_le_mul_left m hgle
  omega

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.comp_circuit
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.cbudget_comp_le
