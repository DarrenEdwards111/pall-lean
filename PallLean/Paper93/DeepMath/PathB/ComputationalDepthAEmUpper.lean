import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSlackAll

/-!
# The matching ceiling: `cbudget (AEm m) ≤ 7m − 1` — AEm is LINEAR

The explicit witness circuit: per gadget, three var gates, two equality gates
and one AND (6 gates); gadgets after the first are chained by one more AND
reading the running conjunction (m − 1 gates).  Total `7m − 1`.

* `gadBlock` / `aemExtend` — the block and the append-one-gadget step;
* **`aemExtend_output` (proved)** — one step ANDs one more `allEq3` onto the
  running output (direct `runFrom` computation, reads resolved one append at a
  time — no `append_assoc` rewriting);
* **`aemFold_spec` (proved)** — the fold computes the conjunction;
* **`AEm_upper` (proved)** — `cbudget (AEm m) ≤ 7m − 1`;
* **`AEm_exact` (proved)** — with `slackComposes_all`:
  `cbudget (AEm m) = 7m − 1`.

This closes AEm as a testbed with a LINEAR ceiling: the direct-sum theorem
`slackComposes_all` determines its exact circuit complexity, and no amount of
iteration on this family can reach a superpolynomial bound.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- The 6-gate gadget block at base `b`: vars, two equalities, one AND. -/
def gadBlock {n : ℕ} (i₀ i₁ i₂ : Fin n) (b : ℕ) : List (CGate n) :=
  [CGate.var i₀, CGate.var i₁, CGate.var i₂,
   CGate.bin (fun u v => u == v) b (b + 1),
   CGate.bin (fun u v => u == v) (b + 1) (b + 2),
   CGate.bin (fun u v => u && v) (b + 3) (b + 4)]

/-- Append one gadget block and one chaining AND to a running circuit. -/
def aemExtend {n : ℕ} (c : List (CGate n)) :
    Fin n × Fin n × Fin n → List (CGate n)
  | (i₀, i₁, i₂) =>
      c ++ gadBlock i₀ i₁ i₂ c.length
        ++ [CGate.bin (fun u v => u && v) (c.length - 1) (c.length + 5)]

theorem aemExtend_length {n : ℕ} (c : List (CGate n)) (i₀ i₁ i₂ : Fin n) :
    (aemExtend c (i₀, i₁, i₂)).length = c.length + 7 := by
  simp [aemExtend, gadBlock]

/-- **The step computation (proved)**: one extension ANDs one more gadget. -/
theorem aemExtend_output {n : ℕ} (x : Fin n → Bool) (c : List (CGate n))
    (hc : 0 < c.length) (i₀ i₁ i₂ : Fin n) :
    output (aemExtend c (i₀, i₁, i₂)) x
      = (output c x && allEq3 (x i₀) (x i₁) (x i₂)) := by
  have hL : (runFrom x [] c).length = c.length := by
    rw [runFrom_length]
    simp
  have hL1 : ((runFrom x [] c) ++ [x i₀]).length = c.length + 1 := by
    simp [hL]
  have hL2 : ((runFrom x [] c) ++ [x i₀] ++ [x i₁]).length = c.length + 2 := by
    simp [hL]
  have hL3 : ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]).length
      = c.length + 3 := by simp [hL]
  -- the three var reads
  have hg0 : ((runFrom x [] c) ++ [x i₀]).getD c.length false = x i₀ := by
    have h := getD_concat (runFrom x [] c) (x i₀)
    rwa [hL] at h
  have hg1 : ((runFrom x [] c) ++ [x i₀] ++ [x i₁]).getD (c.length + 1) false
      = x i₁ := by
    have h := getD_concat ((runFrom x [] c) ++ [x i₀]) (x i₁)
    rwa [hL1] at h
  have hg2 : ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]).getD
      (c.length + 2) false = x i₂ := by
    have h := getD_concat ((runFrom x [] c) ++ [x i₀] ++ [x i₁]) (x i₂)
    rwa [hL2] at h
  -- the equality-gate evaluations
  have e4 : evalGate x ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂])
      (CGate.bin (fun u v => u == v) c.length (c.length + 1))
      = (x i₀ == x i₁) := by
    show (((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]).getD c.length false
        == ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]).getD
          (c.length + 1) false) = (x i₀ == x i₁)
    rw [List.getD_append _ _ false c.length (by rw [hL2]; omega),
      List.getD_append _ _ false c.length (by rw [hL1]; omega), hg0,
      List.getD_append _ _ false (c.length + 1) (by rw [hL2]; omega), hg1]
  have e5 : evalGate x ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
        ++ [x i₀ == x i₁])
      (CGate.bin (fun u v => u == v) (c.length + 1) (c.length + 2))
      = (x i₁ == x i₂) := by
    show (((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
        ++ [x i₀ == x i₁]).getD (c.length + 1) false
        == ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
        ++ [x i₀ == x i₁]).getD (c.length + 2) false) = (x i₁ == x i₂)
    rw [List.getD_append _ _ false (c.length + 1) (by rw [hL3]; omega),
      List.getD_append _ _ false (c.length + 1) (by rw [hL2]; omega), hg1,
      List.getD_append _ _ false (c.length + 2) (by rw [hL3]; omega), hg2]
  have hL4 : ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
      ++ [x i₀ == x i₁]).length = c.length + 4 := by simp [hL]
  have hg4 : ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
      ++ [x i₀ == x i₁]).getD (c.length + 3) false = (x i₀ == x i₁) := by
    have h := getD_concat ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂])
      (x i₀ == x i₁)
    rwa [hL3] at h
  have hg5 : ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
      ++ [x i₀ == x i₁] ++ [x i₁ == x i₂]).getD (c.length + 4) false
      = (x i₁ == x i₂) := by
    have h := getD_concat ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
      ++ [x i₀ == x i₁]) (x i₁ == x i₂)
    rwa [hL4] at h
  have e6 : evalGate x ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
        ++ [x i₀ == x i₁] ++ [x i₁ == x i₂])
      (CGate.bin (fun u v => u && v) (c.length + 3) (c.length + 4))
      = ((x i₀ == x i₁) && (x i₁ == x i₂)) := by
    show (((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
        ++ [x i₀ == x i₁] ++ [x i₁ == x i₂]).getD (c.length + 3) false
        && ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
        ++ [x i₀ == x i₁] ++ [x i₁ == x i₂]).getD (c.length + 4) false)
        = ((x i₀ == x i₁) && (x i₁ == x i₂))
    rw [List.getD_append _ _ false (c.length + 3) (by rw [hL4]; omega), hg4, hg5]
  have hL5 : ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
      ++ [x i₀ == x i₁] ++ [x i₁ == x i₂]).length = c.length + 5 := by
    simp [hL]
  -- the chaining AND
  have e7 : evalGate x ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
        ++ [x i₀ == x i₁] ++ [x i₁ == x i₂]
        ++ [(x i₀ == x i₁) && (x i₁ == x i₂)])
      (CGate.bin (fun u v => u && v) (c.length - 1) (c.length + 5))
      = (output c x && ((x i₀ == x i₁) && (x i₁ == x i₂))) := by
    have hprev : ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
        ++ [x i₀ == x i₁] ++ [x i₁ == x i₂]
        ++ [(x i₀ == x i₁) && (x i₁ == x i₂)]).getD (c.length - 1) false
        = output c x := by
      rw [List.getD_append _ _ false (c.length - 1) (by rw [hL5]; omega),
        List.getD_append _ _ false (c.length - 1) (by rw [hL4]; omega),
        List.getD_append _ _ false (c.length - 1) (by rw [hL3]; omega),
        List.getD_append _ _ false (c.length - 1) (by rw [hL2]; omega),
        List.getD_append _ _ false (c.length - 1) (by rw [hL1]; omega),
        List.getD_append _ _ false (c.length - 1) (by rw [hL]; omega)]
      rfl
    have hout : ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
        ++ [x i₀ == x i₁] ++ [x i₁ == x i₂]
        ++ [(x i₀ == x i₁) && (x i₁ == x i₂)]).getD (c.length + 5) false
        = ((x i₀ == x i₁) && (x i₁ == x i₂)) := by
      have h := getD_concat ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
        ++ [x i₀ == x i₁] ++ [x i₁ == x i₂])
        ((x i₀ == x i₁) && (x i₁ == x i₂))
      rwa [hL5] at h
    show (((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
        ++ [x i₀ == x i₁] ++ [x i₁ == x i₂]
        ++ [(x i₀ == x i₁) && (x i₁ == x i₂)]).getD (c.length - 1) false
        && ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
        ++ [x i₀ == x i₁] ++ [x i₁ == x i₂]
        ++ [(x i₀ == x i₁) && (x i₁ == x i₂)]).getD (c.length + 5) false)
        = (output c x && ((x i₀ == x i₁) && (x i₁ == x i₂)))
    rw [hprev, hout]
  have hL6 : ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
      ++ [x i₀ == x i₁] ++ [x i₁ == x i₂]
      ++ [(x i₀ == x i₁) && (x i₁ == x i₂)]).length = c.length + 6 := by
    simp [hL]
  -- assemble the run
  show (runFrom x [] (c ++ gadBlock i₀ i₁ i₂ c.length
      ++ [CGate.bin (fun u v => u && v) (c.length - 1) (c.length + 5)])).getD
      ((c ++ gadBlock i₀ i₁ i₂ c.length
      ++ [CGate.bin (fun u v => u && v) (c.length - 1) (c.length + 5)]).length
        - 1) false
    = (output c x && allEq3 (x i₀) (x i₁) (x i₂))
  have hlen : (c ++ gadBlock i₀ i₁ i₂ c.length
      ++ [CGate.bin (fun u v => u && v) (c.length - 1) (c.length + 5)]).length
      = c.length + 7 := by simp [gadBlock]
  rw [hlen, runFrom_append, runFrom_append]
  have hidx : c.length + 7 - 1 = c.length + 6 := rfl
  rw [hidx]
  have hrun3 : runFrom x (runFrom x [] c) (gadBlock i₀ i₁ i₂ c.length)
      = runFrom x ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂])
        [CGate.bin (fun u v => u == v) c.length (c.length + 1),
         CGate.bin (fun u v => u == v) (c.length + 1) (c.length + 2),
         CGate.bin (fun u v => u && v) (c.length + 3) (c.length + 4)] := rfl
  rw [hrun3]
  simp only [runFrom]
  rw [e4, e5, e6, e7]
  have hfin := getD_concat ((runFrom x [] c) ++ [x i₀] ++ [x i₁] ++ [x i₂]
    ++ [x i₀ == x i₁] ++ [x i₁ == x i₂]
    ++ [(x i₀ == x i₁) && (x i₁ == x i₂)])
    (output c x && ((x i₀ == x i₁) && (x i₁ == x i₂)))
  rw [hL6] at hfin
  rw [hfin]
  rfl

/-- The base block computes its gadget. -/
theorem gadBlock_base_output {n : ℕ} (x : Fin n → Bool) (i₀ i₁ i₂ : Fin n) :
    output (gadBlock i₀ i₁ i₂ 0) x = allEq3 (x i₀) (x i₁) (x i₂) := by
  show (runFrom x [] (gadBlock i₀ i₁ i₂ 0)).getD
    ((gadBlock i₀ i₁ i₂ 0).length - 1) false = allEq3 (x i₀) (x i₁) (x i₂)
  simp only [gadBlock, runFrom, evalGate, List.nil_append, List.length_cons,
    List.length_nil]
  rfl

/-- Bool fold-AND against a list is the conjunction. -/
theorem foldl_and_all {n : ℕ} (x : Fin n → Bool) :
    ∀ (ts : List (Fin n × Fin n × Fin n)) (A : Bool),
      ts.foldl (fun acc t => acc && allEq3 (x t.1) (x t.2.1) (x t.2.2)) A
        = (A && ts.all fun t => allEq3 (x t.1) (x t.2.1) (x t.2.2)) := by
  intro ts
  induction ts with
  | nil => intro A; simp
  | cons t ts ih =>
    intro A
    rw [List.foldl_cons, ih, List.all_cons, Bool.and_assoc]

/-- **The fold spec (proved)**: the fold ANDs every gadget onto the base. -/
theorem aemFold_spec {n : ℕ} (x : Fin n → Bool) :
    ∀ (ts : List (Fin n × Fin n × Fin n)) (c : List (CGate n)),
      0 < c.length →
      (List.foldl aemExtend c ts).length = c.length + 7 * ts.length ∧
      output (List.foldl aemExtend c ts) x
        = (output c x && ts.all fun t => allEq3 (x t.1) (x t.2.1) (x t.2.2)) := by
  intro ts
  induction ts with
  | nil =>
    intro c hc
    refine ⟨by simp, ?_⟩
    simp
  | cons t ts ih =>
    intro c hc
    obtain ⟨i₀, i₁, i₂⟩ := t
    have hlen := aemExtend_length c i₀ i₁ i₂
    have hout := aemExtend_output x c hc i₀ i₁ i₂
    have hpos : 0 < (aemExtend c (i₀, i₁, i₂)).length := by omega
    obtain ⟨ihl, iho⟩ := ih (aemExtend c (i₀, i₁, i₂)) hpos
    constructor
    · rw [List.foldl_cons, ihl, hlen, List.length_cons]
      ring
    · rw [List.foldl_cons, iho, hout, List.all_cons, Bool.and_assoc]

/-- **THE LINEAR CEILING (proved)**: `cbudget (AEm m) ≤ 7m − 1`. -/
theorem AEm_upper (m : ℕ) (hm : 1 ≤ m) : cbudget (AEm m) ≤ 7 * m - 1 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h0 : (0 : ℕ) < 3 * (m' + 1) := by omega
  have h1 : (1 : ℕ) < 3 * (m' + 1) := by omega
  have h2 : (2 : ℕ) < 3 * (m' + 1) := by omega
  -- the index triple of a gadget
  let trip : Fin (m' + 1) → Fin (3 * (m' + 1)) × Fin (3 * (m' + 1)) × Fin (3 * (m' + 1)) :=
    fun j => (⟨3 * j.val, by have := j.isLt; omega⟩,
      ⟨3 * j.val + 1, by have := j.isLt; omega⟩,
      ⟨3 * j.val + 2, by have := j.isLt; omega⟩)
  -- the witness circuit
  refine Nat.sInf_le ⟨List.foldl aemExtend
    (gadBlock ⟨0, h0⟩ ⟨1, h1⟩ ⟨2, h2⟩ 0)
    (((List.finRange m').map Fin.succ).map trip), ?_, ?_⟩
  · -- it computes AEm (m' + 1)
    intro x
    have hbase : 0 < (gadBlock (⟨0, h0⟩ : Fin (3 * (m' + 1))) ⟨1, h1⟩ ⟨2, h2⟩ 0).length := by
      simp [gadBlock]
    obtain ⟨-, hout⟩ := aemFold_spec x
      (((List.finRange m').map Fin.succ).map trip)
      (gadBlock ⟨0, h0⟩ ⟨1, h1⟩ ⟨2, h2⟩ 0) hbase
    rw [hout, gadBlock_base_output]
    show _ = AEm (m' + 1) x
    rw [AEm, List.finRange_succ, List.all_cons, List.all_map, List.all_map,
      List.all_map]
    have he0 : (⟨0, h0⟩ : Fin (3 * (m' + 1)))
        = ⟨3 * ((0 : Fin (m' + 1))).val,
            by have := (0 : Fin (m' + 1)).isLt; omega⟩ :=
      Fin.ext (by simp)
    have he1 : (⟨1, h1⟩ : Fin (3 * (m' + 1)))
        = ⟨3 * ((0 : Fin (m' + 1))).val + 1,
            by have := (0 : Fin (m' + 1)).isLt; omega⟩ :=
      Fin.ext (by simp)
    have he2 : (⟨2, h2⟩ : Fin (3 * (m' + 1)))
        = ⟨3 * ((0 : Fin (m' + 1))).val + 2,
            by have := (0 : Fin (m' + 1)).isLt; omega⟩ :=
      Fin.ext (by simp)
    rw [he0, he1, he2]
    rfl
  · -- it has length 7(m' + 1) − 1
    obtain ⟨hl, -⟩ := aemFold_spec (fun _ => true)
      (((List.finRange m').map Fin.succ).map trip)
      (gadBlock ⟨0, h0⟩ ⟨1, h1⟩ ⟨2, h2⟩ 0) (by simp [gadBlock])
    rw [hl]
    simp [gadBlock]
    omega

/-- **THE EXACT COMPLEXITY (proved)**: `cbudget (AEm m) = 7m − 1` — the AEm
family is LINEAR, and the direct-sum theorem is exactly tight.  AEm is hereby
closed as a testbed: it can never yield a superpolynomial bound. -/
theorem AEm_exact (m : ℕ) (hm : 1 ≤ m) : cbudget (AEm m) = 7 * m - 1 :=
  le_antisymm (AEm_upper m hm) (slackComposes_all m)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.aemExtend_output
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.AEm_upper
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.AEm_exact
