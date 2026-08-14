import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTwelveGateShape

/-!
# Three-bit majority lies above the dependency-cone floor

The external exact-synthesis search finds that three-bit majority needs four
binary gates.  This file certifies the first nontrivial part of that result
without circuit enumeration or `native_decide`: the read-once-tree extraction
theorem excludes every five-gate implementation.  A concrete seven-gate
implementation leaves the kernel-certified frontier `6 ≤ cbudget ≤ 7`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound

/-- Three-bit majority, in a form with a verified seven-gate circuit. -/
def majorityThreeFloor (x : Fin 3 → Bool) : Bool :=
  (x 0 && x 1) || (x 2 && (x 0 || x 1))

/-- All three input coordinates are essential. -/
theorem majorityThreeFloor_depSet :
    depSet majorityThreeFloor = (Finset.univ : Finset (Fin 3)) := by
  rw [Finset.eq_univ_iff_forall]
  intro i
  fin_cases i
  · exact mem_depSet.mpr ⟨![false, true, false], true, by decide⟩
  · exact mem_depSet.mpr ⟨![true, false, false], true, by decide⟩
  · exact mem_depSet.mpr ⟨![true, false, false], true, by decide⟩

theorem majorityThreeFloor_no_split_one :
    ¬ ∃ op g : Bool → Bool → Bool,
      ∀ a b c, majorityThreeFloor ![a, b, c] = op a (g b c) := by
  decide

theorem majorityThreeFloor_no_split_two :
    ¬ ∃ op g : Bool → Bool → Bool,
      ∀ a b c, majorityThreeFloor ![a, b, c] = op b (g a c) := by
  decide

theorem majorityThreeFloor_no_split_three :
    ¬ ∃ op g : Bool → Bool → Bool,
      ∀ a b c, majorityThreeFloor ![a, b, c] = op c (g a b) := by
  decide

/-- Majority's full three-coordinate restriction is unsplittable, so the
read-once-tree floor theorem adds one gate beyond the cone bound. -/
theorem majorityThreeFloor_cbudget_lower :
    6 ≤ cbudget majorityThreeFloor := by
  apply cbudget_above_floor_of_unsplittable majorityThreeFloor
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide) (by decide)
      (fun _ => false)
  · simpa [Split1, Function.update, Fin.cases] using majorityThreeFloor_no_split_one
  · simpa [Split2, Function.update, Fin.cases] using majorityThreeFloor_no_split_two
  · simpa [Split3, Function.update, Fin.cases] using majorityThreeFloor_no_split_three

/-- A seven-gate implementation of three-bit majority. -/
def majorityThreeFloorCircuit : List (CGate 3) :=
  [CGate.var ⟨0, by omega⟩,
   CGate.var ⟨1, by omega⟩,
   CGate.var ⟨2, by omega⟩,
   CGate.bin (fun a b => a && b) 0 1,
   CGate.bin (fun a b => a || b) 0 1,
   CGate.bin (fun a b => a && b) 2 4,
   CGate.bin (fun a b => a || b) 3 5]

theorem majorityThreeFloorCircuit_computes :
    computes majorityThreeFloorCircuit majorityThreeFloor := by
  intro x
  have hx : x = ![x 0, x 1, x 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> decide

theorem majorityThreeFloor_cbudget_upper :
    cbudget majorityThreeFloor ≤ 7 := by
  have h : cbudget majorityThreeFloor ≤ majorityThreeFloorCircuit.length :=
    Nat.sInf_le ⟨majorityThreeFloorCircuit, majorityThreeFloorCircuit_computes, rfl⟩
  simpa [majorityThreeFloorCircuit] using h

/-- Kernel-certified exact-synthesis frontier.  Only six-gate circuits remain
to exclude before the external exact value `7` is fully internalized. -/
theorem majorityThreeFloor_cbudget_frontier :
    6 ≤ cbudget majorityThreeFloor ∧ cbudget majorityThreeFloor ≤ 7 :=
  ⟨majorityThreeFloor_cbudget_lower, majorityThreeFloor_cbudget_upper⟩

/-! ### Six-gate normal form

The last finite gap cannot be closed by asking the kernel to reduce all labelled
programs at once: that term is unnecessarily enormous.  Instead we first use
the circuit surgeries to force a six-gate implementation into the genuine
`var`/`bin` basis. -/

theorem majorityThreeFloor_not_constant (b : Bool)
    (h : ∀ x, majorityThreeFloor x = b) : False := by
  have h0 : (0 : Fin 3) ∈ depSet majorityThreeFloor := by
    rw [majorityThreeFloor_depSet]
    exact Finset.mem_univ _
  obtain ⟨x, v, hx⟩ := mem_depSet.mp h0
  exact hx (by rw [h, h])

theorem majorityThreeFloor_not_depSet :
    depSet (fun x => !(majorityThreeFloor x)) = (Finset.univ : Finset (Fin 3)) := by
  rw [depSet_not, majorityThreeFloor_depSet]

theorem majorityThreeFloor_not_cbudget_lower :
    6 ≤ cbudget (fun x => !(majorityThreeFloor x)) := by
  apply cbudget_above_floor_of_unsplittable (fun x => !(majorityThreeFloor x))
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide) (by decide)
      (fun _ => false)
  · intro hs
    exact majorityThreeFloor_no_split_one (split1_of_not hs)
  · intro hs
    exact majorityThreeFloor_no_split_two (split2_of_not hs)
  · intro hs
    exact majorityThreeFloor_no_split_three (split3_of_not hs)

/-- A six-gate majority circuit has no constant gate, including at the root. -/
theorem majoritySix_no_cst_mid (c₁ c₂ : List (CGate 3)) (b : Bool)
    (hcomp : computes (c₁ ++ CGate.cst b :: c₂) majorityThreeFloor)
    (hlen : c₁.length + c₂.length + 1 = 6) : False := by
  have hcb := majorityThreeFloor_cbudget_lower
  cases c₂ with
  | cons g rest =>
    have hle := cbudget_le_of_cst_mid c₁ (g :: rest) b majorityThreeFloor hcomp (by simp)
    simp only [List.length_cons] at hle hlen
    omega
  | nil =>
    refine majorityThreeFloor_not_constant b (fun x => ?_)
    have hx := hcomp x
    have hVlen : (runFrom x [] c₁).length = c₁.length := by
      rw [runFrom_length]
      simp
    rw [← hx]
    show (runFrom x [] (c₁ ++ [CGate.cst b])).getD
      ((c₁ ++ [CGate.cst b]).length - 1) false = b
    rw [runFrom_append]
    show ((runFrom x [] c₁) ++ [evalGate x (runFrom x [] c₁) (CGate.cst b)]).getD
      ((c₁ ++ [CGate.cst b]).length - 1) false = b
    have hidx : (c₁ ++ [CGate.cst b]).length - 1 = (runFrom x [] c₁).length := by
      rw [hVlen]
      simp
    rw [hidx, getD_concat]
    rfl

/-- A six-gate majority circuit has no unary gate.  At the root, the unary
truth-table trichotomy would give a circuit of at most five gates for majority,
its complement, or a constant. -/
theorem majoritySix_no_un_mid (c₁ c₂ : List (CGate 3)) (op : Bool → Bool) (q : ℕ)
    (hcomp : computes (c₁ ++ CGate.un op q :: c₂) majorityThreeFloor)
    (hlen : c₁.length + c₂.length + 1 = 6) : False := by
  have hcb := majorityThreeFloor_cbudget_lower
  have hncb := majorityThreeFloor_not_cbudget_lower
  cases c₂ with
  | cons g rest =>
    have hle := cbudget_le_of_un_mid c₁ (g :: rest) op q majorityThreeFloor hcomp (by simp)
    simp only [List.length_cons] at hle hlen
    omega
  | nil =>
    have hc₁len : c₁.length = 5 := by simpa using hlen
    have hval : ∀ x, majorityThreeFloor x = op ((runFrom x [] c₁).getD q false) := by
      intro x
      have hx := hcomp x
      rw [← hx]
      show (runFrom x [] (c₁ ++ [CGate.un op q])).getD
        ((c₁ ++ [CGate.un op q]).length - 1) false
        = op ((runFrom x [] c₁).getD q false)
      rw [runFrom_append]
      show ((runFrom x [] c₁) ++ [evalGate x (runFrom x [] c₁) (CGate.un op q)]).getD
        ((c₁ ++ [CGate.un op q]).length - 1) false
        = op ((runFrom x [] c₁).getD q false)
      have hV : (runFrom x [] c₁).length = c₁.length := by
        rw [runFrom_length]
        simp
      have hi : (c₁ ++ [CGate.un op q]).length - 1 = (runFrom x [] c₁).length := by
        rw [hV]
        simp
      rw [hi, getD_concat]
      rfl
    by_cases hq : q < c₁.length
    · have htake : ∀ x, output (c₁.take (q + 1)) x =
          (runFrom x [] c₁).getD q false := by
        intro x
        unfold output
        have ht : (c₁.take (q + 1)).length = q + 1 := by
          rw [List.length_take]
          omega
        rw [ht]
        exact wire_prefix c₁ x (by omega) (by omega)
      have htlen : (c₁.take (q + 1)).length = q + 1 := by
        rw [List.length_take]
        omega
      rcases unary_shape op with hop | hop | hop
      · exact majorityThreeFloor_not_constant (op false) (fun x => by rw [hval x, hop])
      · have hc : computes (c₁.take (q + 1)) majorityThreeFloor := by
          intro x
          rw [htake x, ← hop ((runFrom x [] c₁).getD q false), ← hval x]
        have hle : cbudget majorityThreeFloor ≤ q + 1 :=
          le_trans (Nat.sInf_le ⟨_, hc, rfl⟩) (le_of_eq htlen)
        omega
      · have hc : computes (c₁.take (q + 1)) (fun x => !(majorityThreeFloor x)) := by
          intro x
          rw [htake x]
          show (runFrom x [] c₁).getD q false = !(majorityThreeFloor x)
          rw [hval x, hop, Bool.not_not]
        have hle : cbudget (fun x => !(majorityThreeFloor x)) ≤ q + 1 :=
          le_trans (Nat.sInf_le ⟨_, hc, rfl⟩) (le_of_eq htlen)
        omega
    · exact majorityThreeFloor_not_constant (op false) (fun x => by
        rw [hval x]
        have hV : (runFrom x [] c₁).length = c₁.length := by
          rw [runFrom_length]
          simp
        rw [List.getD_eq_default _ _ (by omega)])

/-- Every binary gate in a six-gate majority circuit reads two distinct earlier
wires.  Any garbage or repeated read is extensionally a unary gate. -/
theorem majoritySix_bins_genuine (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6)
    (p : ℕ) (hp : p < 6) (op : Bool → Bool → Bool) (j k : ℕ)
    (hg : c.getD p (.cst false) = CGate.bin op j k) :
    j < p ∧ k < p ∧ j ≠ k := by
  have hs := split_at_getD c (show p < c.length by omega)
  rw [hg] at hs
  have hc := hcomp
  rw [hs] at hc
  have ht : (c.take p).length = p := by rw [List.length_take]; omega
  have hd : (c.drop (p + 1)).length = c.length - (p + 1) := List.length_drop
  have hlen' : (c.take p).length + (c.drop (p + 1)).length + 1 = 6 := by omega
  by_cases hk : k < p
  · by_cases hj : j < p
    · refine ⟨hj, hk, ?_⟩
      intro he
      subst he
      have hswap := computes_swap_mid (c.take p) (c.drop (p + 1))
        (CGate.bin op j j) (CGate.un (fun v => op v v) j) majorityThreeFloor hc
        (fun _ _ _ => rfl)
      exact majoritySix_no_un_mid _ _ _ _ hswap hlen'
    · exfalso
      have hswap := computes_swap_mid (c.take p) (c.drop (p + 1))
        (CGate.bin op j k) (CGate.un (fun v => op false v) k) majorityThreeFloor hc
        (fun _ vals hv => by
          have hj0 : vals.getD j false = false := List.getD_eq_default _ _ (by omega)
          show (fun v => op false v) (vals.getD k false) =
            op (vals.getD j false) (vals.getD k false)
          rw [hj0])
      exact majoritySix_no_un_mid _ _ _ _ hswap hlen'
  · exfalso
    have hswap := computes_swap_mid (c.take p) (c.drop (p + 1))
      (CGate.bin op j k) (CGate.un (fun v => op v false) j) majorityThreeFloor hc
      (fun _ vals hv => by
        have hk0 : vals.getD k false = false := List.getD_eq_default _ _ (by omega)
        show (fun v => op v false) (vals.getD j false) =
          op (vals.getD j false) (vals.getD k false)
        rw [hk0])
    exact majoritySix_no_un_mid _ _ _ _ hswap hlen'

theorem majoritySix_gate_dichotomy (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6)
    (p : ℕ) (hp : p < 6) :
    (∃ i : Fin 3, c.getD p (.cst false) = CGate.var i) ∨
    ∃ op j k, c.getD p (.cst false) = CGate.bin op j k ∧
      j < p ∧ k < p ∧ j ≠ k := by
  cases hg : c.getD p (.cst false) with
  | var i => exact Or.inl ⟨i, rfl⟩
  | cst b =>
    have hs := split_at_getD c (show p < c.length by omega)
    rw [hg] at hs
    rw [hs] at hcomp
    exfalso
    apply majoritySix_no_cst_mid (c.take p) (c.drop (p + 1)) b hcomp
    rw [List.length_take, List.length_drop]
    omega
  | un op q =>
    have hs := split_at_getD c (show p < c.length by omega)
    rw [hg] at hs
    rw [hs] at hcomp
    exfalso
    apply majoritySix_no_un_mid (c.take p) (c.drop (p + 1)) op q hcomp
    rw [List.length_take, List.length_drop]
    omega
  | bin op j k =>
    obtain ⟨hj, hk, hjk⟩ := majoritySix_bins_genuine c hcomp hlen p hp op j k hg
    exact Or.inr ⟨op, j, k, rfl, hj, hk, hjk⟩

theorem majoritySix_minimal (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6) :
    c.length = cbudget majorityThreeFloor := by
  have hle : cbudget majorityThreeFloor ≤ c.length := Nat.sInf_le ⟨c, hcomp, rfl⟩
  have hlo := majorityThreeFloor_cbudget_lower
  omega

theorem majoritySix_cone_all (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6) :
    cone c = Finset.range 6 := by
  have hlo := cone_lb_of_unsplittable majorityThreeFloor
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide) (by decide)
      (fun _ => false)
      (by simpa [Split1, Function.update, Fin.cases] using majorityThreeFloor_no_split_one)
      (by simpa [Split2, Function.update, Fin.cases] using majorityThreeFloor_no_split_two)
      (by simpa [Split3, Function.update, Fin.cases] using majorityThreeFloor_no_split_three)
      hcomp (by omega)
  have hsub : cone c ⊆ Finset.range 6 := by
    intro p hp
    rw [Finset.mem_range]
    have := (mem_cone.mp hp).1
    omega
  apply Finset.eq_of_subset_of_card_le hsub
  rw [majorityThreeFloor_depSet, Finset.card_univ, Fintype.card_fin] at hlo
  simpa using hlo

theorem majoritySix_varsEq (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6) :
    (coneVars c).card = (depSet majorityThreeFloor).card := by
  have hs : 0 < c.length := by omega
  have hlo := depSet_card_le_coneVars majorityThreeFloor c hcomp hs
  have hhi := cone_counting c hs
  rw [majorityThreeFloor_depSet, Finset.card_univ, Fintype.card_fin] at hlo ⊢
  omega

theorem majoritySix_var_inj (c : List (CGate 3))
    (hcomp : computes c majorityThreeFloor) (hlen : c.length = 6)
    {w₁ w₂ : ℕ} {i : Fin 3} (h₁ : w₁ < 6) (h₂ : w₂ < 6)
    (hg₁ : c.getD w₁ (.cst false) = CGate.var i)
    (hg₂ : c.getD w₂ (.cst false) = CGate.var i) : w₁ = w₂ := by
  apply var_injective_of_varsEq majorityThreeFloor c hcomp (by omega)
      (majoritySix_varsEq c hcomp hlen)
  · rw [majoritySix_cone_all c hcomp hlen, Finset.mem_range]
    exact h₁
  · rw [majoritySix_cone_all c hcomp hlen, Finset.mem_range]
    exact h₂
  · exact hg₁
  · exact hg₂

/-! ### Kernel classification of three-binary-gate programs

To keep the finite check independent of dependent circuit syntax, binary
operations are encoded by their four-row truth tables (`Fin 16`) and each
source is an index into the inputs and already-computed gates. -/

def codedBin (op : Fin 16) (a b : Bool) : Bool :=
  (op.val.testBit (2 * a.toNat + b.toNat))

def sourceThree (x : Fin 3 → Bool) (i : Fin 3) : Bool := x i

def sourceFour (x : Fin 3 → Bool) (g₁ : Bool) (i : Fin 4) : Bool :=
  if h : i.val < 3 then x ⟨i.val, h⟩ else g₁

def sourceFive (x : Fin 3 → Bool) (g₁ g₂ : Bool) (i : Fin 5) : Bool :=
  if h : i.val < 3 then x ⟨i.val, h⟩ else if i.val = 3 then g₁ else g₂

def threeBinaryProgram
    (op₁ op₂ op₃ : Fin 16) (a₁ b₁ : Fin 3) (a₂ b₂ : Fin 4)
    (a₃ b₃ : Fin 5) (x : Fin 3 → Bool) : Bool :=
  let g₁ := codedBin op₁ (sourceThree x a₁) (sourceThree x b₁)
  let g₂ := codedBin op₂ (sourceFour x g₁ a₂) (sourceFour x g₁ b₂)
  codedBin op₃ (sourceFive x g₁ g₂ a₃) (sourceFive x g₁ g₂ b₃)

/-- The parallel topology computes two functions of input pairs and combines
them at the root. -/
def parallelThreeBinaryProgram
    (op₁ op₂ op₃ : Fin 16) (a₁ b₁ a₂ b₂ : Fin 3)
    (x : Fin 3 → Bool) : Bool :=
  codedBin op₃
    (codedBin op₁ (x a₁) (x b₁))
    (codedBin op₂ (x a₂) (x b₂))

/-- The live chain topology: the first result enters the second gate, whose
result enters the root; the other root input is either a primary input or the
first result.  Operand orientations lose no generality because operations range
over all sixteen truth tables. -/
def chainThreeBinaryProgram
    (op₁ op₂ op₃ : Fin 16) (a₁ b₁ c : Fin 3) (d : Fin 4)
    (x : Fin 3 → Bool) : Bool :=
  let g₁ := codedBin op₁ (x a₁) (x b₁)
  let g₂ := codedBin op₂ g₁ (x c)
  codedBin op₃ g₂ (sourceFour x g₁ d)

-- After liveness and bidependence, the parallel topology has a unique wiring
-- up to permuting variables and reversing operands: two distinct input pairs
-- sharing one coordinate.
theorem parallelCanonical_ne_majority :
    ¬ ∃ (op₁ op₂ op₃ : Fin 16),
      ∀ x : Fin 3 → Bool,
        parallelThreeBinaryProgram op₁ op₂ op₃ 0 1 0 2 x = majorityThreeFloor x := by
  decide

-- In the live chain, the first pair is combined with the third variable.  The
-- root's remaining live source is, up to the pair symmetry, one of the first
-- result, a member of the pair, or the third variable.
set_option maxRecDepth 100000 in
theorem chainCanonical_firstResult_ne_majority :
    ¬ ∃ (op₁ op₂ op₃ : Fin 16),
      ∀ x : Fin 3 → Bool,
        chainThreeBinaryProgram op₁ op₂ op₃ 0 1 2 3 x = majorityThreeFloor x := by
  decide

set_option maxRecDepth 100000 in
theorem chainCanonical_pairInput_ne_majority :
    ¬ ∃ (op₁ op₂ op₃ : Fin 16),
      ∀ x : Fin 3 → Bool,
        chainThreeBinaryProgram op₁ op₂ op₃ 0 1 2 0 x = majorityThreeFloor x := by
  decide

set_option maxRecDepth 100000 in
theorem chainCanonical_thirdInput_ne_majority :
    ¬ ∃ (op₁ op₂ op₃ : Fin 16),
      ∀ x : Fin 3 → Bool,
        chainThreeBinaryProgram op₁ op₂ op₃ 0 1 2 2 x = majorityThreeFloor x := by
  decide

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.majorityThreeFloor_cbudget_lower
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.majorityThreeFloor_cbudget_upper
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.majorityThreeFloor_cbudget_frontier
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.parallelCanonical_ne_majority
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.chainCanonical_firstResult_ne_majority
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.chainCanonical_pairInput_ne_majority
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.chainCanonical_thirdInput_ne_majority
