import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkDAGBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer10BarrierLandscape
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDAGObstruction

/-!
# A sharing-sensitive MCSP surface

The raw shrinkage-to-DAG bridge loses exponentially and is therefore capped at
a linear general-circuit lower bound.  The correct magnification object puts
the DAG measure *inside* the Boolean predicate: a truth table is accepted when
its represented function has small `cbudget`.  An outer De Morgan lower bound
for this predicate is then a lower bound for a metacomplexity problem, not a
generic attempt to unfold the target circuit.

This file builds the first concrete, non-circular substrate:

* `circuitMCSP` is the actual truth-table minimum-circuit-size predicate for
  the repository's full-basis DAG model;
* `cbudget_update_le` proves a sharing-aware local repair theorem: changing one
  truth-table entry costs at most `3n+3` DAG gates, by tapping the old circuit,
  computing equality with the changed input, and patching the output;
* `circuitMCSP_stable_below` / `circuitMCSP_stable_above` show that one-bit
  truth-table restrictions are constant away from the `O(n)` threshold band;
* `circuitMCSP_boundary_edge_band` isolates every YES-to-NO Hamming edge in
  that band, and `circuitMCSP_khrapchenko` turns their count into the exact
  outer De Morgan lower-bound target.

This is genuine MCSP structure and preserves sharing.  It is not yet the
hardness-magnification theorem: the remaining lower bound must exploit the
population of truth tables in the narrow threshold band.  Nothing here proves
`P != NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SharingSensitiveMCSP

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ## Equality to one input, with linear circuit cost -/

def eqTreeOn {n : ℕ} (a : Fin n → Bool) : List (Fin n) → Trans n
  | [] => .cst true
  | i :: is =>
      .bin (· && ·) (.un (fun b => b == a i) (.var i)) (eqTreeOn a is)

def eqTree {n : ℕ} (a : Fin n → Bool) : Trans n :=
  eqTreeOn a (List.finRange n)

theorem eqTreeOn_eval {n : ℕ} (a x : Fin n → Bool) (is : List (Fin n)) :
    eval (eqTreeOn a is) x = is.all (fun i => x i == a i) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [eqTreeOn, eval, ih]

theorem eqTree_eval_true_iff {n : ℕ} (a x : Fin n → Bool) :
    eval (eqTree a) x = true ↔ x = a := by
  rw [eqTree, eqTreeOn_eval, List.all_eq_true]
  constructor
  · intro h
    funext i
    exact beq_iff_eq.mp (h i (List.mem_finRange i))
  · rintro rfl i _
    simp

theorem eqTreeOn_volume {n : ℕ} (a : Fin n → Bool) (is : List (Fin n)) :
    volume (eqTreeOn a is) = 3 * is.length + 1 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [eqTreeOn, volume, ih, List.length_cons]
    omega

theorem eqTree_volume {n : ℕ} (a : Fin n → Bool) :
    volume (eqTree a) = 3 * n + 1 := by
  rw [eqTree, eqTreeOn_volume, List.length_finRange]

/-! ## Tap any circuit, including the empty false circuit -/

/-- Append an identity gate reading the old output.  This makes the circuit
nonempty without changing its function; for an empty circuit the default old
output is `false`, exactly matching `output []`. -/
def tapC {n : ℕ} (c : List (CGate n)) : List (CGate n) :=
  c ++ [.un id (c.length - 1)]

@[simp] theorem tapC_length {n : ℕ} (c : List (CGate n)) :
    (tapC c).length = c.length + 1 := by
  simp [tapC]

theorem tapC_run {n : ℕ} (c : List (CGate n)) (x : Fin n → Bool) :
    runFrom x [] (tapC c) = runFrom x [] c ++ [output c x] := by
  rw [tapC, runFrom_append]
  rfl

theorem tapC_output {n : ℕ} (c : List (CGate n)) (x : Fin n → Bool) :
    output (tapC c) x = output c x := by
  change (runFrom x [] (tapC c)).getD ((tapC c).length - 1) false = output c x
  rw [tapC_length, Nat.add_sub_cancel, tapC_run]
  have hlen : (runFrom x [] c).length = c.length := by
    rw [CbudgetConeBound.runFrom_length]
    simp
  rw [← hlen]
  exact getD_concat _ _

theorem tapC_computes {n : ℕ} (c : List (CGate n))
    (f : (Fin n → Bool) → Bool) (hc : computes c f) :
    computes (tapC c) f := by
  intro x
  rw [tapC_output, hc x]

/-! ## Patch one truth-table entry while retaining all DAG sharing -/

/-- Change the output of `f` at the single input `a`. -/
def patchFn {n : ℕ} (f : (Fin n → Bool) → Bool)
    (a : Fin n → Bool) (b : Bool) : (Fin n → Bool) → Bool :=
  Function.update f a b

def patchOp (b old same : Bool) : Bool := if same then b else old

/-- Patch circuit: tap the old output, append a relocated equality circuit,
then select the new bit exactly at `a`. -/
noncomputable def patchC {n : ℕ} (c : List (CGate n))
    (a : Fin n → Bool) (b : Bool) : List (CGate n) :=
  let base := tapC c
  let ec := compile 0 (eqTree a)
  base ++ ec.map (relocG id base.length) ++
    [.bin (patchOp b) (base.length - 1) (base.length + ec.length - 1)]

theorem patchC_length {n : ℕ} (c : List (CGate n))
    (a : Fin n → Bool) (b : Bool) :
    (patchC c a b).length = c.length + (3 * n + 3) := by
  simp only [patchC, List.length_append, List.length_map, List.length_singleton,
    tapC_length, compile_length, eqTree_volume]
  omega

theorem patchC_computes {n : ℕ} (c : List (CGate n))
    (f : (Fin n → Bool) → Bool) (hc : computes c f)
    (a : Fin n → Bool) (b : Bool) :
    computes (patchC c a b) (patchFn f a b) := by
  intro x
  let base := tapC c
  let ec := compile 0 (eqTree a)
  let V := runFrom x [] base
  let U := runFrom x [] ec
  have hVlen : V.length = base.length := by
    simp only [V]
    rw [CbudgetConeBound.runFrom_length]
    simp
  have hUlen : U.length = ec.length := by
    simp only [U]
    rw [CbudgetConeBound.runFrom_length]
    simp
  have hbasepos : 0 < base.length := by simp [base]
  have hecpos : 0 < ec.length := by
    simp only [ec, compile_length, eqTree_volume]
    omega
  have hold : V.getD (base.length - 1) false = f x := by
    show output base x = f x
    rw [tapC_output]
    exact hc x
  have heq : U.getD (ec.length - 1) false = decide (x = a) := by
    have hec := compile_computes (eqTree a) x
    have hout : output ec x = eval (eqTree a) x := hec
    show output ec x = decide (x = a)
    rw [hout, Bool.eq_iff_iff, eqTree_eval_true_iff]
    exact decide_eq_true_iff.symm
  have hrunReloc :
      runFrom x V (ec.map (relocG id base.length)) = V ++ U := by
    rw [← hVlen]
    simpa [U] using (runFrom_relocG (ρ := id) x ec V [])
  have hOldRead : (V ++ U).getD (base.length - 1) false = f x := by
    rw [List.getD_append V U false (base.length - 1) (by omega), hold]
  have hEqRead :
      (V ++ U).getD (base.length + ec.length - 1) false = decide (x = a) := by
    rw [List.getD_append_right V U false (base.length + ec.length - 1) (by omega)]
    rw [show base.length + ec.length - 1 - V.length = ec.length - 1 by omega]
    exact heq
  unfold output patchC
  rw [runFrom_append, runFrom_append]
  change (runFrom x V (ec.map (relocG id base.length)) ++
      [evalGate x (runFrom x V (ec.map (relocG id base.length)))
        (CGate.bin (patchOp b) (base.length - 1) (base.length + ec.length - 1))]).getD
      ((base ++ ec.map (relocG id base.length) ++
        [CGate.bin (patchOp b) (base.length - 1) (base.length + ec.length - 1)]).length - 1)
      false = patchFn f a b x
  rw [hrunReloc]
  have hstateLen : (V ++ U).length = base.length + ec.length := by
    simp [hVlen, hUlen]
  have houtIdx : (base ++ ec.map (relocG id base.length) ++
      [CGate.bin (patchOp b) (base.length - 1) (base.length + ec.length - 1)]).length - 1
      = base.length + ec.length := by simp
  have hlast : ((V ++ U) ++
      [evalGate x (V ++ U)
        (CGate.bin (patchOp b) (base.length - 1) (base.length + ec.length - 1))]).getD
      (base.length + ec.length) false =
      evalGate x (V ++ U)
        (CGate.bin (patchOp b) (base.length - 1) (base.length + ec.length - 1)) := by
    rw [show base.length + ec.length = (V ++ U).length from hstateLen.symm]
    exact getD_concat _ _
  rw [houtIdx, hlast]
  simp only [evalGate, hOldRead, hEqRead, patchOp, patchFn]
  by_cases hxa : x = a
  · subst x
    simp
  · simp [hxa]

/-- **Sharing-sensitive local repair.**  Flipping one truth-table entry costs
at most `3n+3` general DAG gates. -/
theorem cbudget_update_le {n : ℕ} (f : (Fin n → Bool) → Bool)
    (a : Fin n → Bool) (b : Bool) :
    cbudget (patchFn f a b) ≤ cbudget f + (3 * n + 3) := by
  have hne : {s | ∃ c : List (CGate n), computes c f ∧ c.length = s}.Nonempty := by
    refine ⟨(compile 0 (dnfFor f)).length, compile 0 (dnfFor f), ?_, rfl⟩
    have h := compile_computes (dnfFor f)
    rwa [show (fun x => eval (dnfFor f) x) = f from eval_dnfFor f] at h
  obtain ⟨c, hc, hlen⟩ := Nat.sInf_mem hne
  have hmin : cbudget (patchFn f a b) ≤ (patchC c a b).length :=
    Nat.sInf_le ⟨patchC c a b, patchC_computes c f hc a b, rfl⟩
  rw [patchC_length, hlen] at hmin
  exact hmin

/-! ## Concrete truth-table MCSP -/

noncomputable def fnOfTable {n : ℕ} (z : Fin (2 ^ n) → Bool) :
    (Fin n → Bool) → Bool :=
  fun x => z (Layer10.ttEquiv n x)

theorem fnOfTable_truthTable {n : ℕ} (f : (Fin n → Bool) → Bool) :
    fnOfTable (Layer10.truthTable f) = f := by
  funext x
  simp [fnOfTable, Layer10.truthTable]

theorem truthTable_fnOfTable {n : ℕ} (z : Fin (2 ^ n) → Bool) :
    Layer10.truthTable (fnOfTable z) = z := by
  funext i
  simp [fnOfTable, Layer10.truthTable]

/-- The actual MCSP predicate for the full-basis DAG measure `cbudget`. -/
noncomputable def circuitMCSP (n s : ℕ) : (Fin (2 ^ n) → Bool) → Bool :=
  fun z => decide (cbudget (fnOfTable z) ≤ s)

theorem circuitMCSP_eq_true_iff {n s : ℕ} (z : Fin (2 ^ n) → Bool) :
    circuitMCSP n s z = true ↔ cbudget (fnOfTable z) ≤ s := by
  simp [circuitMCSP]

theorem fnOfTable_update {n : ℕ} (z : Fin (2 ^ n) → Bool)
    (i : Fin (2 ^ n)) (b : Bool) :
    fnOfTable (Function.update z i b) =
      patchFn (fnOfTable z) ((Layer10.ttEquiv n).symm i) b := by
  funext x
  by_cases hx : x = (Layer10.ttEquiv n).symm i
  · subst x
    simp only [fnOfTable, patchFn]
    rw [Equiv.apply_symm_apply, Function.update_self, Function.update_self]
  · have hi : Layer10.ttEquiv n x ≠ i := by
      intro he
      apply hx
      exact (Layer10.ttEquiv n).injective (by simpa using he)
    simp only [fnOfTable, patchFn, Function.update_of_ne hi, Function.update_of_ne hx]

/-- One truth-table-bit change increases inner minimum circuit size by at most
`3n+3`. -/
theorem cbudget_fnOfTable_update_le {n : ℕ} (z : Fin (2 ^ n) → Bool)
    (i : Fin (2 ^ n)) (b : Bool) :
    cbudget (fnOfTable (Function.update z i b)) ≤
      cbudget (fnOfTable z) + (3 * n + 3) := by
  rw [fnOfTable_update]
  exact cbudget_update_le _ _ _

/-- Below the threshold band, MCSP remains YES after any one-bit table change. -/
theorem circuitMCSP_stable_below {n s : ℕ} (z : Fin (2 ^ n) → Bool)
    (hsmall : cbudget (fnOfTable z) + (3 * n + 3) ≤ s)
    (i : Fin (2 ^ n)) (b : Bool) :
    circuitMCSP n s (Function.update z i b) = true := by
  rw [circuitMCSP_eq_true_iff]
  exact (cbudget_fnOfTable_update_le z i b).trans hsmall

/-- Above the threshold band, MCSP remains NO after any one-bit table change. -/
theorem circuitMCSP_stable_above {n s : ℕ} (z : Fin (2 ^ n) → Bool)
    (hlarge : s + (3 * n + 3) < cbudget (fnOfTable z))
    (i : Fin (2 ^ n)) (b : Bool) :
    circuitMCSP n s (Function.update z i b) = false := by
  apply Bool.eq_false_iff.mpr
  intro htrue
  have hsmall := (circuitMCSP_eq_true_iff (n := n) (s := s)
    (Function.update z i b)).mp htrue
  have hback : cbudget (fnOfTable z) ≤
      cbudget (fnOfTable (Function.update z i b)) + (3 * n + 3) := by
    have h := cbudget_update_le
      (fnOfTable (Function.update z i b)) ((Layer10.ttEquiv n).symm i) (z i)
    rw [← fnOfTable_update] at h
    have hrestore : Function.update (Function.update z i b) i (z i) = z := by
      funext j
      by_cases hji : j = i
      · subst j; simp
      · simp [Function.update_of_ne hji]
    rw [hrestore] at h
    exact h
  omega

/-! ## The exact boundary band seen by formula shrinkage -/

/-- Every directed YES-to-NO Hamming edge of MCSP crosses the inner DAG-size
threshold inside a band of width `3n+3`.  This is the sharing-sensitive
combinatorial object that a magnification proof must count. -/
theorem circuitMCSP_boundary_edge_band {n s : ℕ}
    (z : Fin (2 ^ n) → Bool) (i : Fin (2 ^ n)) (b : Bool)
    (hyes : circuitMCSP n s z = true)
    (hno : circuitMCSP n s (Function.update z i b) = false) :
    cbudget (fnOfTable z) ≤ s ∧
      s < cbudget (fnOfTable (Function.update z i b)) ∧
      cbudget (fnOfTable (Function.update z i b)) ≤ s + (3 * n + 3) := by
  have hlo := (circuitMCSP_eq_true_iff z).mp hyes
  have hnot : ¬ cbudget (fnOfTable (Function.update z i b)) ≤ s := by
    intro hsmall
    have ht := (circuitMCSP_eq_true_iff (Function.update z i b)).mpr hsmall
    rw [hno] at ht
    exact Bool.noConfusion ht
  have hhi : s < cbudget (fnOfTable (Function.update z i b)) :=
    Nat.lt_of_not_ge hnot
  have hup := cbudget_fnOfTable_update_le z i b
  exact ⟨hlo, hhi, hup.trans (Nat.add_le_add_right hlo _)⟩

/-- Accepted truth tables for the concrete MCSP threshold. -/
noncomputable def mcspYesSet (n s : ℕ) : Finset (Fin (2 ^ n) → Bool) :=
  Finset.univ.filter (fun z => circuitMCSP n s z = true)

/-- Rejected truth tables for the concrete MCSP threshold. -/
noncomputable def mcspNoSet (n s : ℕ) : Finset (Fin (2 ^ n) → Bool) :=
  Finset.univ.filter (fun z => circuitMCSP n s z = false)

theorem mem_mcspYesSet {n s : ℕ} (z : Fin (2 ^ n) → Bool) :
    z ∈ mcspYesSet n s ↔ circuitMCSP n s z = true := by
  simp [mcspYesSet]

theorem mem_mcspNoSet {n s : ℕ} (z : Fin (2 ^ n) → Bool) :
    z ∈ mcspNoSet n s ↔ circuitMCSP n s z = false := by
  simp [mcspNoSet]

/-- Khrapchenko now applies to the *sharing-sensitive* MCSP boundary.  The
remaining mathematical target is a lower bound on the number/density of the
near-threshold Hamming edges isolated above. -/
theorem circuitMCSP_khrapchenko {n s : ℕ} (t : DMTreeC (2 ^ n))
    (ht : t.eval = circuitMCSP n s) :
    (hamEdges (2 ^ n) (mcspYesSet n s) (mcspNoSet n s)).card ^ 2 ≤
      t.lsize0 * (mcspYesSet n s).card * (mcspNoSet n s).card := by
  apply khrapchenkoC t (mcspYesSet n s) (mcspNoSet n s)
  · intro z hz
    rw [ht]
    exact (mem_mcspYesSet z).mp hz
  · intro z hz
    rw [ht]
    exact (mem_mcspNoSet z).mp hz

end PallLean.Paper93.DeepMath.PathB.SharingSensitiveMCSP

#print axioms PallLean.Paper93.DeepMath.PathB.SharingSensitiveMCSP.cbudget_update_le
#print axioms PallLean.Paper93.DeepMath.PathB.SharingSensitiveMCSP.circuitMCSP_eq_true_iff
#print axioms PallLean.Paper93.DeepMath.PathB.SharingSensitiveMCSP.circuitMCSP_stable_below
#print axioms PallLean.Paper93.DeepMath.PathB.SharingSensitiveMCSP.circuitMCSP_stable_above
#print axioms PallLean.Paper93.DeepMath.PathB.SharingSensitiveMCSP.circuitMCSP_boundary_edge_band
#print axioms PallLean.Paper93.DeepMath.PathB.SharingSensitiveMCSP.circuitMCSP_khrapchenko
