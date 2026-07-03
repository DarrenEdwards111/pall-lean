import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSimulationBrick4

/-!
# N-Frame simulation, brick 5: the assembly — `simulation` discharged for local machines

The last brick.  It closes the remaining structural gap (brick 3's final positions were existential; a *uniform* circuit
needs concrete ones), assembles input-loading + tableau + readout into one circuit, handles the input-space embedding
(workspace larger than input), and discharges the conditional theorem's `simulation` hypothesis for machines presented in
the local model.

  `tabPos` / `tableau_pos` — **PROVED**: the tableau's final configuration positions are *pure arithmetic* — uniform in
        the input — and the tableau holds `iterStep S T cfg` there.
  `layerGo_length` / `tableau_length` — **PROVED**: exact static size accounting, no run needed.
  `loadVars` / `runFrom_map_var` — **PROVED**: the input-loading layer (wire `j` := input bit `j`).
  `machineCircuit` / `machineCircuit_computes` / `machineCircuit_length` — **PROVED**: loading + tableau + readout
        computes `x ↦ iterStep S T x out` in exactly `B + T·(B·s) + 1` gates.
  `retypeInp` / `runFrom_retypeInp` — **PROVED**: the input embedding — a machine whose `B`-bit workspace loads an
        `n`-bit input (rest zero) retypes to a circuit over the `n` real inputs, gate-for-gate.
  `localMachine_cbudget` — **PROVED, the per-instance bound**: a `k`-local machine deciding `f` in `T` steps gives
        `cbudget f ≤ B + T·(B·(7·2ᵏ)) + 1`.
  `simulation_for_local_machines` — **PROVED, the discharge**: a family decided by local machines of polynomially
        bounded tableau size has `PolyCBudget` — the conditional theorem's `simulation` hypothesis, **discharged** for
        this machine model.

## Honest scope — what is now proved, and the one classical step that remains named

With this brick, the chain *"local-machine decider ⇒ polynomial circuit energy"* is machine-checked end to end; combined
with `no_polytime_decider_of_superpoly`, the conditional `P ≠ NP` theorem needs **no** circuit-side hypothesis for
deciders presented as polynomial local machines.  What remains *named, not proved*: that other machine formalisms (the
repo's RAM, standard TMs) translate into polynomial local-machine presentations — the classical encoding step
(TM ⇒ `O(1)`-local per cell; RAM ⇒ `O(log B)`-local via address decoding), standard but a separate formalization.  The
open target `NFrameCircuitLowerBoundTarget SAT` is untouched.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {B : ℕ}

/-! ### Static size accounting -/

/-- **Layer size, statically (proved).** -/
theorem layerGo_length (cs : Fin B → List (CGate B)) (s : ℕ)
    (hs : ∀ i, (cs i).length ≤ s) (pos : Fin B → ℕ) :
    ∀ (is : List (Fin B)) (L : ℕ), (layerGo cs pos s is L).length = is.length * s := by
  intro is
  induction is with
  | nil => intro L; simp [layerGo]
  | cons i is ih =>
    intro L
    simp only [layerGo, List.length_append, ih, padBlock_length pos s L (cs i) (hs i),
      List.length_cons, Nat.succ_mul]
    omega

/-- **Tableau size, statically (proved).** -/
theorem tableau_length (cs : Fin B → List (CGate B)) (s : ℕ)
    (hs : ∀ i, (cs i).length ≤ s) :
    ∀ (T : ℕ) (pos : Fin B → ℕ) (L : ℕ), (tableau cs s T pos L).length = T * (B * s) := by
  intro T
  induction T with
  | zero => intro pos L; simp [tableau]
  | succ T ih =>
    intro pos L
    show (stepLayer cs pos s L
        ++ tableau cs s T (fun i => L + (i.val + 1) * s - 1) (L + B * s)).length = _
    rw [List.length_append, ih]
    unfold stepLayer
    rw [layerGo_length cs s hs pos (List.finRange B) L, List.length_finRange, Nat.succ_mul]
    omega

/-! ### Uniform tableau positions -/

/-- The tableau's final configuration positions: pure arithmetic, uniform in the input. -/
def tabPos (s : ℕ) : (Fin B → ℕ) → ℕ → ℕ → Fin B → ℕ
  | pos, _, 0 => pos
  | _, L, T + 1 => tabPos s (fun i => L + (i.val + 1) * s - 1) (L + B * s) T

/-- **The position-explicit tableau theorem (proved)**: the tableau ends holding `iterStep S T cfg` at the *concrete*
positions `tabPos` — uniform in the input, as a circuit requires. -/
theorem tableau_pos (cs : Fin B → List (CGate B)) (S : Fin B → (Fin B → Bool) → Bool)
    (s : ℕ) (x : Fin B → Bool)
    (hs : ∀ i, (cs i).length ≤ s) (hc0 : ∀ i, 0 < (cs i).length)
    (hcomp : ∀ i, computes (cs i) (S i)) (hs0 : 0 < s) :
    ∀ (T : ℕ) (pos : Fin B → ℕ) (vals : List Bool) (cfg : Fin B → Bool),
      (∀ j, pos j < vals.length) → (∀ j, vals.getD (pos j) false = cfg j) →
      ∃ w' : List Bool,
        runFrom x vals (tableau cs s T pos vals.length) = vals ++ w' ∧
        w'.length = T * (B * s) ∧
        (∀ j, tabPos s pos vals.length T j < vals.length + w'.length) ∧
        (∀ j, (vals ++ w').getD (tabPos s pos vals.length T j) false = iterStep S T cfg j) := by
  intro T
  induction T with
  | zero =>
    intro pos vals cfg hpos hcfg
    refine ⟨[], by simp [tableau, runFrom], by simp, ?_, ?_⟩
    · intro j
      simp only [List.length_nil, tabPos]
      have := hpos j
      omega
    · intro j
      rw [List.append_nil]
      exact hcfg j
  | succ T ih =>
    intro pos vals cfg hpos hcfg
    obtain ⟨w₁, hrun₁, hlen₁, hout₁⟩ :=
      layerGo_spec cs S pos s x vals cfg hs hc0 hcomp hpos hcfg (List.finRange B) []
    rw [List.append_nil] at hrun₁ hout₁
    simp only [List.length_nil, Nat.add_zero] at hrun₁ hout₁
    rw [List.length_finRange] at hlen₁
    have hcfg' : ∀ j : Fin B,
        (vals ++ w₁).getD (vals.length + (j.val + 1) * s - 1) false = S j cfg := by
      intro j
      have hj : j.val < (List.finRange B).length := by
        rw [List.length_finRange]; exact j.isLt
      have := hout₁ j.val hj
      have hget : (List.finRange B).get ⟨j.val, hj⟩ = j := by
        apply Fin.ext
        simp
      rwa [hget] at this
    have hpos' : ∀ j : Fin B, vals.length + (j.val + 1) * s - 1 < (vals ++ w₁).length := by
      intro j
      rw [List.length_append, hlen₁]
      have h1 : (j.val + 1) * s ≤ B * s := Nat.mul_le_mul_right s (by have := j.isLt; omega)
      have h2 : 0 < (j.val + 1) * s := Nat.mul_pos (by omega) hs0
      omega
    obtain ⟨w₂, hrun₂, hlen₂, hposF, houtF⟩ :=
      ih (fun i => vals.length + (i.val + 1) * s - 1) (vals ++ w₁) (fun i => S i cfg)
        hpos' hcfg'
    have hoff : vals.length + B * s = (vals ++ w₁).length := by
      rw [List.length_append, hlen₁]
    refine ⟨w₁ ++ w₂, ?_, ?_, ?_, ?_⟩
    · show runFrom x vals (stepLayer cs pos s vals.length
          ++ tableau cs s T (fun i => vals.length + (i.val + 1) * s - 1)
              (vals.length + B * s)) = _
      rw [runFrom_append]
      unfold stepLayer
      rw [hrun₁, hoff, hrun₂, List.append_assoc]
    · rw [List.length_append, hlen₁, hlen₂]
      ring
    · intro j
      have hj := hposF j
      rw [← hoff] at hj
      show tabPos s (fun i => vals.length + (i.val + 1) * s - 1) (vals.length + B * s) T j
          < vals.length + (w₁ ++ w₂).length
      rw [List.length_append]
      omega
    · intro j
      have hj := houtF j
      rw [List.append_assoc] at hj
      rw [← hoff] at hj
      exact hj

/-! ### Input loading and readout -/

/-- The input-loading layer: wire `j` carries input bit `j`. -/
def loadVars (B : ℕ) : List (CGate B) := (List.finRange B).map CGate.var

theorem runFrom_map_var (x : Fin B → Bool) :
    ∀ (l : List (Fin B)) (vals : List Bool),
      runFrom x vals (l.map CGate.var) = vals ++ l.map x := by
  intro l
  induction l with
  | nil => intro vals; simp [runFrom]
  | cons i l ih =>
    intro vals
    show runFrom x (vals ++ [x i]) (l.map CGate.var) = vals ++ (x i :: l.map x)
    rw [ih, List.append_assoc]
    rfl

theorem loadVars_getD (x : Fin B → Bool) (j : Fin B) :
    ((List.finRange B).map x).getD j.val false = x j := by
  rw [List.getD_eq_getElem _ _ (by simp [j.isLt])]
  simp

/-! ### The machine circuit -/

/-- The full machine circuit: input loading, then the tableau, then the readout of the output coordinate. -/
def machineCircuit (cs : Fin B → List (CGate B)) (s T : ℕ) (out : Fin B) : List (CGate B) :=
  loadVars B ++ tableau cs s T (fun j => j.val) B
    ++ [CGate.un id (tabPos s (fun j => j.val) B T out)]

theorem machineCircuit_length (cs : Fin B → List (CGate B)) (s T : ℕ) (out : Fin B)
    (hs : ∀ i, (cs i).length ≤ s) :
    (machineCircuit cs s T out).length = B + T * (B * s) + 1 := by
  simp only [machineCircuit, List.length_append, List.length_cons, List.length_nil,
    loadVars, List.length_map, List.length_finRange,
    tableau_length cs s hs T (fun j => j.val) B]

/-- **The machine circuit computes the machine (proved)**: its output is `iterStep S T x out`. -/
theorem machineCircuit_computes (cs : Fin B → List (CGate B))
    (S : Fin B → (Fin B → Bool) → Bool) (s T : ℕ) (out : Fin B)
    (hs : ∀ i, (cs i).length ≤ s) (hc0 : ∀ i, 0 < (cs i).length)
    (hcomp : ∀ i, computes (cs i) (S i)) (hs0 : 0 < s) :
    computes (machineCircuit cs s T out) (fun x => iterStep S T x out) := by
  intro x
  have hload : runFrom x [] (loadVars B) = (List.finRange B).map x :=
    runFrom_map_var x (List.finRange B) []
  have hloadlen : ((List.finRange B).map x).length = B := by simp
  obtain ⟨w', hrun, hwlen, hposR, houtR⟩ :=
    tableau_pos cs S s x hs hc0 hcomp hs0 T (fun j => j.val) ((List.finRange B).map x) x
      (fun j => by rw [hloadlen]; exact j.isLt)
      (fun j => loadVars_getD x j)
  rw [hloadlen] at hrun hposR houtR
  unfold output machineCircuit
  rw [runFrom_append, runFrom_append, hload, hrun]
  show (((List.finRange B).map x ++ w')
      ++ [evalGate x ((List.finRange B).map x ++ w')
          (CGate.un id (tabPos s (fun j => j.val) B T out))]).getD
      ((loadVars B ++ tableau cs s T (fun j => j.val) B
        ++ [CGate.un id (tabPos s (fun j => j.val) B T out)]).length - 1) false
      = iterStep S T x out
  have hgate : evalGate x ((List.finRange B).map x ++ w')
      (CGate.un id (tabPos s (fun j => j.val) B T out)) = iterStep S T x out := by
    show id (((List.finRange B).map x ++ w').getD (tabPos s (fun j => j.val) B T out) false)
      = iterStep S T x out
    rw [houtR out]
    rfl
  rw [hgate]
  have hclen : (loadVars B ++ tableau cs s T (fun j => j.val) B
      ++ [CGate.un id (tabPos s (fun j => j.val) B T out)]).length
      = ((List.finRange B).map x ++ w').length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil, loadVars,
      List.length_map, List.length_finRange, hwlen,
      tableau_length cs s hs T (fun j => j.val) B]
  rw [hclen, Nat.add_sub_cancel]
  exact getD_concat _ _

/-! ### The input embedding: workspace larger than the input -/

/-- Retype a `B`-input gate to an `n`-input gate through the input embedding `inp` (workspace bits with no input load
as constants). -/
def retypeInp {n : ℕ} (inp : Fin B → Option (Fin n)) : CGate B → CGate n
  | .var j => (inp j).elim (CGate.cst false) CGate.var
  | .cst b => .cst b
  | .un op j => .un op j
  | .bin op j k => .bin op j k

/-- **Retyping is faithful (proved)**: the retyped circuit over the real inputs runs exactly as the original over the
embedded configuration. -/
theorem runFrom_retypeInp {n : ℕ} (inp : Fin B → Option (Fin n)) (x : Fin n → Bool) :
    ∀ (c : List (CGate B)) (vals : List Bool),
      runFrom x vals (c.map (retypeInp inp))
        = runFrom (fun j => ((inp j).map x).getD false) vals c := by
  intro c
  induction c with
  | nil => intro vals; rfl
  | cons g gs ih =>
    intro vals
    have hgate : evalGate x vals (retypeInp inp g)
        = evalGate (fun j => ((inp j).map x).getD false) vals g := by
      cases g with
      | var j => cases hj : inp j <;> simp [retypeInp, evalGate, hj]
      | cst b => rfl
      | un op j => rfl
      | bin op j k => rfl
    show runFrom x (vals ++ [evalGate x vals (retypeInp inp g)]) (gs.map (retypeInp inp)) = _
    rw [hgate]
    exact ih _

/-! ### The per-instance bound and the discharge -/

/-- **The per-instance bound (proved).**  A `k`-local `B`-bit machine deciding `f` in `T` steps (input embedded by
`inp`, output at `out`) gives `cbudget f ≤ B + T·(B·(7·2ᵏ)) + 1`. -/
theorem localMachine_cbudget {n : ℕ} (S : Fin B → (Fin B → Bool) → Bool)
    (W : Fin B → List (Fin B)) (k : ℕ) (hW : ∀ i, (W i).length ≤ k)
    (hloc : ∀ i x y, (∀ j ∈ W i, x j = y j) → S i x = S i y)
    (T : ℕ) (out : Fin B) (inp : Fin B → Option (Fin n)) (f : (Fin n → Bool) → Bool)
    (hdec : ∀ x : Fin n → Bool, iterStep S T (fun j => ((inp j).map x).getD false) out = f x) :
    cbudget f ≤ B + T * (B * (7 * 2 ^ k)) + 1 := by
  obtain ⟨cs, hcomp, hc0, hsz⟩ := local_machine_circuits S W k hW hloc
  have hs0 : 0 < 7 * 2 ^ k := by positivity
  have hmc := machineCircuit_computes cs S (7 * 2 ^ k) T out hsz hc0 hcomp hs0
  have hcomputes : computes ((machineCircuit cs (7 * 2 ^ k) T out).map (retypeInp inp)) f := by
    intro x
    show (runFrom x [] ((machineCircuit cs (7 * 2 ^ k) T out).map (retypeInp inp))).getD
        (((machineCircuit cs (7 * 2 ^ k) T out).map (retypeInp inp)).length - 1) false = f x
    rw [List.length_map, runFrom_retypeInp inp x]
    have hmc2 := hmc (fun j => ((inp j).map x).getD false)
    unfold output at hmc2
    rw [hmc2]
    exact hdec x
  have hmem : cbudget f ≤ ((machineCircuit cs (7 * 2 ^ k) T out).map (retypeInp inp)).length :=
    Nat.sInf_le ⟨_, hcomputes, rfl⟩
  have hlen : ((machineCircuit cs (7 * 2 ^ k) T out).map (retypeInp inp)).length
      = B + T * (B * (7 * 2 ^ k)) + 1 := by
    rw [List.length_map, machineCircuit_length cs (7 * 2 ^ k) T out hsz]
  omega

/-- **`simulation`, DISCHARGED for local machines (proved).**  A family decided by `k`-local machines whose tableau size
is polynomially bounded has polynomial circuit energy — the conditional theorem's `simulation` hypothesis, proved for
deciders presented in the local-machine model. -/
theorem simulation_for_local_machines (F : ∀ n : ℕ, (Fin n → Bool) → Bool)
    (Bn Tn kn : ℕ → ℕ)
    (M : ∀ n, (Fin (Bn n) → (Fin (Bn n) → Bool) → Bool) ×
        (Fin (Bn n) → List (Fin (Bn n))) × Fin (Bn n) × (Fin (Bn n) → Option (Fin n)))
    (hW : ∀ n i, ((M n).2.1 i).length ≤ kn n)
    (hloc : ∀ n i x y, (∀ j ∈ (M n).2.1 i, x j = y j) → (M n).1 i x = (M n).1 i y)
    (hdec : ∀ n (x : Fin n → Bool),
      iterStep (M n).1 (Tn n) (fun j => (((M n).2.2.2 j).map x).getD false) (M n).2.2.1 = F n x)
    (hpoly : ∃ a, ∀ n, Bn n + Tn n * (Bn n * (7 * 2 ^ kn n)) + 1 ≤ n ^ a + a) :
    PolyCBudget F := by
  obtain ⟨a, ha⟩ := hpoly
  refine ⟨a, fun n => ?_⟩
  exact le_trans
    (localMachine_cbudget (M n).1 (M n).2.1 (kn n) (hW n) (hloc n) (Tn n)
      (M n).2.2.1 (M n).2.2.2 (F n) (hdec n))
    (ha n)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.tableau_pos
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.machineCircuit_computes
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.localMachine_cbudget
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.simulation_for_local_machines
