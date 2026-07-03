import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSimulationBrick3

/-!
# N-Frame simulation, brick 4: locality — `k`-local machines get small step circuits

Brick 3's tableau is generic over the per-coordinate step circuits.  This brick supplies them, from the property that
makes Cook–Levin work: **locality**.  A machine whose every next-configuration bit depends on a window of at most `k`
configuration bits (`k`-local step) has per-coordinate circuits of size `≤ 7·2ᵏ` — polynomial whenever `k = O(log B)`.

  `shannonT` — the Shannon-expansion (decision-tree) transducer over a window list.
  `shannonT_correct` / `shannonT_volume` — **PROVED**: it computes any window-junta, at volume `+6 ≤ 7·2ᵏ`.
  `local_machine_circuits` — **PROVED, the locality brick**: a `k`-local step function yields per-coordinate circuits
        (via the verified compiler) of size `≤ 7·2ᵏ`, satisfying every hypothesis of the tableau theorem.
  `local_machine_tableau` — **PROVED, the assembly**: a `k`-local `B`-bit machine run `T` steps is simulated by a tableau
        of exactly `T·(B·7·2ᵏ)` gates ending in the iterated configuration — for `k`-local machines the whole tableau is
        **polynomial in `B` and `T`** whenever `k = O(log B)`.

## Honest scope — the generic engine is complete; the machine-specific residue is named

Turing-machine tableaux are `O(1)`-local per cell (after standard encoding); RAM models with indirect addressing are
`O(log B)`-local (address decoding).  This brick proves the *generic* locality ⇒ small-circuits ⇒ polynomial-tableau
engine — the mathematical content of `P ⊆ P/poly`.  What remains for `simulation` is brick 5: fixing one concrete machine
model, exhibiting its step function as a `k`-local family (the window analysis for the repo's RAM, or an `O(1)`-local TM
encoding), and assembling input-loading + tableau + output-readout into the end-to-end `PolyCBudget` bound.  Until then
`simulation` remains a named hypothesis of the conditional theorem.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {B : ℕ}

/-! ### The Shannon-expansion transducer over a window -/

/-- Shannon expansion of `g` over the window list `l`: a decision tree branching on each window variable. -/
def shannonT : ((Fin B → Bool) → Bool) → List (Fin B) → Trans B
  | g, [] => Trans.cst (g (fun _ => false))
  | g, i :: l =>
      Trans.bin (· || ·)
        (Trans.bin (· && ·) (Trans.var i) (shannonT (fun y => g (Function.update y i true)) l))
        (Trans.bin (· && ·) (Trans.un not (Trans.var i))
          (shannonT (fun y => g (Function.update y i false)) l))

/-- **Correctness (proved)**: the Shannon transducer computes any function that is a junta on the window list. -/
theorem shannonT_correct : ∀ (l : List (Fin B)) (g : (Fin B → Bool) → Bool),
    (∀ x y, (∀ i ∈ l, x i = y i) → g x = g y) →
    ∀ x, eval (shannonT g l) x = g x := by
  intro l
  induction l with
  | nil =>
    intro g hg x
    exact hg (fun _ => false) x (fun i hi => absurd hi (List.not_mem_nil))
  | cons i l ih =>
    intro g hg x
    have hbranch : ∀ b : Bool,
        ∀ x' y', (∀ j ∈ l, x' j = y' j) →
          g (Function.update x' i b) = g (Function.update y' i b) := by
      intro b x' y' hagree
      refine hg _ _ (fun j hj => ?_)
      rcases List.mem_cons.mp hj with hji | hjl
      · subst hji; simp [Function.update_self]
      · by_cases hji : j = i
        · subst hji; simp [Function.update_self]
        · rw [Function.update_of_ne hji, Function.update_of_ne hji]
          exact hagree j hjl
    have ht := ih (fun y => g (Function.update y i true)) (hbranch true) x
    have hf := ih (fun y => g (Function.update y i false)) (hbranch false) x
    show ((x i && eval (shannonT (fun y => g (Function.update y i true)) l) x)
        || (!x i && eval (shannonT (fun y => g (Function.update y i false)) l) x)) = g x
    rw [ht, hf]
    have hupd : ∀ b : Bool, x i = b → Function.update x i b = x := by
      intro b hb
      funext j
      by_cases hj : j = i
      · subst hj; rw [Function.update_self, hb]
      · rw [Function.update_of_ne hj]
    cases hxi : x i with
    | true => rw [hupd true hxi]; simp
    | false => rw [hupd false hxi]; simp

/-- **Volume bound (proved)**: `volume (shannonT g l) + 6 ≤ 7·2^{|l|}` — the window-exponential decision-tree size. -/
theorem shannonT_volume : ∀ (l : List (Fin B)) (g : (Fin B → Bool) → Bool),
    volume (shannonT g l) + 6 ≤ 7 * 2 ^ l.length := by
  intro l
  induction l with
  | nil =>
    intro g
    show 1 + 6 ≤ 7 * 2 ^ 0
    norm_num
  | cons i l ih =>
    intro g
    have ht := ih (fun y => g (Function.update y i true))
    have hf := ih (fun y => g (Function.update y i false))
    show (1 + volume (shannonT (fun y => g (Function.update y i true)) l) + 1)
        + ((volume (Trans.var i) + 1) + volume (shannonT (fun y => g (Function.update y i false)) l) + 1)
        + 1 + 6 ≤ 7 * 2 ^ (l.length + 1)
    show (1 + volume (shannonT (fun y => g (Function.update y i true)) l) + 1)
        + ((1 + 1) + volume (shannonT (fun y => g (Function.update y i false)) l) + 1)
        + 1 + 6 ≤ 7 * 2 ^ (l.length + 1)
    rw [pow_succ]
    omega

/-! ### The locality brick -/

/-- **`k`-local machines get small step circuits (proved).**  If every step coordinate `S i` depends only on the window
`W i` of at most `k` bits, then per-coordinate circuits exist — nonempty, of size `≤ 7·2ᵏ`, computing `S` — satisfying
every hypothesis of the tableau theorem. -/
theorem local_machine_circuits (S : Fin B → (Fin B → Bool) → Bool)
    (W : Fin B → List (Fin B)) (k : ℕ) (hW : ∀ i, (W i).length ≤ k)
    (hloc : ∀ i x y, (∀ j ∈ W i, x j = y j) → S i x = S i y) :
    ∃ cs : Fin B → List (CGate B),
      (∀ i, computes (cs i) (S i)) ∧ (∀ i, 0 < (cs i).length) ∧
      (∀ i, (cs i).length ≤ 7 * 2 ^ k) := by
  refine ⟨fun i => compile 0 (shannonT (S i) (W i)), ?_, ?_, ?_⟩
  · intro i x
    have h1 := compile_computes (shannonT (S i) (W i)) x
    rw [h1]
    exact shannonT_correct (W i) (S i) (hloc i) x
  · intro i
    rw [compile_length]
    exact volume_pos _
  · intro i
    rw [compile_length]
    calc volume (shannonT (S i) (W i)) ≤ 7 * 2 ^ (W i).length := by
          have := shannonT_volume (W i) (S i)
          omega
      _ ≤ 7 * 2 ^ k := by
          have : (2 : ℕ) ^ (W i).length ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (hW i)
          omega

/-- **The local-machine tableau (proved).**  A `k`-local `B`-bit machine run `T` steps is simulated by a tableau of
exactly `T·(B·(7·2ᵏ))` gates, ending with the iterated configuration `iterStep S T cfg` at in-range positions — the
tableau is polynomial in `B` and `T` whenever `k = O(log B)`. -/
theorem local_machine_tableau (S : Fin B → (Fin B → Bool) → Bool)
    (W : Fin B → List (Fin B)) (k : ℕ) (hW : ∀ i, (W i).length ≤ k)
    (hloc : ∀ i x y, (∀ j ∈ W i, x j = y j) → S i x = S i y)
    (x : Fin B → Bool) (T : ℕ) (pos : Fin B → ℕ) (vals : List Bool) (cfg : Fin B → Bool)
    (hpos : ∀ j, pos j < vals.length) (hcfg : ∀ j, vals.getD (pos j) false = cfg j) :
    ∃ (cs : Fin B → List (CGate B)) (w' : List Bool) (pos' : Fin B → ℕ),
      runFrom x vals (tableau cs (7 * 2 ^ k) T pos vals.length) = vals ++ w' ∧
      w'.length = T * (B * (7 * 2 ^ k)) ∧
      (∀ j, pos' j < vals.length + w'.length) ∧
      (∀ j, (vals ++ w').getD (pos' j) false = iterStep S T cfg j) := by
  obtain ⟨cs, hcomp, hc0, hsz⟩ := local_machine_circuits S W k hW hloc
  obtain ⟨w', pos', h1, h2, h3, h4⟩ :=
    tableau_spec cs S (7 * 2 ^ k) x hsz hc0 hcomp (by positivity) T pos vals cfg hpos hcfg
  exact ⟨cs, w', pos', h1, h2, h3, h4⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.shannonT_correct
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.local_machine_circuits
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.local_machine_tableau
