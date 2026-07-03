import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSimulationBrick1

/-!
# N-Frame simulation, brick 2: the full step layer — all next-configuration bits, with position bookkeeping

Brick 1 rebased a single coordinate circuit onto wires.  This brick assembles the **whole step layer**: given
per-coordinate circuits `cs i` computing the step-coordinate functions `S i` of a `B`-bit configuration, it lays all `B`
blocks — each front-padded to a common size `s`, so the position bookkeeping is uniform arithmetic — and proves the layer
theorem.

  `padBlock` — one coordinate's block: front padding to size `s`, then the rebased circuit; the block's output lands at
        its last wire.
  `layerGo` / `stepLayer` — the layer: blocks laid consecutively at running offsets.
  `runFrom_length` / `runFrom_replicate_cst` — **PROVED**: wire-count accounting and padding semantics.
  `layerGo_spec` — **PROVED, the layer theorem**: from any wire state holding the current configuration `cfg` at
        positions `pos`, the layer appends exactly `#coords · s` wires, and for every processed coordinate the wire at
        position `L + (p+1)·s − 1` carries `S (coord p) cfg` — the **entire next configuration**, at computable positions,
        with exact size accounting.

The output positions `fun p => L + (p+1)·s − 1` are themselves a valid `pos` function for the *next* layer — the
bookkeeping closes over iteration, which is exactly what brick 3 (the `T`-fold tableau) consumes.

## Honest scope

Bricks remaining for `simulation`: (3) `T`-fold iteration of `stepLayer` (the tableau, size `≤ B·s·T + B`); (4) a concrete
machine model's step function realized as the per-coordinate circuits `cs` with `s` polynomial (the RAM window analysis);
(5) polynomial cost accounting end-to-end.  Until then `simulation` remains a named hypothesis of the conditional
theorem.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {B : ℕ}

/-! ### Wire accounting helpers -/

/-- **Wire count (proved)**: running a circuit appends exactly its gate count. -/
theorem runFrom_length (x : Fin B → Bool) (c : List (CGate B)) :
    ∀ vals : List Bool, (runFrom x vals c).length = vals.length + c.length := by
  induction c with
  | nil => intro vals; rfl
  | cons g gs ih =>
    intro vals
    show (runFrom x (vals ++ [evalGate x vals g]) gs).length = vals.length + (gs.length + 1)
    rw [ih, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega

/-- **Padding semantics (proved)**: a run of constant gates appends that many `false` wires. -/
theorem runFrom_replicate_cst (x : Fin B → Bool) (m : ℕ) :
    ∀ vals : List Bool,
      runFrom x vals (List.replicate m (CGate.cst false)) = vals ++ List.replicate m false := by
  induction m with
  | zero => intro vals; simp [runFrom]
  | succ m ih =>
    intro vals
    rw [List.replicate_succ, List.replicate_succ]
    show runFrom x (vals ++ [false]) (List.replicate m (CGate.cst false)) = _
    rw [ih, List.append_assoc]
    rfl

/-! ### The step layer -/

/-- One coordinate's block at start offset `L`: front padding to common size `s`, then the rebased circuit. -/
def padBlock (pos : Fin B → ℕ) (s L : ℕ) (c : List (CGate B)) : List (CGate B) :=
  List.replicate (s - c.length) (CGate.cst false) ++ rebase pos (L + (s - c.length)) c

theorem padBlock_length (pos : Fin B → ℕ) (s L : ℕ) (c : List (CGate B)) (hc : c.length ≤ s) :
    (padBlock pos s L c).length = s := by
  simp [padBlock, rebase_length]
  omega

/-- The layer over a list of coordinates, blocks at running offsets. -/
def layerGo (cs : Fin B → List (CGate B)) (pos : Fin B → ℕ) (s : ℕ) :
    List (Fin B) → ℕ → List (CGate B)
  | [], _ => []
  | i :: is, L => padBlock pos s L (cs i) ++ layerGo cs pos s is (L + s)

/-- The full step layer: all `B` coordinates. -/
def stepLayer (cs : Fin B → List (CGate B)) (pos : Fin B → ℕ) (s L : ℕ) : List (CGate B) :=
  layerGo cs pos s (List.finRange B) L

/-- **The layer theorem (proved).**  From any wire state holding the configuration `cfg` at positions `pos`, the layer
appends exactly `#coords · s` wires, and coordinate `p`'s next-configuration bit `S (coord p) cfg` sits at position
`L + (p+1)·s − 1`. -/
theorem layerGo_spec (cs : Fin B → List (CGate B)) (S : Fin B → (Fin B → Bool) → Bool)
    (pos : Fin B → ℕ) (s : ℕ) (x : Fin B → Bool) (vals : List Bool) (cfg : Fin B → Bool)
    (hs : ∀ i, (cs i).length ≤ s) (hc0 : ∀ i, 0 < (cs i).length)
    (hcomp : ∀ i, computes (cs i) (S i))
    (hpos : ∀ j, pos j < vals.length) (hcfg : ∀ j, vals.getD (pos j) false = cfg j) :
    ∀ (is : List (Fin B)) (w : List Bool),
      ∃ w' : List Bool,
        runFrom x (vals ++ w) (layerGo cs pos s is (vals.length + w.length)) = (vals ++ w) ++ w' ∧
        w'.length = is.length * s ∧
        ∀ (p : ℕ) (hp : p < is.length),
          ((vals ++ w) ++ w').getD (vals.length + w.length + (p + 1) * s - 1) false
            = S (is.get ⟨p, hp⟩) cfg := by
  intro is
  induction is with
  | nil =>
    intro w
    exact ⟨[], by simp [layerGo, runFrom], by simp, fun p hp => absurd hp (by simp)⟩
  | cons i is ih =>
    intro w
    have hsi := hs i
    have hc0i := hc0 i
    -- abbreviations (plain `have`-level, no `set`, to keep rewriting predictable)
    have hrun1 : runFrom x (vals ++ w)
        (List.replicate (s - (cs i).length) (CGate.cst false))
        = (vals ++ w) ++ List.replicate (s - (cs i).length) false :=
      runFrom_replicate_cst x _ (vals ++ w)
    -- extraction through the padding still reads the configuration
    have hbase2 : ∀ j, pos j < ((vals ++ w) ++ List.replicate (s - (cs i).length) false).length := by
      intro j
      simp only [List.length_append, List.length_replicate]
      have := hpos j
      omega
    have hext : (fun j => ((vals ++ w) ++ List.replicate (s - (cs i).length) false).getD
        (pos j) false) = cfg := by
      funext j
      show ((vals ++ w) ++ List.replicate (s - (cs i).length) false).getD (pos j) false = cfg j
      rw [List.getD_append (vals ++ w) _ false (pos j)
        (by rw [List.length_append]; have := hpos j; omega)]
      rw [List.getD_append vals w false (pos j) (hpos j)]
      exact hcfg j
    -- run the rebased circuit via brick 1
    have hrun2 := rebase_go pos ((vals ++ w) ++ List.replicate (s - (cs i).length) false)
      hbase2 x (cs i) []
    rw [List.append_nil, hext] at hrun2
    have hLWc : (runFrom cfg [] (cs i)).length = (cs i).length := by
      rw [runFrom_length]
      simp
    have hheadout : (runFrom cfg [] (cs i)).getD ((cs i).length - 1) false = S i cfg := by
      have := hcomp i cfg
      unfold output at this
      exact this
    -- the head block, assembled
    have hofs : vals.length + w.length + (s - (cs i).length)
        = ((vals ++ w) ++ List.replicate (s - (cs i).length) false).length := by
      simp only [List.length_append, List.length_replicate]
    have hstep : runFrom x (vals ++ w) (padBlock pos s (vals.length + w.length) (cs i))
        = (vals ++ w) ++ (List.replicate (s - (cs i).length) false ++ runFrom cfg [] (cs i)) := by
      unfold padBlock
      rw [runFrom_append, hrun1, hofs, hrun2, List.append_assoc]
    -- the tail, via the induction hypothesis
    obtain ⟨w'', hrun'', hlen'', hpos''⟩ :=
      ih (w ++ (List.replicate (s - (cs i).length) false ++ runFrom cfg [] (cs i)))
    have hlen2 : vals.length
          + (w ++ (List.replicate (s - (cs i).length) false ++ runFrom cfg [] (cs i))).length
        = vals.length + w.length + s := by
      simp only [List.length_append, List.length_replicate, hLWc]
      omega
    refine ⟨(List.replicate (s - (cs i).length) false ++ runFrom cfg [] (cs i)) ++ w'', ?_, ?_, ?_⟩
    · -- the run
      simp only [layerGo]
      rw [runFrom_append, hstep]
      have hoff2 : vals.length + w.length + s
          = vals.length
            + (w ++ (List.replicate (s - (cs i).length) false ++ runFrom cfg [] (cs i))).length :=
        hlen2.symm
      have hstate : (vals ++ w)
            ++ (List.replicate (s - (cs i).length) false ++ runFrom cfg [] (cs i))
          = vals ++ (w ++ (List.replicate (s - (cs i).length) false ++ runFrom cfg [] (cs i))) := by
        rw [List.append_assoc]
      rw [hoff2, hstate, hrun'']
      simp [List.append_assoc]
    · -- the length
      simp only [List.length_append, List.length_replicate, hLWc, hlen'', List.length_cons,
        Nat.succ_mul]
      omega
    · -- the positions
      intro p hp
      match p with
      | 0 =>
        show ((vals ++ w)
            ++ ((List.replicate (s - (cs i).length) false ++ runFrom cfg [] (cs i)) ++ w'')).getD
            (vals.length + w.length + (0 + 1) * s - 1) false = S i cfg
        have hsplit : (vals ++ w)
              ++ ((List.replicate (s - (cs i).length) false ++ runFrom cfg [] (cs i)) ++ w'')
            = (((vals ++ w) ++ List.replicate (s - (cs i).length) false)
                ++ runFrom cfg [] (cs i)) ++ w'' := by
          simp [List.append_assoc]
        have hidx : vals.length + w.length + (0 + 1) * s - 1
            = ((vals ++ w) ++ List.replicate (s - (cs i).length) false).length
              + ((cs i).length - 1) := by
          simp only [List.length_append, List.length_replicate, Nat.zero_add, Nat.one_mul]
          omega
        rw [hsplit, hidx]
        rw [List.getD_append
          (((vals ++ w) ++ List.replicate (s - (cs i).length) false) ++ runFrom cfg [] (cs i))
          w'' false _
          (by
            simp only [List.length_append, List.length_replicate, hLWc]
            omega)]
        rw [List.getD_append_right
          ((vals ++ w) ++ List.replicate (s - (cs i).length) false)
          (runFrom cfg [] (cs i)) false _ (Nat.le_add_right _ _),
          Nat.add_sub_cancel_left]
        exact hheadout
      | Nat.succ q =>
        have hq : q < is.length := by
          simp only [List.length_cons] at hp
          omega
        have htail := hpos'' q hq
        rw [hlen2] at htail
        have hidx2 : vals.length + w.length + s + (q + 1) * s - 1
            = vals.length + w.length + (q + 1 + 1) * s - 1 := by
          rw [show (q + 1 + 1) * s = s + (q + 1) * s from by ring, ← Nat.add_assoc]
        rw [hidx2] at htail
        have hassoc2 : vals
              ++ (w ++ (List.replicate (s - (cs i).length) false ++ runFrom cfg [] (cs i)))
              ++ w''
            = (vals ++ w)
              ++ ((List.replicate (s - (cs i).length) false ++ runFrom cfg [] (cs i)) ++ w'') := by
          simp [List.append_assoc]
        rw [hassoc2] at htail
        exact htail

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.runFrom_length
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.layerGo_spec
