import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSimulationBrick2

/-!
# N-Frame simulation, brick 3: the tableau — `T`-fold iteration of the step layer

Brick 2 built one step layer and showed its output positions close over iteration.  This brick iterates: the **tableau**
lays `T` step layers, and the tableau theorem proves it computes the `T`-fold iterated step of the machine configuration,
with exact size accounting — the Cook–Levin tabling, in the boundary circuit model.

  `iterStep S T cfg` — the machine semantics: `T` applications of the step function.
  `tableau cs s T pos L` — `T` step layers, each reading the previous layer's output positions.
  `tableau_spec` — **PROVED, the tableau theorem**: from any wire state holding the configuration `cfg` at positions
        `pos`, the `T`-layer tableau appends **exactly `T·(B·s)` wires** and ends holding `iterStep S T cfg` at
        computable in-range positions.  Size is *linear in `T`* — the polynomial accounting brick 5 needs.

## Honest scope

The tableau is generic over the per-coordinate step circuits `cs`.  What remains for `simulation`: (4) realizing a
concrete machine model's step function as the circuits `cs` with `s` polynomial in the machine's description (the RAM
window analysis — the genuinely machine-specific work); (5) assembling input-loading + tableau + output-readout into the
end-to-end polynomial `cbudget` bound.  Until then `simulation` remains a named hypothesis of the conditional theorem.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {B : ℕ}

/-- The machine semantics: `T` applications of the step function `S` (coordinatewise). -/
def iterStep (S : Fin B → (Fin B → Bool) → Bool) : ℕ → (Fin B → Bool) → (Fin B → Bool)
  | 0, cfg => cfg
  | T + 1, cfg => iterStep S T (fun i => S i cfg)

/-- The tableau: `T` step layers, each reading the previous layer's output positions. -/
def tableau (cs : Fin B → List (CGate B)) (s : ℕ) : ℕ → (Fin B → ℕ) → ℕ → List (CGate B)
  | 0, _, _ => []
  | T + 1, pos, L =>
      stepLayer cs pos s L
        ++ tableau cs s T (fun i => L + (i.val + 1) * s - 1) (L + B * s)

/-- **The tableau theorem (proved).**  From any wire state holding the configuration `cfg` at positions `pos`, the
`T`-layer tableau appends exactly `T·(B·s)` wires and ends holding the iterated configuration `iterStep S T cfg` at
computable in-range positions. -/
theorem tableau_spec (cs : Fin B → List (CGate B)) (S : Fin B → (Fin B → Bool) → Bool)
    (s : ℕ) (x : Fin B → Bool)
    (hs : ∀ i, (cs i).length ≤ s) (hc0 : ∀ i, 0 < (cs i).length)
    (hcomp : ∀ i, computes (cs i) (S i)) (hs0 : 0 < s) :
    ∀ (T : ℕ) (pos : Fin B → ℕ) (vals : List Bool) (cfg : Fin B → Bool),
      (∀ j, pos j < vals.length) → (∀ j, vals.getD (pos j) false = cfg j) →
      ∃ (w' : List Bool) (pos' : Fin B → ℕ),
        runFrom x vals (tableau cs s T pos vals.length) = vals ++ w' ∧
        w'.length = T * (B * s) ∧
        (∀ j, pos' j < vals.length + w'.length) ∧
        (∀ j, (vals ++ w').getD (pos' j) false = iterStep S T cfg j) := by
  intro T
  induction T with
  | zero =>
    intro pos vals cfg hpos hcfg
    refine ⟨[], pos, by simp [tableau, runFrom], by simp, ?_, ?_⟩
    · intro j
      simp only [List.length_nil]
      have := hpos j
      omega
    · intro j
      rw [List.append_nil]
      exact hcfg j
  | succ T ih =>
    intro pos vals cfg hpos hcfg
    -- one step layer, via brick 2 (at the full coordinate list)
    obtain ⟨w₁, hrun₁, hlen₁, hout₁⟩ :=
      layerGo_spec cs S pos s x vals cfg hs hc0 hcomp hpos hcfg (List.finRange B) []
    rw [List.append_nil] at hrun₁ hout₁
    simp only [List.length_nil, Nat.add_zero] at hrun₁ hout₁
    rw [List.length_finRange] at hlen₁
    -- the new configuration and its positions
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
    -- the remaining T layers, via the induction hypothesis
    obtain ⟨w₂, pos'', hrun₂, hlen₂, hposF, houtF⟩ :=
      ih (fun i => vals.length + (i.val + 1) * s - 1) (vals ++ w₁) (fun i => S i cfg)
        hpos' hcfg'
    refine ⟨w₁ ++ w₂, pos'', ?_, ?_, ?_, ?_⟩
    · -- the run: layer then tableau tail
      show runFrom x vals (stepLayer cs pos s vals.length
          ++ tableau cs s T (fun i => vals.length + (i.val + 1) * s - 1)
              (vals.length + B * s)) = _
      rw [runFrom_append]
      unfold stepLayer
      rw [hrun₁]
      have hoff : vals.length + B * s = (vals ++ w₁).length := by
        rw [List.length_append, hlen₁]
      rw [hoff, hrun₂, List.append_assoc]
    · -- the size: linear in T
      rw [List.length_append, hlen₁, hlen₂]
      ring
    · -- the final positions are in range
      intro j
      have := hposF j
      rw [List.length_append, hlen₁] at this
      rw [List.length_append]
      omega
    · -- the final configuration
      intro j
      have := houtF j
      rw [List.append_assoc] at this
      exact this

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.tableau_spec
