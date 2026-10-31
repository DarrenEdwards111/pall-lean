import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockSwitchingProb

/-!
# Block-DT model, foundation 12: the circuit-collapse rung (branch only)

The probabilistic-method / union-bound step that turns the per-gate switching count into a **single**
random restriction that simultaneously makes *every* bottom gate's canonical block decision tree
**shallow** (depth `< s`).  This is the mechanism by which the switching lemma drops circuit depth:
once every depth-`d` bottom DNF collapses to a shallow DT (hence a small-width CNF), the bottom two
layers swap and merge, reducing the circuit to depth `d-1`.

**Key fuel trick.**  Running the descent with fuel `F = s`, `blockStream_length_le` gives `length ≤ s`,
so `length = s` holds *iff* the canonical descent never terminated early — i.e. iff the true canonical
DT depth is `≥ s`.  Thus the deep set `{stars = K ∧ length = s}` (fuel `s`) is exactly the Håstad bad
event "depth `≥ s`", and avoiding it means `length < s`: a genuinely shallow tree.

* `exists_avoiding_all` — union-bound existence: if `∑_g |B g| < |Ω|`, some `ρ ∈ Ω` avoids every `B g`.
* `gateDeepSet` / `gateDeepSet_card_le` — the per-gate deep set and its switching bound.
* `circuit_collapse_exists` — **the collapse**: if `G · |Short| · (2^w)^s < |Ω|` then there is a
  restriction in the `K`-star shell under which *every* gate's block-DT has depth `< s`.

Clean, no `sorry`, no `native_decide`.  AC⁰/depth-3; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Union-bound existence (probabilistic method).**  If the total size of the bad sets `B g` is less
than `|Ω|`, then some element of `Ω` lies outside every `B g`. -/
theorem exists_avoiding_all {α : Type*} [DecidableEq α] {Ω : Finset α} {G : ℕ} (B : Fin G → Finset α)
    (hcard : ∑ g : Fin G, (B g).card < Ω.card) :
    ∃ ρ ∈ Ω, ∀ g, ρ ∉ B g := by
  classical
  set S : Finset α := Finset.univ.biUnion B with hS
  have hScard : S.card ≤ ∑ g : Fin G, (B g).card := Finset.card_biUnion_le
  have hpos : 0 < (Ω \ S).card := by
    have h := Finset.card_le_card_sdiff_add_card (s := Ω) (t := S)
    omega
  obtain ⟨ρ, hρ⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_sdiff] at hρ
  exact ⟨ρ, hρ.1, fun g hg => hρ.2 (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, hg⟩)⟩

/-- The deep set of a single gate (run with fuel `s`): the `K`-star restrictions whose block-DT does
**not** terminate within `s` blocks (`length = s`), i.e. the canonical depth is `≥ s`. -/
def gateDeepSet (cs : List (Clause n)) (K s : ℕ) : Finset (Restriction n) :=
  Finset.univ.filter (fun ρ => SwitchingCounting.stars ρ = K ∧ (blockStream cs s ρ).length = s)

/-- **Per-gate switching bound.**  `|gateDeepSet| ≤ |{stars ≤ K-s}| · (2^w)^s`. -/
theorem gateDeepSet_card_le (cs : List (Clause n)) (w K s : ℕ)
    (hcons : ∀ T ∈ cs, Consistent T) (hw : ∀ T ∈ cs, T.lits.length ≤ w) :
    (gateDeepSet cs K s).card
      ≤ (Finset.univ.filter (fun σ : Restriction n => SwitchingCounting.stars σ ≤ K - s)).card
        * (2 ^ w) ^ s := by
  refine block_switching_count_tight cs w s K s hcons hw ?_ ?_
  · intro ρ hρ; exact (Finset.mem_filter.mp hρ).2.1
  · intro ρ hρ; exact (Finset.mem_filter.mp hρ).2.2

/-- **Circuit collapse (probabilistic method over the `K`-star shell).**  If the union bound succeeds,
`G · |Short| · (2^w)^s < |Ω| = C(n,K)·2^(n-K)`, then there is a single restriction `ρ` in the `K`-star
shell under which *every* gate's canonical block decision tree is shallow (depth `< s`).  This is the
restriction that drops the circuit's depth by collapsing all bottom gates at once. -/
theorem circuit_collapse_exists (G : ℕ) (gates : Fin G → List (Clause n)) (w K s : ℕ)
    (hcons : ∀ g, ∀ T ∈ gates g, Consistent T)
    (hw : ∀ g, ∀ T ∈ gates g, T.lits.length ≤ w)
    (hbound :
      G * ((Finset.univ.filter (fun σ : Restriction n => SwitchingCounting.stars σ ≤ K - s)).card
            * (2 ^ w) ^ s)
        < n.choose K * 2 ^ (n - K)) :
    ∃ ρ : Restriction n,
      SwitchingCounting.stars ρ = K ∧ ∀ g, (blockStream (gates g) s ρ).length < s := by
  classical
  set Ω : Finset (Restriction n) :=
    Finset.univ.filter (fun ρ => SwitchingCounting.stars ρ = K) with hΩ
  have hΩcard : Ω.card = n.choose K * 2 ^ (n - K) := SwitchingCounting.card_stars_eq K
  have hsum : ∑ g : Fin G, (gateDeepSet (gates g) K s).card < Ω.card := by
    rw [hΩcard]
    calc ∑ g : Fin G, (gateDeepSet (gates g) K s).card
        ≤ ∑ _g : Fin G,
            ((Finset.univ.filter
                (fun σ : Restriction n => SwitchingCounting.stars σ ≤ K - s)).card * (2 ^ w) ^ s) :=
          Finset.sum_le_sum (fun g _ => gateDeepSet_card_le (gates g) w K s (hcons g) (hw g))
      _ = G * ((Finset.univ.filter
                (fun σ : Restriction n => SwitchingCounting.stars σ ≤ K - s)).card * (2 ^ w) ^ s) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ < n.choose K * 2 ^ (n - K) := hbound
  obtain ⟨ρ, hρΩ, hρ⟩ := exists_avoiding_all (fun g => gateDeepSet (gates g) K s) hsum
  have hstarsρ : SwitchingCounting.stars ρ = K := by
    rw [hΩ, Finset.mem_filter] at hρΩ; exact hρΩ.2
  refine ⟨ρ, hstarsρ, fun g => ?_⟩
  have hlen : (blockStream (gates g) s ρ).length ≤ s := blockStream_length_le (gates g) s ρ
  have hne : (blockStream (gates g) s ρ).length ≠ s := by
    intro heq
    exact hρ g (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstarsρ, heq⟩)
  omega

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_avoiding_all
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.gateDeepSet_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.circuit_collapse_exists
