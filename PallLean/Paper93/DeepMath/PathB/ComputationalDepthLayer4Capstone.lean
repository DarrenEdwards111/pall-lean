import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Assembly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Approx
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Bridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Intersection
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4RootOfUnity

/-!
# Layer 4 (Route A) — the assembled general-`q` separation

The final parameter thread, wiring every Layer-4 piece into the end-to-end statement.

* **`qary_full_contradiction`** — the thread: from the `q` residue-indicator approximants (functions `g, A`
  with degree bound `Δ`, agreement `eval (g j) = modIndicator j` on `A j`, and the tight complement
  `4q·|(A j)ᶜ| ≤ 2ⁿ`), plus the band-margin window, derive `False`.  Chains
  `weightChar_repr_of_indicators` (the `hg` for the contradiction) + `inter_three_quarters` (the common
  `(3/4)`-set `G = ⋂ⱼ A j`) + `qary_contradiction`.

* **`exists_tight_indicator_approximant`** — produces one such approximant from an indicator-computing
  `AC⁰[p]` circuit: `exists_tight_agreement_set` (tight) + base change along `φ : ZMod p → K`, with
  `hCind` turning `boolToField (C.eval ·)` into `modIndicator`.

* **`mod_q_indicators_false`** — the assembled separation over `K = F_{p^{q-1}}` (`p ≠ q` prime): there is
  **no** family of `q` circuits `C_0,…,C_{q-1}` on `2m+1` inputs such that each `C_j` computes the residue
  indicator `[#ones ≡ j (mod q)]`, is `AC⁰[p]`, has `4q·#subcircuits ≤ p^t` and `depth ≤ d`, with the
  band-margin window `16·((p-1)t)^{2d} < 2m+3`.  Since `C_0` computes `[#ones ≡ 0] = MOD_q`, this is the
  general-`q` Razborov–Smolensky lower bound: the `MOD_q` residue indicators cannot be jointly computed by
  small constant-depth `AC⁰[p]` circuits in the band-margin window.  Proof: choose the primitive `q`-th
  root `ζ ∈ F_{p^{q-1}}` (`exists_primitiveRoot_galoisField`); for each `j < q` extract the tight indicator
  approximant (`exists_tight_indicator_approximant`, with `hmod` from `hmod_of_isAC0p` and degree `≤ Δ =
  ((p-1)t)^d` via `hdepth`); skolemise to functions `g, A`; apply `qary_full_contradiction`.

A literal `MOD_q ∈ AC⁰[p]` family produces the `C_j` by padding (`padTrue` of the `MOD_q` circuit:
`padTrue_computes_indicator` ⇒ `hCind`, `padTrue_isAC0pSyntax` ⇒ `hAC`, `padTrue_depth` ⇒ `hdepth`); the
one extra bookkeeping step is bounding `#subcircuits (padTrue D)` for `ht`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer4

open Finset MvPolynomial
open Layer3 (toAgree oracleOf boolToZMod subcircuits toAgree_totalDegree_le)

/-- **The final thread.**  From the `q` tight residue-indicator approximants (`g, A`) and the band-margin
window, derive `False` (via `weightChar_repr_of_indicators` + `inter_three_quarters` +
`qary_contradiction`). -/
theorem qary_full_contradiction (K : Type*) [Field K] {ζ : K} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    {q m Δ : ℕ} (hq : 0 < q) (hζq : ζ ^ q = 1)
    (g : ℕ → MvPolynomial (Fin (2 * m + 1)) K) (A : ℕ → Finset (Fin (2 * m + 1) → Bool))
    (hpdeg : ∀ j, (g j).totalDegree ≤ Δ)
    (hp : ∀ j ∈ Finset.range q, ∀ x ∈ A j,
      eval (fun i => boolToField K (x i)) (g j) = modIndicator K q j x)
    (htight : ∀ j ∈ Finset.range q, 4 * q * (Finset.univ \ A j).card ≤ 2 ^ (2 * m + 1))
    (hwindow : 16 * Δ ^ 2 < 2 * m + 3) : False := by
  obtain ⟨G0, hG0deg, hG0eval⟩ := weightChar_repr_of_indicators K hζq hq Δ g A hpdeg hp
  exact qary_contradiction K hζ0 hζ1 ((Finset.range q).inf A) G0 hG0deg
    (fun x hx => hG0eval x (fun j hj => (Finset.mem_inf.mp hx) j hj)) hwindow
    (inter_three_quarters q hq A htight)

open Classical in
/-- **Tight indicator approximant.**  An `AC⁰[p]` circuit computing `[#ones ≡ j]` yields, over `K` (via any
ring hom `φ : ZMod p → K`), a degree-`≤((p-1)t)^{depth}` approximant equal to `modIndicator K q j` on a set
`G` with the tight complement bound `4q·|Gᶜ| ≤ 2ⁿ`. -/
theorem exists_tight_indicator_approximant (p t q j : ℕ) [Fact p.Prime] {K : Type*} [Field K]
    (φ : ZMod p →+* K) {m : ℕ} (C : BoolCircuitSyntax (2 * m + 1))
    (hmod : ∀ a r cs, (BoolCircuitSyntax.modGate a r cs : BoolCircuitSyntax (2 * m + 1)) ∈ subcircuits C → a = p)
    (ht1 : 1 ≤ t) (ht : 4 * q * (subcircuits C).toFinset.card ≤ p ^ t)
    (hCind : ∀ x : Fin (2 * m + 1) → Bool,
      C.eval x = decide ((Finset.univ.filter (fun i => x i = true)).card % q = j)) :
    ∃ (g : MvPolynomial (Fin (2 * m + 1)) K) (G : Finset (Fin (2 * m + 1) → Bool)),
      4 * q * (Finset.univ \ G).card ≤ 2 ^ (2 * m + 1) ∧ g.totalDegree ≤ ((p - 1) * t) ^ C.depth ∧
      ∀ x ∈ G, eval (fun i => boolToField K (x i)) g = modIndicator K q j x := by
  obtain ⟨ω, hω⟩ := exists_tight_agreement_set p t q C hmod ht
  refine ⟨MvPolynomial.map φ (toAgree p t (oracleOf p t C ω) C),
    Finset.univ.filter (fun x : Fin (2 * m + 1) → Bool =>
      eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C) = boolToZMod p (C.eval x)),
    ?_, le_trans (totalDegree_map_le φ _) (toAgree_totalDegree_le p t ht1 _ C), ?_⟩
  · rw [← Finset.filter_not]; exact hω
  · intro x hx
    rw [Finset.mem_filter] at hx
    have hpt : (fun i => boolToField K (x i)) = (fun i => φ (boolToZMod p (x i))) := by
      funext i; cases x i <;> simp [boolToField, boolToZMod]
    rw [hpt, eval_map_comm, hx.2, hCind x, boolToZMod]
    simp only [modIndicator, apply_ite φ, map_one, map_zero, decide_eq_true_eq]

open Classical in
/-- **The assembled general-`q` separation.**  For distinct primes `p ≠ q`, over `K = F_{p^{q-1}}`: no
family of `q` circuits `C_0,…,C_{q-1}` on `2m+1` inputs can have every `C_j` compute the residue indicator
`[#ones ≡ j (mod q)]`, be `AC⁰[p]`, satisfy `4q·#subcircuits ≤ p^t` and `depth ≤ d`, within the
band-margin window `16·((p-1)t)^{2d} < 2m+3`.  (Razborov–Smolensky, general `q`: `MOD_q = [#ones ≡ 0]` is
`C_0`.) -/
theorem mod_q_indicators_false (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    {m t d : ℕ} (ht1 : 1 ≤ t) (hpt1 : 1 ≤ (p - 1) * t)
    (C : ℕ → BoolCircuitSyntax (2 * m + 1))
    (hCind : ∀ j ∈ Finset.range q, ∀ x : Fin (2 * m + 1) → Bool,
      (C j).eval x = decide ((Finset.univ.filter (fun i => x i = true)).card % q = j))
    (hAC : ∀ j ∈ Finset.range q, BoolCircuitSyntax.IsAC0pSyntax p (C j))
    (ht : ∀ j ∈ Finset.range q, 4 * q * (subcircuits (C j)).toFinset.card ≤ p ^ t)
    (hdepth : ∀ j ∈ Finset.range q, (C j).depth ≤ d)
    (hwindow : 16 * (((p - 1) * t) ^ d) ^ 2 < 2 * m + 3) : False := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_galoisField hpq
  let K := GaloisField p (q - 1)
  let φ : ZMod p →+* K := algebraMap (ZMod p) K
  have hq : 0 < q := (Fact.out (p := q.Prime)).pos
  have hζq : ζ ^ q = 1 := hζ.pow_eq_one
  have hζ0 : ζ ≠ 0 := fun h => by simp [h, zero_pow hq.ne'] at hζq
  have hζ1 : ζ ≠ 1 := hζ.ne_one (Fact.out (p := q.Prime)).one_lt
  have hex : ∀ j, ∃ gG : MvPolynomial (Fin (2 * m + 1)) K × Finset (Fin (2 * m + 1) → Bool),
      gG.1.totalDegree ≤ ((p - 1) * t) ^ d ∧ (j ∈ Finset.range q →
        4 * q * (Finset.univ \ gG.2).card ≤ 2 ^ (2 * m + 1) ∧
        ∀ x ∈ gG.2, eval (fun i => boolToField K (x i)) gG.1 = modIndicator K q j x) := by
    intro j
    by_cases hj : j ∈ Finset.range q
    · obtain ⟨g, G, htb, hgd, hge⟩ := exists_tight_indicator_approximant p t q j φ (C j)
        (hmod_of_isAC0p (C j) (hAC j hj)) ht1 (ht j hj) (hCind j hj)
      exact ⟨(g, G), le_trans hgd (Nat.pow_le_pow_right hpt1 (hdepth j hj)), fun _ => ⟨htb, hge⟩⟩
    · exact ⟨(0, Finset.univ), by simp, fun h => absurd h hj⟩
  choose gG hgG using hex
  exact qary_full_contradiction K hζ0 hζ1 hq hζq (fun j => (gG j).1) (fun j => (gG j).2)
    (fun j => (hgG j).1) (fun j hj => ((hgG j).2 hj).2) (fun j hj => ((hgG j).2 hj).1) hwindow

end PallLean.Paper93.DeepMath.PathB.Layer4

#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.qary_full_contradiction
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.mod_q_indicators_false
