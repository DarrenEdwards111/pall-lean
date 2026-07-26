import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementRuler

/-!
# The ⊕-mixture adversary: per-gate semantic demands cannot exceed the floor

An honest NO-GO, machine-checked.  The `EntangledTower` interface demands, per witness gate,
nonlinearity on the served block's private territory.  This file shows that demand — and with it
EVERY demand of per-gate shape — is defeated by an explicit adversary: the **⊕-mixture**

  `mixFn x = ⊕ᵢ (x_{2i} ∧ x_{2i+1})`  (parity of one AND per private territory).

Fixing everything outside block `i`'s territory strips the other AND terms to a constant, so the
restriction is `(u₀ ∧ u₁) ⊕ c` — non-affine.  Hence ONE wire is a legitimate semantic witness for
EVERY block at once, and `b` copies of it satisfy every field of the tower with `|gates| = b`,
independent of `k`.

## What is proved

* **`mixTower`** — the adversary IS a valid `EntangledTower k b (2k)`, for ALL `k, b` (general
  proof, no `decide` over the blocks: fold-evaluation lemma + explicit non-affineness triple).
* **`mixTower_gates_card`** — its gate count is exactly `b`.
* **`per_gate_demand_ceiling`** — THE PIN, a meta-theorem over the interface: any lower bound
  valid for ALL `EntangledTower k b (2k)` is `≤ b`.  The `k`-multiplier is not open at this
  granularity — it is UNREACHABLE.
* **`k_multiplier_unreachable`** — the same, pointed: for `k ≥ 2` the disjoint bound `k·b`
  provably FAILS on a valid semantic tower.

## Honest reading — what this forces

The ⊕-mixture is the SEMANTIC Uhlig: it shows mass production survives per-gate nonlinearity
demands verbatim.  So "demand generation" — the residue of the whole localization arc — cannot
mean any per-gate property.  It must mean **family independence**: a collective property of the
`b` witnesses of a block, within that block, that `b` fixed global mixtures cannot satisfy for
all `k` blocks simultaneously.  And the known family-level measures are exactly the capped ones
(linear-algebraic independence = rank; derivative independence = degree, log-capped by
`AndPeeling`).  This brick does not cross anything; it closes the per-gate door PROVABLY, so the
search is aimed at the only door left.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MixtureAdversary

open PallLean.Paper93.DeepMath.PathB.AffineSemantics
open PallLean.Paper93.DeepMath.PathB.WitnessLocalization
open PallLean.Paper93.DeepMath.PathB.EntanglementRuler

variable {k : ℕ}

/-- The first variable of block `i`'s territory. -/
def idx0 (i : Fin k) : Fin (2 * k) := ⟨2 * i.val, by have := i.isLt; omega⟩

/-- The second variable of block `i`'s territory. -/
def idx1 (i : Fin k) : Fin (2 * k) := ⟨2 * i.val + 1, by have := i.isLt; omega⟩

/-- Block `i`'s private territory: `{2i, 2i+1}` (as the mask `v/2 = i`). -/
def mixMask (i : Fin k) : Fin (2 * k) → Bool := fun v => decide (v.val / 2 = i.val)

/-- One AND per territory. -/
def pairAnd (w : Fin (2 * k) → Bool) (j : Fin k) : Bool :=
  Bool.and (w (idx0 j)) (w (idx1 j))

/-- **The ⊕-mixture**: parity of the per-territory ANDs — one wire touching every block. -/
def mixFn (w : Fin (2 * k) → Bool) : Bool :=
  ((List.finRange k).map (pairAnd w)).foldr Bool.xor false

/-! ### Fold evaluation -/

theorem foldr_xor_all_false {α : Type} (f : α → Bool) :
    ∀ l : List α, (∀ j ∈ l, f j = false) → (l.map f).foldr Bool.xor false = false := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    show Bool.xor (f a) ((l.map f).foldr Bool.xor false) = false
    rw [h a (by simp), ih (fun j hj => h j (by simp [hj]))]
    rfl

/-- Folding XOR over a list where exactly one element contributes. -/
theorem foldr_xor_eq_single {α : Type} (i : α) (t : Bool) (f : α → Bool)
    (hoff : ∀ j, j ≠ i → f j = false) (hon : f i = t) :
    ∀ l : List α, l.Nodup → i ∈ l → (l.map f).foldr Bool.xor false = t := by
  intro l
  induction l with
  | nil => intro _ hmem; cases hmem
  | cons a l ih =>
    intro hnodup hmem
    by_cases hai : a = i
    · subst hai
      have hnotin : a ∉ l := (List.nodup_cons.mp hnodup).1
      have htail : (l.map f).foldr Bool.xor false = false :=
        foldr_xor_all_false f l (fun j hj => hoff j (fun hji => hnotin (hji ▸ hj)))
      show Bool.xor (f a) ((l.map f).foldr Bool.xor false) = t
      rw [htail, hon]
      exact Bool.xor_false t
    · have hmem' : i ∈ l := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm hai
        · exact h
      show Bool.xor (f a) ((l.map f).foldr Bool.xor false) = t
      rw [hoff a hai, ih (List.nodup_cons.mp hnodup).2 hmem']
      exact Bool.false_xor t

/-- **Restriction evaluation (proved, general `k`).**  Gluing `false` outside block `i`'s
territory strips every other AND term: the restriction of the mixture is exactly block `i`'s
AND. -/
theorem mix_restrict (i : Fin k) (u : Fin (2 * k) → Bool) :
    mixFn (glue (mixMask i) (fun _ => false) u)
      = Bool.and (u (idx0 i)) (u (idx1 i)) := by
  show ((List.finRange k).map (pairAnd (glue (mixMask i) (fun _ => false) u))).foldr
      Bool.xor false = _
  apply foldr_xor_eq_single i _ _ ?hoff ?hon (List.finRange k)
    (List.nodup_finRange k) (List.mem_finRange i)
  case hoff =>
    intro j hji
    have h0 : mixMask i (idx0 j) = false := by
      apply decide_eq_false
      intro hc
      exact hji (Fin.ext (by
        have hc' : (2 * j.val) / 2 = i.val := hc
        omega))
    show Bool.and (glue (mixMask i) (fun _ => false) u (idx0 j))
        (glue (mixMask i) (fun _ => false) u (idx1 j)) = false
    simp [glue, h0]
  case hon =>
    have h0 : mixMask i (idx0 i) = true := by
      apply decide_eq_true
      show (2 * i.val) / 2 = i.val
      omega
    have h1 : mixMask i (idx1 i) = true := by
      apply decide_eq_true
      show (2 * i.val + 1) / 2 = i.val
      omega
    show Bool.and (glue (mixMask i) (fun _ => false) u (idx0 i))
        (glue (mixMask i) (fun _ => false) u (idx1 i)) = _
    simp [glue, h0, h1]

/-- A two-variable AND on distinct coordinates is not affine (explicit triple). -/
theorem and_pair_not_affine {n : ℕ} (p q : Fin n) (hpq : p ≠ q) :
    ¬ IsAffineFn (fun u : Fin n → Bool => Bool.and (u p) (u q)) := by
  intro haff
  have h := haff (fun _ => true) (fun v => if v = p then true else false)
    (fun v => if v = q then true else false)
  simp [hpq, Ne.symm hpq] at h

/-! ### The adversary tower -/

/-- **The ⊕-mixture adversary (proved, all `k, b`).**  `b` copies of the mixture wire satisfy
every field of the semantic tower — each is a legitimate witness for EVERY block — with
`|gates| = b`, independent of `k`. -/
def mixTower (k b : ℕ) : EntangledTower k b (2 * k) where
  gates := Finset.range b
  wireFn := fun _ => mixFn
  privMask := mixMask
  priv_disjoint := by
    intro i j hij v hv
    have h1 : v.val / 2 = i.val := of_decide_eq_true hv
    apply decide_eq_false
    intro h2
    exact hij (Fin.ext (by omega))
  witness := fun _ => Finset.range b
  wit_sub := fun _ => Finset.Subset.refl _
  wit_size := fun _ => le_of_eq (Finset.card_range b).symm
  wit_semantic := by
    intro i g _
    refine ⟨fun _ => false, fun haff => ?_⟩
    rw [show (fun u => mixFn (glue (mixMask i) (fun _ => false) u))
        = (fun u => Bool.and (u (idx0 i)) (u (idx1 i))) from funext (mix_restrict i)] at haff
    exact and_pair_not_affine (idx0 i) (idx1 i)
      (Fin.ne_of_val_ne (by show 2 * i.val ≠ 2 * i.val + 1; omega)) haff

/-- The adversary's gate count is exactly `b`. -/
theorem mixTower_gates_card (k b : ℕ) : (mixTower k b).gates.card = b :=
  Finset.card_range b

/-- **THE PIN (proved).**  Any lower bound valid for ALL semantic towers at layout `(k, b, 2k)`
is at most `b`: per-gate semantic demands cannot exceed the floor.  The `k`-multiplier is not
open at this granularity — it is unreachable. -/
theorem per_gate_demand_ceiling (k b bound : ℕ)
    (h : ∀ C : EntangledTower k b (2 * k), bound ≤ C.gates.card) : bound ≤ b := by
  have hb := h (mixTower k b)
  rwa [mixTower_gates_card] at hb

/-- The disjoint bound `k·b` FAILS on a valid semantic tower whenever `k ≥ 2, b ≥ 1`. -/
theorem k_multiplier_unreachable (k b : ℕ) (hk : 2 ≤ k) (hb : 1 ≤ b) :
    ∃ C : EntangledTower k b (2 * k), C.gates.card < k * b :=
  ⟨mixTower k b, by
    rw [mixTower_gates_card]
    have h2 : 2 * b ≤ k * b := Nat.mul_le_mul_right b hk
    omega⟩

end PallLean.Paper93.DeepMath.PathB.MixtureAdversary

#print axioms PallLean.Paper93.DeepMath.PathB.MixtureAdversary.mix_restrict
#print axioms PallLean.Paper93.DeepMath.PathB.MixtureAdversary.mixTower_gates_card
#print axioms PallLean.Paper93.DeepMath.PathB.MixtureAdversary.per_gate_demand_ceiling
#print axioms PallLean.Paper93.DeepMath.PathB.MixtureAdversary.k_multiplier_unreachable
