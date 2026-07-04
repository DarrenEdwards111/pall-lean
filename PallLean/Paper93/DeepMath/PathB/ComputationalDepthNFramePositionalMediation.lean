import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMediationCounting

/-!
# N-Frame: positional information flow — the two-party split, and the xor no-go

The last door, surveyed with theorems.  In the trichotomy's mediation branch the factorization has a
*position*: the mediating bit is computed at wire `r` from the cone below it, and only then may the `i`-free
context act.  That is a genuine two-party communication structure — and this file both formalizes it and
proves the sharpest reason it is hard to use:

  `mediation_positional` — **PROVED, the split**: single-reader mediation refines to
        `f x = G (h x) x` with `G` insensitive to `xᵢ` **and** `h` local to the variables read inside
        `coneOf c r` — bottom party computes one bit from the cone, top party finishes without `xᵢ`.
  `coneVars_card_le` — **PROVED, the positional bound**: the bottom party reads at most `r + 1` variables —
        early mediators are information-starved.
  `xor_mediates_pair` — **PROVED, the local no-go**: for **every** Boolean function, `xᵢ` is 1-bit mediated
        by `xᵢ ⊕ xⱼ` — the context undoes the xor from `xⱼ`.  So the mediation factorization cannot be
        refuted per-variable or per-pair for *any* target: two selectors can always share one xor wire.

## Honest scope

The split is the correct interface, and the xor no-go fixes its strength exactly: any refutation of branch
three must charge the **aggregate** — many selectors against the total wire budget, using bottom-locality and
position, not local behavior at one or two variables.  That aggregate information accounting is the open wall,
shared with the classical field.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The xor no-go: mediation cannot be refuted locally -/

/-- **THE XOR NO-GO (proved)**: for every Boolean function, `xᵢ` is 1-bit mediated by the single value
`xᵢ ⊕ xⱼ` — the `i`-free context recovers `xᵢ` by undoing the xor with `xⱼ`.  Mediation is unrefutable
per-variable and per-pair. -/
theorem xor_mediates_pair {n : ℕ} (f : (Fin n → Bool) → Bool) (i₁ i₂ : Fin n)
    (hne : i₂ ≠ i₁) :
    ∃ G : Bool → (Fin n → Bool) → Bool,
      (∀ x, f x = G (xor (x i₁) (x i₂)) x) ∧
      (∀ (v : Bool) (x : Fin n → Bool) (b' : Bool),
        G v (Function.update x i₁ b') = G v x) := by
  refine ⟨fun v x => f (Function.update x i₁ (xor v (x i₂))), ?_, ?_⟩
  · intro x
    show f x = f (Function.update x i₁ (xor (xor (x i₁) (x i₂)) (x i₂)))
    have h1 : xor (xor (x i₁) (x i₂)) (x i₂) = x i₁ := by
      cases hx1 : x i₁ <;> cases hx2 : x i₂ <;> rfl
    rw [h1, Function.update_eq_self]
  · intro v x b'
    show f (Function.update (Function.update x i₁ b') i₁
        (xor v ((Function.update x i₁ b') i₂)))
      = f (Function.update x i₁ (xor v (x i₂)))
    rw [Function.update_idem, Function.update_of_ne hne]

/-! ### The positional split -/

/-- **THE TWO-PARTY SPLIT (proved)**: single-reader mediation with the bottom party made explicit — the
mediating bit is local to the variables read inside the reader's cone. -/
theorem mediation_positional {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n)
    (c : List (CGate n)) (hcomp : computes c f)
    (p r : ℕ) (hpg : c.getD p (CGate.cst false) = CGate.var i)
    (hU : ∀ q, c.getD q (CGate.cst false) = CGate.var i → q = p)
    (hpr : p ∈ childrenOf c r) (hrint : r < c.length - 1)
    (hRuniq : ∀ r', p ∈ childrenOf c r' → r' = r) :
    ∃ G : Bool → (Fin n → Bool) → Bool,
      (∀ x, f x = G ((runFrom x [] c).getD r false) x) ∧
      (∀ (v : Bool) (x : Fin n → Bool) (b' : Bool),
        G v (Function.update x i b') = G v x) ∧
      (∀ x x' : Fin n → Bool,
        (∀ i' : Fin n, (∃ q ∈ coneOf c r, c.getD q (CGate.cst false) = CGate.var i') →
          x i' = x' i') →
        (runFrom x [] c).getD r false = (runFrom x' [] c).getD r false) := by
  obtain ⟨G, hG1, hG2⟩ := mediation_of_single_reader f i c hcomp p r hpg hU hpr hrint hRuniq
  refine ⟨G, hG1, hG2, ?_⟩
  intro x x' hagree
  exact cone_val_agree c r x x'
    (fun q hq i' hgate => hagree i' ⟨q, hq, hgate⟩) r (cone_self c r)

/-- **THE POSITIONAL BOUND (proved)**: the bottom party reads at most `r + 1` variables — a mediator at
position `r` is computed from an `(r+1)`-wire prefix. -/
theorem coneVars_card_le {n : ℕ} (c : List (CGate n)) (r : ℕ) :
    ∀ (V : Finset (Fin n)),
      (∀ i' ∈ V, ∃ q ∈ coneOf c r, c.getD q (CGate.cst false) = CGate.var i') →
      V.card ≤ r + 1 := by
  classical
  intro V hV
  set pos : Fin n → ℕ := fun i' =>
    if h : ∃ q ∈ coneOf c r, c.getD q (CGate.cst false) = CGate.var i'
    then h.choose else 0 with hposdef
  have hposmem : ∀ i' ∈ V, pos i' ∈ coneOf c r ∧
      c.getD (pos i') (CGate.cst false) = CGate.var i' := by
    intro i' hi'
    have h := hV i' hi'
    have hp : pos i' = h.choose := by
      rw [hposdef]
      exact dif_pos h
    rw [hp]
    exact ⟨h.choose_spec.1, h.choose_spec.2⟩
  have hmaps : ∀ i' ∈ V, pos i' ∈ Finset.range (r + 1) := by
    intro i' hi'
    rw [Finset.mem_range]
    have h := cone_le c r (pos i') (hposmem i' hi').1
    omega
  have hinj : Set.InjOn pos ↑V := by
    intro a ha a' ha' hEq
    obtain ⟨-, hg⟩ := hposmem a (Finset.mem_coe.mp ha)
    obtain ⟨-, hg'⟩ := hposmem a' (Finset.mem_coe.mp ha')
    rw [hEq] at hg
    exact CGate.var.inj (hg.symm.trans hg')
  have hcard : V.card ≤ (Finset.range (r + 1)).card :=
    Finset.card_le_card_of_injOn pos
      (fun i' hi' => Finset.mem_coe.mpr (hmaps i' (Finset.mem_coe.mp hi'))) hinj
  rw [Finset.card_range] at hcard
  exact hcard

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.xor_mediates_pair
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.mediation_positional
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.coneVars_card_le
