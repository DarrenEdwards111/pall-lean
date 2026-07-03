import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameW2YaoBrick3

/-!
# N-Frame: Yao bricks 4 — the per-flip charging certificates

The global threshold-crossing count is the open heart of the rung.  This brick proves the **local mechanism** that count
sums: across a single bit-flip, an output change must be *chargeable* — either the regime class switches, or a step
**reading the flipped variable inside the live region** is responsible.

  `stepActive_flip` / `progPar_congr` — **PROVED**: activation status and parity contributions are local to the read
        variable.
  `stable_split_flip_eq` — **PROVED, certificate A**: if the last-activation split survives a flip at `v` and no step of
        the live region `s :: p₂` reads `v`, the output cannot change (the prefix is already erased; the live region
        reads nothing that moved).
  `crossing_charge_active` — **PROVED, the active charging dichotomy**: an output change across a flip, under a valid
        split for the pre-flip input, forces a **`v`-reading step in the live region** — a chargeable witness.
        (Regime-class switches are covered by the hypothesis: if the split stops being valid, that *is* the class
        switch.)
  `crossing_charge_passive` — **PROVED, the passive charging dichotomy**: from the all-passive regime, an output change
        forces either an **activation birth** (class switch) or a **`v`-reading step** — a chargeable witness.

## Honest scope — what the certificates do and do not give

These are the per-flip charges.  The open content is the **global sum**: over the `C(n, ⌈n/2⌉)`-sized family of
majority-threshold crossings, showing distinct crossings cannot share charges — the fixed read order limits how many
crossings a single step can serve — yielding the super-polynomial length bound (Yao's combinatorics; BDFP's exponential
variant for the restricted class).  That summation is *not* here and is not claimed.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

/-! ### Locality of activation and parity -/

/-- **Activation is local to the read variable (proved)**: a flip elsewhere cannot change a step's status. -/
theorem stepActive_flip (s : (Bool → Bool → Bool) × Fin n) (x : Fin n → Bool)
    (v : Fin n) (b : Bool) (hne : s.2 ≠ v) :
    stepActive s (Function.update x v b) ↔ stepActive s x := by
  unfold stepActive
  rw [Function.update_of_ne hne]

/-- **Parity contributions are local (proved)**: agreeing reads give equal parities. -/
theorem progPar_congr (p : W2Prog n) (x y : Fin n → Bool)
    (h : ∀ s ∈ p, x s.2 = y s.2) :
    progPar p x = progPar p y := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    show xor (s.1 false (x s.2)) (progPar p x) = xor (s.1 false (y s.2)) (progPar p y)
    rw [h s List.mem_cons_self, ih (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))]

/-! ### Certificate A: a stable split with no live reads cannot change the output -/

/-- **Certificate A (proved)**: if the split at the last active step survives the flip and no step of the live region
`s :: p₂` reads `v`, the output is unchanged — the prefix is erased, and the live region reads nothing that moved. -/
theorem stable_split_flip_eq (p₁ : W2Prog n) (s : (Bool → Bool → Bool) × Fin n) (p₂ : W2Prog n)
    (x : Fin n → Bool) (v : Fin n) (b : Bool) (r0 : Bool)
    (hact : stepActive s x) (hpass : ∀ s' ∈ p₂, ¬ stepActive s' x)
    (hnr : ∀ s' ∈ s :: p₂, s'.2 ≠ v) :
    w2run (p₁ ++ s :: p₂) r0 (Function.update x v b) = w2run (p₁ ++ s :: p₂) r0 x := by
  have hact' : stepActive s (Function.update x v b) :=
    (stepActive_flip s x v b (hnr s List.mem_cons_self)).mpr hact
  have hpass' : ∀ s' ∈ p₂, ¬ stepActive s' (Function.update x v b) := by
    intro s' hs'
    rw [stepActive_flip s' x v b (hnr s' (List.mem_cons_of_mem _ hs'))]
    exact hpass s' hs'
  rw [w2run_after_active p₁ s p₂ _ hact' hpass' r0,
    w2run_after_active p₁ s p₂ x hact hpass r0,
    Function.update_of_ne (hnr s List.mem_cons_self),
    progPar_congr p₂ (Function.update x v b) x
      (fun s' hs' => Function.update_of_ne (hnr s' (List.mem_cons_of_mem _ hs')) b x)]

/-! ### The charging dichotomies -/

/-- **The active charging dichotomy (proved)**: an output change across a flip, under a split valid for the pre-flip
input that remains structurally intact, forces a `v`-reading step in the live region — the chargeable witness.  (If the
split does *not* survive, that is the class-switch charge.) -/
theorem crossing_charge_active (p₁ : W2Prog n) (s : (Bool → Bool → Bool) × Fin n)
    (p₂ : W2Prog n) (x : Fin n → Bool) (v : Fin n) (b : Bool) (r0 : Bool)
    (hact : stepActive s x) (hpass : ∀ s' ∈ p₂, ¬ stepActive s' x)
    (hne : w2run (p₁ ++ s :: p₂) r0 (Function.update x v b) ≠ w2run (p₁ ++ s :: p₂) r0 x) :
    ∃ s' ∈ s :: p₂, s'.2 = v := by
  by_contra hcon
  push_neg at hcon
  exact hne (stable_split_flip_eq p₁ s p₂ x v b r0 hact hpass hcon)

/-- **The passive charging dichotomy (proved)**: from the all-passive regime, an output change across a flip forces an
activation birth (the class switch) or a `v`-reading step (the chargeable witness). -/
theorem crossing_charge_passive (p : W2Prog n) (x : Fin n → Bool) (v : Fin n) (b : Bool)
    (r0 : Bool) (hall : ∀ s ∈ p, ¬ stepActive s x)
    (hne : w2run p r0 (Function.update x v b) ≠ w2run p r0 x) :
    (∃ s ∈ p, stepActive s (Function.update x v b)) ∨ ∃ s ∈ p, s.2 = v := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  apply hne
  rw [w2run_allPassive p _ h1 r0, w2run_allPassive p x hall r0,
    progPar_congr p (Function.update x v b) x
      (fun s hs => Function.update_of_ne (h2 s hs) b x)]

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.stable_split_flip_eq
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.crossing_charge_active
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.crossing_charge_passive
