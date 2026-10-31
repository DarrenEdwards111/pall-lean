import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameW2Correspondence

/-!
# N-Frame: Yao bricks 1 — the transformation-monoid substrate for width-2 lower bounds

The dimension-2 super-polynomial rung is a `W2Prog` length bound for majority (Yao's theorem, classically verified).
This file lays its substrate: the **transformation-monoid normal form** of one-bit-register programs — the algebra every
width-2 argument (BDFP, Yao) runs on — plus a first genuine lower bound through the full pipeline.

  `applyChain` / `applyChain_perm_or_const` — **PROVED, the normal form**: a composition of one-bit maps is either a
        parity-of-NOTs *permutation* or a *constant* (the last constant-producing step erases all history before it).
        This is the two-regime structure (`{id, not}` group vs. absorbing constants of the transformation monoid `T₂`)
        that threshold-crossing arguments exploit.
  `w2run_eq_applyChain` — **PROVED**: a program run *is* such a chain, stepwise.
  `w2run_unread` / `exists_unread` — **PROVED**: short programs have unread variables (pigeonhole).
  `foldr_xor_flip` / `parityFn_flip` — **PROVED**: flipping one input flips parity.
  `w2_parity_length` / `w2_parity_volume` — **PROVED, first bound through the pipeline**: any one-bit-register program
        computing parity has length `≥ n`, hence any dimension-≤2 observer computing parity has volume `≥ n` — via
        `w2_lb_transfer`, validating the interface end-to-end.  (Tight-ish: `xorVars` gives `≤ 2n+1` at dimension 2 —
        parity is provably *easy* at dimension 2; the hard function there is majority.)

## Honest scope — the roadmap of the remaining Yao bricks, named

Remaining for the super-polynomial rung (open, research-grade): (Y2) per-step classification against a *fixed* variable
ordering — which steps can produce constants, and at which majority-threshold crossings; (Y3) the counting argument —
majority forces super-polynomially many constant-regime switches (Yao's combinatorics; BDFP's exponential variant may
apply directly to this oblivious subclass); (Y4) the transfer of that count into length.  None of that is here.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

/-! ### The transformation-monoid normal form -/

/-- Apply a chain of one-bit maps in order. -/
def applyChain (ms : List (Bool → Bool)) (r : Bool) : Bool :=
  ms.foldl (fun r m => m r) r

/-- **The normal form (proved)**: a chain of one-bit maps is either a parity-of-NOTs permutation or a constant. -/
theorem applyChain_perm_or_const (ms : List (Bool → Bool)) :
    (∃ p : Bool, ∀ r, applyChain ms r = xor r p) ∨ (∃ c : Bool, ∀ r, applyChain ms r = c) := by
  induction ms with
  | nil =>
    left
    exact ⟨false, fun r => by cases r <;> rfl⟩
  | cons m ms ih =>
    -- classify the head map by its value table
    rcases hft : (m false, m true) with ⟨b0, b1⟩
    have hf : m false = b0 := congrArg Prod.fst hft
    have ht : m true = b1 := congrArg Prod.snd hft
    by_cases hconst : b0 = b1
    · -- constant head: everything after is a fixed chain value
      right
      refine ⟨applyChain ms b0, fun r => ?_⟩
      show applyChain ms (m r) = applyChain ms b0
      cases r
      · rw [hf]
      · rw [ht, ← hconst]
    · -- permutation head: `m r = xor r q` for `q = m false`
      have hm : ∀ r, m r = xor r b0 := by
        intro r
        cases r
        · rw [hf]; cases b0 <;> rfl
        · rw [ht]
          cases hb0 : b0
          · cases hb1 : b1
            · exact absurd (by rw [hb0, hb1]) hconst
            · rfl
          · cases hb1 : b1
            · rfl
            · exact absurd (by rw [hb0, hb1]) hconst
      rcases ih with ⟨p, hp⟩ | ⟨c, hc⟩
      · left
        refine ⟨xor b0 p, fun r => ?_⟩
        show applyChain ms (m r) = xor r (xor b0 p)
        rw [hm r, hp (xor r b0)]
        cases r <;> cases b0 <;> cases p <;> rfl
      · right
        exact ⟨c, fun r => hc (m r)⟩

/-- **A program run is a chain (proved).** -/
theorem w2run_eq_applyChain (p : W2Prog n) (r0 : Bool) (x : Fin n → Bool) :
    w2run p r0 x = applyChain (p.map (fun s r => s.1 r (x s.2))) r0 := by
  unfold w2run applyChain
  rw [List.foldl_map]

/-! ### Unread variables -/

/-- **Unread variables do not matter (proved).** -/
theorem w2run_unread (p : W2Prog n) (v : Fin n) (hv : ∀ s ∈ p, s.2 ≠ v)
    (r0 : Bool) (x : Fin n → Bool) (b : Bool) :
    w2run p r0 (Function.update x v b) = w2run p r0 x := by
  induction p generalizing r0 with
  | nil => rfl
  | cons s p ih =>
    show w2run p (s.1 r0 (Function.update x v b s.2)) _ = w2run p (s.1 r0 (x s.2)) x
    rw [Function.update_of_ne (hv s List.mem_cons_self)]
    exact ih (fun s' hs' => hv s' (List.mem_cons_of_mem _ hs')) _

/-- **Short programs have unread variables (proved, pigeonhole).** -/
theorem exists_unread (p : W2Prog n) (hlen : p.length < n) :
    ∃ v : Fin n, ∀ s ∈ p, s.2 ≠ v := by
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ (p.map Prod.snd).toFinset := by
    intro v _
    obtain ⟨s, hs, hsv⟩ := hcon v
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨s, hs, hsv⟩
  have h1 : n ≤ (p.map Prod.snd).toFinset.card := by
    have := Finset.card_le_card hsub
    simpa using this
  have h2 : (p.map Prod.snd).toFinset.card ≤ p.length := by
    have := (p.map Prod.snd).toFinset_card_le
    rwa [List.length_map] at this
  omega

/-! ### Parity flips under single-bit flips -/

theorem foldr_xor_congr (l : List (Fin n)) (x y : Fin n → Bool)
    (h : ∀ j ∈ l, x j = y j) :
    l.foldr (fun i a => xor (x i) a) false = l.foldr (fun i a => xor (y i) a) false := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show xor (x a) _ = xor (y a) _
    rw [h a List.mem_cons_self, ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]

theorem foldr_xor_flip (l : List (Fin n)) (hnd : l.Nodup) (v : Fin n) (hv : v ∈ l)
    (x : Fin n → Bool) (b : Bool) :
    l.foldr (fun i a => xor (Function.update x v b i) a) false
      = xor (l.foldr (fun i a => xor (x i) a) false) (xor b (x v)) := by
  induction l with
  | nil => exact absurd hv List.not_mem_nil
  | cons a l ih =>
    obtain ⟨hal, hlnd⟩ := List.nodup_cons.mp hnd
    by_cases hav : a = v
    · subst hav
      show xor (Function.update x a b a) _ = _
      rw [Function.update_self]
      have hcongr : l.foldr (fun i acc => xor (Function.update x a b i) acc) false
          = l.foldr (fun i acc => xor (x i) acc) false :=
        foldr_xor_congr l _ x (fun j hj =>
          Function.update_of_ne (fun hja => hal (by rw [← hja]; exact hj)) ..)
      rw [hcongr]
      simp only [List.foldr_cons]
      generalize (l.foldr (fun i acc => xor (x i) acc) false) = F
      cases b <;> cases hx : x a <;> cases F <;> rfl
    · have hvl : v ∈ l := by
        rcases List.mem_cons.mp hv with h | h
        · exact absurd h.symm hav
        · exact h
      show xor (Function.update x v b a) _ = _
      rw [Function.update_of_ne hav, ih hlnd hvl]
      simp only [List.foldr_cons]
      generalize (l.foldr (fun i acc => xor (x i) acc) false) = F
      cases x a <;> cases F <;> cases b <;> cases hx : x v <;> rfl

/-- **Flipping one input flips parity (proved).** -/
theorem parityFn_flip (hn : 0 < n) (x : Fin n → Bool) (v : Fin n) :
    parityFn n (Function.update x v (!x v)) = !(parityFn n x) := by
  show (List.finRange n).foldr (fun i a => xor (Function.update x v (!x v) i) a) false = _
  rw [foldr_xor_flip (List.finRange n) (List.nodup_finRange n) v (List.mem_finRange v) x (!x v)]
  show xor (parityFn n x) (xor (!x v) (x v)) = !(parityFn n x)
  cases parityFn n x <;> cases x v <;> rfl

/-! ### The first bound through the pipeline -/

/-- **Parity needs length `n` (proved)**: every variable must be read. -/
theorem w2_parity_length (hn : 0 < n) (r0 : Bool) (p : W2Prog n)
    (hcomp : ∀ x, w2run p r0 x = parityFn n x) :
    n ≤ p.length := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨v, hv⟩ := exists_unread p hlt
  have h1 := hcomp (fun _ => false)
  have h2 := hcomp (Function.update (fun _ => false) v (!(fun _ : Fin n => false) v))
  rw [w2run_unread p v hv r0 (fun _ => false), h1,
    parityFn_flip hn (fun _ => false) v] at h2
  cases hpar : parityFn n (fun _ => false) <;> rw [hpar] at h2 <;> exact Bool.noConfusion h2

/-- **The first dimension-2 bound through the full pipeline (proved)**: any dimension-≤2 observer computing parity has
volume `≥ n` — `w2_lb_transfer` validated end-to-end.  (Parity is provably *easy* at dimension 2 — `xorVars` gives
`≤ 2n+1` — the super-polynomial target there is majority.) -/
theorem w2_parity_volume (hn : 0 < n) (t : Trans n) (hwidth : width t ≤ 2)
    (hcomp : eval t = parityFn n) :
    n ≤ volume t :=
  w2_lb_transfer hn (parityFn n) n
    (fun r0 p hp => w2_parity_length hn r0 p hp) t hwidth hcomp

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.applyChain_perm_or_const
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.w2_parity_length
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.w2_parity_volume
