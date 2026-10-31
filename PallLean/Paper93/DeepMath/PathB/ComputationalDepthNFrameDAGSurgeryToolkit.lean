import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDAGConnectivity

/-!
# N-Frame: the semantic surgery toolkit — unary elimination, gate replacement, and the minimal-circuit normal form

Entry into Schnorr/Stockmeyer territory needs surgeries that act on what gates *compute*, not just where they
sit.  This file builds them and lands the first structural consequence:

  `elimUnGate` / `computes_elim_un` — **PROVED, the second surgery**: an interior unary gate is deleted by
        *composing its operation into every reader* — either operand position, double reads included — and
        redirecting them to its source wire, through arbitrary fan-out.
  `computes_congr_at` — **PROVED**: a gate may be replaced by any gate agreeing on the actual prefix values —
        the tool that turns garbage-reading gates into constants.
  `shrink_of_cst_mem` — **PROVED**: a circuit for a non-constant function shrinks below any constant gate it
        contains — position-free, because a non-constant function's output gate is never a constant.
  `minimal_no_cst` / `minimal_un_last` — **PROVED, the normal form**: a minimal circuit for a non-constant
        function contains **no constant gate at all**, and every unary gate it contains is the output — the
        interior of a minimal DAG observer is pure `var`/`bin`.

## Honest scope

These are the load-bearing rewrites of classical gate elimination, formalized sharing-aware; the normal form is
their first structural dividend.  The numerical dividend — the semantic DAG two-kill under `¬TopDecomp` and the
Schnorr-style case analyses past the `2·m·D − 1` connectivity record — is the next file's work, and the genuine
`2.5n`/`3n` frontier beyond is named, not claimed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Positional helpers -/

theorem take_len {n : ℕ} (c : List (CGate n)) (p : ℕ) (hp : p ≤ c.length) :
    (c.take p).length = p := by
  rw [List.length_take]
  omega

theorem getD_map_lt {n : ℕ} (c : List (CGate n)) (σ : CGate n → CGate n) (p : ℕ)
    (hp : p < c.length) :
    (c.map σ).getD p (CGate.cst false) = σ (c.getD p (CGate.cst false)) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hp]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
  rfl

/-- Split a circuit at a known position. -/
theorem circuit_split_at {n : ℕ} (c : List (CGate n)) (p : ℕ) (hp : p < c.length) :
    c = c.take p ++ c.getD p (CGate.cst false) :: c.drop (p + 1) := by
  conv_lhs => rw [← List.take_append_drop p c]
  congr 1
  rw [List.drop_eq_getElem_cons hp]
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
  rfl

theorem output_of_last_cst {n : ℕ} (c₁ : List (CGate n)) (b : Bool) (x : Fin n → Bool) :
    output (c₁ ++ [CGate.cst b]) x = b := by
  show (runFrom x [] (c₁ ++ [CGate.cst b])).getD
      ((c₁ ++ [CGate.cst b]).length - 1) false = b
  rw [runFrom_append]
  show ((runFrom x [] c₁) ++ [evalGate x (runFrom x [] c₁) (CGate.cst b)]).getD
      ((c₁ ++ [CGate.cst b]).length - 1) false = b
  have hV : (runFrom x [] c₁).length = c₁.length := by
    rw [runFrom_length]
    simp
  rw [show (c₁ ++ [(CGate.cst b : CGate n)]).length - 1 = (runFrom x [] c₁).length by
    rw [List.length_append, hV]
    show c₁.length + 1 - 1 = c₁.length
    omega]
  exact getD_concat _ _

/-! ### Gate replacement at a position -/

/-- **Gate replacement (proved)**: a gate may be replaced by any gate agreeing on the actual prefix values. -/
theorem computes_congr_at {n : ℕ} (c₁ : List (CGate n)) (g g' : CGate n)
    (c₂ : List (CGate n)) (f : (Fin n → Bool) → Bool)
    (heq : ∀ x, evalGate x (runFrom x [] c₁) g = evalGate x (runFrom x [] c₁) g')
    (hcomp : computes (c₁ ++ g :: c₂) f) : computes (c₁ ++ g' :: c₂) f := by
  intro x
  have hrun : runFrom x [] (c₁ ++ g' :: c₂) = runFrom x [] (c₁ ++ g :: c₂) := by
    rw [show c₁ ++ g' :: c₂ = (c₁ ++ [g']) ++ c₂ by simp,
      show c₁ ++ g :: c₂ = (c₁ ++ [g]) ++ c₂ by simp,
      runFrom_append x [] (c₁ ++ [g']) c₂, runFrom_append x [] c₁ [g'],
      runFrom_append x [] (c₁ ++ [g]) c₂, runFrom_append x [] c₁ [g]]
    show runFrom x (runFrom x [] c₁ ++ [evalGate x (runFrom x [] c₁) g']) c₂
        = runFrom x (runFrom x [] c₁ ++ [evalGate x (runFrom x [] c₁) g]) c₂
    rw [heq x]
  show (runFrom x [] (c₁ ++ g' :: c₂)).getD ((c₁ ++ g' :: c₂).length - 1) false = f x
  rw [hrun, show (c₁ ++ g' :: c₂).length = (c₁ ++ g :: c₂).length by
    rw [List.length_append, List.length_append, List.length_cons, List.length_cons]]
  exact hcomp x

/-! ### The unary elimination surgery -/

/-- Rewire one gate after deleting the unary wire `p = un u w`: readers compose `u` and redirect to `w` — in
either operand position, double reads included — and later references shift down. -/
def elimUnGate {n : ℕ} (p : ℕ) (u : Bool → Bool) (w : ℕ) : CGate n → CGate n
  | .var i => .var i
  | .cst c => .cst c
  | .un op j => if j = p then .un (fun a => op (u a)) (elimRef p w)
      else .un op (elimRef p j)
  | .bin op j k =>
      if j = p then
        (if k = p then .bin (fun a c => op (u a) (u c)) (elimRef p w) (elimRef p w)
         else .bin (fun a c => op (u a) c) (elimRef p w) (elimRef p k))
      else if k = p then .bin (fun a c => op a (u c)) (elimRef p j) (elimRef p w)
      else .bin op (elimRef p j) (elimRef p k)

theorem evalGate_elimUn {n : ℕ} (x : Fin n → Bool) (vals : List Bool) (p : ℕ)
    (u : Bool → Bool) (w : ℕ) (hw : w ≠ p)
    (hp : vals.getD p false = u (vals.getD w false)) (g : CGate n) :
    evalGate x (vals.eraseIdx p) (elimUnGate p u w g) = evalGate x vals g := by
  cases g with
  | var i => rfl
  | cst c => rfl
  | un op j =>
    show evalGate x (vals.eraseIdx p)
        (if j = p then CGate.un (fun a => op (u a)) (elimRef p w)
         else CGate.un op (elimRef p j))
        = op (vals.getD j false)
    by_cases hj : j = p
    · rw [if_pos hj]
      show op (u ((vals.eraseIdx p).getD (elimRef p w) false)) = op (vals.getD j false)
      rw [getD_eraseIdx_elimRef vals p w hw, hj, hp]
    · rw [if_neg hj]
      show op ((vals.eraseIdx p).getD (elimRef p j) false) = op (vals.getD j false)
      rw [getD_eraseIdx_elimRef vals p j hj]
  | bin op j k =>
    show evalGate x (vals.eraseIdx p)
        (if j = p then
          (if k = p then CGate.bin (fun a c => op (u a) (u c)) (elimRef p w) (elimRef p w)
           else CGate.bin (fun a c => op (u a) c) (elimRef p w) (elimRef p k))
         else if k = p then CGate.bin (fun a c => op a (u c)) (elimRef p j) (elimRef p w)
         else CGate.bin op (elimRef p j) (elimRef p k))
        = op (vals.getD j false) (vals.getD k false)
    by_cases hj : j = p
    · by_cases hk : k = p
      · rw [if_pos hj, if_pos hk]
        show op (u ((vals.eraseIdx p).getD (elimRef p w) false))
            (u ((vals.eraseIdx p).getD (elimRef p w) false))
            = op (vals.getD j false) (vals.getD k false)
        rw [getD_eraseIdx_elimRef vals p w hw, hj, hk, hp]
      · rw [if_pos hj, if_neg hk]
        show op (u ((vals.eraseIdx p).getD (elimRef p w) false))
            ((vals.eraseIdx p).getD (elimRef p k) false)
            = op (vals.getD j false) (vals.getD k false)
        rw [getD_eraseIdx_elimRef vals p w hw, getD_eraseIdx_elimRef vals p k hk, hj, hp]
    · by_cases hk : k = p
      · rw [if_neg hj, if_pos hk]
        show op ((vals.eraseIdx p).getD (elimRef p j) false)
            (u ((vals.eraseIdx p).getD (elimRef p w) false))
            = op (vals.getD j false) (vals.getD k false)
        rw [getD_eraseIdx_elimRef vals p w hw, getD_eraseIdx_elimRef vals p j hj, hk, hp]
      · rw [if_neg hj, if_neg hk]
        show op ((vals.eraseIdx p).getD (elimRef p j) false)
            ((vals.eraseIdx p).getD (elimRef p k) false)
            = op (vals.getD j false) (vals.getD k false)
        rw [getD_eraseIdx_elimRef vals p j hj, getD_eraseIdx_elimRef vals p k hk]

theorem runFrom_elimUn {n : ℕ} (x : Fin n → Bool) (p : ℕ) (u : Bool → Bool) (w : ℕ)
    (hwp : w < p) :
    ∀ (gs : List (CGate n)) (vals : List Bool), p < vals.length →
      vals.getD p false = u (vals.getD w false) →
      runFrom x (vals.eraseIdx p) (gs.map (elimUnGate p u w))
        = (runFrom x vals gs).eraseIdx p := by
  intro gs
  induction gs with
  | nil => intro vals _ _; rfl
  | cons g rest ih =>
    intro vals hp hval
    show runFrom x (vals.eraseIdx p ++ [evalGate x (vals.eraseIdx p) (elimUnGate p u w g)])
        (rest.map (elimUnGate p u w))
        = (runFrom x (vals ++ [evalGate x vals g]) rest).eraseIdx p
    rw [evalGate_elimUn x vals p u w (by omega) hval g]
    rw [← List.eraseIdx_append_of_lt_length hp [evalGate x vals g]]
    exact ih (vals ++ [evalGate x vals g])
      (by rw [List.length_append]; show p < vals.length + 1; omega)
      (by
        rw [List.getD_append vals [evalGate x vals g] false p hp,
          List.getD_append vals [evalGate x vals g] false w (by omega)]
        exact hval)

/-- **The unary surgery (proved)**: an interior unary gate with an in-range source is deleted — every reader
composes its operation and redirects to the source, through arbitrary fan-out. -/
theorem computes_elim_un {n : ℕ} (c₁ c₂ : List (CGate n)) (u : Bool → Bool) (w : ℕ)
    (f : (Fin n → Bool) → Bool)
    (hcomp : computes (c₁ ++ CGate.un u w :: c₂) f) (hw : w < c₁.length) (hne : c₂ ≠ []) :
    computes (c₁ ++ c₂.map (elimUnGate c₁.length u w)) f := by
  have hc2 : 1 ≤ c₂.length := by
    cases c₂ with
    | nil => exact absurd rfl hne
    | cons g rest => show 1 ≤ rest.length + 1; omega
  intro x
  have hx := hcomp x
  have hV : (runFrom x [] c₁).length = c₁.length := by
    rw [runFrom_length]
    simp
  set v₀ : Bool := evalGate x (runFrom x [] c₁) (CGate.un u w) with hv₀
  have hsplit : runFrom x [] (c₁ ++ CGate.un u w :: c₂)
      = runFrom x (runFrom x [] c₁ ++ [v₀]) c₂ := by
    rw [show c₁ ++ CGate.un u w :: c₂ = (c₁ ++ [CGate.un u w]) ++ c₂ by simp,
      runFrom_append, runFrom_append]
    rfl
  have hVe : (runFrom x [] c₁ ++ [v₀]).eraseIdx c₁.length = runFrom x [] c₁ := by
    rw [List.eraseIdx_append_of_length_le (le_of_eq hV) [v₀]]
    rw [show c₁.length - (runFrom x [] c₁).length = 0 by omega]
    rw [show ([v₀] : List Bool).eraseIdx 0 = ([] : List Bool) from rfl, List.append_nil]
  have hval : (runFrom x [] c₁ ++ [v₀]).getD c₁.length false
      = u ((runFrom x [] c₁ ++ [v₀]).getD w false) := by
    rw [show c₁.length = (runFrom x [] c₁).length from hV.symm, getD_concat]
    rw [List.getD_append (runFrom x [] c₁) [v₀] false w (by omega)]
    rfl
  have hnew : runFrom x (runFrom x [] c₁) (c₂.map (elimUnGate c₁.length u w))
      = (runFrom x (runFrom x [] c₁ ++ [v₀]) c₂).eraseIdx c₁.length := by
    have h1 := runFrom_elimUn x c₁.length u w hw c₂ (runFrom x [] c₁ ++ [v₀])
      (by rw [List.length_append, hV]; show c₁.length < c₁.length + 1; omega) hval
    rw [hVe] at h1
    exact h1
  show (runFrom x [] (c₁ ++ c₂.map (elimUnGate c₁.length u w))).getD
      ((c₁ ++ c₂.map (elimUnGate c₁.length u w)).length - 1) false = f x
  rw [runFrom_append, hnew]
  rw [show (c₁ ++ c₂.map (elimUnGate c₁.length u w)).length = c₁.length + c₂.length by
    rw [List.length_append, List.length_map]]
  rw [getD_eraseIdx_ge _ c₁.length (c₁.length + c₂.length - 1) (by omega)]
  rw [show c₁.length + c₂.length - 1 + 1 = c₁.length + c₂.length by omega]
  have hxold : (runFrom x (runFrom x [] c₁ ++ [v₀]) c₂).getD
      ((c₁ ++ CGate.un u w :: c₂).length - 1) false = f x := by
    rw [← hsplit]
    exact hx
  rw [show (c₁ ++ CGate.un u w :: c₂).length - 1 = c₁.length + c₂.length by
    rw [List.length_append, List.length_cons]; omega] at hxold
  exact hxold

/-! ### The position-free shrink and the normal form -/

/-- **The constant shrink (proved)**: a circuit for a non-constant function shrinks below any constant gate it
contains — the output gate of a non-constant function is never a constant, so the split is always interior. -/
theorem shrink_of_cst_mem {n : ℕ} (d : List (CGate n)) (f' : (Fin n → Bool) → Bool)
    (b : Bool) (hcomp : computes d f') (hmem : CGate.cst b ∈ d)
    (hnc : ∃ u w : Fin n → Bool, f' u ≠ f' w) :
    ∃ d' : List (CGate n), computes d' f' ∧ d'.length + 1 = d.length := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hmem
  cases t with
  | nil =>
    exfalso
    obtain ⟨u, w, hne⟩ := hnc
    apply hne
    rw [← hcomp u, ← hcomp w]
    show output (s ++ [CGate.cst b]) u = output (s ++ [CGate.cst b]) w
    rw [output_of_last_cst, output_of_last_cst]
  | cons g rest =>
    refine ⟨s ++ (g :: rest).map (elimGate s.length b),
      computes_elim s (g :: rest) b f' hcomp (List.cons_ne_nil g rest), ?_⟩
    rw [List.length_append, List.length_map, List.length_append, List.length_cons,
      List.length_cons, List.length_cons]
    omega

/-- **Normal form I (proved)**: a minimal circuit for a non-constant function contains no constant gate. -/
theorem minimal_no_cst {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hmin : c.length = cbudget f)
    (hnc : ∃ u w : Fin n → Bool, f u ≠ f w) (b : Bool) : CGate.cst b ∉ c := by
  intro hmem
  obtain ⟨d', hd', hlen⟩ := shrink_of_cst_mem c f b hcomp hmem hnc
  have hb : cbudget f ≤ d'.length := Nat.sInf_le ⟨d', hd', rfl⟩
  omega

/-- **Normal form II (proved)**: in a minimal circuit for a non-constant function, every unary gate is the
output — the interior is pure `var`/`bin`. -/
theorem minimal_un_last {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hmin : c.length = cbudget f)
    (hnc : ∃ u w : Fin n → Bool, f u ≠ f w) (p : ℕ) (u : Bool → Bool) (w : ℕ)
    (hg : c.getD p (CGate.cst false) = CGate.un u w) (hp : p < c.length) :
    p = c.length - 1 := by
  by_contra hplast
  have hpint : p < c.length - 1 := by omega
  have hsplit := circuit_split_at c p hp
  rw [hg] at hsplit
  have htlen : (c.take p).length = p := take_len c p (by omega)
  have hdne : c.drop (p + 1) ≠ [] := by
    intro hcon
    have h := congrArg List.length hcon
    rw [List.length_drop] at h
    simp at h
    omega
  by_cases hw : w < p
  · -- in-range source: the unary surgery kills it
    have hcomp' : computes (c.take p ++ CGate.un u w :: c.drop (p + 1)) f := by
      rw [← hsplit]
      exact hcomp
    have hres := computes_elim_un (c.take p) (c.drop (p + 1)) u w f hcomp'
      (by omega) hdne
    have hb : cbudget f ≤ (c.take p ++ (c.drop (p + 1)).map
        (elimUnGate (c.take p).length u w)).length := Nat.sInf_le ⟨_, hres, rfl⟩
    rw [List.length_append, List.length_map, List.length_drop, htlen] at hb
    omega
  · -- garbage source: the gate is a constant in disguise
    have hcomp' : computes (c.take p ++ CGate.un u w :: c.drop (p + 1)) f := by
      rw [← hsplit]
      exact hcomp
    have hrep := computes_congr_at (c.take p) (CGate.un u w) (CGate.cst (u false))
      (c.drop (p + 1)) f (by
        intro x
        show u ((runFrom x [] (c.take p)).getD w false) = u false
        rw [List.getD_eq_default _ false (by
          rw [runFrom_length x (c.take p) []]
          show ([] : List Bool).length + (c.take p).length ≤ w
          simp only [List.length_nil]
          omega)]) hcomp'
    obtain ⟨d', hd', hlen⟩ := shrink_of_cst_mem _ f (u false) hrep (by
      apply List.mem_append_right
      exact List.mem_cons_self) hnc
    have hb : cbudget f ≤ d'.length := Nat.sInf_le ⟨d', hd', rfl⟩
    rw [List.length_append, List.length_cons, List.length_drop, htlen] at hlen
    omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.computes_congr_at
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.computes_elim_un
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.shrink_of_cst_mem
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.minimal_no_cst
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.minimal_un_last
