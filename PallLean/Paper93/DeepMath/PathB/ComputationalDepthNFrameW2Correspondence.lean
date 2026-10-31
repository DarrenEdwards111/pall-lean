import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDimOneRung

/-!
# N-Frame: the width-2 correspondence brick — dimension-2 observers are one-bit-register programs

The dimension-2 super-polynomial rung has a verified classical basis (Yao's majority bound for general width-2 branching
programs; BDFP's exponential bound for a restricted class).  This brick builds the bridge those results transfer across:
**every dimension-≤2 boundary observer is a one-bit-register sequential program** — a layered width-2 branching program
in its oblivious form — of length at most its volume.

  `W2Prog` / `w2run` — the one-bit-register program: a sequence of steps `r ← op r (x v)` (all four per-state transition
        patterns expressible — the oblivious layered width-2 BP).
  `width_le_two_bin` — **PROVED, the structural fact**: a dimension-≤2 binary node has at least one dimension-1 child.
  `width_one_form` — **PROVED**: dimension-1 observers compute `h (x v)` — a unary function of one variable.
  `w2_correspondence` — **PROVED, the brick**: every dimension-≤2 observer is computed by a `W2Prog` of length
        `≤ volume` — the embedding is length-faithful.
  `w2_lb_transfer` — **PROVED, the interface**: any length lower bound for one-bit-register programs computing `f`
        transfers verbatim to a volume lower bound at dimension 2.

So the dimension-2 rung's future content — the Yao-type super-polynomial length bound for majority — is now a statement
purely about `W2Prog`, and `w2_lb_transfer` carries it into the boundary model the moment it is proved.

## Honest scope

The embedding and transfer are complete; the Yao-side length bound itself is **not** proved here — it is the named,
classically-verified, research-grade target of the coming sessions.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

/-! ### The one-bit-register program (oblivious layered width-2 BP) -/

/-- A one-bit-register program: each step reads one variable and updates `r ← op r (x v)`. -/
abbrev W2Prog (n : ℕ) := List ((Bool → Bool → Bool) × Fin n)

/-- Run a program from initial register `r0`. -/
def w2run (p : W2Prog n) (r0 : Bool) (x : Fin n → Bool) : Bool :=
  p.foldl (fun r s => s.1 r (x s.2)) r0

theorem w2run_append (p q : W2Prog n) (r0 : Bool) (x : Fin n → Bool) :
    w2run (p ++ q) r0 x = w2run q (w2run p r0 x) x :=
  List.foldl_append ..

/-! ### Structure of dimension-≤2 observers -/

/-- **A dimension-≤2 binary node has a dimension-1 child (proved)** — and both children are dimension-≤2. -/
theorem width_le_two_bin (op : Bool → Bool → Bool) (t₁ t₂ : Trans n)
    (h : width (Trans.bin op t₁ t₂) ≤ 2) :
    width t₁ ≤ 2 ∧ width t₂ ≤ 2 ∧ (width t₁ = 1 ∨ width t₂ = 1) := by
  have hp₁ := width_pos t₁
  have hp₂ := width_pos t₂
  have hw : width (Trans.bin op t₁ t₂)
      = (if width t₁ = width t₂ then width t₁ + 1 else max (width t₁) (width t₂)) := rfl
  rw [hw] at h
  revert h
  split <;> omega

/-- **Dimension-1 observers compute `h (x v)` (proved)**: a unary function of one variable. -/
theorem width_one_form (hn : 0 < n) (t : Trans n) (h1 : width t = 1) :
    ∃ (v : Fin n) (h : Bool → Bool), ∀ x, eval t x = h (x v) := by
  obtain ⟨w, hw⟩ := width_one_junta t h1
  cases w with
  | none =>
    exact ⟨⟨0, hn⟩, fun _ => eval t (fun _ => false),
      fun x => hw x (fun _ => false) (fun j hj => nomatch hj)⟩
  | some v =>
    refine ⟨v, fun b => eval t (Function.update (fun _ => false) v b), fun x => ?_⟩
    apply hw
    intro j hj
    have hjv : j = v := (Option.some_injective _ hj).symm
    subst hjv
    rw [Function.update_self]

/-! ### The correspondence -/

/-- **The correspondence brick (proved)**: every dimension-≤2 observer is computed by a one-bit-register program of
length at most its volume. -/
theorem w2_correspondence (hn : 0 < n) :
    ∀ t : Trans n, width t ≤ 2 →
      ∃ (r0 : Bool) (p : W2Prog n), p.length ≤ volume t ∧ ∀ x, w2run p r0 x = eval t x := by
  intro t
  induction t with
  | var i =>
    intro _
    exact ⟨false, [(fun _ b => b, i)], le_refl 1, fun x => rfl⟩
  | cst b =>
    intro _
    exact ⟨b, [], by simp [volume], fun x => rfl⟩
  | un op t ih =>
    intro hw
    obtain ⟨r0, p, hlen, hrun⟩ := ih (by
      have : width (Trans.un op t) = width t := rfl
      omega)
    refine ⟨r0, p ++ [(fun r _ => op r, ⟨0, hn⟩)], ?_, fun x => ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil, volume]
      omega
    · rw [w2run_append]
      show op (w2run p r0 x) = op (eval t x)
      rw [hrun x]
  | bin op t₁ t₂ ih₁ ih₂ =>
    intro hw
    obtain ⟨hw₁, hw₂, hone⟩ := width_le_two_bin op t₁ t₂ hw
    have hvol₁ := volume_pos t₁
    have hvol₂ := volume_pos t₂
    rcases hone with h1 | h1
    · -- t₁ is the one-variable side: compute t₂ first, then fold t₁'s value in
      obtain ⟨v, h, hform⟩ := width_one_form hn t₁ h1
      obtain ⟨r0, p, hlen, hrun⟩ := ih₂ hw₂
      refine ⟨r0, p ++ [(fun r b => op (h b) r, v)], ?_, fun x => ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil, volume]
        omega
      · rw [w2run_append]
        show op (h (x v)) (w2run p r0 x) = op (eval t₁ x) (eval t₂ x)
        rw [hrun x, hform x]
    · -- t₂ is the one-variable side: compute t₁ first, then fold t₂'s value in
      obtain ⟨v, h, hform⟩ := width_one_form hn t₂ h1
      obtain ⟨r0, p, hlen, hrun⟩ := ih₁ hw₁
      refine ⟨r0, p ++ [(fun r b => op r (h b), v)], ?_, fun x => ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil, volume]
        omega
      · rw [w2run_append]
        show op (w2run p r0 x) (h (x v)) = op (eval t₁ x) (eval t₂ x)
        rw [hrun x, hform x]

/-- **The transfer interface (proved)**: a length lower bound for one-bit-register programs computing `f` is a volume
lower bound at dimension 2.  The future Yao-type majority bound plugs in here. -/
theorem w2_lb_transfer (hn : 0 < n) (f : (Fin n → Bool) → Bool) (L : ℕ)
    (hlb : ∀ (r0 : Bool) (p : W2Prog n), (∀ x, w2run p r0 x = f x) → L ≤ p.length)
    (t : Trans n) (hwidth : width t ≤ 2) (hcomp : eval t = f) :
    L ≤ volume t := by
  obtain ⟨r0, p, hlen, hrun⟩ := w2_correspondence hn t hwidth
  have := hlb r0 p (fun x => by rw [hrun x, hcomp])
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.width_le_two_bin
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.w2_correspondence
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.w2_lb_transfer
