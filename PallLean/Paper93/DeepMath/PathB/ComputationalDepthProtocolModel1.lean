import PallLean.Paper93.DeepMath.PathB.ComputationalDepthInfoTheory8

/-!
# Communication protocol model 1: the transcript and the rectangle property

A deterministic two-party communication protocol as a tree: `alice` nodes send a
bit computed from Alice's input, `bob` nodes from Bob's, leaves output a value.
The transcript is the sequence of bits along the path; the output is the leaf.

The KEY structural fact — the **rectangle property** (cut-and-paste): the set of
inputs `(x,y)` producing a given transcript is a combinatorial RECTANGLE.  This is
what makes InfoTheory8 apply (conditioned on the transcript, the inputs are
independent).

* **`Protocol`** — the protocol tree; **`trans`** — the transcript; **`run`** — the
  output;
* **`trans_cutPaste` (proved)** — if `(x,y)` and `(x',y')` share a transcript then
  so does `(x,y')`: the fibers of `trans` are rectangles;
* **`run_eq_of_trans_eq` (proved)** — the transcript determines the output.

This is the deterministic-protocol substrate for the information-cost / round
arguments.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CommProtocol

variable {α β τ : Type*}

/-- A deterministic two-party communication protocol tree. -/
inductive Protocol (α β τ : Type*)
  | leaf (t : τ) : Protocol α β τ
  | alice (f : α → Bool) (l r : Protocol α β τ) : Protocol α β τ
  | bob (g : β → Bool) (l r : Protocol α β τ) : Protocol α β τ

/-- The transcript (sequence of bits sent) on inputs `x, y`. -/
def trans : Protocol α β τ → α → β → List Bool
  | .leaf _, _, _ => []
  | .alice f l r, x, y => f x :: (bif f x then trans r x y else trans l x y)
  | .bob g l r, x, y => g y :: (bif g y then trans r x y else trans l x y)

/-- The output (leaf reached) on inputs `x, y`. -/
def run : Protocol α β τ → α → β → τ
  | .leaf t, _, _ => t
  | .alice f l r, x, y => bif f x then run r x y else run l x y
  | .bob g l r, x, y => bif g y then run r x y else run l x y

/-- **The rectangle property (proved)**: transcript fibers are rectangles.  If
`(x,y)` and `(x',y')` produce the same transcript, so does the "cut-and-paste"
`(x,y')`. -/
theorem trans_cutPaste (P : Protocol α β τ) :
    ∀ (x : α) (y : β) (x' : α) (y' : β),
      trans P x y = trans P x' y' → trans P x y' = trans P x' y' := by
  induction P with
  | leaf t => intro x y x' y' _; rfl
  | alice f l r ihl ihr =>
    intro x y x' y' h
    simp only [trans, List.cons.injEq] at h ⊢
    obtain ⟨hfx, htail⟩ := h
    refine ⟨hfx, ?_⟩
    rw [hfx] at htail ⊢
    cases hv : f x' with
    | false => simp only [hv, cond_false] at htail ⊢; exact ihl x y x' y' htail
    | true => simp only [hv, cond_true] at htail ⊢; exact ihr x y x' y' htail
  | bob g l r ihl ihr =>
    intro x y x' y' h
    simp only [trans, List.cons.injEq] at h ⊢
    obtain ⟨hgy, htail⟩ := h
    refine ⟨trivial, ?_⟩
    rw [hgy] at htail
    cases hv : g y' with
    | false => simp only [hv, cond_false] at htail ⊢; exact ihl x y x' y' htail
    | true => simp only [hv, cond_true] at htail ⊢; exact ihr x y x' y' htail

/-- **The transcript determines the output (proved)**. -/
theorem run_eq_of_trans_eq (P : Protocol α β τ) :
    ∀ (x : α) (y : β) (x' : α) (y' : β),
      trans P x y = trans P x' y' → run P x y = run P x' y' := by
  induction P with
  | leaf t => intro x y x' y' _; rfl
  | alice f l r ihl ihr =>
    intro x y x' y' h
    simp only [trans, List.cons.injEq] at h
    obtain ⟨hfx, htail⟩ := h
    simp only [run]
    rw [hfx] at htail ⊢
    cases hv : f x' with
    | false => simp only [hv, cond_false] at htail ⊢; exact ihl x y x' y' htail
    | true => simp only [hv, cond_true] at htail ⊢; exact ihr x y x' y' htail
  | bob g l r ihl ihr =>
    intro x y x' y' h
    simp only [trans, List.cons.injEq] at h
    obtain ⟨hgy, htail⟩ := h
    simp only [run]
    rw [hgy] at htail ⊢
    cases hv : g y' with
    | false => simp only [hv, cond_false] at htail ⊢; exact ihl x y x' y' htail
    | true => simp only [hv, cond_true] at htail ⊢; exact ihr x y x' y' htail

end PallLean.Paper93.DeepMath.PathB.CommProtocol

#print axioms PallLean.Paper93.DeepMath.PathB.CommProtocol.trans_cutPaste
#print axioms PallLean.Paper93.DeepMath.PathB.CommProtocol.run_eq_of_trans_eq
