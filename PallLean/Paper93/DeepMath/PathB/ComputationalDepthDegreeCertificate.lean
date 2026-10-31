import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWireDegreeBound

/-!
# A difference certificate for the log lower bound

`WireDegreeBound.nlCount_ge_of_degree` turns "high degree" into "many nonlinear gates".  This file
supplies the concrete way to witness high degree: a **nonzero iterated finite difference**.  If the
`(2^m + 1)`-fold difference of a circuit's output is nonzero at some point, the circuit has more than
`m` nonlinear gates.

* **`iterDelta`** — apply the finite difference `Delta` once per direction in a list.
* **`iterDelta_isDegLe_zero` (proved)** — degree `≤ m` forces every `(m+1)`-fold difference to vanish.
* **`highDegree_needs_nonlinear` (proved)** — a nonzero `(2^m+1)`-fold difference of `output c`
  certifies `m < nlCount c`.

**Honest scope.**  This is the certificate side of the log bound.  Instantiating it needs a function
with a genuinely nonzero high-order difference (`DegreeCertificateAnd` does this for the AND family).
The bound remains logarithmic in the degree.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DegreeCertificate

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.DegreeCalculus
open PallLean.Paper93.DeepMath.PathB.WireDegreeBound

variable {n : ℕ}

/-- Apply `Delta` once per direction in `ds`. -/
def iterDelta : List (Fin n → Bool) → ((Fin n → Bool) → Bool) → ((Fin n → Bool) → Bool)
  | [], F => F
  | a :: ds, F => iterDelta ds (Delta a F)

/-- **Degree ≤ m forces every (m+1)-fold difference to vanish (proved).** -/
theorem iterDelta_isDegLe_zero : ∀ (m : ℕ) (F : (Fin n → Bool) → Bool), IsDegLe m F →
    ∀ (ds : List (Fin n → Bool)), ds.length = m + 1 → iterDelta ds F = fun _ => false := by
  intro m
  induction m with
  | zero =>
    intro F hF ds hds
    cases ds with
    | nil => simp at hds
    | cons a ds' =>
      have hnil : ds' = [] := by
        cases ds' with
        | nil => rfl
        | cons => simp at hds
      subst hnil
      funext x
      simp only [iterDelta, Delta]
      rw [hF x (fun i => Bool.xor (x i) (a i))]
      exact Bool.xor_self _
  | succ m ih =>
    intro F hF ds hds
    cases ds with
    | nil => simp at hds
    | cons a ds' =>
      have hlen : ds'.length = m + 1 := by simpa using hds
      simp only [iterDelta]
      exact ih (Delta a F) (hF a) ds' hlen

/-- **A nonzero high-order difference certifies many nonlinear gates (proved).**  If the `(2^m+1)`-fold
finite difference of `output c` is nonzero somewhere, then `c` has more than `m` nonlinear gates. -/
theorem highDegree_needs_nonlinear (c : List (CGate n)) (m : ℕ) (ds : List (Fin n → Bool))
    (x : Fin n → Bool) (hlen : ds.length = 2 ^ m + 1) (hcert : iterDelta ds (output c) x = true) :
    m < nlCount c := by
  apply nlCount_ge_of_degree c m
  intro hdeg
  have hzero := iterDelta_isDegLe_zero (2 ^ m) (output c) hdeg ds hlen
  rw [hzero] at hcert
  simp at hcert

end PallLean.Paper93.DeepMath.PathB.DegreeCertificate

#print axioms PallLean.Paper93.DeepMath.PathB.DegreeCertificate.iterDelta_isDegLe_zero
#print axioms PallLean.Paper93.DeepMath.PathB.DegreeCertificate.highDegree_needs_nonlinear
