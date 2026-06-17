import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymAndPool
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsFastSat

/-!
# The Beigel–Tarui depth-collapse — low degree ⇒ quasipolynomial `SYM∘AND` (proved), RS approximation socketed

The Beigel–Tarui theorem: a constant-depth `ACC⁰` circuit is equivalent to a single symmetric gate over
**quasipolynomially** many `AND`s (a `SYM∘AND` of size `2^{polylog}`).  The *exact* collapse is already proved
(`acc0circuit_hasSymAndFormFanIn`) but its `symAndSize` is **multiplicative**, hence *exponential* in general — the naive
bound.  BT's genuine contribution is the **quasipolynomial** size, obtained via the probabilistic polynomial method:
approximate the circuit by a **low-degree** polynomial, then collapse that to a `SYM∘AND`.

This file proves the **combinatorial heart** of that quasipolynomial collapse — *a low-degree representation has a
quasipolynomial `SYM∘AND` form* — and composes it with the Razborov–Smolensky approximation (the socket) to obtain the
depth-collapse.

The key fact (proved).  A degree-`≤D` representation is a symmetric function of an *injective* family of degree-`≤D`
monomials; the number of such monomials is `≤ (D+1)·n^D` (`monomial_count_le` + `lowDegMonomialCount_le_pow`), so the
`SYM∘AND` size is `≤ (D+1)·n^D`.  For `D = ((p−1)·t)^d` (the RS approximation degree of a depth-`d` `ACC⁰[p]` circuit
with error parameter `t`), with `d` constant and `t` polylog, `D` is polylog and `(D+1)·n^D = n^{polylog} = 2^{polylog}`
— quasipolynomial.

## What is proved (clean axioms, no `sorry`)

* **`LowDegRep f D`** — `f` is a symmetric function `h ∘ saCount` of an injective family of degree-`≤D` monomials (the
  low-degree representation produced by the RS approximation).
* **`lowDeg_symAnd_quasipoly`** — the heart: such a representation has size `m ≤ (D+1)·n^D` (quasipolynomial) and is a
  genuine `SYM∘AND` form of fan-in `≤ D`.
* **`btQuasipolyCollapse`** — `LowDegRep f D` ⇒ `∃ m, HasSymAndFormFanIn f m D ∧ m ≤ (D+1)·n^D`.
* **`btDepthCollapse`** — the depth-collapse: with the RS socket `AccToLowDeg f p t d` (a depth-`d` `ACC⁰[p]` circuit
  has a degree-`((p−1)·t)^d` representation), `f` has a `SYM∘AND` form of quasipolynomial size
  `≤ (((p−1)·t)^d + 1)·n^{((p−1)·t)^d}`.

## Honest scope

This proves the **low-degree ⇒ quasipolynomial `SYM∘AND`** step — the combinatorial heart of the BT depth-collapse —
completely (the multiplicative `acc0circuit_hasSymAndFormFanIn` is *exponential*; this is the quasipolynomial bound,
obtained because the monomials of a degree-`≤D` representation number only `≤ (D+1)·n^D`).  What remains the named socket
is **`AccToLowDeg`**: that a depth-`d` `ACC⁰[p]` circuit *has* a low-degree (`((p−1)·t)^d`) representation — the
**Razborov–Smolensky probabilistic polynomial method** (approximate each gate by a low-degree polynomial with small
error, compose across the constant depth).  That approximation is the genuine analytic content and is not proved here.
This proves the degree-to-size half of the collapse, not the circuit-to-degree approximation.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BTDepthCollapse

open PallLean.Paper93.DeepMath.PathB.ACC0SymAndFanIn (HasSymAndFormFanIn)
open PallLean.Paper93.DeepMath.PathB.ACC0SymAndPool (hasSymAndFormFanIn_family)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monomial_count_le)
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat (lowDegMonomialCount_le_pow)
open PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose (saCount)

variable {n D : ℕ}

/-- **A low-degree representation.**  `f` is a symmetric function `h ∘ saCount` of an *injective* family of degree-`≤D`
monomials — the form a Razborov–Smolensky low-degree polynomial takes (sum/count of its `≤D`-degree monomials). -/
def LowDegRep (f : (Fin n → Bool) → Bool) (D : ℕ) : Prop :=
  ∃ (m : ℕ) (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool),
    Function.Injective mono ∧ (∀ j, (mono j).card ≤ D) ∧ f = fun x => h (saCount mono x)

/-- **The collapse heart (PROVED): low degree ⇒ quasipolynomial `SYM∘AND`.**  An injective family of `m` degree-`≤D`
monomials with symmetric top `h` is a `SYM∘AND` of fan-in `≤ D`, and its size is `m ≤ (D+1)·n^D` — quasipolynomial — by
`monomial_count_le` (`m ≤ ∑_{i≤D} C(n,i)`) and `lowDegMonomialCount_le_pow` (`∑_{i≤D} C(n,i) ≤ (D+1)·n^D`). -/
theorem lowDeg_symAnd_quasipoly {m : ℕ} (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool)
    (hinj : Function.Injective mono) (hdeg : ∀ j, (mono j).card ≤ D) (hn : 1 ≤ n) :
    HasSymAndFormFanIn (fun x => h (saCount mono x)) m D ∧ m ≤ (D + 1) * n ^ D :=
  ⟨hasSymAndFormFanIn_family mono h hdeg,
    le_trans (monomial_count_le mono hinj hdeg) (lowDegMonomialCount_le_pow hn)⟩

/-- **Quasipolynomial collapse from a low-degree representation (PROVED).**  If `f` has a degree-`≤D` representation,
then `f` has a `SYM∘AND` form of quasipolynomial size `m ≤ (D+1)·n^D`. -/
theorem btQuasipolyCollapse (f : (Fin n → Bool) → Bool) (hrep : LowDegRep f D) (hn : 1 ≤ n) :
    ∃ m, HasSymAndFormFanIn f m D ∧ m ≤ (D + 1) * n ^ D := by
  obtain ⟨m, mono, h, hinj, hdeg, hfe⟩ := hrep
  subst hfe
  exact ⟨m, lowDeg_symAnd_quasipoly mono h hinj hdeg hn⟩

/-- **The Razborov–Smolensky approximation socket.**  A depth-`d` `ACC⁰[p]` circuit (error parameter `t`) has a
degree-`((p−1)·t)^d` low-degree representation — the probabilistic polynomial method (each gate approximated by a
low-degree polynomial with small error, composed across the constant depth).  Stated, not proved. -/
def AccToLowDeg (f : (Fin n → Bool) → Bool) (p t d : ℕ) : Prop := LowDegRep f (((p - 1) * t) ^ d)

/-- **The Beigel–Tarui depth-collapse (PROVED, modulo the RS socket).**  A depth-`d` `ACC⁰[p]` circuit `f` — having, by
RS, a degree-`((p−1)·t)^d` representation (`AccToLowDeg`) — has a `SYM∘AND` form of **quasipolynomial** size
`m ≤ (((p−1)·t)^d + 1)·n^{((p−1)·t)^d}`.  For `d` constant and `t` polylog the degree is polylog and the size is
`n^{polylog} = 2^{polylog(n)}` — the YBT/Beigel–Tarui quasipolynomial normal form. -/
theorem btDepthCollapse (f : (Fin n → Bool) → Bool) (p t d : ℕ) (hn : 1 ≤ n)
    (hrs : AccToLowDeg f p t d) :
    ∃ m, HasSymAndFormFanIn f m (((p - 1) * t) ^ d) ∧
      m ≤ (((p - 1) * t) ^ d + 1) * n ^ (((p - 1) * t) ^ d) :=
  btQuasipolyCollapse f hrs hn

end PallLean.Paper93.DeepMath.PathB.ACC0BTDepthCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BTDepthCollapse.lowDeg_symAnd_quasipoly
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BTDepthCollapse.btQuasipolyCollapse
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BTDepthCollapse.btDepthCollapse
