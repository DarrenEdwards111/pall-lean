import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATSubsetCut
import Mathlib.Data.Fintype.Basic

/-!
# The nested-case `(a,a,c)` no-factorization crux (kernel-verified, axiom-free)

Nested two-wire brick 11b — the load-bearing Boolean obstruction for the *resistant*
`(a,a,c)` sign profile of the nested case (`reconvR c = {u,v}`, `Reach c u v`).

In the `(a,a,c)` shape two sign gates are below the outer wire `u` only (`a`), one is
below **both** wires (`c`).  Sub-case **β** (a `v`-reader lies outside the `u`-prefix,
so that prefix is read-once) forces the circuit output, as a function of the three sign
bits, into the shape
```
    Φ ( op ( w , h(...) ) , g(r) )
```
where the outer wire `op(w, h(...))` **splits** at one sign `w ∈ {p,q,r}` (the split
theorem `gtree_split_cnt`), and `g(r)` is a `c`-only side channel (`r` = the `c` sign,
the only sign below the inner wire `v`).  The gadget must nonetheless equal
`allEq3 = (·==·) && (·==·)` on the reachable set.

**The crux — verified here — is that this is impossible**: for *every* choice of the
combiners `Φ, op, h : Bool → Bool → Bool` and `g : Bool → Bool`, and for *every* split
position, there is a triple on which the β-shape disagrees with `allEq3`.  The three
theorems cover the three split positions (`p`, `q`, `r`); each is a `decide` over the
`4+4+4+2 = 14` defining Bool-values of the combiners (`16384` combiner choices), so the
statements are **kernel-checked and depend on no axioms at all** — not even `propext`.

This is exactly the pure-Boolean claim flagged *unverified* in the campaign log; it is
now discharged **true**, so the β horn of the `(a,a,c)` kill has a sound foundation.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- A binary Bool combiner, encoded by its four values `a_{xy}`. -/
@[inline] def ap2 (a00 a01 a10 a11 x y : Bool) : Bool :=
  cond x (cond y a11 a10) (cond y a01 a00)

/-- A unary Bool combiner, encoded by its two values `b_x`. -/
@[inline] def ap1 (b0 b1 x : Bool) : Bool := cond x b1 b0

/-- **β-form, split at the first `a`-sign `p` (proved, axiom-free).**  The outer wire is
`op(p, h(q,r))`; `allEq3` is not `Φ` of it with a `c`-only side channel `g(r)`. -/
theorem aac_beta_no_factor_split_p :
    ∀ (F0 F1 F2 F3 o0 o1 o2 o3 h0 h1 h2 h3 g0 g1 : Bool),
      ∃ p q r, allEq3 p q r ≠
        ap2 F0 F1 F2 F3 (ap2 o0 o1 o2 o3 p (ap2 h0 h1 h2 h3 q r)) (ap1 g0 g1 r) := by
  decide

/-- **β-form, split at the second `a`-sign `q` (proved, axiom-free).**  Symmetric to the
`p` split; the outer wire is `op(q, h(p,r))`. -/
theorem aac_beta_no_factor_split_q :
    ∀ (F0 F1 F2 F3 o0 o1 o2 o3 h0 h1 h2 h3 g0 g1 : Bool),
      ∃ p q r, allEq3 p q r ≠
        ap2 F0 F1 F2 F3 (ap2 o0 o1 o2 o3 q (ap2 h0 h1 h2 h3 p r)) (ap1 g0 g1 r) := by
  decide

/-- **β-form, split at the `c`-sign `r` (proved, axiom-free).**  Here `r` (the `c` sign)
enters the outer wire `op(r, h(p,q))` *and* the side channel `g(r)`; still no `allEq3`. -/
theorem aac_beta_no_factor_split_r :
    ∀ (F0 F1 F2 F3 o0 o1 o2 o3 h0 h1 h2 h3 g0 g1 : Bool),
      ∃ p q r, allEq3 p q r ≠
        ap2 F0 F1 F2 F3 (ap2 o0 o1 o2 o3 r (ap2 h0 h1 h2 h3 p q)) (ap1 g0 g1 r) := by
  decide

/-! ### Consumable `→ False` forms

The circuit β analysis produces the factorisation as an equality between the gadget's
reachable-set output (`= allEq3`) and a *general* `Bool → Bool → Bool` combiner form
`Φ (op (w) (h …)) (g r)`.  The `decide` crux above is stated over the four *defining
Bool-values* of each combiner; the two η-lemmas turn any concrete combiner into that
form, so the crux discharges the general statement.  These `_contra` lemmas are the exact
interface the `(a,a,c)` β kill will call: hand it the structural equality, get `False`. -/

/-- A binary Bool function is its own four-value `ap2` reconstruction. -/
theorem ap2_eta (f : Bool → Bool → Bool) (x y : Bool) :
    f x y = ap2 (f false false) (f false true) (f true false) (f true true) x y := by
  cases x <;> cases y <;> rfl

/-- A unary Bool function is its own two-value `ap1` reconstruction. -/
theorem ap1_eta (g : Bool → Bool) (x : Bool) : g x = ap1 (g false) (g true) x := by
  cases x <;> rfl

/-- **β-kill interface, split at `p` (proved).**  If the gadget output factors as
`Φ(op(p, h(q,r)), g(r))` on all sign triples while equalling `allEq3`, that is a
contradiction. -/
theorem aac_beta_no_factor_split_p_contra
    (Φ op h : Bool → Bool → Bool) (g : Bool → Bool)
    (hF : ∀ p q r, allEq3 p q r = Φ (op p (h q r)) (g r)) : False := by
  obtain ⟨p, q, r, hne⟩ := aac_beta_no_factor_split_p
    (Φ false false) (Φ false true) (Φ true false) (Φ true true)
    (op false false) (op false true) (op true false) (op true true)
    (h false false) (h false true) (h true false) (h true true)
    (g false) (g true)
  apply hne
  rw [hF p q r, ap2_eta Φ (op p (h q r)) (g r), ap2_eta op p (h q r),
    ap2_eta h q r, ap1_eta g r]

/-- **β-kill interface, split at `q` (proved).** -/
theorem aac_beta_no_factor_split_q_contra
    (Φ op h : Bool → Bool → Bool) (g : Bool → Bool)
    (hF : ∀ p q r, allEq3 p q r = Φ (op q (h p r)) (g r)) : False := by
  obtain ⟨p, q, r, hne⟩ := aac_beta_no_factor_split_q
    (Φ false false) (Φ false true) (Φ true false) (Φ true true)
    (op false false) (op false true) (op true false) (op true true)
    (h false false) (h false true) (h true false) (h true true)
    (g false) (g true)
  apply hne
  rw [hF p q r, ap2_eta Φ (op q (h p r)) (g r), ap2_eta op q (h p r),
    ap2_eta h p r, ap1_eta g r]

/-- **β-kill interface, split at `r` (the `c`-sign) (proved).** -/
theorem aac_beta_no_factor_split_r_contra
    (Φ op h : Bool → Bool → Bool) (g : Bool → Bool)
    (hF : ∀ p q r, allEq3 p q r = Φ (op r (h p q)) (g r)) : False := by
  obtain ⟨p, q, r, hne⟩ := aac_beta_no_factor_split_r
    (Φ false false) (Φ false true) (Φ true false) (Φ true true)
    (op false false) (op false true) (op true false) (op true true)
    (h false false) (h false true) (h true false) (h true true)
    (g false) (g true)
  apply hne
  rw [hF p q r, ap2_eta Φ (op r (h p q)) (g r), ap2_eta op r (h p q),
    ap2_eta h p q, ap1_eta g r]

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.aac_beta_no_factor_split_p
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.aac_beta_no_factor_split_q
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.aac_beta_no_factor_split_r
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.aac_beta_no_factor_split_p_contra
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.aac_beta_no_factor_split_r_contra
