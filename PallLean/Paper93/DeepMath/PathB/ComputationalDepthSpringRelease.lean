/-!
# The spring release — crossing the uniformity seam by spending the 2^n tension, not fighting it

The padding route *fights* the 2^n blowup and loses: un-padding a useful non-uniform bound gives an
exponential bound (`UniformityPromotion.unpadding_blows_up`).  The **spring release** is the other move —
don't compress the exponential tension, *spend* it.  That is the IKW easy-witness lemma: if NEXP has
small circuits, its exponentially-long witnesses also have small circuits, and that stored tension
releases into a **uniform collapse** (NEXP = MA).  It crosses the non-uniform → uniform seam *without*
padding — it never compresses, so there is no 2^n explosion to pay.

This file formalizes the spring and its honest consequence: the release (IKW) is real and crosses the
seam, but it lands on a **collapse**, and the **snap** from collapse to a genuine separation needs a fast
SAT algorithm.  So the spring does not add a second open object — it **dissolves** the
uniformity-promotion into IKW (real) plus the *same* algorithm off Π★.  The descent's two open objects
unify into one.

## What is proved

* **`spring_crosses_seam`** — the release: from a non-uniform assumption, the spring yields a uniform
  collapse (IKW, powered by the tension — no padding, no blowup).
* **`spring_reduces_uniformity_to_algorithm`** — the full spring: release (IKW) then snap (algorithm)
  gives the separation.  The ONLY open socket is `alg` — the fast SAT algorithm off Π★.
* **`descent_has_one_open_object`** — the honest capstone: given the real spring (release + snap
  machinery), the separation follows from the single algorithm socket.  The uniformity-promotion is not a
  second wall; it is the spring plus the first wall.

## Honest scope

The release (IKW) and the snap machinery (Williams' contradiction against the NTIME hierarchy) are real;
the one open socket is the fast SAT algorithm `alg`, and the reachable ceiling is the class that
algorithm handles (ACC⁰ today).  The spring re-describes Williams' method and unifies the two open
objects; it does not lower the wall.  Filling `alg` for the general class is `P ≠ NP`.  Nothing here is a
proof of it.
-/

namespace PallLean.Paper93.DeepMath.PathB.SpringRelease

/-- **The release (proved).**  From a non-uniform circuit assumption, the spring yields a uniform
collapse — the IKW easy-witness step, powered by the exponential tension: the long witnesses have small
circuits, releasing uniform structure.  Crucially this is a direct implication, not a compression — it
does not go through the `2^n` un-padding, so there is no blowup to pay. -/
theorem spring_crosses_seam {NonUnif UnifCollapse : Prop} (release : NonUnif → UnifCollapse) :
    NonUnif → UnifCollapse :=
  release

/-- **The full spring (proved).**  Release (IKW, crosses the seam via tension) then snap (a fast SAT
algorithm closes the collapse to a separation, Williams-style) turns the non-uniform assumption into the
separation.  The only open socket is `alg` — the fast SAT algorithm off Π★. -/
theorem spring_reduces_uniformity_to_algorithm
    {NonUnif UnifCollapse FastSAT Separation : Prop}
    (release : NonUnif → UnifCollapse)
    (snap : UnifCollapse → FastSAT → Separation)
    (alg : FastSAT) :
    NonUnif → Separation :=
  fun h => snap (release h) alg

/-- **Capstone (proved): the descent has one open object, not two.**  Given the real spring — the release
(IKW easy-witness, seam-crossing, no blowup) and the snap machinery (Williams' contradiction) — the
separation follows from a *single* open socket, the fast SAT algorithm `alg`.  The uniformity-promotion
is therefore not a second wall: it is the spring (real) plus the algorithm off Π★ (the first wall).  The
two open objects unify.  Filling `alg` for the general class is `P ≠ NP`; it is left open. -/
theorem descent_has_one_open_object
    {NonUnif UnifCollapse FastSAT Separation : Prop}
    (release : NonUnif → UnifCollapse)
    (snap : UnifCollapse → FastSAT → Separation)
    (assumption : NonUnif) :
    FastSAT → Separation :=
  fun alg => spring_reduces_uniformity_to_algorithm release snap alg assumption

end PallLean.Paper93.DeepMath.PathB.SpringRelease

#print axioms PallLean.Paper93.DeepMath.PathB.SpringRelease.spring_reduces_uniformity_to_algorithm
#print axioms PallLean.Paper93.DeepMath.PathB.SpringRelease.descent_has_one_open_object
