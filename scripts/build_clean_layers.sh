#!/usr/bin/env bash
# Build + verify ONLY the clean computational-depth layers (Layer 3/4/7/8/9 + circuit model + extraction).
#
# These 37 modules are sorry-free with standard axioms only, and are entirely independent of the
# unrelated `PallLean.Step4Compiler` P-vs-NP experiment. A plain `lake build` of the whole `PallLean`
# library would also try (and historically fail) to build `Step4Compiler`; this target builds exactly the
# AC⁰[p] / general-circuit / frontier-infrastructure development and asserts zero `sorryAx`.
#
# Usage:  ./scripts/build_clean_layers.sh
# Exit 0 iff every clean module builds and no capstone depends on `sorryAx`.
set -euo pipefail
cd "$(dirname "$0")/.."

CLEAN_MODULES=(
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4CircuitReal
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pFoundations
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pApprox
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pPoly
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pPolyFull
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pPolyMod
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Agreement
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Averaging
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3DegreeComposition
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3DimensionCount
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Smolensky
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4BaseChange
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4ModqChar
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4RootOfUnity
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4DimGeneral
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4QaryReduction
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4QarySpan
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4WeightRepr
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Approx
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Padding
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Assembly
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Intersection
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Bridge
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Capstone
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4PadSubcircuits
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer7CircuitFamily
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer7ParityFamily
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer7ModqFamily
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer8GeneralCircuit
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer8Shannon
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer8ShannonCount
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer8ShannonExplicit
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer8LinearBound
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer9KarpLipton
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer9PpolyLowerBound
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer9NaturalProofs
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthMathlibCandidates
)

echo "== Building ${#CLEAN_MODULES[@]} clean computational-depth modules (excludes Step4Compiler) =="
lake build "${CLEAN_MODULES[@]}"

echo "== Verifying capstones are sorry-free with standard axioms only =="
CAPSTONE_CHECK=$(mktemp /tmp/clean_layers_axioms_XXXX.lean)
cat > "$CAPSTONE_CHECK" <<'LEAN'
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer7ModqFamily
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Capstone
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer8ShannonExplicit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer8LinearBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer9KarpLipton
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer9PpolyLowerBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer9NaturalProofs
open PallLean.Paper93.DeepMath.PathB
#print axioms Layer3.parity_function_lower_bound
#print axioms Layer4.mod_q_indicators_false
#print axioms Layer4.mod_q_family_false
#print axioms Layer4.qary_contradiction
#print axioms Layer7.parity_not_in_nonuniform_AC0p
#print axioms Layer7.modq_not_in_nonuniform_AC0p
#print axioms Layer8.shannon_counting_bound
#print axioms Layer8.exists_function_needing_exp_size
#print axioms Layer8.andAll_needs_linear_size
#print axioms Layer9.karpLipton_collapse
#print axioms Layer9.exists_lang_not_in_Ppoly
#print axioms Layer9.razborov_rudich_barrier
LEAN

OUT=$(lake env lean "$CAPSTONE_CHECK" 2>&1)
rm -f "$CAPSTONE_CHECK"
echo "$OUT"

if echo "$OUT" | grep -qi "sorryAx"; then
  echo "FAIL: a capstone depends on sorryAx" >&2
  exit 1
fi
if echo "$OUT" | grep -qiE "error"; then
  echo "FAIL: axiom check reported an error" >&2
  exit 1
fi
echo "OK: clean computational-depth layers build; all capstones sorry-free, [propext, Classical.choice, Quot.sound]."
