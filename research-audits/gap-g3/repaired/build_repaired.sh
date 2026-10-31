#!/bin/bash
# Reproduce GapG3Repaired against codex/godmove-gap-repairs @ 21921958 WITHOUT modifying that branch.
# Usage: build_repaired.sh <pall-lean clone with built .lake/packages> <scratch dir>
set -e
REPO=${1:-/workspace/pvsnp/pall-lean}; SCR=${2:-/workspace/pvsnp/g3scratch}
HERE=$(cd "$(dirname "$0")" && pwd)
export PATH=$HOME/.elan/bin:$PATH
mkdir -p "$SCR/out"
[ -d "$SCR/wt" ] || git -C "$REPO" worktree add --detach "$SCR/wt" 21921958
mkdir -p "$SCR/wt/.lake"; ln -sfn "$REPO/.lake/packages" "$SCR/wt/.lake/packages"
cd "$SCR/wt"
taskset -c 0-2 nice -n 10 lake build PallLean.MlProjFar PallLean.PiStarConcrete PallLean.ProductDeriv PallLean.Step4Compiler \
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposablePpolyDischarge \
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCircuitUpgrade \
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATCircuitSeparationBridge \
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATVerifierSpec \
  PallLean.Paper93.DeepMath.PathB.ComputationalDepthWireTreeCircuit
LP=$(lake env printenv LEAN_PATH):$SCR/out
cd research-audits/nframe-fixed-invariant
for m in GodMoveBooleanInterpolation GodMovePinnedSATQueries GodMoveFaithfulHandshake GodMoveSymbolicPinnedInput GodMoveCircuitArithmetization GodMoveCircuitNormalization GodMoveCircuitRuntimeCost GodMoveMonomialMinor GodMoveUnitCharacteristic GodMoveCircuitRankObstruction GodMoveCircuitStorage GodMoveCircuitConnection GodMovePinnedFaceLayout GodMoveBooleanFace GodMoveMultilinearRestriction GodMoveMachineFaceExtraction GodMoveInjectiveRankTransport GodMoveMachineSourceMinor GodMoveSATUnitExtraction GodMoveDesignatedSheetNormalization GodMoveFullShiftProductSpace GodMoveQuadraticSheetLift GodMoveSATDesignatedExtraction; do
  [ -f "$SCR/out/$m.olean" ] || LEAN_PATH=$LP nice -n 5 lean -o "$SCR/out/$m.olean" -i "$SCR/out/$m.ilean" $m.lean > /dev/null
done
LEAN_PATH=$LP nice -n 5 lean "$HERE/G3RepairedFaceLocality.lean"
