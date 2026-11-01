#!/bin/bash
# Kernel-check G3RepairedFaceLocality.lean (G3-B) and G3RepairedMeasureRange.lean (G3-C) against
# codex/godmove-gap-repairs @ 21921958 WITHOUT building the Cook-Levin emitter chain (EmitPairT etc.).
# Usage: build_trimmed.sh <worktree at 21921958 with PathB oleans built> <scratch dir>
# Faithfulness: see NOTES G3.7 (2026-11-01). The ONLY non-verbatim module is trim/ComputationalDepthCookLevinEmitClockBounds3.lean
# (the PolyBounded kit PB_const/PB_id/PB_le/PB_add/PB_mul, verbatim, with Emit-chain imports/opens removed).
# All other modules (ComposablePpolyDischarge + 26 research-audit modules) are compiled from the 21921958 sources unchanged.
# The worktree is not modified: oleans go to <scratch>/overlay (symlink copy of the worktree's build) and <scratch>/out.
set -o pipefail
export PATH=$HOME/.elan/bin:$PATH
HERE=$(cd "$(dirname "$0")" && pwd)
WT=${1:-/workspace/pvsnp/wt-g3}; T=${2:-/workspace/pvsnp/g3trim}
P=PallLean/Paper93/DeepMath/PathB; OV=$T/overlay; OUT=$T/out
[ "$(git -C $WT rev-parse HEAD)" = "$(git -C $WT rev-parse 21921958)" ] || { echo "worktree not at 21921958"; exit 2; }
mkdir -p $OUT $T/logs $T/src/$P
[ -d $OV/PallLean ] || { mkdir -p $OV && cp -rs $WT/.lake/build/lib/lean/PallLean $OV/; }
cp $HERE/trim/ComputationalDepthCookLevinEmitClockBounds3.lean $T/src/$P/
export LEAN_PATH=$(cd $WT && lake env printenv LEAN_PATH | sed "s#$WT/.lake/build/lib/lean#$OV#"):$OUT
cd $WT
run() { echo "== $(basename $1) $(date +%T)"; nice -n 10 lean $5 -o $2 -i $3 $1 > $4 2>&1 || { echo "FAIL $1"; tail -30 $4; exit 1; }; }
[ -f $OV/$P/ComputationalDepthCookLevinEmitClockBounds3.olean ] || run $T/src/$P/ComputationalDepthCookLevinEmitClockBounds3.lean $OV/$P/ComputationalDepthCookLevinEmitClockBounds3.olean $OV/$P/ComputationalDepthCookLevinEmitClockBounds3.ilean $T/logs/ClockBounds3.log "-R $T/src"
[ -f $OV/$P/ComputationalDepthComposablePpolyDischarge.olean ] || run $WT/$P/ComputationalDepthComposablePpolyDischarge.lean $OV/$P/ComputationalDepthComposablePpolyDischarge.olean $OV/$P/ComputationalDepthComposablePpolyDischarge.ilean $T/logs/ComposablePpolyDischarge.log
cd $WT/research-audits/nframe-fixed-invariant
for m in $(cat $HERE/trim/audit_order.txt); do
  [ -f $OUT/$m.olean ] || run $m.lean $OUT/$m.olean $OUT/$m.ilean $T/logs/$m.log "-R ."
done
cd $WT
nice -n 10 lean -R $HERE $HERE/G3RepairedFaceLocality.lean > $T/logs/repaired_axioms.log 2>&1; echo REPAIRED_EXIT $?
nice -n 10 lean -R $HERE $HERE/G3RepairedMeasureRange.lean > $T/logs/range_axioms.log 2>&1; echo RANGE_EXIT $?
