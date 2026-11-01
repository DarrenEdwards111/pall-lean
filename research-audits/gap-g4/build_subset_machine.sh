#!/bin/bash
# Kernel-check SubsetMachine.lean (G4.4 item 4) against codex/godmove-gap-repairs @ 21921958 (trimmed closure of G3.7)
# plus Def12Measure.lean and G4SATLink.lean. Prereq: research-audits/gap-g3/repaired/build_trimmed.sh has populated <scratch>.
set -eo pipefail
export PATH=$HOME/.elan/bin:$PATH
HERE=$(cd "$(dirname "$0")" && pwd)
WT=${1:-/workspace/pvsnp/wt-g3}; T=${2:-/workspace/pvsnp/g3trim}; O=${3:-/workspace/pvsnp/g4link/out}
[ "$(git -C $WT rev-parse HEAD)" = "$(git -C $WT rev-parse 21921958)" ] || { echo "worktree not at 21921958"; exit 2; }
mkdir -p $O
export LEAN_PATH=$(cd $WT && lake env printenv LEAN_PATH | sed "s#$WT/.lake/build/lib/lean#$T/overlay#"):$T/out:$O
( cd $WT/research-audits/nframe-fixed-invariant && [ -f $T/out/GodMoveSATSourceCanonicity.olean ] || \
  nice -n 10 lean -R . -o $T/out/GodMoveSATSourceCanonicity.olean -i $T/out/GodMoveSATSourceCanonicity.ilean GodMoveSATSourceCanonicity.lean >/dev/null )
( cd $HERE && nice -n 10 lean -R . -o $O/Def12Measure.olean -i $O/Def12Measure.ilean Def12Measure.lean >/dev/null )
( cd $HERE && nice -n 10 lean -R . -o $O/G4SATLink.olean -i $O/G4SATLink.ilean G4SATLink.lean >/dev/null )
cd $HERE && nice -n 10 lean SubsetMachine.lean 2>&1 | tee subset_machine_axioms.log
