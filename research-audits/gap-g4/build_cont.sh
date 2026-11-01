#!/bin/bash
# Kernel-check ContDef12.lean (generic Def.12 lower bound via substitutions; Mathlib + Def12Measure) and
# ContLink.lean (contLang lower bound + in-model SAT corollary; imports SubsetMachine) and SATPad.lean (SATLang padding invariance) against
# codex/godmove-gap-repairs @ 21921958 (trimmed closure of G3.7). Prereq: research-audits/gap-g3/repaired/build_trimmed.sh
# has populated <scratch>. Serial, nice 10.
set -eo pipefail
export PATH=$HOME/.elan/bin:$PATH
HERE=$(cd "$(dirname "$0")" && pwd)
WT=${1:-/workspace/pvsnp/wt-g3}; T=${2:-/workspace/pvsnp/g3trim}; O=${3:-/workspace/pvsnp/g4link/out}
[ "$(git -C $WT rev-parse HEAD)" = "$(git -C $WT rev-parse 21921958)" ] || { echo "worktree not at 21921958"; exit 2; }
mkdir -p $O
export LEAN_PATH=$(cd $WT && lake env printenv LEAN_PATH | sed "s#$WT/.lake/build/lib/lean#$T/overlay#"):$T/out:$O
( cd $WT/research-audits/nframe-fixed-invariant && [ -f $T/out/GodMoveSATSourceCanonicity.olean ] || \
  nice -n 10 lean -R . -o $T/out/GodMoveSATSourceCanonicity.olean -i $T/out/GodMoveSATSourceCanonicity.ilean GodMoveSATSourceCanonicity.lean >/dev/null )
cd $HERE
for f in Def12Measure G4SATLink SubsetMachine; do
  [ -f $O/$f.olean ] && [ $O/$f.olean -nt $f.lean ] || nice -n 10 lean -R . -o $O/$f.olean -i $O/$f.ilean $f.lean >/dev/null
done
STAGE=${STAGE:-all}
if [ "$STAGE" = gen ] || [ "$STAGE" = all ]; then
  nice -n 10 lean -R . -o $O/ContDef12.olean -i $O/ContDef12.ilean ContDef12.lean 2>&1 | tee cont_def12_axioms.log
fi
if [ "$STAGE" = link ] || [ "$STAGE" = all ]; then
  nice -n 10 lean ContLink.lean 2>&1 | tee cont_link_axioms.log
fi
if [ "$STAGE" = pad ] || [ "$STAGE" = all ]; then
  nice -n 10 lean SATPad.lean 2>&1 | tee sat_pad_axioms.log
fi
