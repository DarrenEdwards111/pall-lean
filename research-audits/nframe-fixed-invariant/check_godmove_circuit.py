#!/usr/bin/env python3
"""Build source-matched dependencies, then check the focused GodMove bridge.

Run from any directory. By default use this checkout's Lake environment.
--dependency-checkout may select an existing cache only after every imported
PallLean source has been checked byte-for-byte against this checkout.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time


STAGES = [
    ['GodMoveBooleanInterpolation', 'GodMovePinnedSATQueries', 'GodMoveMonomialMinor',
     'GodMoveMultilinearRestriction', 'GodMoveAnyCertificateRank',
     'GodMoveIdempotentExtractionExtension', 'GodMoveExpanderScreen',
     'GodMovePositiveBoundaryMap', 'GodMoveRamanujanCalibration'],
    ['GodMoveOperatorSubsetDAG', 'GodMoveCircuitGluing'],
    ['GodMoveFaithfulHandshake', 'GodMoveCircuitArithmetization',
     'GodMoveCircuitRuntimeCost', 'GodMoveSymbolicPinnedInput', 'GodMoveCircuitNormalization',
     'GodMoveTopCoefficientMinor', 'GodMoveInjectiveRankTransport',
     'GodMoveFullShiftProductSpace', 'GodMoveShiftedRankUpper',
     'GodMoveExecutableScreen'],
    ['GodMoveUnitCharacteristic', 'GodMoveCharacteristicUnsat',
     'GodMoveCharacteristicPadding', 'GodMoveCharacteristicCounting',
     'GodMoveCircuitStorage', 'GodMoveNormalizationDerivativeObstruction',
     'GodMovePinnedFaceLayout', 'GodMoveBooleanFace', 'GodMoveDesignatedSheetNormalization'],
    ['GodMoveCircuitRankObstruction', 'GodMoveQuadraticSheetLift',
     'GodMoveFiniteStateInterpolation'],
    ['GodMoveCircuitConnection', 'GodMoveDesignatedComplementRows'],
    ['GodMoveCircuitPolynomialSize', 'GodMoveMachineFaceExtraction',
     'GodMoveLinearTimeRankObstruction'],
    ['GodMoveBooleanDifferentiation', 'GodMoveZeroShiftRankCeiling',
     'GodMoveDirectVerifierCircuit', 'GodMoveMachineSourceMinor'],
    ['GodMoveComputedWireRank', 'GodMoveSATUnitExtraction', 'GodMoveSATSourceCanonicity'],
    ['GodMoveVerifierInvariantBarrier', 'GodMoveSATDesignatedExtraction',
     'GodMoveSATPaperWindowLower', 'GodMoveExpanderPositiveProjection',
     'GodMoveRuntimeSnapshotRank'],
    ['GodMoveComputedWireLowerBound', 'GodMoveProductionGaugeBridge',
     'GodMoveProductionMinimizerBarrier', 'GodMoveSATDesignatedProjection',
     'GodMoveSATRuntimeFrontier', 'GodMoveDesignatedPositiveBoundary'],
    ['GodMoveUnitOutputGauge', 'GodMoveProductionConnection',
     'GodMoveExpanderBoundaryExamples', 'GodMoveBoundaryNFrameGauge',
     'GodMoveExecutableBoundary', 'GodMoveRuntimeSnapshotGauge'],
    ['GodMoveConstrainedBoundaryMinimum', 'GodMoveBoundaryRuntimeCost',
     'GodMoveSnapshotDerivativeObstruction'],
    ['GodMoveBoundaryWireGap', 'GodMoveBoundaryRuntimeBarrier'],
    ['GodMoveGaugeLocalOperators', 'GodMoveCompactGaugeCost',
     'GodMoveOperationalBoundaryBarrier'],
    ['GodMoveProjectorKernel', 'GodMoveCircuitInterface'],
    ['GodMoveCompactProjector', 'GodMoveEqualityCircuit', 'GodMoveGluedCircuitRank',
     'GodMoveSubsetCoefficient'],
    ['GodMoveSeparatedApplication'],
    ['GodMoveSamplingBarrier', 'GodMoveSampledWireGauge', 'GodMoveRankIncrementSAT'],
    ['GodMoveSampledSAT', 'GodMoveSmallSeparatingSamples', 'GodMoveWireSampleCertificate'],
    ['GodMoveBooleanWireTable', 'GodMoveRationalRowBasis', 'GodMoveSampleRefinement'],
    ['GodMoveRowSpanSeparation'],
    ['GodMoveExhaustiveDiscovery', 'GodMoveSampledWireBasis'],
    ['GodMoveExhaustiveWireBasis'],
    ['GodMoveCubeWitnessSearch', 'GodMoveNumericCounterexample', 'GodMoveBlackBoxQueryBarrier'],
    ['GodMoveAdaptiveDiscovery'],
    ['GodMoveAdaptiveRefinement', 'GodMoveAdaptiveDiscoveryExamples'],
    ['GodMoveBinaryAdder', 'GodMoveCircuitCNFSize', 'GodMoveGramPrecision'],
    ['GodMoveRationalClearing', 'GodMoveMachineCircuitOracle'],
    ['GodMoveSignedBinary', 'GodMoveResidualQueries'],
    ['GodMoveControlledWord', 'GodMoveGramSamplePrecision'],
    ['GodMoveWireSum'],
    ['GodMoveWeightedWireQuery'],
    ['GodMoveRationalMachineQuery'],
    ['GodMoveMachineRowFinder'],
    ['GodMoveMachineDiscovery'],
    ['GodMoveMachineDiscoveryPrecision'],
    ['GodMoveDiscoveryQuantifierAudit', 'GodMoveDiscoveryAssumptionCheck'],
]
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def imports(path):
    for line in path.read_text().splitlines():
        match = re.match(r'^import\s+(.+)', line)
        if match:
            yield from match[1].split('--')[0].split()


def main():
    audit = Path(__file__).resolve().parent
    checkout = audit.parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dependency-checkout', type=Path, default=checkout)
    parser.add_argument('--log-dir', type=Path)
    args = parser.parse_args()
    base = args.dependency_checkout.resolve()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='godmove-circuit-checks-'))
    logs.mkdir(parents=True, exist_ok=True)
    pending = [audit / (name + '.lean') for stage in STAGES for name in stage]
    direct = set()
    for path in pending:
        direct.update(m for m in imports(path) if m.startswith('PallLean.'))
    seen = set()
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        if path.is_relative_to(checkout / 'PallLean'):
            relative = path.relative_to(checkout)
            if path.read_bytes() != (base / relative).read_bytes():
                raise RuntimeError(f'Dependency source mismatch: {relative}')
        for module in imports(path):
            if module.startswith('PallLean.'):
                pending.append(checkout / (module.replace('.', '/') + '.lean'))
            elif module.startswith('GodMove'):
                pending.append(audit / (module + '.lean'))
    for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
        if (checkout / name).read_bytes() != (base / name).read_bytes():
            raise RuntimeError(f'Dependency configuration mismatch: {name}')
    print(f'Source closure matched: {len(seen)} files. Logs: {logs}', flush=True)
    with (logs / 'dependencies.log').open('w') as log:
        result = subprocess.run(['lake', 'build', *sorted(direct)], cwd=base,
                                stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'Dependency build failed; see {logs / "dependencies.log"}')
    env = os.environ.copy()
    env['LEAN_PATH'] = str(audit) + ':' + subprocess.check_output(
        ['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=base, text=True).strip()
    lean = subprocess.check_output(['lake', 'env', 'which', 'lean'],
                                   cwd=base, text=True).strip()

    def check(name):
        start = time.monotonic()
        result = subprocess.run(
            [lean, f'--root={audit}', '-o', str(audit / (name + '.olean')),
             str(audit / (name + '.lean'))], cwd=base, env=env, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        output = result.stdout
        (logs / (name + '.log')).write_text(output)
        blocks = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.S)
        axioms = sorted({axiom.strip() for _, block in blocks
                         for axiom in block.split(',') if axiom.strip()})
        record = {
            'file': name, 'exit_code': result.returncode,
            'seconds': round(time.monotonic() - start, 2),
            'printed_axiom_checks': len(blocks) + output.count('does not depend on any axioms'),
            'axioms': axioms, 'warnings': output.count('warning:'),
            'passed': result.returncode == 0 and set(axioms) <= STANDARD_AXIOMS,
        }
        print(json.dumps(record), flush=True)
        return record

    records = []
    for stage in STAGES:
        with ThreadPoolExecutor(max_workers=3) as pool:
            stage_records = list(pool.map(check, stage))
        records.extend(stage_records)
        if any(not row['passed'] for row in stage_records):
            break
    summary = {
        'checkout_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'],
                                                cwd=checkout, text=True).strip(),
        'lean_version': subprocess.check_output([lean, '--version'], text=True).strip(),
        'source_closure_files': len(seen), 'checks': records,
        'all_passed': len(records) == sum(map(len, STAGES)) and all(r['passed'] for r in records),
    }
    (logs / 'results.json').write_text(json.dumps(summary, indent=2) + '\n')
    print('ALL_PASSED=' + str(summary['all_passed']), flush=True)
    return 0 if summary['all_passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
