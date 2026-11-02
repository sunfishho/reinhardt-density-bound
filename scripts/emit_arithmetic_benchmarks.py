#!/usr/bin/env python3
"""Emit comparable, kernel-checked benchmarks without modifying production proofs."""
from pathlib import Path
import argparse
import json

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--identity', default='H1_0', choices=['H1_0', 'H1_1', 'H1_2', 'H2'])
    parser.add_argument('--block', type=int, default=1)
    args = parser.parse_args()
    tag = f'{args.identity}B{args.block:03d}'
    out = ROOT / 'Certificate/Benchmarks'
    out.mkdir(exist_ok=True)
    g = f'Certificate.Generated.{tag}.data'
    variants = {
        'OriginalGram': f'checkEqual (gramPolynomial {g} basis) gram',
        'RowMergeGram': f'checkEqual (fastGramPolynomial {g} basis) gram',
        'DirectMergeGram': f'checkEqualMerged (fastGramPolynomial {g} basis) gram',
        'SparseDirectGram': f'checkEqualMerged (sparseGramPolynomial {g} basis) gram',
        'OriginalWeighted': 'checkEqual (mulFast gram multiplier) weighted',
        'DirectMergeWeighted': 'checkEqualMerged (mulMerged gram multiplier) weighted',
        'ShortWeighted': 'checkEqualMerged (mulShort gram multiplier) weighted',
    }
    jobs = []
    for variant, expression in variants.items():
        name = f'{tag}{variant}'
        text = f'''import Certificate.SOS.{tag}Data
import Certificate.FastExpansion
import Certificate.MergeArithmetic
import Certificate.SparseExpansion
namespace Certificate.Benchmarks.{name}
open Certificate.Sparse Certificate.SOS.{tag}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem checked : {expression} = true := by decide +kernel
#print axioms checked
end Certificate.Benchmarks.{name}
'''
        if variant == 'ShortWeighted':
            text = text.replace('import Certificate.MergeArithmetic\n', 'import Certificate.MergeArithmetic\nimport Certificate.ShortMultiplication\n')
        path = out / f'{name}.lean'
        if not path.exists() or path.read_text()!=text:path.write_text(text)
        jobs.append(dict(variant=variant, source=str(path.relative_to(ROOT)),
                         theorem=f'Certificate.Benchmarks.{name}.checked'))
    manifest = ROOT / 'logs' / f'benchmark_{tag}_manifest.json'
    manifest.write_text(json.dumps(jobs, indent=2) + '\n')
    print(manifest)


if __name__ == '__main__':
    main()
