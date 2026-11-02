#!/usr/bin/env python3
"""Emit kernel-reducible exact data, without generating executable machine code."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
x=json.loads((ROOT/'data/exact/H1_0.json').read_text());b=x['blocks'][0]
assert b['n']==104
s='import Certificate.DiagonalCheck\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nnamespace Certificate.BenchmarkLite\n'
for key,v in [('n',b['n']),('denominator',b['denominator']),('factorDenominator',b['factor_denominator']),('sqrtScale',x['sqrt_scale']),('sqrtLo',x['sqrt_lo']),('sqrtHi',x['sqrt_hi'])]:
 s+=f'noncomputable def {key} : '+('Nat' if key=='n' else 'Int')+f' := {v}\n'
def literal(x):return f'Int.ofNat {x}' if x>=0 else f'Int.negSucc {-x-1}'
for key,src in [('gramA','A'),('gramB','B'),('factor','L')]:
 for i,row in enumerate(b[src]):s+=f'noncomputable def {key}_{i} : List Int := ['+', '.join(literal(v) for v in row)+']\n'
 s+=f'noncomputable def {key} : List (List Int) := ['+', '.join(f'{key}_{i}' for i in range(b['n']))+']\n'
s+='end Certificate.BenchmarkLite\n'
p=ROOT/'Certificate/BenchmarkDataLite.lean'
if p.exists() and p.read_text()==s:print('Benchmark data unchanged')
else:p.write_text(s);print('Wrote',p)
