#!/usr/bin/env python3
"""Propose small exact sums; Lean checks every merge and the final identity."""
import json
from pathlib import Path
from emit_chunked_sos import merge, polynomial, write_if_changed

ROOT = Path(__file__).resolve().parents[1]

def emit_sum_tree(ident, data, output, checks_per_module=8):
    namespace = f'Certificate.Assembly.{ident}'
    package = f'Certificate.Assembly.SumTrees.{ident}'
    destination = output/'SumTrees'/ident
    destination.mkdir(parents=True, exist_ok=True)
    tags = [f'{ident}B{b["index"]:03d}' for b in data['blocks']]
    exprs = [f'(scale Certificate.SOS.{tag}.weight Certificate.SOS.{tag}.weighted)' for tag in tags]
    level = []
    for b, expr in zip(data['blocks'], exprs):
        terms = [(int(c)*b['scale_multiplier'], tuple(e)) for c,e in b['weighted_integer_poly']]
        level.append(dict(expression=expr, terms=terms, total=f'eval x {expr}', proof=None))
    nodes = []
    while len(level)>1:
        newlevel = []
        for start in range(0,len(level),2):
            if start+1==len(level):
                newlevel.append(level[start]);continue
            left,right = level[start:start+2]
            name=f'node{len(nodes):03d}'
            terms=merge(left['terms'],right['terms'])
            text=polynomial(name,terms)
            text+=f'theorem {name}_check : merge {left["expression"]} {right["expression"]} = {name} := by\n  decide +kernel\n'
            total=f'({left["total"]} + {right["total"]})'
            text+=f'theorem {name}_total (x : Fin 8 → ℝ) : eval x {name} = {total} := by\n'
            rewrites=[f'← {name}_check','eval_merge']+[c['proof'] for c in (left,right) if c['proof']]
            text+='  rw ['+', '.join(rewrites)+']\n'
            node=dict(expression=name,terms=terms,total=total,proof=name+'_total',text=text)
            nodes.append(node);newlevel.append(node)
        level=newlevel
    root=level[0]
    assert [(c,list(e)) for c,e in root['terms'] if c] == [(int(c),e) for c,e in data['summed_sos']]
    modules=[]
    options='open Certificate.Sparse\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n'
    for start in range(0,len(nodes),checks_per_module):
        index=start//checks_per_module
        module=f'{package}.Chunk{index:03d}'
        imports=(f'import {modules[-1]}\n' if modules else
                 ''.join(f'import Certificate.SOS.{tag}Data\n' for tag in tags))
        source=imports+f'namespace {namespace}\n'+options
        source+='\n'.join(n['text'] for n in nodes[start:start+checks_per_module])
        source+=f'#print axioms {nodes[min(start+checks_per_module,len(nodes))-1]["proof"]}\nend {namespace}\n'
        write_if_changed(destination/f'Chunk{index:03d}.lean',source)
        modules.append(module)
    source=f'import {modules[-1]}\nimport Certificate.Identities.{ident}Data\nimport Certificate.MergeArithmetic\n'
    source+=f'namespace {namespace}\n'+options
    source+='noncomputable def blocks : List Polynomial := [\n  '+',\n  '.join(exprs)+']\n'
    source+=f'''theorem sum_check : checkEqualMerged {root['expression']} Certificate.Identities.{ident}.recordedSOS = true := by
  decide +kernel

theorem sum_identity (x : Fin 8 → ℝ) :
    eval x Certificate.Identities.{ident}.recordedSOS = (blocks.map (eval x)).sum := by
  rw [← eq_of_checkMerged x _ _ sum_check, {root['proof']}]
  simp only [blocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, add_assoc]
#print axioms sum_identity
end {namespace}
'''
    write_if_changed(output/f'{ident}Sum.lean',source)
    write_if_changed(destination/'manifest.json',json.dumps({'identity':ident,'modules':modules,'checks':len(nodes)},indent=2)+'\n')
    return modules

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--identity',required=True);args=p.parse_args()
    data=json.loads((ROOT/f'data/polynomials/{args.identity}.json').read_text())
    print(json.dumps(emit_sum_tree(args.identity,data,ROOT/'Certificate/Assembly')))
