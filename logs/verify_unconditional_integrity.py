from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def strip_lean(s):
    out=[];i=0;depth=0;quoted=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i): depth+=1;i+=2
            elif s.startswith('-/',i): depth-=1;i+=2
            else:
                if s[i]=='\n':out.append('\n')
                i+=1
        elif quoted:
            if s[i]=='\\':i+=2
            elif s[i]=='"':quoted=False;i+=1;out.append(' ')
            else:i+=1
        elif s.startswith('/-',i):depth=1;i+=2;out.append(' ')
        elif s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j
        elif s[i]=='"':quoted=True;i+=1;out.append(' ')
        else:out.append(s[i]);i+=1
    assert depth==0 and not quoted
    return ''.join(out)
files=[ROOT/'Certificate.lean',*sorted((ROOT/'Certificate').rglob('*.lean'))]
forbidden={'sorry','admit','axiom','sorryAx','native_decide'}
hits=[]
for p in files:
    for m in re.finditer(r'\b(?:sorry|admit|axiom|sorryAx|native_decide)\b',strip_lean(p.read_text())):
        hits.append({'file':str(p.relative_to(ROOT)),'token':m.group(),'line':strip_lean(p.read_text())[:m.start()].count('\n')+1})
scan={'files_scanned':len(files),'forbidden_tokens':sorted(forbidden),'hits':hits,'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in files}}
(ROOT/'logs/unconditional_source_scan.json').write_text(json.dumps(scan,indent=2)+'\n')
assert not hits,hits
r=json.loads((ROOT/'logs/final/verification.json').read_text())
b=json.loads((ROOT/'logs/final/verification_before_fundamental_arc.json').read_text())
meta=json.loads((ROOT/'logs/unconditional_new_targets.json').read_text())
s=json.loads((ROOT/'logs/unconditional_status.json').read_text())
old={m['source']:m for m in b['source_and_artifact_manifest'] if m['source']!='Certificate.lean'}
new={m['source']:m for m in r['source_and_artifact_manifest']}
changed=[name for name,rec in old.items() if new.get(name)!=rec]
assert not changed,changed
assert set(b['verified_theorems'])<=set(r['verified_theorems'])
added=set(r['verified_theorems'])-set(b['verified_theorems'])
assert added==set(meta['targets'])
assert len(b['verified_theorems'])==447
assert len(added)==80
assert len(r['verified_theorems'])==527
assert len(old)==1256
assert len(new)==1267
assert len(files)==1541
assert r['remaining_geometric_inputs']==[]
axioms=sorted({x for xs in r['verified_theorems'].values() for x in xs})
assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
assert r['published_geometry_provenance_sha256']==digest(ROOT/'data/published_geometry_provenance.json')
assert not s['stale_reports']
for key in meta['flags']:
    assert r[key] is True and s[key] is True,key
assert r['balanced_frame_boundary_constructed'] is True
assert r['unconditional_packing_density_theorem_verified'] is True
assert s['full_density_theorem_verified'] is True
for k,n in [('generated_matrix_proofs_passed',248),('polynomial_reductions_passed',4),('multipliers_passed',75),('gram_expansions_passed',248),('assembled_blocks_passed',248)]:assert s[k]==n
assert len(s['assembled_identities'])==4
res={'named_targets':len(r['verified_theorems']),'added_targets':sorted(added),'removed_targets':[],
'allowed_axioms_only':True,'axioms':axioms,'prior_non_root_records_preserved':len(old),
'changed_prior_non_root_records':changed,'manifest_local_modules':len(new),
'production_sources_scanned':len(files),'source_scan_clean':True,'provenance_hash_current':True,
'new_verified_flags':{k:s[k] for k in meta['flags']},'stale_reports':s['stale_reports'],
'balanced_frame_boundary_constructed':True,'unconditional_packing_density_theorem_verified':True}
(ROOT/'logs/unconditional_final_integrity.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({k:v for k,v in res.items() if k!='added_targets'},indent=2))
