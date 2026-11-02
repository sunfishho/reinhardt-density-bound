#!/usr/bin/env python3
"""Rebuild the quotient/reduction stage after checker changes.
This stage alone does not verify expansion from Gram matrices or differentiation of V.
"""
from pathlib import Path
import hashlib,json,re,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'logs/ideals';OUT.mkdir(exist_ok=True)
for ident in ['H2','H1_0','H1_1','H1_2']:
 started=time.monotonic();reports=[]
 for kind in ['Data','Proof']:
  name=f'Certificate/Identities/{ident}{kind}'
  run=subprocess.run(['/usr/bin/time','-p',sys.executable,str(ROOT/'scripts/lean_cached.py'),'-o',name+'.olean',name+'.lean'],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  (OUT/f'{ident}_{kind}.log').write_text(run.stdout)
  reports.append(dict(stage=kind,exit_code=run.returncode))
  if run.returncode:print(run.stdout);raise SystemExit(run.returncode)
 theorem=f'Certificate.Identities.{ident}.quotient_identity'
 match=re.search(re.escape("'"+theorem+"'")+r' depends on axioms: \[([^]]*)\]',run.stdout)
 assert match,'missing axiom audit';axioms={a.strip() for a in match.group(1).split(',') if a.strip()}
 assert axioms <= {'propext','Classical.choice','Quot.sound'},axioms
 files=[ROOT/'Certificate/SparsePolynomial.lean']+[ROOT/f'Certificate/Identities/{ident}{kind}.lean' for kind in ['Data','Proof']]
 report=dict(identity=ident,quotient_stage_verified=True,full_certificate_identity_verified=False,source_sha256=hashlib.sha256(b''.join(f.read_bytes() for f in files)).hexdigest(),axioms=sorted(axioms),seconds=time.monotonic()-started,stages=reports)
 (OUT/f'{ident}.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
