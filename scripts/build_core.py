#!/usr/bin/env python3
"""Rebuild the proved general lemmas and audit; not the pending specific certificate."""
from pathlib import Path
import json,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[1]
mods=['DiagonalCheck','MatrixPositivity','IntervalSoundness','GramSoundness','NumericBound','ControlCost','Multipliers','MultiplierData','NormalForm','AxiomAudit']
reports=[]
for mod in mods:
 start=time.monotonic()
 run=subprocess.run([sys.executable,str(ROOT/'scripts/lean_cached.py'),'-o',f'Certificate/{mod}.olean',f'Certificate/{mod}.lean'],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (ROOT/'logs'/f'core_{mod}.log').write_text(run.stdout)
 report=dict(module=mod,exit_code=run.returncode,seconds=time.monotonic()-start)
 reports.append(report);print(report,flush=True)
 (ROOT/'logs/core_build.json').write_text(json.dumps(reports,indent=2)+'\n')
 if run.returncode:print(run.stdout);raise SystemExit(run.returncode)
 if 'sorryAx' in run.stdout or 'Lean.ofReduceBool' in run.stdout:raise SystemExit('Unexpected proof dependency')
