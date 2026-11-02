"""
Independent exact verification of one identity of the d4invg certificate.
usage: python3 02_verify_exact.py <ident in H1_0,H1_1,H1_2,H2> <den bits>
Steps: exact Gram blocks from the stored cone slacks s_i (+ eps I), rounded to 2^-den; exact total = sum_b m_b^T Q_b m_b q_b,
normal form; residual vs my independently derived target; projection of the residual into block '1'; exact re-check of the
identity; exact LDL^T of every block.
"""
import sys, json, time, math
import numpy as np
sys.path.insert(0, '/Users/matthewho/Downloads/Stanford/convex_problems/open_problems/trajectories/fable_5_1_review/semantic_overlap_review/main_results/recovered_audit_checks/reinhardt')
from m12lib import *

ident = sys.argv[1]; DEN = int(sys.argv[2]) if len(sys.argv) > 2 else 40
TAG = sys.argv[3]; TJ = sys.argv[4]; OUTD = sys.argv[5]
t0 = time.time()
data = json.load(open(TJ))
def poly_from_json(lst): return {tuple(e): Q3(Fr(sa), Fr(sb)) for e, sa, sb in lst}
target = poly_from_json(data['targets'][ident])
cons = {k: poly_from_json(v) for k, v in data['constraints'].items()}
def q_poly(name):
    if name == '1': return pconst(1)
    if '*' in name:
        n1, n2 = name.split('*'); return pmul(cons[n1], cons[n2])
    return cons[name]

def round_dyadic(x, den):
    return Fr(int(round(x*(1 << den))), 1 << den)
def build_block(sv, n, eps, den):
    Q = [[Fr(0)]*n for _ in range(n)]; idx = 0
    for j in range(n):              # Clarabel svec: upper triangle, column-major, off-diagonals scaled by sqrt2
        for i in range(j + 1):
            val = float(sv[idx]) if i == j else float(sv[idx])/math.sqrt(2.0)
            fr = round_dyadic(val, den); Q[i][j] = fr; Q[j][i] = fr; idx += 1
    assert idx == len(sv)
    if n > 1:
        e = round_dyadic(eps, den)
        for i in range(n): Q[i][i] += e
    return Q
def gram_poly(Q, basis, q):
    n = len(basis); Pm = {}
    for i in range(n):
        bi = basis[i]; Qi = Q[i]
        for j in range(i, n):
            c = Qi[j]
            if isinstance(c, Q3):
                if c.iszero(): continue
            elif c == 0: continue
            if j != i: c = c*2
            e = tuple(x + y for x, y in zip(bi, basis[j]))
            v = Pm.get(e); Pm[e] = Q3.of(c) if v is None else v + Q3.of(c)
    return pmul(Pm, q)

z = np.load(f'/Users/matthewho/Downloads/Stanford/convex_problems/open_problems/trajectories/fable_5_1_review/semantic_overlap_review/main_results/recovered_audit_checks/reinhardt/certs/{TAG}_{ident}.npz', allow_pickle=False)
names = [str(x) for x in z['names']]; sizes = [int(x) for x in z['sizes']]; eps = float(z['eps'])
print(f"[{ident}] den=2^-{DEN} eps={eps:.3e} blocks={len(names)} sizes={sorted(set(sizes))} target terms={len(target)}", flush=True)
blocks = []; total = {}
for i, (nm, n) in enumerate(zip(names, sizes)):
    basis = [tuple(int(v) for v in row) for row in z[f'basis_{i}']]
    assert len(basis) == n and all(is_standard(e) for e in basis)
    Q = build_block(z[f's_{i}'], n, eps, DEN)
    q = q_poly(nm)
    # degree bookkeeping: 2*max basis degree + deg q <= target degree bound
    blocks.append((nm, Q, basis, q))
    total = padd(total, gram_poly(Q, basis, q))
total = nf(total)
resid = padd(target, total, Q3(-1))           # target - sum_b sigma_b q_b   (normal forms)
maxres = max((abs(float(c)) for c in resid.values()), default=0.0)
print(f"[{ident}] exact total built ({time.time()-t0:.1f}s); residual terms {len(resid)}, max|residual| = {maxres:.3e}", flush=True)
assert all(is_standard(e) for e in resid)
# ---- projection into block '1'
nm0, Q0, B0, q0 = blocks[0]; assert nm0 == '1' and len(q0) == 1 and E0 in q0
bidx = {e: i for i, e in enumerate(B0)}; kdeg = max(sum(e) for e in B0)
gamma = None; maxproj = 0.0
for t, rt in resid.items():
    if ident == 'H2' and t == E0:
        gamma = rt; continue
    ea = [0]*NV; eb = list(t)
    for i in range(NV):
        while eb[i] > 0 and sum(eb) > kdeg and sum(ea) < kdeg:
            ea[i] += 1; eb[i] -= 1
    ea, eb = tuple(ea), tuple(eb)
    assert ea in bidx and eb in bidx and tuple(x + y for x, y in zip(ea, eb)) == t
    al, be = bidx[ea], bidx[eb]
    maxproj = max(maxproj, abs(float(rt)))
    if al == be: Q0[al][al] = Q3.of(Q0[al][al]) + rt
    else:
        half = rt*Fr(1, 2); Q0[al][be] = Q3.of(Q0[al][be]) + half; Q0[be][al] = Q3.of(Q0[be][al]) + half
print(f"[{ident}] projected {len(resid) - (1 if gamma is not None else 0)} residual coefficients into block '1' (max |delta| {maxproj:.3e})", flush=True)
# ---- exact re-check of the identity with the modified block
total2 = {}
for nm, Q, basis, q in blocks: total2 = padd(total2, gram_poly(Q, basis, q))
check = padd(target, nf(total2), Q3(-1))
if gamma is not None: check = padd(check, pconst(gamma), Q3(-1))
identity_ok = (len(check) == 0)
print(f"[{ident}] EXACT IDENTITY target - sum sigma_b q_b" + (" - gamma" if gamma is not None else "") + f" == 0 : {identity_ok}", flush=True)
if gamma is not None:
    print(f"[{ident}] gamma_exact = {gamma.pretty()}  = {float(gamma):.15f}", flush=True)
# ---- exact PSD of every block
psd_ok = True; minpiv = float('inf'); worst = None; report = []
for bi_, (nm, Q, basis, q) in enumerate(blocks):
    t1 = time.time()
    ok, piv, info = ldl_exact(Q)
    mp_ = min((float(x) for x in piv), default=float('inf')) if ok else float('nan')
    report.append((nm, len(basis), ok, mp_))
    if not ok:
        psd_ok = False; print(f"   block {bi_} '{nm}' NOT PSD: {info[:2]}", flush=True)
    else:
        if mp_ < minpiv: minpiv = mp_; worst = nm
    if bi_ == 0: print(f"   block 0 '1' ({len(basis)}x{len(basis)}, Q(sqrt3) entries): PSD={ok}, min pivot {mp_:.3e} ({time.time()-t1:.1f}s)", flush=True)
print(f"[{ident}] ALL BLOCKS EXACTLY PSD: {psd_ok}; min pivot over all blocks {minpiv:.3e} (block '{worst}'); strictly positive definite: {all(r[3] > 0 for r in report)}", flush=True)
json.dump(dict(ident=ident, den=DEN, eps=eps, max_residual=maxres, max_projection=maxproj, identity_exact=identity_ok, psd_exact=psd_ok,
               min_pivot=minpiv, gamma=(gamma.pretty(), float(gamma)) if gamma is not None else None,
               blocks=[dict(name=r[0], n=r[1], psd=r[2], min_pivot=r[3]) for r in report], time=time.time()-t0),
          open(f'{OUTD}/exact_{ident}_den{DEN}.json', 'w'), indent=1)
print(f"[{ident}] done in {time.time()-t0:.1f}s -> exact_{ident}_den{DEN}.json", flush=True)
