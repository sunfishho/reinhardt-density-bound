import sys, time, json; sys.path.insert(0, '/Users/matthewho/Downloads/Stanford/convex_problems/open_problems/trajectories/fable_5_1_review/semantic_overlap_review/main_results/recovered_audit_checks/reinhardt')
from m12_problem import *
import sympy as sp
t0 = time.time()
out = {}
print("== symbolic checks of problem data ==")
print("det X =", sp.factor(X.det()), "   (should be h^2 - a^2 - p^2)")
print("tr X =", X.trace(), "; R^T R =", matred(R.T*R) == sp.eye(2), "; R^3 =", matred(R**3), "; R = exp(J pi/3):", matred(R) == sp.Matrix([[sp.Rational(1,2), -s3/2],[s3/2, sp.Rational(1,2)]]))
for k in range(3):
    print(f" Z_{k} =", ZK[k].tolist(), " rho_{k} = -tr(X Z_k) =", RHO[k], " N_k comps (a',p',h') =", NK_COMPS[k], " tr N_k =", red3(NK[k].trace()))
# permutation property R Z_k R^{-1} in {Z_j}
def which(Zm):
    for j, Z in enumerate(ZK):
        if matred(Zm - Z) == sp.zeros(2, 2): return j
    return None
print(" R Z_k R^-1 = Z_perm(k):", [which(matred(R*ZK[k]*R.T)) for k in range(3)], "  R^-1 Z_k R = Z_.(k):", [which(matred(R.T*ZK[k]*R)) for k in range(3)])
# vertex reduction:  W(u) = I + delta(u) X Z_u,  delta = -2/tr(Z_u X);  claim W(u) = sum_k lam_k W_k, lam_k = u_k rho_k / sum_j u_j rho_j
u0, u1, u2 = sp.symbols('u0 u1 u2')
Zu = Z_of_u(u0, u1, u2)
Zu_lin = u0*ZK[0] + u1*ZK[1] + u2*ZK[2]
print(" Z_u affine = sum u_k Z_k (on sum u = 1):", matred((Zu - Zu_lin).subs(u0, 1 - u1 - u2)) == sp.zeros(2, 2))
trZuX = red3((Zu*X).trace()); print(" tr(Z_u X) = -(sum u_k rho_k):", sp.simplify(red3(trZuX + (u0*RHO[0] + u1*RHO[1] + u2*RHO[2]).subs(u0, 1-u1-u2)).subs(u0, 1-u1-u2)) == 0)
Wu = I2 - 2*X*Zu/trZuX
Wsum = sp.zeros(2, 2)
for k, u_ in enumerate([u0, u1, u2]):
    Wsum += ((u_*RHO[k])/(u0*RHO[0] + u1*RHO[1] + u2*RHO[2]))*(I2 + 2*X*ZK[k]/RHO[k])
diffW = (Wu - Wsum).subs(u0, 1 - u1 - u2).subs(s3, sp.sqrt(3))
print(" W(u) == sum_k lam_k W_k(X) (lam_k = u_k rho_k/sum_j u_j rho_j):", all(sp.simplify(sp.together(e)) == 0 for e in diffW))
# tangency: tr(X W_k) = 0 identically (=> det X conserved), h-component of R^-1 X R equals h
for k in range(3):
    print(f" tr(X N_{k}) =", sp.simplify(red3((X*NK[k]).trace())), end=';')
print("\n (a,p,h)-components of R^-1 X R:", conj_comps(R), " ; of R^-2 X R^2:", conj_comps(matred(R**2)))
# star/half-plane correspondence: hv_hp_j == (15 sqrt3/2) rho_k - 1 for some k ?
C = constraint_polys()
for j in range(3):
    match = [k for k in range(3) if sp.expand(red3(C[f'hv_hp{j}'] - (15*s3/2*RHO[k] - 1))) == 0]
    print(f" hv_hp{j} = (15 sqrt3/2)*rho_k - 1 for k =", match, "  poly:", C[f'hv_hp{j}'])
# horoball images: Moebius R.z, check R.(inf) = 1/sqrt3 and diameter 8/27
z = sp.symbols('z')
Rz = (R[0,0]*z + R[0,1])/(R[1,0]*z + R[1,1])
print(" R.oo =", sp.limit(Rz.subs(s3, sp.sqrt(3)), z, sp.oo), "; R^2.oo =", sp.limit(((R**2)[0,0]*z + (R**2)[0,1])/((R**2)[1,0]*z + (R**2)[1,1]).subs(s3, sp.sqrt(3)), z, sp.oo))
# image of the horocycle y=9/2 under R: top point height = 1/(c^2 y0) with c = sqrt3/2 -> 8/27
print(" image horoball diameter 1/(c^2*4.5) =", sp.nsimplify(1/((sp.sqrt(3)/2)**2*sp.Rational(9,2))))
print(" all constraint names:", list(C.keys()))
for nm, pol in C.items(): print("   ", nm, "=", pol)

print("\n== build exact targets from the stored V ==")
V, meta = load_V(sys.argv[1])
print(" V: #terms", len(V.as_ordered_terms()), " degree", sp.Poly(V, *SYMS).total_degree(), " region meta:", {k: meta[k] for k in ('d','Cg','CX','rhomin','products','xregion','sym3','tstar','eps_H1','eps_H2')})
targets = {}
for k in range(3):
    t1 = time.time()
    Hk = H_of_V_sympy(V, k)
    pd = nf(from_sympy(Hk, SYMS, s3))
    targets[f'H1_{k}'] = pd
    print(f" H_{k}(V): raw terms {len(sp.Poly(Hk, *SYMS, s3).terms())}, normal form terms {len(pd)}, degree {pdeg(pd)}, all standard: {all(is_standard(e) for e in pd)}  ({time.time()-t1:.1f}s)")
t1 = time.time()
H2 = H2_target_sympy(V)
pd2 = nf(from_sympy(H2, SYMS, s3)); targets['H2'] = pd2
print(f" H2 target V(R,R^-1XR)-V(I,X): normal form terms {len(pd2)}, degree {pdeg(pd2)}, only X-variables: {all(sum(e[:4])==0 for e in pd2)}  ({time.time()-t1:.1f}s)")
# cross-check my nf against sympy's groebner/reduced on the H2 target and on H1_0
G = sp.groebner([g11*g22 - g12*g21 - 1, h**2 - a**2 - p**2 - 1], g11, g22, g12, g21, h, a, p, order='lex')
print(" sympy Groebner basis:", list(G.exprs))
for name in ['H2', 'H1_0']:
    t1 = time.time()
    raw = H2 if name == 'H2' else H_of_V_sympy(V, 0)
    raw_r = raw.subs(s3, sp.sqrt(3))
    _, rem = sp.reduced(sp.expand(raw_r), list(G.exprs), g11, g22, g12, g21, h, a, p, order='lex')
    mine = to_sympy(targets[name], SYMS, s3).subs(s3, sp.sqrt(3))
    print(f" nf cross-check ({name}): sympy remainder == my normal form:", sp.expand(rem - mine) == 0, f"({time.time()-t1:.1f}s)")
# save
cons_json = {nm: poly_to_json(from_sympy(pol, SYMS, s3)) for nm, pol in C.items()}
json.dump(dict(targets={k: poly_to_json(v) for k, v in targets.items()}, constraints=cons_json,
               rho=[poly_to_json(from_sympy(r, SYMS, s3)) for r in RHO],
               nk=[[poly_to_json(from_sympy(c, SYMS, s3)) for c in comps_] for comps_ in NK_COMPS]),
          open(sys.argv[2], 'w'))
print(f"saved targets.json  (total {time.time()-t0:.1f}s)")
