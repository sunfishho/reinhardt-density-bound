"""
Independent (sympy) construction of all problem data for the M12 verification.
Conventions (file format only): variables x = (g11, g12, g21, g22, a, p, h); X = [[a, p-h],[p+h, -a]] (b = p-h, c = p+h),
det X = h^2 - a^2 - p^2 = 1;  L = (3/2)(c - b) = 3h.
Everything else (Z_k, rho_k, N_k, R, constraints) is derived here from the papers:
  Hales 2017 (3),(6),(7),(14): Z_u = [[a,b],[c,-a]], a=(u1-u2)/sqrt3, b=(u0-2u1-2u2)/3, c=u0;  X' = X(delta Z_u - X), delta = -2/tr(Z_u X)
  Hales 2017 (28): g(0)=I, g(tf)=R=exp(J pi/3), X(tf) = R^{-1} X(0) R
  HV 2024 Def 5.0.1: h** = h* minus {y>4.5}, its R,R^2 horoball images (radius 4/27 at +-1/sqrt3), and {y > 15(1/sqrt3 - x)} + R,R^2 images
"""
import sympy as sp, json, os
from fractions import Fraction as Fr
from m12lib import *

g11, g12, g21, g22, a, p, h, s3 = sp.symbols('g11 g12 g21 g22 a p h s3')
SYMS = [g11, g12, g21, g22, a, p, h]
INV_S3 = s3/3                      # 1/sqrt3 = sqrt3/3  (keep everything polynomial in s3)
def red3(expr):
    """reduce s3^2 -> 3 in a sympy expression (polynomial in s3)."""
    P = sp.Poly(sp.expand(expr), s3)
    out = 0
    for (k,), c in P.terms():
        out += c * 3**(k//2) * (s3 if k % 2 else 1)
    return sp.expand(out)

gmat = sp.Matrix([[g11, g12], [g21, g22]])
X = sp.Matrix([[a, p - h], [p + h, -a]])
b_ = p - h; c_ = p + h
I2 = sp.eye(2)
J = sp.Matrix([[0, -1], [1, 0]])
R = sp.Matrix([[sp.Rational(1, 2), -s3/2], [s3/2, sp.Rational(1, 2)]])    # exp(J pi/3)
Rinv = R.T
def matred(M): return M.applyfunc(red3)

def Z_of_u(u0, u1, u2):
    return sp.Matrix([[(u1 - u2)*INV_S3, sp.Rational(1, 3)*u0 - sp.Rational(2, 3)*u1 - sp.Rational(2, 3)*u2], [u0, -(u1 - u2)*INV_S3]])
ZK = [Z_of_u(1, 0, 0), Z_of_u(0, 1, 0), Z_of_u(0, 0, 1)]
RHO = [red3(-(X*Z).trace()) for Z in ZK]                        # rho_k = -tr(X Z_k)
NK = [matred(rho*I2 + 2*X*Z) for rho, Z in zip(RHO, ZK)]       # N_k = rho_k W_k,  W_k = I + (2/rho_k) X Z_k
def comps(M):
    """(a,p,h)-components of a traceless matrix M = a D + p S + h J, D=diag(1,-1), S=[[0,1],[1,0]], J=[[0,-1],[1,0]]."""
    return (red3(M[0, 0]), red3((M[0, 1] + M[1, 0])/2), red3((M[1, 0] - M[0, 1])/2))
NK_COMPS = [comps(N) for N in NK]
L = 3*h                                                        # (3/2)(c - b)

def H_of_V_sympy(V, k):
    gX = gmat*X
    dgV = sum(sp.diff(V, gmat[i, j])*gX[i, j] for i in range(2) for j in range(2))
    dXV = sp.diff(V, a)*NK_COMPS[k][0] + sp.diff(V, p)*NK_COMPS[k][1] + sp.diff(V, h)*NK_COMPS[k][2]
    return red3(RHO[k]*(L - dgV) - dXV)

def conj_comps(M):
    """(a,p,h)-components of M^{-1} X M for M orthogonal (M^{-1} = M^T)."""
    return comps(matred(M.T*X*M))

def H2_target_sympy(V):
    ar, pr, hr = conj_comps(R)                                 # X -> R^{-1} X R
    VR = V.subs({g11: R[0, 0], g12: R[0, 1], g21: R[1, 0], g22: R[1, 1]}, simultaneous=True)
    VR = VR.subs({a: ar, p: pr, h: hr}, simultaneous=True)
    VI = V.subs({g11: 1, g12: 0, g21: 0, g22: 1}, simultaneous=True)
    return red3(VR - VI)

def load_V(meta_path):
    meta = json.load(open(meta_path))
    V = 0
    for e, c in zip(meta['Vbasis'], meta['v']):
        if c == 0: continue
        fr = Fr(c)                                            # exact dyadic value of the stored double
        mon = 1
        for i, k in enumerate(e):
            if k: mon *= SYMS[i]**k
        V += sp.Rational(fr.numerator, fr.denominator)*mon
    return V, meta

# ---------------------------------------------------------------- region constraints (mine)
def constraint_polys(Cg=Fr(16, 5), hmax=Fr(12, 5), rhomin=Fr(769, 10000)):
    """dict name -> sympy polynomial (in SYMS and s3), each >= 0 on the region S."""
    C = {}
    Cg = sp.Rational(Cg.numerator, Cg.denominator); hmax = sp.Rational(hmax.numerator, hmax.denominator)
    rhomin = sp.Rational(rhomin.numerator, rhomin.denominator)
    # sector theta in [0, pi/3]  <=>  g21 >= 0  and  sqrt3 g22 - g21 >= 0 ; and the same for R^j g R^{-j}
    def sector(M):
        return red3(M[1, 0]), red3(s3*M[1, 1] - M[1, 0])
    C['s1'], C['s2'] = sector(gmat)
    for j in (1, 2):
        Rj = matred(R**j)
        C[f's1r{j}'], C[f's2r{j}'] = sector(matred(Rj*gmat*Rj.T))
    C['qg'] = Cg - (g11**2 + g12**2 + g21**2 + g22**2)
    for k in range(3): C[f'rho{k}'] = RHO[k] - rhomin
    C['h-1'] = h - 1
    C['hmax-h'] = hmax - h
    C['qX'] = (hmax**2 - 1) - a**2 - p**2
    # HV h**: y <= 4.5 (y = 1/c)
    C['hv_y'] = c_ - sp.Rational(2, 9)
    # horoballs at +-1/sqrt3 of radius 4/27: (x -+ 1/sqrt3)^2 + y^2 - (8/27) y >= 0, times c^2 (x = a/c, y = 1/c)
    C['hv_hb+'] = red3((a - c_*INV_S3)**2 + 1 - sp.Rational(8, 27)*c_)
    C['hv_hb-'] = red3((a + c_*INV_S3)**2 + 1 - sp.Rational(8, 27)*c_)
    # half-plane exclusion: y <= 15(1/sqrt3 - x), times c:  15(c/sqrt3 - a) - 1 >= 0 ; and X -> R^{-j} X R^{j}
    hp0 = red3(15*(c_*INV_S3 - a) - 1)
    C['hv_hp0'] = hp0
    for j in (1, 2):
        aj, pj, hj = conj_comps(matred(R**j))
        C[f'hv_hp{j}'] = red3(hp0.subs({a: aj, p: pj, h: hj}, simultaneous=True))
    return C

LIN_G = ['s1', 's2', 's1r1', 's2r1', 's1r2', 's2r2']
LIN_X = ['rho0', 'rho1', 'rho2', 'h-1', 'hmax-h']

def q_for_name(name, C):
    """constraint product polynomial (sympy) for a block name ('1', single name, or 'A*B')."""
    if name == '1': return sp.Integer(1)
    if '*' in name:
        n1, n2 = name.split('*')
        return red3(C[n1]*C[n2])
    return C[name]

def poly_to_json(pd):
    return [[list(e), str(c.a), str(c.b)] for e, c in sorted(pd.items())]
def poly_from_json(lst):
    return {tuple(e): Q3(Fr(sa), Fr(sb)) for e, sa, sb in lst}
