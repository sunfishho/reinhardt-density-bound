"""
M12 independent verification library (written from scratch; only the FILE FORMAT conventions of M6 are reused:
variables (g11,g12,g21,g22,a,p,h) as exponent tuples of length 7, X = [[a, p-h],[p+h, -a]]).
  * Q3      : exact arithmetic in Q(sqrt3), elements a + b*sqrt3 with Fraction a,b
  * polys   : dict {exponent tuple (len 7): Q3}
  * nf      : normal form modulo the ideal <g11*g22 - g12*g21 - 1, h^2 - a^2 - p^2 - 1>
              (Groebner basis for lex g11 > g22 > ... and h > a > p: leading monomials g11*g22 and h^2 are coprime,
              so Buchberger's criterion makes the two generators a Groebner basis; reduction = substitution, worklist version)
  * ldl_exact : exact LDL^T (symmetric Gaussian elimination without pivoting) -> PSD test
"""
from fractions import Fraction as Fr
import math, itertools

class Q3:
    __slots__ = ('a', 'b')
    def __init__(self, a=0, b=0):
        self.a = a if type(a) is Fr else Fr(a)
        self.b = b if type(b) is Fr else Fr(b)
    @staticmethod
    def of(x):
        return x if isinstance(x, Q3) else Q3(x, 0)
    def __add__(s, o):
        o = Q3.of(o); return Q3(s.a + o.a, s.b + o.b)
    __radd__ = __add__
    def __sub__(s, o):
        o = Q3.of(o); return Q3(s.a - o.a, s.b - o.b)
    def __rsub__(s, o):
        return Q3.of(o) - s
    def __neg__(s):
        return Q3(-s.a, -s.b)
    def __mul__(s, o):
        o = Q3.of(o); return Q3(s.a*o.a + 3*s.b*o.b, s.a*o.b + s.b*o.a)
    __rmul__ = __mul__
    def inv(s):
        n = s.a*s.a - 3*s.b*s.b
        if n == 0: raise ZeroDivisionError
        return Q3(s.a/n, -s.b/n)
    def __truediv__(s, o):
        return s * Q3.of(o).inv()
    def __rtruediv__(s, o):
        return Q3.of(o) * s.inv()
    def iszero(s):
        return s.a == 0 and s.b == 0
    def sign(s):
        """exact sign of a + b*sqrt3."""
        a, b = s.a, s.b
        if b == 0: return (a > 0) - (a < 0)
        if a == 0: return (b > 0) - (b < 0)
        sa = 1 if a > 0 else -1; sb = 1 if b > 0 else -1
        if sa == sb: return sa
        # opposite signs: |a| vs |b|sqrt3  <=>  a^2 vs 3 b^2
        return sa if a*a > 3*b*b else sb
    def __eq__(s, o):
        o = Q3.of(o); return s.a == o.a and s.b == o.b
    def __hash__(s): return hash((s.a, s.b))
    def __lt__(s, o): return (s - Q3.of(o)).sign() < 0
    def __le__(s, o): return (s - Q3.of(o)).sign() <= 0
    def __gt__(s, o): return (s - Q3.of(o)).sign() > 0
    def __ge__(s, o): return (s - Q3.of(o)).sign() >= 0
    def __abs__(s): return s if s.sign() >= 0 else -s
    def __float__(s): return float(s.a) + float(s.b)*math.sqrt(3.0)
    def mpf(s, mp):
        return mp.mpf(s.a.numerator)/s.a.denominator + mp.mpf(s.b.numerator)/s.b.denominator*mp.sqrt(3)
    def __repr__(s):
        return f"Q3({s.a}, {s.b})"
    def pretty(s):
        return f"{s.a} + ({s.b})*sqrt3"

SQ3 = Q3(0, 1)
ONE = Q3(1, 0)
ZEROQ = Q3(0, 0)
NV = 7
G11, G12, G21, G22, A, P, H = range(7)
E0 = (0,)*NV

def emono(i, k=1):
    e = [0]*NV; e[i] = k; return tuple(e)

# ------------------------------------------------------------------ polynomial dicts
def padd(p, q, s=None):
    """p + s*q (s Q3 or number, default 1)."""
    r = dict(p)
    for e, c in q.items():
        v = r.get(e)
        cs = c if s is None else c*s
        v = cs if v is None else v + cs
        if v.iszero(): r.pop(e, None)
        else: r[e] = v
    return r
def pneg(p): return {e: -c for e, c in p.items()}
def pscale(p, s):
    s = Q3.of(s)
    if s.iszero(): return {}
    return {e: c*s for e, c in p.items()}
def pmul(p, q):
    r = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            e = tuple(x + y for x, y in zip(e1, e2))
            c = c1*c2
            v = r.get(e)
            r[e] = c if v is None else v + c
    return {e: c for e, c in r.items() if not c.iszero()}
def pconst(c): return {E0: Q3.of(c)} if not Q3.of(c).iszero() else {}
def pvar(i): return {emono(i): ONE}
def pderiv(p, i):
    r = {}
    for e, c in p.items():
        if e[i]:
            e2 = list(e); e2[i] -= 1; e2 = tuple(e2)
            v = c*e[i]
            r[e2] = r[e2] + v if e2 in r else v
    return r
def pdeg(p): return max((sum(e) for e in p), default=-1)
def is_standard(e): return not (e[G11] >= 1 and e[G22] >= 1) and e[H] <= 1

def nf(p):
    """normal form modulo <g11 g22 - g12 g21 - 1, h^2 - a^2 - p^2 - 1>; worklist substitution."""
    out = {}
    work = list(p.items())
    while work:
        e, c = work.pop()
        if e[G11] >= 1 and e[G22] >= 1:
            e1 = list(e); e1[G11] -= 1; e1[G22] -= 1
            e2 = list(e1); e2[G12] += 1; e2[G21] += 1
            work.append((tuple(e1), c)); work.append((tuple(e2), c))
        elif e[H] >= 2:
            e1 = list(e); e1[H] -= 2
            e2 = list(e1); e2[A] += 2
            e3 = list(e1); e3[P] += 2
            work.append((tuple(e1), c)); work.append((tuple(e2), c)); work.append((tuple(e3), c))
        else:
            v = out.get(e)
            out[e] = c if v is None else v + c
    return {e: c for e, c in out.items() if not c.iszero()}

def std_monomials(maxdeg, var_idx=range(NV)):
    """standard monomials of total degree <= maxdeg in the given variables (all degrees)."""
    out = []
    var_idx = list(var_idx)
    for deg in range(maxdeg + 1):
        for comb in itertools.combinations_with_replacement(var_idx, deg):
            e = [0]*NV
            for i in comb: e[i] += 1
            e = tuple(e)
            if is_standard(e): out.append(e)
    return out

def peval_float(p, x):
    """float evaluation at x (len 7)."""
    tot = 0.0
    for e, c in p.items():
        t = float(c)
        for i in range(NV):
            if e[i]: t *= x[i]**e[i]
        tot += t
    return tot

def pmax_abs_float(p): return max((abs(float(c)) for c in p.values()), default=0.0)

# ------------------------------------------------------------------ sympy interface
def from_sympy(expr, syms, s3):
    """expr polynomial in syms (7 symbols, in variable order) and s3 (= sqrt3 symbol) with rational coeffs -> dict."""
    import sympy as sp
    P = sp.Poly(sp.expand(expr), *syms, s3, domain='QQ')
    out = {}
    for mon, coef in P.terms():
        e = tuple(int(m) for m in mon[:NV]); k = int(mon[NV])
        c = Fr(int(coef.numerator), int(coef.denominator))
        # s3^k -> 3^(k//2) * s3^(k%2)
        c = c * (3**(k//2))
        q = Q3(c, 0) if k % 2 == 0 else Q3(0, c)
        v = out.get(e)
        out[e] = q if v is None else v + q
    return {e: c for e, c in out.items() if not c.iszero()}

def to_sympy(p, syms, s3):
    import sympy as sp
    tot = sp.Integer(0)
    for e, c in p.items():
        m = sp.Integer(1)
        for i in range(NV):
            if e[i]: m *= syms[i]**e[i]
        tot += (sp.Rational(c.a.numerator, c.a.denominator) + sp.Rational(c.b.numerator, c.b.denominator)*s3)*m
    return tot

# ------------------------------------------------------------------ exact linear algebra
def ldl_exact(Q):
    """Q: list of lists of Q3, symmetric.  Returns (is_psd, pivots(list of Q3), fail_info).
    Symmetric Gaussian elimination without pivoting: Q PSD  <=>  all pivots >= 0 and each zero pivot has a zero column."""
    n = len(Q)
    A = [[Q3.of(Q[i][j]) for j in range(n)] for i in range(n)]
    pivots = []
    for j in range(n):
        d = A[j][j]
        sgn = d.sign()
        if sgn < 0:
            return False, pivots, ('negative pivot', j, d)
        pivots.append(d)
        if sgn == 0:
            for i in range(j + 1, n):
                if not A[i][j].iszero():
                    return False, pivots, ('zero pivot with nonzero column', j, i)
            continue
        dinv = d.inv()
        rowj = A[j]
        for i in range(j + 1, n):
            lij = A[i][j]
            if lij.iszero(): continue
            f = lij*dinv
            rowi = A[i]
            for k in range(i, n):        # lower triangle only (k >= i)
                if not rowj[k].iszero():
                    rowi[k] = rowi[k] - f*rowj[k]
        # mirror the updated lower triangle into the upper triangle for rows > j (needed since we read rowj[k] for k>=i)
        for i in range(j + 1, n):
            rowi = A[i]
            for k in range(i + 1, n):
                A[k][i] = rowi[k]
    return True, pivots, None
