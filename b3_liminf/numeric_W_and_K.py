# Marginal weight W_L(U) = W_X + W_Y - W_Z for Omega_L* = {0<X<=Y<=L, 0<Z<Y, X^3+Y^3-Z^3<=1}
from mpmath import cbrt, mp, mpf, quad

mp.dps = 30


def c3(t):
    return cbrt(t) if t > 0 else mpf(0)


def WX(U, L):  # X = U fixed: Y in (U, L], Z in (cbrt(max(0,U^3+Y^3-1)), Y)
    if U >= 1:
        return mpf(0)
    br = cbrt(1 - U**3)  # where U^3+Y^3-1 = 0
    f = lambda Y: Y - c3(U**3 + Y**3 - 1)
    pts = [U] + ([br] if U < br < L else []) + [L]
    return quad(f, pts)


def WY(
    U,
):  # Y = U fixed: X in (0, min(U,1)], Z in (cbrt(max(0,X^3+U^3-1)), U); need X^3 + U^3 - Z^3 <= 1
    hi = min(U, mpf(1))
    br = cbrt(1 - U**3) if U < 1 else mpf(0)
    f = lambda X: U - c3(X**3 + U**3 - 1)
    pts = [mpf(0)] + ([br] if 0 < br < hi else []) + [hi]
    return quad(f, pts)


def WZ(
    U, L
):  # Z = U fixed: Y in (max(X,U), min(L, cbrt(U^3+1-X^3))), X in (0,1), X <= Y
    def f(X):
        lo = max(X, U)
        up = min(L, cbrt(U**3 + 1 - X**3))
        return up - lo if up > lo else mpf(0)

    # breakpoints: X=U, and X where cbrt(U^3+1-X^3)=L, and X where cbrt(U^3+1-X^3)=X
    pts = [mpf(0)]
    for b in [U, cbrt(max(mpf(0), U**3 + 1 - L**3)), cbrt((U**3 + 1) / 2)]:
        if 0 < b < 1:
            pts.append(b)
    pts = sorted(set(pts)) + [mpf(1)]
    return quad(f, pts)


def W(U, L):
    return WX(U, L) + WY(U) - WZ(U, L)


K = quad(lambda t: quad(lambda z: 1 / (1 + t**3 - z**3), [0, 1]), [0, 1]) / 3
print("K_* =", K, " K_*^(-1/3) =", K ** (-mpf(1) / 3))
for L in [mpf(1), cbrt(2), mpf(2), mpf(10), mpf(1000)]:
    vals = [(U, W(U, L)) for U in [mpf(k) / 200 for k in range(1, 200)]]
    mn = min(vals, key=lambda p: p[1])
    print(
        f"L={float(L):8.4f}  min W on (0,1) grid = {float(mn[1]): .6e} at U={float(mn[0]):.3f}   W(0.01)={float(W(mpf('0.01'), L)):.3e}  W(0.99)={float(W(mpf('0.99'), L)):.3e}"
    )
