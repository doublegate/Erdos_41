# Rigorous, fully directed-rounding certificate that W_2(U) > 0 for all U in (0,1).
#
# Omega_L = {0 < X <= Y <= L, 0 < Z < Y, X^3 + Y^3 - Z^3 <= 1},  L = 2.
# W_L(U) = W_X(U) + W_Y(U) - W_Z(U), the areas of the slices X = U, Y = U, Z = U.
#
# For U in a cell [u0, u1]:
#   W_X(U) >= W_X(u1)                    (W_X is non-increasing in U)
#   W_Y(U) >= area{0<X<=u0, 0<Z<u0, Z^3 >= X^3 + u1^3 - 1}     (subset of the Y = U slice)
#   W_Z(U) <= area{0<X<1, max(X,u0) < Y < cbrt(u1^3 + 1 - X^3)} (superset of the Z = U slice)
# Every integrand below is monotone on the range where it is integrated, so a Riemann sum
# taken at the appropriate cell endpoint is a lower (resp. upper) bound for the integral.
# All arithmetic is mpmath interval arithmetic (outward/directed rounding); every lower bound
# is the lower endpoint of an enclosing interval and every upper bound the upper endpoint.
import sys

from mpmath import iv, mpf

iv.dps = 40
ONE_THIRD = iv.mpf(1) / 3  # interval enclosing 1/3
ZERO = iv.mpf(0)
L = iv.mpf(2)


def cbrt_pos(x):
    """Enclosure of cbrt(max(0, x)) for an interval x (directed rounding)."""
    if x.b <= 0:
        return ZERO
    hi = (iv.mpf(x.b) ** ONE_THIRD).b
    lo = mpf(0) if x.a <= 0 else (iv.mpf(x.a) ** ONE_THIRD).a
    return iv.mpf([lo, hi])


def riemann_lower(f, a, b, n, mono):
    """Guaranteed lower bound of the integral of f >= 0 over [a,b] (a,b intervals); f monotone."""
    lo_a, hi_b = a.b, b.a  # integrate only over [a.b, b.a] (f >= 0 => lower bound)
    if not hi_b > lo_a:
        return ZERO  # interval zero: keeps every later sum in outward-rounded iv arithmetic
    A, B = iv.mpf(lo_a), iv.mpf(hi_b)
    h = (B - A) / n
    s = ZERO
    for k in range(n):
        x = (
            A + h * k if mono == "inc" else A + h * (k + 1)
        )  # minimum of a monotone f on the cell
        s += f(x)
    return (s * h).a


def riemann_upper(f, a, b, n, mono):
    """Guaranteed upper bound of the integral of f >= 0 over [a,b] (a,b intervals); f monotone."""
    A, B = (
        iv.mpf(a.a),
        iv.mpf(b.b),
    )  # integrate over the enlarged [a.a, b.b] (f >= 0 => upper bound)
    if not B.b > A.a:
        return ZERO
    h = (B - A) / n
    s = ZERO
    for k in range(n):
        x = (
            A + h * (k + 1) if mono == "inc" else A + h * k
        )  # maximum of a monotone f on the cell
        s += f(x)
    return (s * h).b


N = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
M = int(sys.argv[2]) if len(sys.argv) > 2 else 200


def WX_low(u):
    # X = u: integrand g(Y) = Y - cbrt(max(0, u^3 + Y^3 - 1)), Y in [u, L].
    # g is increasing (= Y) for Y^3 <= 1 - u^3 and decreasing afterwards.
    # br = cbrt(1 - u^3) is only known as an interval; the sliver between br.a and br.b is dropped
    # (g >= 0), so the result stays a lower bound.
    U = iv.mpf(u)
    br = cbrt_pos(1 - U**3)
    g = lambda Y: Y - cbrt_pos(U**3 + Y**3 - 1)
    lo1 = riemann_lower(g, U, iv.mpf(br.a), N, "inc") if br.a > U.b else ZERO
    start = br if br.b > U.a else U
    lo2 = riemann_lower(g, iv.mpf(max(start.b, U.b)), L, N, "dec")
    return lo1 + lo2


def WY_low(u0, u1):
    U0, U1 = iv.mpf(u0), iv.mpf(u1)

    def f(X):  # (u0 - cbrt(max(0, X^3 + u1^3 - 1)))_+ , non-increasing in X
        v = U0 - cbrt_pos(X**3 + U1**3 - 1)
        return iv.mpf(max(mpf(0), v.a))  # lower enclosure of the positive part

    return riemann_lower(f, ZERO, U0, N, "dec")


def WZ_up(u0, u1):
    U0, U1 = iv.mpf(u0), iv.mpf(u1)

    def f(X):  # (cbrt(u1^3 + 1 - X^3) - max(X, u0))_+ , non-increasing in X
        m = iv.mpf([max(X.a, U0.a), max(X.b, U0.b)])
        v = cbrt_pos(U1**3 + 1 - X**3) - m
        return iv.mpf(max(mpf(0), v.b))  # upper enclosure of the positive part

    return riemann_upper(f, ZERO, iv.mpf(1), N, "dec")


def lower_endpoint(x):
    """Exact lower endpoint of an interval (or number), as a degenerate interval: comparisons are decisive."""
    v = iv.mpf(x)
    return iv.mpf(v.a)


worst = None
for k in range(M):
    u0, u1 = (
        mpf(k) / M,
        mpf(k + 1) / M,
    )  # consecutive cells share the same endpoint value
    total = (
        iv.mpf(WX_low(u1)) + iv.mpf(WY_low(u0, u1)) - iv.mpf(WZ_up(u0, u1))
    )  # outward-rounded
    lb = lower_endpoint(total)
    positive = lb > 0
    if positive is not True:  # False or undecided both count as failure
        print(f"FAIL: lower bound {lb} not certified > 0 on cell [{u0}, {u1}]")
        sys.exit(1)
    if worst is None or (lb < worst[0]) is True:
        worst = (lb, u0, u1)
print(
    f"CERTIFIED (directed rounding, N={N}, M={M}): W_2(U) >= {iv.nstr(worst[0], 10)} for all U in (0,1); "
    f"worst cell [{float(worst[1]):.4f}, {float(worst[2]):.4f}]"
)
