import random
from itertools import combinations_with_replacement


def triples(m):  # I_m^<: 1<=i<=j<=m, 1<=k<j, k!=i  (1-based)
    for j in range(1, m + 1):
        for i in range(1, j + 1):
            for k in range(1, j):
                if k != i:
                    yield i, j, k


# 1. identity on random reals
for m in range(2, 12):
    a = [None] + [random.uniform(-5, 5) for _ in range(m)]
    lhs = sum(a[i] + a[j] - a[k] for i, j, k in triples(m))
    rhs = sum((r * r - m) * a[r] for r in range(1, m + 1))
    assert abs(lhs - rhs) < 1e-9 * max(1, abs(lhs)), (m, lhs, rhs)
    assert sum(1 for _ in triples(m)) == m * (m - 1) * (2 * m - 1) // 6
print("identity + count OK for m=2..11")


# 2. greedy B3 sequence; check injectivity of w and the finite inequality on prefixes
def is_b3_add(S, sums, x):
    new = set()
    for a, b in combinations_with_replacement(S + [x], 2):
        s = a + b + x
        if s in sums or s in new:
            return None
        new.add(s)
    return new


S, sums, x = [], set(), 0
while len(S) < 40:
    x += 1
    nw = is_b3_add(S, sums, x)
    if nw is not None:
        S.append(x)
        sums |= nw
print("greedy B3 prefix:", S[:12], "... a_40 =", S[-1])
for m in [5, 10, 20, 30, 40]:
    a = [None] + S[:m]
    ws = [a[i] + a[j] - a[k] for i, j, k in triples(m)]
    N = len(ws)
    assert len(set(ws)) == N and min(ws) >= 2, "injectivity/positivity failed"
    lhs = sum((r * r - m) * a[r] for r in range(1, m + 1))
    print(
        f"m={m:2d} N={N:6d}  sum(r^2-m)a_r={lhs:12d}  >=  N(N+3)/2={N * (N + 3) // 2:12d} : {lhs >= N * (N + 3) // 2}"
    )
