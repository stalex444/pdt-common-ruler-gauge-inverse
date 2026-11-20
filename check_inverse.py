"""Replay the fixed-input gauge inverse and its local sensitivity with mpmath."""
from mpmath import mp

mp.dps = 50
EM = mp.mpf("137.036")
WEAK = mp.mpf("0.23121")
STRONG_REF = mp.mpf("0.1180")
STRONG_ERR = mp.mpf("0.0009")
WEAK_ERR = mp.mpf("0.00004")
K = (EM * mp.pi**2) ** (mp.mpf(1) / 15)
TURN = mp.mpf(7) / 6


def weak(b):
    return K**3 * (b - 1) / b**7


def strong(b):
    a = K / b
    return (1 - 1 / b)**3 / (4 * (1 - 1 / a)**3 * (b / a)**2)


def root(lo, hi, increasing):
    for _ in range(165):
        mid = (lo + hi) / 2
        if (weak(mid) < WEAK) == increasing:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def split_from_ratio(ruler, ratio):
    """Invert the positive ratio via t²(1+t), independently of the weak branches."""
    rhs = 4 * (ruler - 1) * ratio / ruler**2
    low, high = mp.mpf(0), max(mp.mpf(1), mp.root(rhs, 3))
    for _ in range(165):
        mid = (low + high) / 2
        if mid**2 * (1 + mid) < rhs:
            low = mid
        else:
            high = mid
    t = (low + high) / 2
    return (1 + ruler * t) / (1 + t)


if __name__ == "__main__":
    assert weak(K) < WEAK < weak(TURN)
    print("K =", mp.nstr(K, 16))
    for name, b, lower, upper in [
        ("rising", root(mp.mpf(1), TURN, True), "0.01923413", "0.01923414"),
        ("falling", root(TURN, K, False), "0.11728454", "0.11728455"),
    ]:
        a = K / b
        value = strong(b)
        assert abs((1 - 1 / b) / (b / a)**3 - WEAK) < mp.mpf("1e-47")
        assert mp.mpf(lower) < value < mp.mpf(upper)
        assert mp.almosteq(value, WEAK * K**2 * (b - 1)**2 / (4 * (K - b)**3))
        assert abs(split_from_ratio(K, value / WEAK) - b) < mp.mpf("1e-47")
        slope = mp.diff(strong, b) / mp.diff(weak, b)
        residual = (value - STRONG_REF) / STRONG_ERR
        print(name, "a, b, strong, residual / strong error, propagated weak error:",
              *(mp.nstr(v, 12) for v in (a, b, value, residual, abs(slope) * WEAK_ERR)))
