"""Independent exact checks of the field index and the gauge inverse (SymPy)."""

from itertools import product

from sympy import Poly, QQ, Rational, symbols
from sympy.polys.rings import ring


def check_fibers():
    _, x, y = ring("x,y", QQ)
    count = 0
    quadratic_cases = []
    for n, m in product(range(2, 8), range(2, 13)):
        weak_difference = (x - 1) * y**n - (y - 1) * x**n
        rulers = {QQ(4, 3), QQ(3, 2), QQ(2), QQ(3), QQ(n), QQ(n, n - 1)}
        for ruler in sorted(rulers):
            ratio_difference = (x - 1)**2 * (y - ruler)**m - (y - 1)**2 * (x - ruler)**m
            common_factor = weak_difference.gcd(ratio_difference).monic()
            expected = x - y
            if (n, m, ruler) == (2, 4, 2):
                expected *= x*y - x - y
                quadratic_cases.append((n, m, ruler))
            if common_factor != expected.monic():
                raise AssertionError((n, m, ruler, common_factor))
            count += 1
    assert quadratic_cases == [(2, 4, 2)]
    print(f"{count} exact generic-fiber checks passed, including the quadratic exception.")


def check_rational_inverse():
    variable = symbols("T")
    count = 0
    for ruler, t in product(map(Rational, ("4/3", "3/2", "2", "3", "7")),
                            map(Rational, ("1/3", "1/2", "1", "2", "5"))):
        x = (1 + ruler*t) / (1 + t)
        weak = ruler**3 * (x - 1) / x**7
        ratio = ruler**2 * (x - 1)**2 / (4*(ruler - x)**3)
        r = 4 * (ruler - 1) * ratio / ruler**2
        weak_equation = Poly(weak*(1 + ruler*variable)**7
                             - ruler**3*(ruler - 1)*variable*(1 + variable)**6, variable)
        ratio_equation = Poly(variable**3 + variable**2 - r, variable)
        remainder = weak_equation.rem(ratio_equation)
        a, b, c = (remainder.nth(i) for i in (2, 1, 0))
        denominator = b**2 - a*c - a*b
        if not denominator or (r*a**2 + a*c - b*c)/denominator != t:
            raise AssertionError((ruler, t, denominator))
        count += 1
    print(f"{count} rational inverse evaluations passed using exact polynomial division.")


if __name__ == "__main__":
    check_fibers()
    check_rational_inverse()
