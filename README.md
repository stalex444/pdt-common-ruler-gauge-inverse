# Three Gauge Couplings on a Common Ruler

At exponent 15, the PDT electromagnetic formula fixes a single product, $K=ab$. The weak mixing angle admits two ways to divide that same ruler between $a$ and $b$. What does each split imply for the strong coupling?

For the rounded electroweak inputs $\alpha^{-1}=137.036$ and $\sin^2\hat\theta_W(M_Z)=0.23121$, **exactly two pairs of real bases $a,b>1$ satisfy both formulas**. Lean proves the following enclosures using those two inputs alone. The displayed $a$ values are approximate.

| Split of the ruler | $a$ | Certified interval for $b$ | Certified interval for $\alpha_s$ |
|---|---:|---|---|
| Rising weak response | 1.43916239 | [1.1236537214, 1.1236537215] | [0.01923413, 0.01923414] |
| Falling weak response | 1.32524833 | [1.2202393601, 1.2202393603] | [0.11728454, 0.11728455] |

PDT’s proposed bases are the real roots $\rho>1$ of $\rho^3=\rho+1$ and $Q>1$ of $Q^4=Q+1$. The weak response turns at $b=7/6$. The quartic places $Q\approx1.22074408$ above that turn, identifying the falling branch before comparing the strong value. Its fitted coordinate is $b\approx1.22023936$. The headline theorem proves existence, exhaustion and both strong enclosures together in `PDTGauge.Result.two_electroweak_solutions`. [Formal statement](Challenge.lean) · [Lean proof](Solution.lean)

## How the common ruler works

Let $\lambda(x)=1-1/x$, $\psi=b/a$ and let $p$ be a fixed positive integer. The three formulas from the earlier arithmetic classification are

$$
A=\frac{(ab)^p}{\pi^2},\qquad W=\frac{\lambda(b)}{\psi^3},\qquad
S=\frac{\lambda(b)^3}{4\lambda(a)^3\psi^2}.
$$

The electromagnetic reading $A$ fixes $K=(\pi^2 A)^{1/p}$. For admissible bases, $K>1$, $1<b<K$ and $a=K/b$. Substitution gives

$$
W_K(b)=K^3\frac{b-1}{b^7},\qquad
W'_K(b)=K^3\frac{7-6b}{b^8},\qquad
R_K(b)=\frac{S}{W}=\frac{K^2(b-1)^2}{4(K-b)^3}.
$$

When $K>7/6$ and $W_K(K)<W<W_K(7/6)$, the weak reading occurs exactly once on each side of the turn. The lower inequality accounts for the endpoint $b=K$, where $a=1$ and the admissible interval ends. The ratio $R_K$ increases strictly throughout the interval. Thus, whenever two splits give the same electromagnetic and weak readings, the split with larger $b$ must give the larger strong reading. This is an ordering theorem for the formulas, valid beyond the numerical example. [Proof of the branch ordering](CommonRuler/Inverse.lean)

## How to invert a proposed triple

Given $K>1$ and positive proposed readings $W,S$, form $r=S/W$. There is exactly one $b\in(1,K)$ satisfying the cubic

$$
K^2(b-1)^2=4r(K-b)^3.
$$

The split reproduces the proposed triple exactly if and only if $W_K(b)=W$. In that case the unique bases are $a=K/b$ and $b$. One convenient variable is $t=(b-1)/(K-b)>0$. Every ruler then uses the same cubic shape,

$$
t^2(1+t)=\frac{4(K-1)}{K^2}r,\qquad b=\frac{1+Kt}{1+t}.
$$

The existence proof uses the opposite signs of the first cubic, after moving all terms to one side, at $b=1$ and $b=K$. Strict increase of $R_K$ gives uniqueness. The central-value proof then brackets $K$ using bounds on $\pi$, brackets each weak root by exact rational inequalities, and encloses its strong reading. [Inverse and compatibility theorems](Solution.lean) · [Rational certificates](CommonRuler/Centers.lean)

## Physical comparison and relation to the earlier entry

The electromagnetic input is the rounded low-energy inverse fine-structure constant. The weak input is the MS-bar value $0.23121(4)$ at the Z mass in PDG 2022, Table 1.1. PDG 2024 gives the comparison value $\alpha_s(M_Z)=0.1180\pm0.0009$. The falling-branch result is $0.00071546$ below it, or $0.795$ times the quoted strong uncertainty. Propagating the weak uncertainty to first order at fixed electromagnetic input contributes about $0.000262$ to the inferred strong value. The comparison uses the scales and editions stated here. [CODATA 2022](https://physics.nist.gov/cuu/pdf/wallet_2022.pdf) · [PDG weak input](https://pdg.lbl.gov/2022/reviews/rpp2022-rev-phys-constants.pdf) · [PDG strong comparison](https://pdg.lbl.gov/2024/reviews/rpp2024-rev-qcd.pdf)

The earlier Palomar entry used all three measurement windows. Under its hypotheses they fix the integer exponent at 15, and the stated polynomial families select $(\rho,Q)$. Here the exponent is supplied to the inverse, and the two bases range over all real numbers greater than one. The strong value is withheld in the two-input calculation. Its earlier role in selecting the exponent makes this a consistency check of already specified formulas. Deriving their energy-scale dependence remains a physical question. [Earlier public registration](https://palomar-registry.org/entry?id=PALOMAR-2026-11-19-000013&version=1) · [Original formulas at the registered commit](https://github.com/stalex444/pdt-arithmetic-classification/tree/96ec711a1dc10a81ede064976f1fd19a9a94690f)

## Reproduce the checks

With the Lean toolchain in `lean-toolchain`, run these commands from the repository root.

```sh
lake exe cache get
lake build
PATH="$(lean --print-prefix)/bin:$PATH" lake comparator
```

The last command uses Lake’s sandbox on Linux. On macOS the local replay uses `lake comparator --inadvisably-no-sandbox` with the same toolchain path. The eleven theorems listed in [comparator.json](comparator.json) have their specifications in [Challenge.lean](Challenge.lean). Its eleven placeholders define the review challenge. The implementation and solution contain the proofs.

For the numerical replay, run `python3 check_inverse.py` with mpmath 1.3.0 installed. It uses bisection on both weak branches, evaluates the original strong formula, and independently recovers each split from the scaled cubic. The formal bounds use exact rational arithmetic.
