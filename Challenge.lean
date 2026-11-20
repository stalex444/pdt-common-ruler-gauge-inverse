module

public import Mathlib

@[expose] public section
noncomputable section
namespace PDTGauge
open Set

/-- Rounded inverse fine-structure input used by the original classification. -/
def emCenter : ℝ := 137.036
/-- MS-bar weak-mixing input at the Z mass. -/
def weakCenter : ℝ := 0.23121
def lam (x : ℝ) : ℝ := 1 - 1/x
def psi (a b : ℝ) : ℝ := b/a
def em (p : ℕ) (a b : ℝ) : ℝ := (a*b)^p / Real.pi^2

def weak (a b : ℝ) : ℝ := lam b / (psi a b)^3
def strong (a b : ℝ) : ℝ := (lam b)^3 / (4 * (lam a)^3 * (psi a b)^2)
def weakAt (K b : ℝ) : ℝ := K^3 * (b-1) / b^7
def ratioAt (K b : ℝ) : ℝ := K^2 * (b-1)^2 / (4*(K-b)^3)

/-- A split of the ruler matching just the two electroweak centers. -/
def fitsCenters (z : ℝ × ℝ) : Prop :=
  1 < z.1 ∧ 1 < z.2 ∧ em 15 z.1 z.2 = emCenter ∧ weak z.1 z.2 = weakCenter

end PDTGauge

namespace PDTGauge.Result
open Set

/-- A fixed electromagnetic reading determines the product at any positive integer exponent. -/
theorem electromagnetic_fixes_ruler {p : ℕ} (hp : p ≠ 0) {a b c d : ℝ}
    (ha : 1<a) (hb : 1<b) (hc : 1<c) (hd : 1<d) :
    em p a b = em p c d ↔ a*b = c*d := by sorry

/-- The weak response increases up to 7/6 and decreases from there to the ruler endpoint. -/
theorem weak_turn {K : ℝ} (hK : 7/6 < K) :
    StrictMonoOn (weakAt K) (Icc 1 (7/6)) ∧ StrictAntiOn (weakAt K) (Icc (7/6) K) := by sorry

/-- A target between the far endpoint and the maximum gives exactly one root on each side. -/
theorem two_weak_branches {K w : ℝ} (hK : 7/6 < K)
    (hl : weakAt K K < w) (hu : w < weakAt K (7/6)) :
    (∃! b, b ∈ Ioo 1 (7/6) ∧ weakAt K b = w) ∧
    (∃! b, b ∈ Ioo (7/6) K ∧ weakAt K b = w) := by sorry

/-- For both observables the fixed-product substitution is exact. -/
theorem ruler_factorization {a b : ℝ} (ha : 1<a) (hb : 1<b) :
    weak a b = weakAt (a*b) b ∧ strong a b = weak a b * ratioAt (a*b) b := by sorry

/-- The larger quartic-side coordinate gives the larger strong reading on a common weak level. -/
theorem branch_order {a b c d : ℝ} (ha : 1<a) (hb : 1<b) (hc : 1<c) (hd : 1<d)
    (hK : a*b = c*d) (hw : weak a b = weak c d) (hbd : b<d) :
    strong a b < strong c d := by sorry

/-- Each positive strong-to-weak ratio has a unique inverse on the entire admissible split interval. -/
theorem inverse_from_ratio {K r : ℝ} (hK : 1<K) (hr : 0<r) :
    ∃! b, b ∈ Ioo 1 K ∧ K^2*(b-1)^2 = r*(4*(K-b)^3) := by sorry

/-- In the coordinate t=(b-1)/(K-b), every ruler uses the same positive cubic. -/
theorem scaled_inverse_cubic {K b : ℝ} (hb : b ∈ Ioo 1 K) :
    let t := (b-1)/(K-b)
    0<t ∧ t^2*(1+t) = 4*(K-1)*ratioAt K b/K^2 ∧ b = (1+K*t)/(1+t) := by sorry

/-- After solving the ratio cubic, a measured weak value gives an exact compatibility test. -/
theorem compatible_iff {K w s b : ℝ} (hw : 0<w) (hb : b ∈ Ioo 1 K)
    (hroot : K^2*(b-1)^2 = (s/w)*(4*(K-b)^3)) :
    (∃ a' b' : ℝ, 1<a' ∧ 1<b' ∧ a'*b'=K ∧ weak a' b'=w ∧ strong a' b'=s) ↔
      weakAt K b = w := by sorry

/-- Equality of all three readings identifies both bases at a fixed positive exponent. -/
theorem three_readings_identify {p : ℕ} (hp : p ≠ 0) {a b c d : ℝ}
    (ha : 1<a) (hb : 1<b) (hc : 1<c) (hd : 1<d)
    (he : em p a b = em p c d) (hw : weak a b = weak c d) (hs : strong a b = strong c d) :
    a=c ∧ b=d := by sorry

/-- The real quartic root above one belongs to the falling side of the weak response. -/
theorem quartic_side {Q : ℝ} (hQ : 1<Q) (he : Q^4=Q+1) : 7/6 < Q := by sorry

/-- The exact inverse image of the two rounded centers consists of two pairs.
Their strong predictions and second coordinates lie in disjoint rational intervals. -/
theorem two_electroweak_solutions :
    ∃ L H : ℝ × ℝ,
      (∀ z, fitsCenters z ↔ z=L ∨ z=H) ∧
      L.2 ∈ Icc 1.1236537214 1.1236537215 ∧ H.2 ∈ Icc 1.2202393601 1.2202393603 ∧
      strong L.1 L.2 ∈ Icc 0.01923413 0.01923414 ∧
      strong H.1 H.2 ∈ Icc 0.11728454 0.11728455 := by sorry

end PDTGauge.Result
