module

public import Mathlib

/-! Joint recovery for two rational functions with a common zero and distinct poles. -/
@[expose] public section
noncomputable section
namespace CommonRulerField
open Polynomial IntermediateField
open scoped IntermediateField

variable {k : Type*} [Field k]

/-- Single-reading field index, with a monic reduced denominator. -/
theorem index_fraction (a b : k[X]) (hb : b.Monic) (hc : IsCoprime a b) :
    Module.finrank (IntermediateField.adjoin k
      {algebraMap k[X] (RatFunc k) a / algebraMap k[X] (RatFunc k) b}) (RatFunc k) =
      max a.natDegree b.natDegree := by
  classical
  have hg : GCDMonoid.gcd a b = 1 := by
    rw [← NormalizedGCDMonoid.normalize_gcd]
    exact normalize_eq_one.mpr (hc.isRelPrime (gcd_dvd_left a b) (gcd_dvd_right a b))
  rw [RatFunc.finrank_eq_max_natDegree, RatFunc.num_div, RatFunc.denom_div _ hb.ne_zero]
  simp [hg, hb.leadingCoeff]

theorem index_dvd {E : IntermediateField k (RatFunc k)} {z : RatFunc k}
    (hz : z ∈ E) : Module.finrank E (RatFunc k) ∣
      Module.finrank (IntermediateField.adjoin k {z}) (RatFunc k) :=
  IntermediateField.finrank_dvd_of_le_left (IntermediateField.adjoin_simple_le_iff.mpr hz)

abbrev lin (c : k) : k[X] := X - C c
abbrev liftP (p : k[X]) : RatFunc k := algebraMap k[X] (RatFunc k) p
theorem cop {c d : k} (h : c ≠ d) : IsCoprime (lin c) (lin d) :=
  Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr h).isUnit

/-- Normalized weak reading with variable pole order. -/
def weakMap (k : Type*) [Field k] (n : ℕ) : RatFunc k :=
  liftP (lin 1) / liftP (X ^ n : k[X])

/-- Normalized ratio reading with a double zero at one. -/
def ratioMap (K : k) (m : ℕ) : RatFunc k :=
  liftP (lin 1 ^ 2) / liftP (lin K ^ m)

theorem single_degrees (K : k) (hK : K ≠ 1) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    Module.finrank (IntermediateField.adjoin k {weakMap k n}) (RatFunc k) = n ∧
    Module.finrank (IntermediateField.adjoin k {ratioMap K m}) (RatFunc k) = m := by
  have h0 : IsCoprime (lin (1:k)) X := by simpa [lin] using (cop (one_ne_zero : (1:k) ≠ 0))
  constructor
  · rw [weakMap, index_fraction _ _ (monic_X.pow n) h0.pow_right]
    simp only [lin, natDegree_X_sub_C, natDegree_pow, natDegree_X, Nat.mul_one, max_eq_right (by omega : 1 ≤ n)]
  · rw [ratioMap, index_fraction _ _ ((monic_X_sub_C K).pow m) (cop hK.symm).pow_left.pow_right]
    simp only [lin, natDegree_X_sub_C, natDegree_pow, Nat.mul_one, max_eq_right hm]

end CommonRulerField
