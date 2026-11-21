module

public import CommonRuler.FieldDegree

/-! The resonant pole order. A simple zero after subtracting one observable from another
reduces an observable degree by one. The only failure is the degree-two involution. -/

@[expose] public section
noncomputable section
namespace CommonRulerField
open Polynomial IntermediateField
open scoped IntermediateField

private theorem cancel_index {E : IntermediateField ℝ (RatFunc ℝ)} (a : ℝ) (d : ℕ)
    (P : ℝ[X]) (hp : P.natDegree ≤ d+1) (hz : P.IsRoot a)
    (hs : P.derivative.eval a ≠ 0)
    (hm : liftP P / liftP (lin a ^ (d+1)) ∈ E) :
    Module.finrank E (RatFunc ℝ) ∣ d := by
  classical
  let U := P /ₘ lin a
  have hfac : lin a * U = P := mul_divByMonic_eq_iff_isRoot.mpr hz
  have hu : IsCoprime U (lin a) := (isCoprime_of_is_root_of_eval_derivative_ne_zero P a hs).symm
  have hlin : liftP (lin a) ≠ 0 := RatFunc.algebraMap_ne_zero (monic_X_sub_C a).ne_zero
  have hmem : liftP U / liftP (lin a ^ d) ∈ E := by
    convert hm using 1
    conv_rhs => rw [← hfac]
    simp only [map_mul, map_pow, pow_succ]
    field_simp
  have hd := index_dvd hmem
  rw [index_fraction _ _ ((monic_X_sub_C a).pow d) hu.pow_right] at hd
  have du : U.natDegree ≤ d := by
    dsimp [U,lin]
    rw [natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
    omega
  simpa only [lin, natDegree_pow, natDegree_X_sub_C, Nat.mul_one, max_eq_right du] using hd

private theorem lift_C_mem (E : IntermediateField ℝ (RatFunc ℝ)) (c : ℝ) :
    liftP (Polynomial.C c) ∈ E := by
  change algebraMap ℝ[X] (RatFunc ℝ) (algebraMap ℝ ℝ[X] c) ∈ E
  rw [← IsScalarTower.algebraMap_apply]
  exact E.algebraMap_mem c

/-- Except at the quadratic exception, the two observables generate the rational function field
also when the second denominator order is twice the first. -/
theorem resonant_recovery (K : ℝ) (hK : 1<K) (n : ℕ) (hn : 2≤n)
    (hne : ¬ (n=2 ∧ K=2)) :
    IntermediateField.adjoin ℝ {weakMap ℝ n, ratioMap K (2*n)} = ⊤ := by
  classical
  let E := IntermediateField.adjoin ℝ {weakMap ℝ n, ratioMap K (2*n)}
  have hf : weakMap ℝ n ∈ E := IntermediateField.subset_adjoin ℝ _ (by simp)
  have hg : ratioMap K (2*n) ∈ E := IntermediateField.subset_adjoin ℝ _ (by simp)
  have dn := index_dvd hf
  rw [(single_degrees K hK.ne' n (2*n) hn (by omega)).1] at dn
  have hnX : liftP (X : ℝ[X]) ≠ 0 := RatFunc.algebraMap_ne_zero X_ne_zero
  have hnA : liftP (lin (1:ℝ)) ≠ 0 := RatFunc.algebraMap_ne_zero (monic_X_sub_C _).ne_zero
  have hnB : liftP (lin K) ≠ 0 := RatFunc.algebraMap_ne_zero (monic_X_sub_C _).ne_zero
  have hk0 : K ≠ 0 := by linarith
  have hH : liftP (lin K ^ (2*n)) / liftP ((X : ℝ[X]) ^ (2*n)) ∈ E := by
    convert E.div_mem (E.pow_mem hf 2) hg using 1
    simp only [weakMap,ratioMap,map_pow,pow_mul]
    field_simp
    ring
  let d := 2*n-1
  have he : d+1=2*n := by dsimp [d]; omega
  suffices dd : Module.finrank E (RatFunc ℝ) ∣ d by
    apply IntermediateField.finrank_eq_one_iff_eq_top.mp
    apply Nat.dvd_one.mp
    exact (Nat.dvd_add_iff_right dd).mpr (he ▸ dvd_mul_of_dvd_right dn 2)
  by_cases h : K ≠ (n:ℝ)
  · let P : ℝ[X] := (C K-X)^(2*n) - C (K^(2*n)) * lin 1^2
    refine cancel_index 0 d P ?_ ?_ ?_ ?_
    · rw [he]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · have hn' : (C K-X).natDegree ≤ 1 := by
          simpa using natDegree_sub_le (C K) (X : ℝ[X])
        rw [natDegree_pow]
        simpa using Nat.mul_le_mul_left (2*n) hn'
      · refine (natDegree_C_mul_le _ _).trans ?_
        simp only [lin,natDegree_pow,natDegree_X_sub_C,Nat.mul_one]; omega
    · simp [P,Polynomial.IsRoot,lin]
    · have ke : K^(2*n) = K^(2*n-1)*K := by rw [← pow_succ]; congr 1; omega
      have sign : (2*K^(2*n-1))*(K-(n:ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hk0)) (sub_ne_zero.mpr h)
      convert sign using 1
      simp [P,lin, derivative_pow, ke]
      ring
    · rw [he]
      have flip : C K - X = -lin K := by simp [lin]
      convert E.sub_mem hH (E.mul_mem (lift_C_mem E (K^(2*n))) (E.pow_mem hf 2)) using 1
      simp only [P, flip, lin, C_0, sub_zero, map_sub, map_mul, map_pow, map_neg,
        weakMap, pow_mul]
      field_simp
      ring
  · push Not at h
    have nh : (2:ℝ) < n := by
      have hn' : 2<n := by
        by_contra! hh
        have en : n=2 := by omega
        exact hne ⟨en, by simpa [en] using h⟩
      exact_mod_cast hn'
    let P : ℝ[X] := C (K^n) * (lin 1 * X^n) - C (K-1)*X^(2*n)
    refine cancel_index K d P ?_ ?_ ?_ ?_
    · rw [he]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
        simp only [lin,natDegree_pow,natDegree_X_sub_C,natDegree_X,Nat.mul_one]; omega
      · refine (natDegree_C_mul_le _ _).trans ?_
        simp [natDegree_pow]
    · simp [P,Polynomial.IsRoot,lin,pow_mul]; ring
    · have e1 : K^n = K^(n-1)*K := by rw [← pow_succ]; congr 1; omega
      have e2 : K^(2*n-1) = K^n * K^(n-1) := by rw [← pow_add]; congr 1; omega
      have neg : K - (n:ℝ)*(K-1) ≠ 0 := by rw [h]; nlinarith
      have nr := mul_ne_zero (mul_ne_zero (pow_ne_zero n hk0) (pow_ne_zero (n-1) hk0)) neg
      convert nr using 1
      simp [P,lin,derivative_pow,e2]
      linear_combination (K^n)*e1
    · rw [he]
      convert E.div_mem (E.sub_mem (E.mul_mem (lift_C_mem E (K^n)) hf)
          (lift_C_mem E (K-1))) hH using 1
      simp only [P,map_sub,map_mul,map_pow,weakMap,pow_mul]
      field_simp
      ring

/-- At K=2 and exponents 2 and 4 the second observable is rational in the first. -/
theorem exceptional_index :
    Module.finrank (IntermediateField.adjoin ℝ {weakMap ℝ 2, ratioMap (2:ℝ) 4}) (RatFunc ℝ) = 2 := by
  let E := IntermediateField.adjoin ℝ {weakMap ℝ 2}
  have hf : weakMap ℝ 2 ∈ E := IntermediateField.subset_adjoin ℝ _ (by simp)
  have hrat : ratioMap (2:ℝ) 4 = (weakMap ℝ 2)^(2:ℕ) / (1 - 4*weakMap ℝ 2)^(2:ℕ) := by
    have hx : liftP (X:ℝ[X]) ≠ 0 := RatFunc.algebraMap_ne_zero X_ne_zero
    have h2 : liftP (lin (2:ℝ)) ≠ 0 := RatFunc.algebraMap_ne_zero (monic_X_sub_C _).ne_zero
    have e : (liftP (X:ℝ[X]))^2 - 4*liftP (lin (1:ℝ)) = (liftP (lin (2:ℝ)))^2 := by
      norm_num [lin, map_ofNat]; ring
    simp only [ratioMap,weakMap,map_pow]
    rw [show 1 - 4*(liftP (lin (1:ℝ)) / liftP (X:ℝ[X])^2) =
        (liftP (lin (2:ℝ)))^2 / liftP (X:ℝ[X])^2 by field_simp; linear_combination e]
    field_simp
  have hg : ratioMap (2:ℝ) 4 ∈ E := by
    rw [hrat]
    exact E.div_mem (E.pow_mem hf 2) (E.pow_mem (E.sub_mem E.one_mem (E.mul_mem (E.natCast_mem 4) hf)) 2)
  have efield : IntermediateField.adjoin ℝ {weakMap ℝ 2, ratioMap (2:ℝ) 4} = E := by
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      intro y hy
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hy
      rcases hy with rfl|rfl
      · exact hf
      · exact hg
    · apply IntermediateField.adjoin_simple_le_iff.mpr
      exact IntermediateField.subset_adjoin ℝ _ (by simp)
  rw [efield]
  exact (single_degrees (2:ℝ) (by norm_num) 2 4 (by decide) (by decide)).1

end CommonRulerField
