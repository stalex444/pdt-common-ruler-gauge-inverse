module

public import CommonRuler.FieldDegree

@[expose] public section
noncomputable section
namespace CommonRulerField
open Polynomial IntermediateField
open scoped IntermediateField
variable {k : Type*} [Field k]

/-- Away from the resonance m=2n the pair generates the rational function field,
even when the two individual degrees have a common factor. -/
theorem nonresonant_recovery (K : k) (h0 : K ≠ 0) (h1 : K ≠ 1)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hneq : m ≠ 2*n) :
    IntermediateField.adjoin k {weakMap k n, ratioMap K m} = ⊤ := by
  let E := IntermediateField.adjoin k {weakMap k n, ratioMap K m}
  let d := Module.finrank E (RatFunc k)
  have hf : weakMap k n ∈ E := IntermediateField.subset_adjoin k _ (by simp)
  have hg : ratioMap K m ∈ E := IntermediateField.subset_adjoin k _ (by simp)
  obtain ⟨degF,degG⟩ := single_degrees K h1 n m hn hm
  have dn : d ∣ n := degF ▸ index_dvd hf
  have dm : d ∣ m := degG ▸ index_dvd hg
  let B := lin K
  let A := lin (1:k)
  have hBX : IsCoprime B X := by simpa [B,lin] using cop h0
  have hAX : IsCoprime A X := by simpa [A,lin] using (cop (one_ne_zero : (1:k) ≠ 0))
  have hBA : IsCoprime B A := cop h1
  have nonX : liftP (X : k[X]) ≠ 0 := RatFunc.algebraMap_ne_zero X_ne_zero
  have nonA : liftP A ≠ 0 := RatFunc.algebraMap_ne_zero (monic_X_sub_C _).ne_zero
  have nonB : liftP B ≠ 0 := RatFunc.algebraMap_ne_zero (monic_X_sub_C _).ne_zero
  have hH : liftP (B ^ m) / liftP ((X : k[X]) ^ (2*n)) ∈ E := by
    convert E.div_mem (E.pow_mem hf 2) hg using 1
    simp only [weakMap, ratioMap, map_pow, zpow_ofNat]
    change liftP B ^ m / liftP (X : k[X]) ^ (2*n) =
      (liftP A / liftP (X : k[X]) ^ n) ^ 2 / (liftP A ^ 2 / liftP B ^ m)
    rw [mul_comm 2 n, pow_mul]
    field_simp [nonA, nonB, nonX]
  apply IntermediateField.finrank_eq_one_iff_eq_top.mp
  apply Nat.dvd_one.mp
  rcases lt_or_gt_of_ne hneq with h | h
  · let s := 2*n-1
    have ex : s*n+n = 2*n*n := by dsimp [s]; rw [← Nat.succ_mul]; congr 1; omega
    have zmem : liftP (B ^ (m*n)) / liftP ((X:k[X]) ^ (s*n) * A) ∈ E := by
      convert E.div_mem (E.pow_mem hH n) hf using 1
      simp only [zpow_natCast, weakMap, map_pow, map_mul, div_pow, ← pow_mul]
      change liftP B ^ (m*n) / (liftP (X : k[X]) ^ (s*n) * liftP A) =
        (liftP B ^ (m*n) / liftP (X : k[X]) ^ (2*n*n)) /
          (liftP A / liftP (X : k[X]) ^ n)
      rw [← ex, pow_add]
      field_simp [nonX, nonA]
    have zd := index_dvd zmem
    rw [index_fraction _ _ ((monic_X.pow _).mul (monic_X_sub_C _))
      (hBX.pow_left.pow_right.mul_right hBA.pow_left)] at zd
    have cmp : m*n ≤ s*n+1 := by
      have hs : m ≤ s := by dsimp [s]; omega
      exact (Nat.mul_le_mul_right n hs).trans (by omega)
    simp only [B,lin,natDegree_pow,natDegree_X_sub_C,natDegree_mul
      (pow_ne_zero _ X_ne_zero) (monic_X_sub_C _).ne_zero,natDegree_X,Nat.mul_one,
      max_eq_right cmp] at zd
    exact (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right dn s)).mpr zd
  · let s := 2*n+1
    have ex : s*n = 2*n*n+n := by dsimp [s]; ring
    have zmem : liftP (B ^ (m*n) * A) / liftP ((X:k[X]) ^ (s*n)) ∈ E := by
      convert E.mul_mem (E.pow_mem hH n) hf using 1
      simp only [zpow_natCast, weakMap, map_pow, map_mul, div_pow, ← pow_mul]
      change (liftP B ^ (m*n) * liftP A) / liftP (X : k[X]) ^ (s*n) =
        (liftP B ^ (m*n) / liftP (X : k[X]) ^ (2*n*n)) *
          (liftP A / liftP (X : k[X]) ^ n)
      rw [ex, pow_add, div_mul_div_comm]
    have zd := index_dvd zmem
    rw [index_fraction _ _ (monic_X.pow _) ((hBX.pow_left.mul_left hAX).pow_right)] at zd
    have cmp : s*n ≤ m*n+1 := by
      have hs : s ≤ m := by dsimp [s]; omega
      exact (Nat.mul_le_mul_right n hs).trans (by omega)
    simp only [B,A,lin,natDegree_pow,natDegree_X_sub_C,natDegree_mul
      (pow_ne_zero _ (monic_X_sub_C _).ne_zero) (monic_X_sub_C _).ne_zero,natDegree_X,
      Nat.mul_one,max_eq_left cmp] at zd
    exact (Nat.dvd_add_iff_right (dvd_mul_of_dvd_left dm n)).mpr zd
end CommonRulerField
