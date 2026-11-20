module

public import CommonRuler.Inverse

/-! Rational enclosures for the published input centers. The strong measurement
does not enter the hypotheses. All decimals in the statements are exact rationals. -/
@[expose] public section
noncomputable section
namespace PDTGauge
open Set

/-- The electromagnetic center fixes the common ruler to this short interval. -/
theorem center_ruler {K : ℝ} (hp : 0 < K) (h : K^15 / Real.pi^2 = emCenter) :
    K ∈ Icc 1.617120172122 1.617120172123 := by
  have hh := (div_eq_iff (pow_ne_zero 2 Real.pi_ne_zero)).mp h
  unfold emCenter at hh
  have hL := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d20.le 2
  have hU := pow_le_pow_left₀ (by positivity) Real.pi_lt_d20.le 2
  constructor
  · by_contra! h
    exact (pow_lt_pow_left₀ h hp.le (by decide : 15 ≠ 0)).not_ge (calc
      (1.617120172122 : ℝ)^15 ≤ 137.036 * 3.14159265358979323846^2 := by norm_num
      _ ≤ 137.036 * Real.pi^2 := by gcongr
      _ = K^15 := hh.symm)
  · by_contra! h
    exact (pow_lt_pow_left₀ h (by norm_num) (by decide : 15 ≠ 0)).not_ge (calc
      K^15 = 137.036*Real.pi^2 := hh
      _ ≤ 137.036 * 3.14159265358979323847^2 := by gcongr
      _ ≤ (1.617120172123 : ℝ)^15 := by norm_num)

private theorem weak_ruler_mono {k K x : ℝ} (hk : 0 ≤ k) (h : k ≤ K) (hx : 1 ≤ x) :
    weakAt k x ≤ weakAt K x := by
  dsimp [weakAt]
  gcongr

private theorem score_box {k K u l b h : ℝ} (hk : 0 ≤ k)
    (hK : K ∈ Icc k u) (hb : b ∈ Icc l h) (hl : 1 < l) (hh : h < k) :
    weakCenter*(k^2*(l-1)^2/(4*(u-l)^3)) ≤ weakCenter*ratioAt K b ∧
    weakCenter*ratioAt K b ≤ weakCenter*(u^2*(h-1)^2/(4*(k-h)^3)) := by
  obtain ⟨hkl,hku⟩ := hK
  obtain ⟨hbl,hbu⟩ := hb
  have h1 : 0 ≤ l-1 := by linarith
  have h2 : 0 ≤ b-1 := by linarith
  have h3 : 0 < k-h := by linarith
  have h4 : 0 < K-b := by linarith
  have h5 : 0 ≤ K := by linarith
  unfold weakCenter ratioAt
  constructor <;> gcongr

/-- At the two published centers and exponent 15 the two solutions lie in
disjoint certified brackets. Their implied strong readings are enclosed directly. -/
theorem center_brackets {K : ℝ} (hp : 0 < K) (h : K^15/Real.pi^2 = emCenter) :
    (∃ b ∈ Icc 1.1236537214 1.1236537215, weakAt K b = weakCenter ∧
      weakCenter*ratioAt K b ∈ Icc 0.01923413 0.01923414) ∧
    (∃ b ∈ Icc 1.2202393601 1.2202393603, weakAt K b = weakCenter ∧
      weakCenter*ratioAt K b ∈ Icc 0.11728454 0.11728455) := by
  have hr := center_ruler hp h
  have lo (x : ℝ) (hx : 1 ≤ x) := weak_ruler_mono (by norm_num) hr.1 hx
  have hi (x : ℝ) (hx : 1 ≤ x) := weak_ruler_mono hp.le hr.2 hx
  constructor
  · have L := (hi 1.1236537214 (by norm_num)).trans
        (by norm_num [weakAt,weakCenter] : weakAt 1.617120172123 1.1236537214 ≤ weakCenter)
    have U := (lo 1.1236537215 (by norm_num)).trans'
        (by norm_num [weakAt,weakCenter] : weakCenter ≤ weakAt 1.617120172122 1.1236537215)
    obtain ⟨b,hb,hw⟩ := intermediate_value_Icc (by norm_num : (1.1236537214:ℝ) ≤ 1.1236537215)
      (weak_continuousOn K (by norm_num)) ⟨L,U⟩
    have hs := score_box (by norm_num) hr hb (by norm_num) (by norm_num)
    exact ⟨b,hb,hw,le_trans (by norm_num [weakCenter]) hs.1,le_trans hs.2 (by norm_num [weakCenter])⟩
  · have L := (hi 1.2202393603 (by norm_num)).trans
        (by norm_num [weakAt,weakCenter] : weakAt 1.617120172123 1.2202393603 ≤ weakCenter)
    have U := (lo 1.2202393601 (by norm_num)).trans'
        (by norm_num [weakAt,weakCenter] : weakCenter ≤ weakAt 1.617120172122 1.2202393601)
    obtain ⟨b,hb,hw⟩ := intermediate_value_Icc' (by norm_num : (1.2202393601:ℝ) ≤ 1.2202393603)
      (weak_continuousOn K (by norm_num)) ⟨L,U⟩
    have hs := score_box (by norm_num) hr hb (by norm_num) (by norm_num)
    exact ⟨b,hb,hw,le_trans (by norm_num [weakCenter]) hs.1,le_trans hs.2 (by norm_num [weakCenter])⟩

/-- The condition on the ruler used by the central-value certificate has a witness. -/
theorem center_ruler_exists : ∃ K : ℝ, 0 < K ∧ K^15/Real.pi^2 = emCenter := by
  have hT : 0 < emCenter := by norm_num [emCenter]
  have hpos : 0 < emCenter * Real.pi^2 := mul_pos hT (pow_pos Real.pi_pos _)
  refine ⟨(emCenter * Real.pi^2) ^ ((15:ℝ)⁻¹), Real.rpow_pos_of_pos hpos _, ?_⟩
  apply (div_eq_iff (pow_ne_zero 2 Real.pi_ne_zero)).2
  simpa only [Nat.cast_ofNat] using Real.rpow_inv_natCast_pow hpos.le (by decide : 15 ≠ 0)

/-- The quartic root greater than one lies on the decreasing weak branch. -/
theorem quartic_above_turn {Q : ℝ} (hQ : 1 < Q) (heq : Q^4 = Q+1) : 7/6 < Q := by
  by_contra! h
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ Q) h 4
  linarith

/-- Every admissible solution of the two measured-center equations has the
strong reading in the indicated interval for its branch. -/
theorem center_strong_by_branch {a b : ℝ} (ha : 1<a) (hb : 1<b)
    (hem : (a*b)^15/Real.pi^2 = emCenter) (hw : weak a b = weakCenter) :
    (b ≤ 7/6 → strong a b ∈ Icc 0.01923413 0.01923414) ∧
    (7/6 ≤ b → strong a b ∈ Icc 0.11728454 0.11728455) := by
  let K := a*b
  have hp : 0 < K := mul_pos (zero_lt_one.trans ha) (zero_lt_one.trans hb)
  have hr := center_ruler hp hem
  obtain ⟨⟨x,hx,hwx,hsx⟩,⟨y,hy,hwy,hsy⟩⟩ := center_brackets hp hem
  have hm : weakAt K b = weakCenter := (weak_on_ruler ha hb).symm.trans hw
  have hbk : b < K := by simpa [K] using mul_lt_mul_of_pos_right ha (zero_lt_one.trans hb)
  have hs : strong a b = weakCenter * ratioAt K b := (strong_factorization ha hb).trans (by rw [hw])
  rw [hs]
  constructor
  · intro h
    have hx' : x ∈ Icc 1 (7/6 : ℝ) := ⟨(by norm_num : (1:ℝ) ≤ 1.1236537214).trans hx.1,
      hx.2.trans (by norm_num)⟩
    have he := (weak_increasing hp).injOn ⟨hb.le,h⟩ hx' (hm.trans hwx.symm)
    simpa only [he] using hsx
  · intro h
    have hy' : y ∈ Icc (7/6 : ℝ) K := ⟨(by norm_num : (7/6 : ℝ) ≤ 1.2202393601).trans hy.1,
      hy.2.trans ((by norm_num : (1.2202393603:ℝ) ≤ 1.617120172122).trans hr.1)⟩
    have he := (weak_decreasing hp).injOn ⟨h,hbk.le⟩ hy' (hm.trans hwy.symm)
    simpa only [he] using hsy

end PDTGauge

