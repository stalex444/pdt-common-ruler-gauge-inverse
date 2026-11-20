module

public import CommonRuler.Definitions

/-! Exact inverse of the three gauge observables on the domain a,b > 1.
The electromagnetic observable fixes K = ab at a given positive exponent. -/
@[expose] public section
noncomputable section
namespace PDTGauge
open Set

theorem weak_on_ruler {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    weak a b = weakAt (a*b) b := by
  have ha' : a ≠ 0 := by linarith
  have hb' : b ≠ 0 := by linarith
  unfold weak weakAt lam psi
  field_simp

/-- The strong observable divided by the weak observable at a fixed product. -/
theorem strong_factorization {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    strong a b = weak a b * ratioAt (a*b) b := by
  have ha' : a ≠ 0 := by linarith
  have hb' : b ≠ 0 := by linarith
  have hsub : a-1 ≠ 0 := by linarith
  have hK : a*b-b = (a-1)*b := by ring
  unfold strong weak ratioAt lam psi
  rw [hK]
  field_simp

theorem ratio_strictMono {K : ℝ} (hK : 1 < K) :
    StrictMonoOn (ratioAt K) (Ioo 1 K) := by
  intro x hx y hy hxy
  have hx' : 0 < x-1 := sub_pos.mpr hx.1
  have hy' : 0 < y-1 := sub_pos.mpr hy.1
  have hxK : 0 < K-x := sub_pos.mpr hx.2
  have hyK : 0 < K-y := sub_pos.mpr hy.2
  have hK' : 0 < K := by linarith
  have num : K^2 * (x-1)^2 < K^2 * (y-1)^2 :=
    mul_lt_mul_of_pos_left (pow_lt_pow_left₀ (by linarith : x-1 < y-1) hx'.le (by decide : 2 ≠ 0)) (by positivity)
  have den : 4*(K-y)^3 ≤ 4*(K-x)^3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hyK.le (by linarith) 3) (by norm_num)
  exact lt_of_lt_of_le (div_lt_div_of_pos_right num (by positivity : 0 < 4*(K-x)^3))
    (div_le_div_of_nonneg_left (by positivity) (by positivity) den)

private theorem coord_mem {a b : ℝ} (ha : 1 < a) (hb : 1 < b) : b ∈ Ioo 1 (a*b) := by
  exact ⟨hb, by simpa using mul_lt_mul_of_pos_right ha (zero_lt_one.trans hb)⟩

/-- At equal product and weak value, the larger b gives the larger strong value. -/
theorem strong_orders_branches {a b c d : ℝ} (ha : 1<a) (hb : 1<b) (hc : 1<c) (hd : 1<d)
    (hK : a*b = c*d) (hw : weak a b = weak c d) (hbd : b<d) : strong a b < strong c d := by
  have hpos : 0 < weak a b := by
    rw [weak_on_ruler ha hb]
    unfold weakAt
    have := sub_pos.mpr hb
    have : 0 < a := by linarith
    have : 0 < b := by linarith
    positivity
  have hbi := coord_mem ha hb
  have hdi := coord_mem hc hd
  rw [← hK] at hdi
  rw [strong_factorization ha hb, strong_factorization hc hd, ← hw, ← hK]
  exact mul_lt_mul_of_pos_left
    (ratio_strictMono (hb.trans hbi.2) hbi hdi hbd) hpos

/-- For any fixed positive exponent, the three exact readouts identify both bases. -/
theorem identifiable {p : ℕ} (hp : p ≠ 0) {a b c d : ℝ}
    (ha : 1<a) (hb : 1<b) (hc : 1<c) (hd : 1<d)
    (hem : (a*b)^p / Real.pi^2 = (c*d)^p / Real.pi^2)
    (hw : weak a b = weak c d) (hs : strong a b = strong c d) : a=c ∧ b=d := by
  have hpow := (div_left_inj' (pow_ne_zero 2 Real.pi_ne_zero)).mp hem
  have hK := (pow_left_inj₀ (mul_nonneg (by linarith : 0 ≤ a) (by linarith : 0 ≤ b))
    (mul_nonneg (by linarith : 0 ≤ c) (by linarith : 0 ≤ d)) hp).mp hpow
  have hbd : b=d := by
    rcases lt_trichotomy b d with h | h | h
    · exact False.elim ((strong_orders_branches ha hb hc hd hK hw h).ne hs)
    · exact h
    · exact False.elim ((strong_orders_branches hc hd ha hb hK.symm hw.symm h).ne hs.symm)
  subst d
  exact ⟨mul_right_cancel₀ (by linarith : b ≠ 0) hK, rfl⟩

private theorem weak_deriv (K : ℝ) {b : ℝ} (hb : 0 < b) :
    deriv (weakAt K) b = K^3*(7-6*b)/b^8 := by
  unfold weakAt
  have deriv' := (((hasDerivAt_id b).sub_const 1).const_mul (K^3)).div
    ((hasDerivAt_id b).pow 7) (pow_ne_zero _ hb.ne')
  change HasDerivAt (fun z : ℝ => K^3 * (z-1) / z^7)
    ((K^3*1*b^7-K^3*(b-1)*(7*b^6*1))/(b^7)^2) b at deriv'
  rw [deriv'.deriv]
  field_simp
  ring

theorem weak_continuousOn (K : ℝ) {l u : ℝ} (hl : 0 < l) :
    ContinuousOn (weakAt K) (Icc l u) := by
  unfold weakAt
  exact (by fun_prop : Continuous (fun b : ℝ => K^3 * (b-1))).continuousOn.div
    (by fun_prop) (fun b hb => pow_ne_zero _ (hl.trans_le hb.1).ne')

theorem weak_increasing {K : ℝ} (hK : 0 < K) : StrictMonoOn (weakAt K) (Icc 1 (7/6)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc ..) (weak_continuousOn K (by norm_num))
  intro b hb
  rw [interior_Icc] at hb
  obtain ⟨hl,hu⟩ := hb
  rw [weak_deriv K (by linarith)]
  have : 0 < 7-6*b := by linarith
  have : 0 < b := by linarith
  positivity

theorem weak_decreasing {K : ℝ} (hK : 0 < K) : StrictAntiOn (weakAt K) (Icc (7/6) K) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc ..) (weak_continuousOn K (by norm_num))
  intro b hb
  rw [interior_Icc] at hb
  obtain ⟨hl,_⟩ := hb
  have hpos : 0 < b := by linarith
  rw [weak_deriv K hpos]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (pow_pos hK _) (by linarith)) (pow_pos hpos _)

/-- Exactly one solution on each open branch when the descending branch
crosses the target before a reaches one. The turning point itself is excluded. -/
theorem two_branches {K w : ℝ} (hK : 7/6 < K)
    (hl : weakAt K K < w) (hu : w < weakAt K (7/6)) :
    (∃! b, b ∈ Ioo 1 (7/6) ∧ weakAt K b = w) ∧
    (∃! b, b ∈ Ioo (7/6) K ∧ weakAt K b = w) := by
  have hpos : 0 < K := by linarith
  have h1 : weakAt K 1 < w := by
    have hdiff : 0 < K-1 := by linarith
    have hp : 0 < weakAt K K := by unfold weakAt; positivity
    simpa [weakAt] using hp.trans hl
  obtain ⟨x,hx,hxw⟩ := intermediate_value_Icc (by norm_num : (1:ℝ)≤7/6)
    (weak_continuousOn K (by norm_num)) ⟨h1.le,hu.le⟩
  obtain ⟨y,hy,hyw⟩ := intermediate_value_Icc' hK.le
    (weak_continuousOn K (by norm_num)) ⟨hl.le,hu.le⟩
  constructor
  · refine ⟨x, ⟨⟨lt_of_le_of_ne hx.1 (by rintro rfl; linarith),
      lt_of_le_of_ne hx.2 (by rintro rfl; linarith)⟩, hxw⟩, ?_⟩
    rintro z ⟨hz, he⟩
    exact (weak_increasing hpos).injOn ⟨hz.1.le,hz.2.le⟩ hx (he.trans hxw.symm)
  · refine ⟨y, ⟨⟨lt_of_le_of_ne hy.1 (by rintro rfl; linarith),
      lt_of_le_of_ne hy.2 (by rintro rfl; linarith)⟩, hyw⟩, ?_⟩
    rintro z ⟨hz, he⟩
    exact (weak_decreasing hpos).injOn ⟨hz.1.le,hz.2.le⟩ hy (he.trans hyw.symm)

end PDTGauge

