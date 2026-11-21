module

public import CommonRuler.Centers
public import Classification
public import CommonRuler.RationalInverse

/-! The inverse problem in terms of the original three formulas. -/
@[expose] public section
noncomputable section
namespace PDTGauge.Result
open Set

/-- The two single-measurement field extensions have exactly the specified degrees. -/
theorem degrees_of_single_readings {k : Type*} [Field k] (K : k) (hK : K ≠ 1)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    Module.finrank (IntermediateField.adjoin k {CommonRulerField.weakMap k n}) (RatFunc k) = n ∧
    Module.finrank (IntermediateField.adjoin k {CommonRulerField.ratioMap K m}) (RatFunc k) = m := CommonRulerField.single_degrees K hK n m hn hm

/-- Away from m=2n rational recovery holds over arbitrary coefficient fields. -/
theorem nonresonant_field_recovery {k : Type*} [Field k] (K : k) (h0 : K ≠ 0) (h1 : K ≠ 1)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hne : m ≠ 2*n) :
    IntermediateField.adjoin k {CommonRulerField.weakMap k n, CommonRulerField.ratioMap K m} = ⊤ := CommonRulerField.nonresonant_recovery K h0 h1 n m hn hm hne

/-- At a fixed ruler, the two unnormalized rational functions W and S/W of the
gauge application generate the entire function field. -/
theorem gauge_functions_generate (K : ℝ) (hK : 1<K) :
    let x := (RatFunc.X : RatFunc ℝ)
    let c := RatFunc.C K
    let w := c^3*(x-1)/x^7
    let r := c^2*(x-1)^2/(4*(c-x)^3)
    IntermediateField.adjoin ℝ {w,r} = ⊤ := by
  let x := (RatFunc.X : RatFunc ℝ)
  let c := RatFunc.C K
  let w := c^3*(x-1)/x^7
  let r := c^2*(x-1)^2/(4*(c-x)^3)
  let E := IntermediateField.adjoin ℝ {w,r}
  change E = ⊤
  have hw : w ∈ E := IntermediateField.subset_adjoin ℝ _ (by simp)
  have hr : r ∈ E := IntermediateField.subset_adjoin ℝ _ (by simp)
  have hc : c ∈ E := E.algebraMap_mem K
  have hc0 : c ≠ 0 := (map_ne_zero RatFunc.C).mpr (by linarith)
  have f : CommonRulerField.weakMap ℝ 7 = w/c^3 := by
    simp only [CommonRulerField.weakMap, CommonRulerField.liftP, CommonRulerField.lin, map_pow,
      map_sub, RatFunc.algebraMap_X, map_one]
    change (x-1)/x^7 = (c^3*(x-1)/x^7)/c^3
    field_simp [hc0]
  have g : CommonRulerField.ratioMap K 3 = -(4*r/c^2) := by
    simp only [CommonRulerField.ratioMap, CommonRulerField.liftP, CommonRulerField.lin, map_pow,
      map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_one]
    change (x-1)^2/(x-c)^3 = -(4*(c^2*(x-1)^2/(4*(c-x)^3))/c^2)
    rw [show c-x = -(x-c) by ring]
    field_simp [hc0]
  apply top_le_iff.mp
  rw [← CommonRulerField.nonresonant_recovery K (by linarith) hK.ne' 7 3 (by decide)
    (by decide) (by decide)]
  apply IntermediateField.adjoin_le_iff.mpr
  intro y hy
  rcases Set.mem_insert_iff.mp hy with he | he
  · rw [he,f]
    exact E.div_mem hw (E.pow_mem hc 3)
  · rw [Set.mem_singleton_iff.mp he,g]
    exact E.neg_mem (E.div_mem (E.mul_mem (E.natCast_mem 4) hr) (E.pow_mem hc 2))

/-- Compute a physical split directly by field operations wherever the displayed
denominator is nonzero. The coefficients use only K, the weak reading and the scaled ratio. -/
theorem explicit_gauge_inverse {K x : ℝ} (hx : x ∈ Set.Ioo 1 K) :
    let t := (x-1)/(K-x)
    let w := weakAt K x
    let r := 4*(K-1)*ratioAt K x/K^2
    let (a,b,c) := inverseCoefficients K w r
    let d := b^2-a*c-a*b
    d ≠ 0 → t=(r*a^2+a*c-b*c)/d := by
  obtain ⟨hc, hw⟩ := physical_cubic_equations hx
  exact rational_recovery _ _ _ _ hc hw

/-- A fixed electromagnetic reading determines the product at any positive integer exponent. -/
theorem electromagnetic_fixes_ruler {p : ℕ} (hp : p ≠ 0) {a b c d : ℝ}
    (ha : 1<a) (hb : 1<b) (hc : 1<c) (hd : 1<d) :
    em p a b = em p c d ↔ a*b = c*d := by
  unfold em
  rw [div_left_inj' (pow_ne_zero 2 Real.pi_ne_zero)]
  exact pow_left_inj₀ (mul_nonneg (by linarith) (by linarith))
    (mul_nonneg (by linarith) (by linarith)) hp

/-- The weak response increases up to 7/6 and decreases from there to the ruler endpoint. -/
theorem weak_turn {K : ℝ} (hK : 7/6 < K) :
    StrictMonoOn (weakAt K) (Icc 1 (7/6)) ∧ StrictAntiOn (weakAt K) (Icc (7/6) K) :=
  ⟨weak_increasing (by linarith),weak_decreasing (by linarith)⟩

/-- A target between the far endpoint and the maximum gives exactly one root on each side. -/
theorem two_weak_branches {K w : ℝ} (hK : 7/6 < K)
    (hl : weakAt K K < w) (hu : w < weakAt K (7/6)) :
    (∃! b, b ∈ Ioo 1 (7/6) ∧ weakAt K b = w) ∧
    (∃! b, b ∈ Ioo (7/6) K ∧ weakAt K b = w) :=
  two_branches hK hl hu

/-- For both observables the fixed-product substitution is exact. -/
theorem ruler_factorization {a b : ℝ} (ha : 1<a) (hb : 1<b) :
    weak a b = weakAt (a*b) b ∧ strong a b = weak a b * ratioAt (a*b) b :=
  ⟨weak_on_ruler ha hb, strong_factorization ha hb⟩

/-- The larger quartic-side coordinate gives the larger strong reading on a common weak level. -/
theorem branch_order {a b c d : ℝ} (ha : 1<a) (hb : 1<b) (hc : 1<c) (hd : 1<d)
    (hK : a*b = c*d) (hw : weak a b = weak c d) (hbd : b<d) :
    strong a b < strong c d :=
  strong_orders_branches ha hb hc hd hK hw hbd

private theorem ratio_equation {K r b : ℝ} (hb : b<K) :
    ratioAt K b = r ↔ K^2*(b-1)^2 = r*(4*(K-b)^3) := by
  unfold ratioAt
  exact div_eq_iff (by have := sub_pos.mpr hb; positivity)

/-- Each positive strong-to-weak ratio has a unique inverse on the entire admissible split interval. -/
theorem inverse_from_ratio {K r : ℝ} (hK : 1<K) (hr : 0<r) :
    ∃! b, b ∈ Ioo 1 K ∧ K^2*(b-1)^2 = r*(4*(K-b)^3) := by
  let f := fun x : ℝ => K^2*(x-1)^2 - r*(4*(K-x)^3)
  have hk : 0 < K := by linarith
  have hk1 : 0 < K-1 := sub_pos.mpr hK
  have hl : f 1 < 0 := by dsimp [f]; simp; positivity
  have hu : 0 < f K := by dsimp [f]; simp; positivity
  have hcont : Continuous f := by dsimp [f]; fun_prop
  obtain ⟨b,hb,he⟩ := intermediate_value_Icc hK.le hcont.continuousOn ⟨hl.le,hu.le⟩
  have hbi : b ∈ Ioo 1 K := ⟨lt_of_le_of_ne hb.1 (by rintro rfl; linarith),
    lt_of_le_of_ne hb.2 (by rintro rfl; linarith)⟩
  have hroot := sub_eq_zero.mp he
  refine ⟨b,⟨hbi,hroot⟩,?_⟩
  rintro x ⟨hx,heq⟩
  exact (ratio_strictMono hK).injOn hx hbi
    (((ratio_equation hx.2).2 heq).trans ((ratio_equation hbi.2).2 hroot).symm)

private theorem split_at {K b : ℝ} (hb : b ∈ Ioo 1 K) :
    1 < K/b ∧ (K/b)*b = K := by
  have hp := zero_lt_one.trans hb.1
  exact ⟨(one_lt_div hp).2 hb.2, div_mul_cancel₀ K hp.ne'⟩

/-- In the coordinate t=(b-1)/(K-b), every ruler uses the same positive cubic. -/
theorem scaled_inverse_cubic {K b : ℝ} (hb : b ∈ Ioo 1 K) :
    let t := (b-1)/(K-b)
    0<t ∧ t^2*(1+t) = 4*(K-1)*ratioAt K b/K^2 ∧ b = (1+K*t)/(1+t) := by
  dsimp only
  have hD := sub_pos.mpr hb.2
  have hN := sub_pos.mpr hb.1
  have hK : 0<K := zero_lt_one.trans (hb.1.trans hb.2)
  have ht := div_pos hN hD
  refine ⟨ht, ?_, ?_⟩
  · unfold ratioAt
    field_simp [hD.ne', hK.ne']
    ring
  · apply (eq_div_iff (by linarith : 1+(b-1)/(K-b) ≠ 0)).2
    field_simp [hD.ne']
    ring

/-- After solving the ratio cubic, a measured weak value gives an exact compatibility test. -/
theorem compatible_iff {K w s b : ℝ} (hw : 0<w) (hb : b ∈ Ioo 1 K)
    (hroot : K^2*(b-1)^2 = (s/w)*(4*(K-b)^3)) :
    (∃ a' b' : ℝ, 1<a' ∧ 1<b' ∧ a'*b'=K ∧ weak a' b'=w ∧ strong a' b'=s) ↔
      weakAt K b = w := by
  have hK := hb.1.trans hb.2
  have hratio := (ratio_equation hb.2).2 hroot
  constructor
  · rintro ⟨x,y,hx,hy,hxy,hW,hS⟩
    have hyK : y < K := by
      rw [← hxy]
      simpa using mul_lt_mul_of_pos_right hx (zero_lt_one.trans hy)
    have hh := strong_factorization hx hy
    rw [hS,hW,hxy] at hh
    have hrat : ratioAt K y = s/w := (eq_div_iff hw.ne').2 (by linarith)
    have he := (ratio_strictMono hK).injOn (x₁ := y) ⟨hy,hyK⟩ hb (hrat.trans hratio.symm)
    rw [← he, ← hxy, ← weak_on_ruler hx hy, hW]
  · intro hW
    obtain ⟨ha,hprod⟩ := split_at hb
    have hweak := weak_on_ruler ha hb.1
    rw [hprod,hW] at hweak
    refine ⟨K/b,b,ha,hb.1,hprod,hweak,?_⟩
    rw [strong_factorization ha hb.1,hweak,hprod,hratio]
    field_simp

/-- Equality of all three readings identifies both bases at a fixed positive exponent. -/
theorem three_readings_identify {p : ℕ} (hp : p ≠ 0) {a b c d : ℝ}
    (ha : 1<a) (hb : 1<b) (hc : 1<c) (hd : 1<d)
    (he : em p a b = em p c d) (hw : weak a b = weak c d) (hs : strong a b = strong c d) :
    a=c ∧ b=d :=
  identifiable hp ha hb hc hd he hw hs

/-- The real quartic root above one belongs to the falling side of the weak response. -/
theorem quartic_side {Q : ℝ} (hQ : 1<Q) (he : Q^4=Q+1) : 7/6 < Q :=
  quartic_above_turn hQ he

/-- The exact inverse image of the two rounded centers consists of two pairs.
Their strong predictions and second coordinates lie in disjoint rational intervals. -/
theorem two_electroweak_solutions :
    ∃ L H : ℝ × ℝ,
      (∀ z, fitsCenters z ↔ z=L ∨ z=H) ∧
      L.2 ∈ Icc 1.1236537214 1.1236537215 ∧ H.2 ∈ Icc 1.2202393601 1.2202393603 ∧
      strong L.1 L.2 ∈ Icc 0.01923413 0.01923414 ∧
      strong H.1 H.2 ∈ Icc 0.11728454 0.11728455 := by
  obtain ⟨K,hK,hem⟩ := center_ruler_exists
  have hrange := center_ruler hK hem
  obtain ⟨⟨x,hx,hWx,hSx⟩,⟨y,hy,hWy,hSy⟩⟩ := center_brackets hK hem
  have hxlow : x ∈ Icc 1 (7/6:ℝ) := ⟨(by norm_num : (1:ℝ) ≤ 1.1236537214).trans hx.1,
    hx.2.trans (by norm_num)⟩
  have hyhigh : y ∈ Icc (7/6:ℝ) K := ⟨(by norm_num : (7/6:ℝ) ≤ 1.2202393601).trans hy.1,
    hy.2.trans ((by norm_num : (1.2202393603:ℝ) ≤ 1.617120172122).trans hrange.1)⟩
  have hxdom : x ∈ Ioo 1 K := ⟨(by norm_num : (1:ℝ) < 1.1236537214).trans_le hx.1,
    (hx.2.trans_lt (by norm_num : (1.1236537215:ℝ) < 1.617120172122)).trans_le hrange.1⟩
  have hydom : y ∈ Ioo 1 K := ⟨(by norm_num : (1:ℝ) < 1.2202393601).trans_le hy.1,
    (hy.2.trans_lt (by norm_num : (1.2202393603:ℝ) < 1.617120172122)).trans_le hrange.1⟩
  have lift {b : ℝ} (hb : b ∈ Ioo 1 K) (hW : weakAt K b = weakCenter) :
      fitsCenters (K/b,b) ∧ strong (K/b) b = weakCenter * ratioAt K b := by
    obtain ⟨ha,he⟩ := split_at hb
    have hw := (weak_on_ruler ha hb.1).trans (by rw [he,hW])
    exact ⟨⟨ha,hb.1,by simpa [em,he] using hem,hw⟩,
      by rw [strong_factorization ha hb.1,he,hw]⟩
  obtain ⟨hL,hSL⟩ := lift hxdom hWx
  obtain ⟨hH,hSH⟩ := lift hydom hWy
  refine ⟨(K/x,x),(K/y,y),?_,hx,hy,hSL.symm ▸ hSx,hSH.symm ▸ hSy⟩
  rintro ⟨a,b⟩
  constructor
  · rintro ⟨ha,hb,he,hw⟩
    have hprod := (electromagnetic_fixes_ruler (by decide : 15 ≠ 0) ha hb hL.1 hL.2.1).1
      (he.trans hL.2.2.1.symm)
    change a*b=(K/x)*x at hprod
    rw [(split_at hxdom).2] at hprod
    have hbK : b<K := by rw [← hprod]; simpa using mul_lt_mul_of_pos_right ha (zero_lt_one.trans hb)
    have hwb : weakAt K b = weakCenter := by rw [← hprod, ← weak_on_ruler ha hb]; exact hw
    have hp : a = K/b := (eq_div_iff (zero_lt_one.trans hb).ne').2 hprod
    rcases le_total b (7/6) with h | h
    · have heq : b=x := (weak_increasing hK).injOn ⟨hb.le,h⟩ hxlow (hwb.trans hWx.symm)
      exact Or.inl (by subst b; simp [hp])
    · have heq : b=y := (weak_decreasing hK).injOn ⟨h,hbK.le⟩ hyhigh (hwb.trans hWy.symm)
      exact Or.inr (by subst b; simp [hp])
  · rintro (he | he) <;> rw [he]
    · exact hL
    · exact hH

end PDTGauge.Result
