module

public import CommonRuler.Inverse

/-! A rational inverse for the common-ruler readings, computed by reducing the
weak equation modulo the monic ratio cubic. Coefficients are ordered (quadratic,
linear, constant). The formula applies wherever its displayed denominator is nonzero. -/
@[expose] public section
noncomputable section
namespace PDTGauge

def reducedPower {k : Type*} [Field k] (u r : k) : ℕ → k × k × k
  | 0 => (0,0,1)
  | n+1 =>
    let (a,b,c) := reducedPower u r n
    (a+u*(b-a), b+u*c, c+u*a*r)

def inverseCoefficients {k : Type*} [Field k] (K w r : k) : k × k × k :=
  let (a,b,c) := reducedPower K r 7
  let (i,j,l) := reducedPower 1 r 6
  let v := K^3*(K-1)
  (w*a-v*(j-i), w*b-v*l, w*c-v*i*r)

private theorem reducedPower_eval {k : Type*} [Field k] (u r t : k) (n : ℕ)
    (ht : t^3+t^2=r) :
    let (a,b,c) := reducedPower u r n
    a*t^2+b*t+c = (1+u*t)^n := by
  induction n with
  | zero => simp [reducedPower]
  | succ n ih =>
    rcases h : reducedPower u r n with ⟨a,b,c⟩
    simp only [reducedPower,h, pow_succ]
    simp only [h] at ih
    rw [← ih, ← ht]
    ring

theorem rational_recovery {k : Type*} [Field k] (K w r t : k)
    (hc : t^3+t^2=r) (hw : w*(1+K*t)^7=K^3*(K-1)*t*(1+t)^6) :
    let (a,b,c) := inverseCoefficients K w r
    let d := b^2-a*c-a*b
    d ≠ 0 → t=(r*a^2+a*c-b*c)/d := by
  rcases h : reducedPower K r 7 with ⟨a,b,c⟩
  rcases h' : reducedPower (1:k) r 6 with ⟨i,j,l⟩
  have h7 := reducedPower_eval K r t 7 hc
  have h6 := reducedPower_eval (1:k) r t 6 hc
  simp only [h] at h7
  simp only [h',one_mul] at h6
  simp only [inverseCoefficients,h,h']
  let A := w*a - K^3*(K-1)*(j-i)
  let B := w*b - K^3*(K-1)*l
  let C := w*c - K^3*(K-1)*i*r
  change B^2-A*C-A*B ≠ 0 → t=(r*A^2+A*C-B*C)/(B^2-A*C-A*B)
  have h2 : A*t^2+B*t+C=0 := by
    dsimp [A,B,C]
    linear_combination w*h7 - K^3*(K-1)*t*h6 + hw + K^3*(K-1)*i*hc
  intro hd
  apply (eq_div_iff hd).mpr
  linear_combination A^2*hc + (B-A-A*t)*h2

/-- Relate the two polynomial equations used by the inverse to the observed weak
value and scaled ratio at an admissible split. -/
theorem physical_cubic_equations {K x : ℝ} (hx : x ∈ Set.Ioo 1 K) :
    let t := (x-1)/(K-x)
    let r := 4*(K-1)*ratioAt K x/K^2
    t^3+t^2=r ∧ weakAt K x*(1+K*t)^7=K^3*(K-1)*t*(1+t)^6 := by
  have hk : 0 < K := lt_trans (by norm_num) (lt_trans hx.1 hx.2)
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  dsimp [weakAt,ratioAt]
  constructor <;> field_simp [sub_ne_zero.mpr hx.2.ne', hx0.ne', hk.ne'] <;> ring
end PDTGauge
