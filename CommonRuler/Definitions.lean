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
