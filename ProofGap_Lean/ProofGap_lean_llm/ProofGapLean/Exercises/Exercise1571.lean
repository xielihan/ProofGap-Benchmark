import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1571

noncomputable section

def height (R x : ℝ) : ℝ := 2 * R * x ^ 2 / (x ^ 2 - R ^ 2)
def volume (R x : ℝ) : ℝ :=
  (2 / 3 : ℝ) * Real.pi * R * x ^ 4 / (x ^ 2 - R ^ 2)
def optimalRadius (R : ℝ) : ℝ := Real.sqrt 2 * R

def Feasible (R x h : ℝ) : Prop :=
  0 < R ∧ R < x ∧ h = height R x

def IsOptimal (R x h : ℝ) : Prop :=
  Feasible R x h ∧ ∀ x₁ h₁, Feasible R x₁ h₁ →
    (1 / 3 : ℝ) * Real.pi * x ^ 2 * h ≤
      (1 / 3 : ℝ) * Real.pi * x₁ ^ 2 * h₁

private theorem optimalRadius_sq (R : ℝ) :
    optimalRadius R ^ 2 = 2 * R ^ 2 := by
  unfold optimalRadius
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem gap1 (R x h : ℝ) (hfeas : Feasible R x h) :
    h = height R x := by
  exact hfeas.2.2

theorem gap2 (R x : ℝ) :
    volume R x =
      (1 / 3 : ℝ) * Real.pi * x ^ 2 * height R x := by
  unfold volume height
  ring

theorem gap3 (R x : ℝ) :
    (1 / 3 : ℝ) * Real.pi * x ^ 2 * height R x =
      (2 / 3 : ℝ) * Real.pi * R * x ^ 4 / (x ^ 2 - R ^ 2) := by
  unfold height
  ring

theorem gap4 (R x : ℝ) :
    volume R x =
      (2 / 3 : ℝ) * Real.pi * R * x ^ 4 / (x ^ 2 - R ^ 2) := by
  rfl

theorem gap5 (R x : ℝ) (hx : x ^ 2 ≠ R ^ 2) :
    deriv (volume R) x =
      (4 / 3 : ℝ) * Real.pi * R * x ^ 3 * (x ^ 2 - 2 * R ^ 2) /
        (x ^ 2 - R ^ 2) ^ 2 := by
  have hden : x ^ 2 - R ^ 2 ≠ 0 := sub_ne_zero.mpr hx
  have hnum :
      HasDerivAt
        (fun y : ℝ => (2 / 3 : ℝ) * Real.pi * R * y ^ 4)
        (4 * ((2 / 3 : ℝ) * Real.pi * R) * x ^ 3) x := by
    convert
      (hasDerivAt_pow 4 x).const_mul
        ((2 / 3 : ℝ) * Real.pi * R) using 1 <;> ring
  have hden' :
      HasDerivAt (fun y : ℝ => y ^ 2 - R ^ 2) (2 * x) x := by
    convert (hasDerivAt_pow 2 x).sub_const (R ^ 2) using 1 <;> ring
  have hquot := hnum.div hden' hden
  change deriv
      (fun y : ℝ =>
        (2 / 3 : ℝ) * Real.pi * R * y ^ 4 /
          (y ^ 2 - R ^ 2)) x = _
  calc
    deriv
        (fun y : ℝ =>
          (2 / 3 : ℝ) * Real.pi * R * y ^ 4 /
            (y ^ 2 - R ^ 2)) x =
        ((4 * ((2 / 3 : ℝ) * Real.pi * R) * x ^ 3) *
              (x ^ 2 - R ^ 2) -
            ((2 / 3 : ℝ) * Real.pi * R * x ^ 4) * (2 * x)) /
          (x ^ 2 - R ^ 2) ^ 2 := hquot.deriv
    _ =
        (4 / 3 : ℝ) * Real.pi * R * x ^ 3 *
            (x ^ 2 - 2 * R ^ 2) /
          (x ^ 2 - R ^ 2) ^ 2 := by
      field_simp [hden]
      ring

theorem gap6 (R x : ℝ) (hR : 0 < R) (hx : R < x)
    (hcrit : deriv (volume R) x = 0) :
    x = optimalRadius R := by
  have hxpos : 0 < x := lt_trans hR hx
  have hprod : 0 < (x - R) * (x + R) :=
    mul_pos (sub_pos.mpr hx) (by linarith)
  have hsq : R ^ 2 < x ^ 2 := by
    nlinarith
  have hxne : x ^ 2 ≠ R ^ 2 := ne_of_gt hsq
  rw [gap5 R x hxne] at hcrit
  have hden2 : (x ^ 2 - R ^ 2) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (sub_ne_zero.mpr hxne)
  have hnum_eq := (div_eq_iff hden2).mp hcrit
  have hnum :
      (4 / 3 : ℝ) * Real.pi * R * x ^ 3 *
          (x ^ 2 - 2 * R ^ 2) = 0 := by
    simpa using hnum_eq
  have hprefix : 0 < (4 / 3 : ℝ) * Real.pi * R * x ^ 3 := by
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) Real.pi_pos) hR)
      (pow_pos hxpos 3)
  have hquad : x ^ 2 - 2 * R ^ 2 = 0 :=
    (mul_eq_zero.mp hnum).resolve_left (ne_of_gt hprefix)
  have hoptpos : 0 < optimalRadius R := by
    unfold optimalRadius
    exact mul_pos (Real.sqrt_pos.2 (by norm_num)) hR
  nlinarith [optimalRadius_sq R]

theorem gap7 (R : ℝ) (hR : 0 < R) :
    deriv (volume R) (optimalRadius R) = 0 := by
  have hR2 : 0 < R ^ 2 := pow_pos hR 2
  have hne : (optimalRadius R) ^ 2 ≠ R ^ 2 := by
    rw [optimalRadius_sq]
    nlinarith
  rw [gap5 R (optimalRadius R) hne]
  rw [optimalRadius_sq]
  ring

theorem gap8 (R : ℝ) (hR : 0 < R) :
    R < optimalRadius R := by
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs1 : 1 < Real.sqrt 2 := by
    nlinarith
  unfold optimalRadius
  simpa using (mul_lt_mul_of_pos_right hs1 hR)

theorem gap9 (R : ℝ) (hR : 0 < R) :
    volume R (optimalRadius R) = (8 / 3 : ℝ) * Real.pi * R ^ 3 := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hopt4 : (optimalRadius R) ^ 4 = 4 * R ^ 4 := by
    calc
      (optimalRadius R) ^ 4 = ((optimalRadius R) ^ 2) ^ 2 := by ring
      _ = (2 * R ^ 2) ^ 2 := by rw [optimalRadius_sq]
      _ = 4 * R ^ 4 := by ring
  unfold volume
  rw [optimalRadius_sq, hopt4]
  field_simp [hRne]
  <;> ring

theorem gap10 (R : ℝ) (hR : 0 < R) :
    ∀ x ∈ Set.Ioi R, volume R (optimalRadius R) ≤ volume R x := by
  intro x hx
  have hdiff : 0 < x - R := sub_pos.mpr hx
  have hsum : 0 < x + R := by linarith
  have hprod : 0 < (x - R) * (x + R) := mul_pos hdiff hsum
  have hsq : R ^ 2 < x ^ 2 := by
    nlinarith
  have hd : 0 < x ^ 2 - R ^ 2 := sub_pos.mpr hsq
  rw [gap9 R hR]
  unfold volume
  apply (le_div_iff₀ hd).2
  have hk : 0 ≤ (2 / 3 : ℝ) * Real.pi * R :=
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) hR).le
  have hnonneg :=
    mul_nonneg hk (sq_nonneg (x ^ 2 - 2 * R ^ 2))
  nlinarith

theorem gap11 (R : ℝ) (hR : 0 < R) :
    IsOptimal R (optimalRadius R) (4 * R) := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hheight : 4 * R = height R (optimalRadius R) := by
    unfold height
    rw [optimalRadius_sq]
    field_simp [hRne]
    <;> ring
  constructor
  · exact ⟨hR, gap8 R hR, hheight⟩
  · intro x₁ h₁ hfeas
    calc
      (1 / 3 : ℝ) * Real.pi * (optimalRadius R) ^ 2 * (4 * R) =
          (1 / 3 : ℝ) * Real.pi * (optimalRadius R) ^ 2 *
            height R (optimalRadius R) := by rw [hheight]
      _ = volume R (optimalRadius R) := (gap2 R (optimalRadius R)).symm
      _ ≤ volume R x₁ := gap10 R hR x₁ hfeas.2.1
      _ = (1 / 3 : ℝ) * Real.pi * x₁ ^ 2 * height R x₁ := gap2 R x₁
      _ = (1 / 3 : ℝ) * Real.pi * x₁ ^ 2 * h₁ := by
        rw [← hfeas.2.2]

end

end ProofGap.Exercise1571
