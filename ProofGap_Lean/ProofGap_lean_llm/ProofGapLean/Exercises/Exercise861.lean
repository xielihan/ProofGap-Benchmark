import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise861

noncomputable section

/-- The real, sign-preserving cube root. -/
def signedCbrt (x : ℝ) : ℝ :=
  Real.sign x * Real.rpow |x| (1 / 3 : ℝ)

def c₁ (x : ℝ) : ℝ :=
  signedCbrt x

def c₂ (x : ℝ) : ℝ :=
  signedCbrt (1 + c₁ x)

def y (x : ℝ) : ℝ :=
  signedCbrt (1 + c₂ x)

/-- Exercise 861, gap 1.
All three cube-root inputs are required to be nonzero. -/
private theorem signedCbrt_pos {x : ℝ} (hx : 0 < x) :
    0 < signedCbrt x := by
  rw [signedCbrt, Real.sign_of_pos hx, one_mul, abs_of_pos hx]
  exact Real.rpow_pos_of_pos hx _

private theorem signedCbrt_mul_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    signedCbrt (a * b) = signedCbrt a * signedCbrt b := by
  simp only [signedCbrt, Real.sign_of_pos ha, Real.sign_of_pos hb,
    Real.sign_of_pos (mul_pos ha hb), one_mul, abs_of_pos ha,
    abs_of_pos hb, abs_of_pos (mul_pos ha hb)]
  exact Real.mul_rpow ha.le hb.le

private theorem signedCbrt_sq (x : ℝ) (hx : x ≠ 0) :
    signedCbrt (x ^ 2) = Real.rpow |x| (2 / 3 : ℝ) := by
  have ha : 0 < |x| := abs_pos.mpr hx
  have hs : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  rw [signedCbrt, Real.sign_of_pos hs, one_mul, abs_of_pos hs, ← sq_abs x]
  change Real.rpow (|x| ^ (2 : ℕ)) (1 / 3 : ℝ) =
    Real.rpow |x| (2 / 3 : ℝ)
  calc
    Real.rpow (|x| ^ (2 : ℕ)) (1 / 3 : ℝ) =
        Real.rpow (Real.rpow |x| (((2 : ℕ) : ℝ))) (1 / 3 : ℝ) := by
      apply congrArg (fun t : ℝ => Real.rpow t (1 / 3 : ℝ))
      exact (Real.rpow_natCast |x| 2).symm
    _ = Real.rpow |x| ((((2 : ℕ) : ℝ)) * (1 / 3 : ℝ)) := by
      exact (Real.rpow_mul ha.le _ _).symm
    _ = Real.rpow |x| (2 / 3 : ℝ) := by norm_num

private theorem signedCbrt_deriv_coeff (x : ℝ) (hx : x ≠ 0) :
    (1 / 3 : ℝ) * |x| ^ ((1 / 3 : ℝ) - 1) =
      1 / (3 * signedCbrt (x ^ 2)) := by
  have ha : 0 < |x| := abs_pos.mpr hx
  have hr : Real.rpow |x| (2 / 3 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos ha _).ne'
  rw [signedCbrt_sq x hx]
  change (1 / 3 : ℝ) * Real.rpow |x| ((1 / 3 : ℝ) - 1) =
    1 / (3 * Real.rpow |x| (2 / 3 : ℝ))
  rw [show (1 / 3 : ℝ) - 1 = -(2 / 3 : ℝ) by norm_num]
  have hneg :
      Real.rpow |x| (-(2 / 3 : ℝ)) =
        (Real.rpow |x| (2 / 3 : ℝ))⁻¹ := by
    exact Real.rpow_neg ha.le _
  rw [hneg]
  field_simp [hr]

private theorem hasDerivAt_signedCbrt_raw (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt signedCbrt
      ((1 / 3 : ℝ) * |x| ^ ((1 / 3 : ℝ) - 1)) x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have heq :
        signedCbrt =ᶠ[nhds x]
          (fun z : ℝ => -((-z) ^ (1 / 3 : ℝ))) := by
      filter_upwards [isOpen_Iio.mem_nhds hneg] with z hz
      change z < 0 at hz
      simpa [signedCbrt, Real.sign_of_neg hz, abs_of_neg hz]
    have hbase :
        HasDerivAt (fun z : ℝ => z ^ (1 / 3 : ℝ))
          ((1 / 3 : ℝ) * (-x) ^ ((1 / 3 : ℝ) - 1)) (-x) :=
      Real.hasDerivAt_rpow_const (Or.inl (neg_ne_zero.mpr hx))
    have hd :
        HasDerivAt (fun z : ℝ => -((-z) ^ (1 / 3 : ℝ)))
          ((1 / 3 : ℝ) * (-x) ^ ((1 / 3 : ℝ) - 1)) x := by
      simpa [Function.comp_def] using
        (hbase.comp x ((hasDerivAt_id x).neg)).neg
    have hd' := hd.congr_of_eventuallyEq heq
    simpa [abs_of_neg hneg] using hd'
  · have heq :
        signedCbrt =ᶠ[nhds x] (fun z : ℝ => z ^ (1 / 3 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hpos] with z hz
      change 0 < z at hz
      simpa [signedCbrt, Real.sign_of_pos hz, abs_of_pos hz]
    have hd :
        HasDerivAt (fun z : ℝ => z ^ (1 / 3 : ℝ))
          ((1 / 3 : ℝ) * x ^ ((1 / 3 : ℝ) - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx)
    have hd' := hd.congr_of_eventuallyEq heq
    simpa [abs_of_pos hpos] using hd'

private theorem hasDerivAt_signedCbrt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt signedCbrt (1 / (3 * signedCbrt (x ^ 2))) x := by
  rw [← signedCbrt_deriv_coeff x hx]
  exact hasDerivAt_signedCbrt_raw x hx

theorem gap1 (x : ℝ) (h₁ : x ≠ 0) (h₂ : 1 + c₁ x ≠ 0)
    (h₃ : 1 + c₂ x ≠ 0) :
    HasDerivAt y
      (1 / (3 * signedCbrt ((1 + c₂ x) ^ 2)) *
        (1 / (3 * signedCbrt ((1 + c₁ x) ^ 2))) *
        (1 / (3 * signedCbrt (x ^ 2)))) x := by
  have hc1 :
      HasDerivAt c₁ (1 / (3 * signedCbrt (x ^ 2))) x := by
    simpa [c₁] using hasDerivAt_signedCbrt x h₁
  have hc2 :
      HasDerivAt c₂
        (1 / (3 * signedCbrt ((1 + c₁ x) ^ 2)) *
          (1 / (3 * signedCbrt (x ^ 2)))) x := by
    simpa [c₂, Function.comp_def] using
      (hasDerivAt_signedCbrt (1 + c₁ x) h₂).comp x (hc1.const_add 1)
  simpa [y, Function.comp_def, mul_assoc] using
    (hasDerivAt_signedCbrt (1 + c₂ x) h₃).comp x (hc2.const_add 1)

/-- Exercise 861, gap 2.
The omitted nonzero conditions make the displayed reciprocals meaningful. -/
theorem gap2 (x : ℝ) (h₁ : x ≠ 0) (h₂ : 1 + c₁ x ≠ 0)
    (h₃ : 1 + c₂ x ≠ 0) :
    1 / (3 * signedCbrt ((1 + c₂ x) ^ 2)) *
          (1 / (3 * signedCbrt ((1 + c₁ x) ^ 2))) *
          (1 / (3 * signedCbrt (x ^ 2))) =
      1 /
        (27 * signedCbrt (x ^ 2 * (1 + c₁ x) ^ 2) *
          signedCbrt ((1 + c₂ x) ^ 2)) := by
  have hx0 : signedCbrt (x ^ 2) ≠ 0 :=
    (signedCbrt_pos (sq_pos_of_ne_zero h₁)).ne'
  have hc10 : signedCbrt ((1 + c₁ x) ^ 2) ≠ 0 :=
    (signedCbrt_pos (sq_pos_of_ne_zero h₂)).ne'
  have hc20 : signedCbrt ((1 + c₂ x) ^ 2) ≠ 0 :=
    (signedCbrt_pos (sq_pos_of_ne_zero h₃)).ne'
  rw [signedCbrt_mul_of_pos
    (sq_pos_of_ne_zero h₁) (sq_pos_of_ne_zero h₂)]
  field_simp [hx0, hc10, hc20]
  ring

/-- Exercise 861, gap 3.
All three cube-root inputs are required to be nonzero. -/
theorem gap3 (x : ℝ) (h₁ : x ≠ 0) (h₂ : 1 + c₁ x ≠ 0)
    (h₃ : 1 + c₂ x ≠ 0) :
    HasDerivAt y
      (1 /
        (27 * signedCbrt (x ^ 2 * (1 + c₁ x) ^ 2) *
          signedCbrt ((1 + c₂ x) ^ 2))) x := by
  have h := gap1 x h₁ h₂ h₃
  rw [gap2 x h₁ h₂ h₃] at h
  exact h

end

end ProofGap.Exercise861
