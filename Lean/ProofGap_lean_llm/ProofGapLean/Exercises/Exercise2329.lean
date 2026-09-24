import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

open scoped Interval

namespace ProofGap.Exercise2329

noncomputable section

def φ (a x : ℝ) : ℝ := Real.exp (-a * x) / x
def targetIntegral (a b : ℝ) : ℝ :=
  ∫ x in a..b, φ a x * Real.sin x

def meanValueExpression (a b ξ : ℝ) : ℝ :=
  (φ a a - φ a b) * (Real.cos a - Real.cos ξ) +
    φ a b * (Real.cos a - Real.cos b)

def θValue (a b ξ : ℝ) : ℝ :=
  a / 2 * meanValueExpression a b ξ

private def primitive (a x : ℝ) : ℝ := Real.cos a - Real.cos x

private def weight (a x : ℝ) : ℝ :=
  Real.exp (-a * x) * (a * x + 1) / x ^ 2

private theorem hasDerivAt_phi (a x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (φ a) (-weight a x) x := by
  have hlin : HasDerivAt (fun y : ℝ => -a * y) (-a) x := by
    simpa using (hasDerivAt_id x).const_mul (-a)
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-a * y))
      (-a * Real.exp (-a * x)) x := by
    convert (Real.hasDerivAt_exp (-a * x)).comp x hlin using 1 <;> ring
  unfold φ weight
  convert hexp.div (hasDerivAt_id x) hx using 1 <;>
    simp [id] <;> field_simp [hx] <;> ring

private theorem exists_meanValue (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ξ ∈ Set.Icc a b,
      targetIntegral a b = meanValueExpression a b ξ := by
  have hle : a ≤ b := hab.le
  have hu : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (φ a) (-weight a x) x := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    exact hasDerivAt_phi a x (ha.trans_le hx.1).ne'
  have hv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (primitive a) (Real.sin x) x := by
    intro x hx
    unfold primitive
    convert (hasDerivAt_const x (Real.cos a)).sub (Real.hasDerivAt_cos x) using 1 <;> ring
  have hwInt : IntervalIntegrable (weight a) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hle]
    unfold weight
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      exact (sq_pos_of_pos (ha.trans_le hx.1)).ne'
  have hsinInt : IntervalIntegrable Real.sin MeasureTheory.volume a b :=
    Real.continuous_sin.intervalIntegrable a b
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    hwInt.neg hsinInt
  have hprim : ContinuousOn (primitive a) (Set.uIcc a b) := by
    unfold primitive
    fun_prop
  have hw0 : ∀ x ∈ Set.uIoc a b, 0 ≤ weight a x := by
    intro x hx
    rw [Set.uIoc_of_le hle] at hx
    unfold weight
    have hxpos : 0 < x := ha.trans_le hx.1.le
    positivity
  rcases exists_eq_const_mul_intervalIntegral_of_nonneg hprim hwInt hw0 with
    ⟨ξ, hξ, hmean⟩
  rw [Set.uIcc_of_le hle] at hξ
  have hweight : (∫ x in a..b, weight a x) = φ a a - φ a b := by
    have hderiv := intervalIntegral.integral_eq_sub_of_hasDerivAt hu hwInt.neg
    rw [intervalIntegral.integral_neg] at hderiv
    linarith
  have hpa : primitive a a = 0 := by simp [primitive]
  have hrewrite :
      (∫ x in a..b, weight a x * primitive a x) =
        primitive a ξ * (φ a a - φ a b) := by
    calc
      _ = ∫ x in a..b, primitive a x * weight a x := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = _ := by rw [hmean, hweight]
  unfold targetIntegral
  have htarget :
      (∫ x in a..b, φ a x * Real.sin x) =
        φ a b * primitive a b +
          ∫ x in a..b, weight a x * primitive a x := by
    rw [hpa] at hparts
    simp only [mul_zero, sub_zero] at hparts
    have hneg :
        -(∫ x in a..b, -weight a x * primitive a x) =
          ∫ x in a..b, weight a x * primitive a x := by
      calc
        _ = ∫ x in a..b, -(-weight a x * primitive a x) :=
          (intervalIntegral.integral_neg).symm
        _ = _ := by
          apply intervalIntegral.integral_congr
          intro x hx
          ring
    linarith [hparts, hneg]
  refine ⟨ξ, hξ, ?_⟩
  rw [htarget, hrewrite]
  unfold meanValueExpression primitive
  ring

private theorem phi_nonneg_of_le (a x : ℝ) (ha : 0 < a) (hax : a ≤ x) :
    0 ≤ φ a x := by
  unfold φ
  exact div_nonneg (Real.exp_pos _).le (ha.trans_le hax).le

private theorem phi_le_phi (a x y : ℝ) (ha : 0 < a)
    (hax : a ≤ x) (hxy : x ≤ y) : φ a y ≤ φ a x := by
  unfold φ
  have hxpos : 0 < x := ha.trans_le hax
  have hypos : 0 < y := hxpos.trans_le hxy
  have hexp : Real.exp (-a * y) ≤ Real.exp (-a * x) := by
    rw [Real.exp_le_exp]
    nlinarith
  calc
    Real.exp (-a * y) / y ≤ Real.exp (-a * x) / y :=
      div_le_div_of_nonneg_right hexp hypos.le
    _ ≤ Real.exp (-a * x) / x :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hxpos hxy

private theorem theta_abs_lt_one (a b ξ : ℝ) (ha : 0 < a)
    (hab : a < b) (hξ : ξ ∈ Set.Icc a b) :
    |θValue a b ξ| < 1 := by
  have hub : 0 ≤ φ a b := phi_nonneg_of_le a b ha hab.le
  have hle : φ a b ≤ φ a a := phi_le_phi a a b ha le_rfl hab.le
  have hd : 0 ≤ φ a a - φ a b := sub_nonneg.mpr hle
  have hp : |Real.cos a - Real.cos ξ| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [Real.neg_one_le_cos a, Real.cos_le_one a,
      Real.neg_one_le_cos ξ, Real.cos_le_one ξ]
  have hq : |Real.cos a - Real.cos b| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [Real.neg_one_le_cos a, Real.cos_le_one a,
      Real.neg_one_le_cos b, Real.cos_le_one b]
  have hmean : |meanValueExpression a b ξ| ≤ 2 * φ a a := by
    unfold meanValueExpression
    calc
      _ ≤ |(φ a a - φ a b) * (Real.cos a - Real.cos ξ)| +
          |φ a b * (Real.cos a - Real.cos b)| := abs_add_le _ _
      _ = (φ a a - φ a b) * |Real.cos a - Real.cos ξ| +
          φ a b * |Real.cos a - Real.cos b| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hd, abs_of_nonneg hub]
      _ ≤ (φ a a - φ a b) * 2 + φ a b * 2 := by
            exact add_le_add (mul_le_mul_of_nonneg_left hp hd)
              (mul_le_mul_of_nonneg_left hq hub)
      _ = 2 * φ a a := by ring
  unfold θValue
  rw [abs_mul, abs_of_pos (half_pos ha)]
  calc
    a / 2 * |meanValueExpression a b ξ| ≤ a / 2 * (2 * φ a a) :=
      mul_le_mul_of_nonneg_left hmean (half_pos ha).le
    _ = Real.exp (-a * a) := by
      unfold φ
      field_simp [ha.ne']
    _ < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [sq_pos_of_pos ha])

theorem gap1 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ξ ∈ Set.Icc a b,
      targetIntegral a b =
        (φ a a - φ a b) * (∫ x in a..ξ, Real.sin x) +
          φ a b * ∫ x in a..b, Real.sin x := by
  rcases exists_meanValue a b ha hab with ⟨ξ, hξ, htarget⟩
  refine ⟨ξ, hξ, ?_⟩
  rw [htarget]
  unfold meanValueExpression
  rw [integral_sin, integral_sin]

theorem gap2 (a b ξ : ℝ) :
    (φ a a - φ a b) * (∫ x in a..ξ, Real.sin x) +
        φ a b * (∫ x in a..b, Real.sin x) =
      meanValueExpression a b ξ := by
  unfold meanValueExpression
  rw [integral_sin, integral_sin]

theorem gap3 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ξ ∈ Set.Icc a b,
      targetIntegral a b = meanValueExpression a b ξ := by
  exact exists_meanValue a b ha hab

theorem gap4 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ξ ∈ Set.Icc a b,
      targetIntegral a b =
        (φ a a - φ a b) *
            (-2 * Real.sin ((a + ξ) / 2) * Real.sin ((a - ξ) / 2)) +
          φ a b *
            (-2 * Real.sin ((a + b) / 2) * Real.sin ((a - b) / 2)) := by
  rcases gap3 a b ha hab with ⟨ξ, hξ, htarget⟩
  refine ⟨ξ, hξ, ?_⟩
  rw [htarget]
  unfold meanValueExpression
  rw [Real.cos_sub_cos, Real.cos_sub_cos]

theorem gap5 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ξ ∈ Set.Icc a b, ∃ θ : ℝ,
      θ = θValue a b ξ ∧ targetIntegral a b = 2 / a * θ := by
  rcases gap3 a b ha hab with ⟨ξ, hξ, htarget⟩
  refine ⟨ξ, hξ, θValue a b ξ, rfl, ?_⟩
  rw [htarget]
  unfold θValue
  field_simp [ha.ne']

theorem gap6 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ θ : ℝ, targetIntegral a b = 2 / a * θ := by
  rcases gap5 a b ha hab with ⟨ξ, hξ, θ, hθ, htarget⟩
  exact ⟨θ, htarget⟩

theorem gap7 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ξ ∈ Set.Icc a b, a ≤ ξ := by
  exact ⟨a, ⟨le_rfl, hab.le⟩, le_rfl⟩

theorem gap8 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ξ ∈ Set.Icc a b, ξ ≤ b := by
  exact ⟨b, ⟨hab.le, le_rfl⟩, le_rfl⟩

theorem gap9 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ θ : ℝ, targetIntegral a b = 2 / a * θ ∧ |θ| < 1 := by
  rcases gap3 a b ha hab with ⟨ξ, hξ, htarget⟩
  refine ⟨θValue a b ξ, ?_, theta_abs_lt_one a b ξ ha hab hξ⟩
  rw [htarget]
  unfold θValue
  field_simp [ha.ne']

end

end ProofGap.Exercise2329
