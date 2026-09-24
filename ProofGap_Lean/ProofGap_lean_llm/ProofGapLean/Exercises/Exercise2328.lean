import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped Interval

namespace ProofGap.Exercise2328

noncomputable section

def a : ℝ := 100 * Real.pi
def b : ℝ := 200 * Real.pi
def f (x : ℝ) : ℝ := Real.sin x
def φ (x : ℝ) : ℝ := 1 / x
def targetIntegral : ℝ := ∫ x in a..b, φ x * f x

def correctedMeanValue (ξ : ℝ) : ℝ :=
  (φ a - φ b) * ∫ x in a..ξ, f x

def θValue (ξ : ℝ) : ℝ := Real.sin (ξ / 2) ^ 2

private theorem a_pos : 0 < a := by
  unfold a
  positivity

private theorem a_le_b : a ≤ b := by
  unfold a b
  nlinarith [Real.pi_pos]

private theorem cos_a : Real.cos a = 1 := by
  unfold a
  convert Real.cos_nat_mul_two_pi 50 using 1 <;> norm_num <;> ring

private theorem cos_b : Real.cos b = 1 := by
  unfold b
  convert Real.cos_nat_mul_two_pi 100 using 1 <;> norm_num <;> ring

private theorem correctedMeanValue_formula (ξ : ℝ) :
    correctedMeanValue ξ = (1 - Real.cos ξ) / (200 * Real.pi) := by
  unfold correctedMeanValue φ f
  rw [integral_sin, cos_a]
  unfold a b
  field_simp [Real.pi_ne_zero]
  ring

private theorem targetIntegral_eq_aux :
    targetIntegral = ∫ x in a..b, (1 - Real.cos x) / x ^ 2 := by
  have hu : ∀ x ∈ Set.uIcc a b,
      HasDerivAt φ (-(x ^ 2)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le a_le_b] at hx
    have hxpos : 0 < x := a_pos.trans_le hx.1
    unfold φ
    simpa [one_div] using hasDerivAt_inv hxpos.ne'
  have hv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => 1 - Real.cos y) (Real.sin x) x := by
    intro x hx
    convert (hasDerivAt_const x 1).sub (Real.hasDerivAt_cos x) using 1 <;> ring
  have huInt : IntervalIntegrable (fun x : ℝ => -(x ^ 2)⁻¹)
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le a_le_b]
    exact ((continuous_id.continuousOn.pow 2).inv₀ (fun x hx =>
      (sq_pos_of_pos (a_pos.trans_le hx.1)).ne')).neg
  have hvInt : IntervalIntegrable Real.sin MeasureTheory.volume a b :=
    Real.continuous_sin.intervalIntegrable a b
  have H := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv huInt hvInt
  rw [cos_a, cos_b] at H
  simp only [sub_self, mul_zero, zero_sub] at H
  unfold targetIntegral φ f
  calc
    (∫ x in a..b, 1 / x * Real.sin x) =
        -(∫ x in a..b, -(x ^ 2)⁻¹ * (1 - Real.cos x)) := H
    _ = ∫ x in a..b, (1 - Real.cos x) / x ^ 2 := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [Pi.neg_apply]
      rw [div_eq_mul_inv]
      ring

private def auxIntegrand (x : ℝ) : ℝ := (1 - Real.cos x) / x ^ 2

private theorem aux_intervalIntegrable :
    IntervalIntegrable auxIntegrand MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le a_le_b]
  unfold auxIntegrand
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro x hx
    exact (sq_pos_of_pos (a_pos.trans_le hx.1)).ne'

private theorem targetIntegral_bounds :
    0 ≤ targetIntegral ∧ targetIntegral ≤ 1 / (100 * Real.pi) := by
  have hsqInt : IntervalIntegrable (fun x : ℝ => 2 / x ^ 2)
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le a_le_b]
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      exact (sq_pos_of_pos (a_pos.trans_le hx.1)).ne'
  have hnonneg : 0 ≤ ∫ x in a..b, auxIntegrand x := by
    have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume a b :=
      continuous_const.intervalIntegrable a b
    have hmono := intervalIntegral.integral_mono_on a_le_b hzero aux_intervalIntegrable
      (fun x hx => by
        unfold auxIntegrand
        exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one x)) (sq_nonneg x))
    simpa using hmono
  have hupper : (∫ x in a..b, auxIntegrand x) ≤
      ∫ x in a..b, 2 / x ^ 2 := by
    apply intervalIntegral.integral_mono_on a_le_b aux_intervalIntegrable hsqInt
    intro x hx
    unfold auxIntegrand
    rw [div_le_div_iff_of_pos_right (sq_pos_of_pos (a_pos.trans_le hx.1))]
    linarith [Real.neg_one_le_cos x]
  have heval : (∫ x in a..b, 2 / x ^ 2) = 1 / (100 * Real.pi) := by
    have hd : ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun y : ℝ => -2 / y) (2 / x ^ 2) x := by
      intro x hx
      rw [Set.uIcc_of_le a_le_b] at hx
      have hxpos : 0 < x := a_pos.trans_le hx.1
      convert (hasDerivAt_inv hxpos.ne').const_mul (-2) using 1 <;>
        simp [div_eq_mul_inv] <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hsqInt]
    unfold a b
    field_simp [Real.pi_ne_zero]
    ring
  rw [targetIntegral_eq_aux]
  exact ⟨hnonneg, hupper.trans_eq heval⟩

private theorem exists_correctedMeanValue :
    ∃ ξ ∈ Set.Icc a b, targetIntegral = correctedMeanValue ξ := by
  let c : ℝ := a + Real.pi
  have hac : a ≤ c := by dsimp [c]; linarith [Real.pi_pos]
  have hcb : c ≤ b := by
    dsimp [c]
    unfold a b
    nlinarith [Real.pi_pos]
  have hfun : correctedMeanValue =
      fun ξ : ℝ => (1 - Real.cos ξ) / (200 * Real.pi) := by
    funext ξ
    exact correctedMeanValue_formula ξ
  have hcont : Continuous correctedMeanValue := by
    rw [hfun]
    fun_prop
  have hca : correctedMeanValue a = 0 := by
    rw [correctedMeanValue_formula, cos_a]
    ring
  have hccos : Real.cos c = -1 := by
    dsimp [c]
    rw [Real.cos_add_pi, cos_a]
  have hcc : correctedMeanValue c = 1 / (100 * Real.pi) := by
    rw [correctedMeanValue_formula, hccos]
    field_simp [Real.pi_ne_zero]
    ring
  have ht : targetIntegral ∈ Set.Icc (correctedMeanValue a) (correctedMeanValue c) := by
    rw [hca, hcc]
    exact targetIntegral_bounds
  have himage := intermediate_value_Icc hac hcont.continuousOn ht
  rcases himage with ⟨ξ, hξ, hval⟩
  refine ⟨ξ, ⟨hξ.1, hξ.2.trans hcb⟩, ?_⟩
  exact hval.symm

theorem gap1 :
    ContinuousOn f (Set.Icc a b) := by
  exact Real.continuous_sin.continuousOn

theorem gap2 :
    AntitoneOn φ (Set.Icc a b) := by
  intro x hx y hy hxy
  unfold φ
  exact one_div_le_one_div_of_le (a_pos.trans_le hx.1) hxy

theorem gap3 :
    AntitoneOn φ (Set.Icc a b) := by
  exact gap2

theorem gap4 (x : ℝ) (hx : x ∈ Set.Icc a b) :
    0 ≤ φ x := by
  unfold φ
  exact one_div_nonneg.mpr (a_pos.trans_le hx.1).le

theorem gap5 :
    ∃ ξ ∈ Set.Icc a b,
      targetIntegral = correctedMeanValue ξ := by
  exact exists_correctedMeanValue

theorem gap6 (ξ : ℝ) :
    correctedMeanValue ξ =
      (1 - Real.cos ξ) / (200 * Real.pi) := by
  exact correctedMeanValue_formula ξ

theorem gap7 (ξ : ℝ) :
    (1 - Real.cos ξ) / (200 * Real.pi) =
      Real.sin (ξ / 2) ^ 2 / (100 * Real.pi) := by
  have htrig : 1 - Real.cos ξ = 2 * Real.sin (ξ / 2) ^ 2 := by
    have hc : Real.cos ξ = Real.cos (2 * (ξ / 2)) := by congr 1 <;> ring
    rw [hc, Real.cos_two_mul']
    nlinarith [Real.sin_sq_add_cos_sq (ξ / 2)]
  rw [htrig]
  field_simp [Real.pi_ne_zero]
  ring

theorem gap8 (ξ : ℝ) :
    ∃ θ : ℝ, θ = θValue ξ ∧
      Real.sin (ξ / 2) ^ 2 / (100 * Real.pi) =
        θ / (100 * Real.pi) := by
  exact ⟨θValue ξ, rfl, rfl⟩

theorem gap9 :
    ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      targetIntegral = θ / (100 * Real.pi) := by
  rcases gap5 with ⟨ξ, hξ, htarget⟩
  refine ⟨θValue ξ, ?_, ?_⟩
  · unfold θValue
    constructor
    · positivity
    · nlinarith [Real.neg_one_le_sin (ξ / 2), Real.sin_le_one (ξ / 2)]
  · rw [htarget, gap6, gap7]
    rfl

theorem gap10 :
    ∃ ξ ∈ Set.Icc a b, a ≤ ξ := by
  exact ⟨a, ⟨le_rfl, a_le_b⟩, le_rfl⟩

theorem gap11 :
    ∃ ξ ∈ Set.Icc a b, ξ ≤ b := by
  exact ⟨b, ⟨a_le_b, le_rfl⟩, le_rfl⟩

theorem gap12 :
    ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      targetIntegral = θ / (100 * Real.pi) ∧ 0 ≤ θ := by
  rcases gap9 with ⟨θ, hθ, htarget⟩
  exact ⟨θ, hθ, htarget, hθ.1⟩

theorem gap13 :
    ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      targetIntegral = θ / (100 * Real.pi) ∧ θ ≤ 1 := by
  rcases gap9 with ⟨θ, hθ, htarget⟩
  exact ⟨θ, hθ, htarget, hθ.2⟩

end

end ProofGap.Exercise2328
