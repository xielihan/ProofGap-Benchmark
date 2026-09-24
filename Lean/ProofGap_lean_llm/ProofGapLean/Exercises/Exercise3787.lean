import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3787

noncomputable section

open Filter MeasureTheory
open scoped Interval

def integrand (α x : ℝ) : ℝ :=
  Real.cos x / (1 + (x + α) ^ 2)

def parameterDerivative (α x : ℝ) : ℝ :=
  -(2 * (x + α) * Real.cos x) / (1 + (x + α) ^ 2) ^ 2

def F (α : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), integrand α x

def localRadius (α₀ : ℝ) : ℝ :=
  max |α₀ - 1| |α₀ + 1|

private lemma localRadius_nonneg (α₀ : ℝ) :
    0 ≤ localRadius α₀ := by
  exact le_trans (abs_nonneg (α₀ - 1)) (le_max_left _ _)

private lemma abs_le_localRadius
    (α₀ α : ℝ) (hα : α ∈ Set.Ioo (α₀ - 1) (α₀ + 1)) :
    |α| ≤ localRadius α₀ := by
  rw [abs_le]
  constructor
  · have hleft : -(localRadius α₀) ≤ α₀ - 1 := by
      exact le_trans (neg_le_neg (le_max_left _ _))
        (neg_abs_le (α₀ - 1))
    linarith [hα.1]
  · have hright : α₀ + 1 ≤ localRadius α₀ := by
      exact le_trans (le_abs_self (α₀ + 1)) (le_max_right _ _)
    linarith [hα.2]

private lemma hasDerivAt_integrand (α x : ℝ) :
    HasDerivAt (fun a : ℝ => integrand a x)
      (-(2 * (x + α) * Real.cos x) /
        (1 + (x + α) ^ 2) ^ 2) α := by
  unfold integrand
  have hsum : HasDerivAt (fun a : ℝ => x + a) 1 α := by
    simpa using (hasDerivAt_const α x).add (hasDerivAt_id α)
  have hden :
      HasDerivAt (fun a : ℝ => 1 + (x + a) ^ 2)
        (2 * (x + α)) α := by
    convert (hsum.pow 2).const_add 1 using 1 <;> ring
  convert
    (hasDerivAt_const α (Real.cos x)).div hden
      (by nlinarith [sq_nonneg (x + α)]) using 1 <;>
    field_simp <;> ring

private lemma parameterDerivative_eq_deriv (α x : ℝ) :
    parameterDerivative α x =
      deriv (fun a : ℝ => integrand a x) α := by
  rw [(hasDerivAt_integrand α x).deriv]
  unfold parameterDerivative
  rfl

private lemma one_div_shift_sq_le
    (α₀ α x : ℝ) (hα : α ∈ Set.Ioo (α₀ - 1) (α₀ + 1)) :
    1 / (1 + (x + α) ^ 2) ≤
      (2 * (1 + localRadius α₀ ^ 2)) / (1 + x ^ 2) := by
  have hR := localRadius_nonneg α₀
  have ha := abs_le_localRadius α₀ α hα
  have ha_sq : α ^ 2 ≤ localRadius α₀ ^ 2 := by
    have hs :=
      (sq_le_sq₀ (abs_nonneg α) hR).2 ha
    simpa only [sq_abs] using hs
  have hxy :
      x ^ 2 ≤ 2 * (x + α) ^ 2 + 2 * α ^ 2 := by
    nlinarith [sq_nonneg (x + α + α)]
  have hcross :
      0 ≤ localRadius α₀ ^ 2 * (x + α) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpoly :
      1 + x ^ 2 ≤
        2 * (1 + localRadius α₀ ^ 2) * (1 + (x + α) ^ 2) := by
    nlinarith [sq_nonneg (x + α), sq_nonneg α]
  exact
    (div_le_div_iff₀ (by positivity : 0 < 1 + (x + α) ^ 2)
      (by positivity : 0 < 1 + x ^ 2)).2 (by
        nlinarith [hpoly])

private lemma norm_integrand_le_global
    (α₀ α x : ℝ) (hα : α ∈ Set.Ioo (α₀ - 1) (α₀ + 1)) :
    ‖integrand α x‖ ≤
      (2 * (1 + localRadius α₀ ^ 2)) / (1 + x ^ 2) := by
  rw [Real.norm_eq_abs]
  unfold integrand
  rw [abs_div, abs_of_pos (by positivity : 0 < 1 + (x + α) ^ 2)]
  calc
    |Real.cos x| / (1 + (x + α) ^ 2) ≤
        1 / (1 + (x + α) ^ 2) := by
      exact div_le_div_of_nonneg_right
        (abs_le.mpr ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩)
        (by positivity)
    _ ≤ _ := one_div_shift_sq_le α₀ α x hα

private lemma norm_parameterDerivative_le_global
    (α₀ α x : ℝ) (hα : α ∈ Set.Ioo (α₀ - 1) (α₀ + 1)) :
    ‖parameterDerivative α x‖ ≤
      (4 * (1 + localRadius α₀ ^ 2)) / (1 + x ^ 2) := by
  have hy :
      |2 * (x + α) * Real.cos x /
          (1 + (x + α) ^ 2) ^ 2| ≤
        2 / (1 + (x + α) ^ 2) := by
    have hden : 0 < 1 + (x + α) ^ 2 := by positivity
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos (sq_pos_of_pos hden)]
    have hcos :
        |Real.cos x| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩
    have habs : |x + α| ≤ 1 + (x + α) ^ 2 := by
      nlinarith [sq_nonneg (|x + α| - 1), sq_abs (x + α)]
    have hnum :
        |x + α| * |Real.cos x| ≤ 1 + (x + α) ^ 2 :=
      (mul_le_of_le_one_right (abs_nonneg (x + α)) hcos).trans habs
    have hmul :=
      mul_le_mul_of_nonneg_right hnum hden.le
    apply (div_le_div_iff₀ (sq_pos_of_pos hden) hden).2
    nlinarith
  rw [Real.norm_eq_abs]
  unfold parameterDerivative
  rw [show
      -(2 * (x + α) * Real.cos x) / (1 + (x + α) ^ 2) ^ 2 =
        -(2 * (x + α) * Real.cos x /
          (1 + (x + α) ^ 2) ^ 2) by ring, abs_neg]
  calc
    |2 * (x + α) * Real.cos x /
        (1 + (x + α) ^ 2) ^ 2| ≤
        2 / (1 + (x + α) ^ 2) := hy
    _ ≤ 4 * (1 + localRadius α₀ ^ 2) / (1 + x ^ 2) := by
      have h := mul_le_mul_of_nonneg_left
        (one_div_shift_sq_le α₀ α x hα) (by norm_num : (0 : ℝ) ≤ 2)
      convert h using 1 <;> ring

private lemma integrableOn_integrand
    (α₀ α : ℝ) (hα : α ∈ Set.Ioo (α₀ - 1) (α₀ + 1)) :
    IntegrableOn (integrand α) (Set.Ioi (0 : ℝ)) := by
  have hmajor :
      Integrable
        (fun x : ℝ =>
          (2 * (1 + localRadius α₀ ^ 2)) * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul
      (2 * (1 + localRadius α₀ ^ 2))
  apply hmajor.integrableOn.mono'
  · have hden_cont :
        Continuous (fun x : ℝ => 1 + (x + α) ^ 2) := by
      fun_prop
    exact
      (Real.continuous_cos.div hden_cont
        (fun x => by nlinarith [sq_nonneg (x + α)]))
        |>.aestronglyMeasurable
  · filter_upwards with x
    simpa only [div_eq_mul_inv] using norm_integrand_le_global α₀ α x hα

theorem gap1 (α₀ : ℝ) :
    ∀ x α : ℝ, localRadius α₀ < x →
      α ∈ Set.Ioo (α₀ - 1) (α₀ + 1) →
        |integrand α x| ≤
          1 / (1 + (x - localRadius α₀) ^ 2) := by
  intro x α hx hα
  have ha := abs_le_localRadius α₀ α hα
  have ha_lower : -(localRadius α₀) ≤ α := (abs_le.mp ha).1
  have hz : 0 ≤ x - localRadius α₀ := (sub_pos.mpr hx).le
  have hzy : x - localRadius α₀ ≤ x + α := by linarith
  have hy : 0 ≤ x + α := hz.trans hzy
  have hsq :
      (x - localRadius α₀) ^ 2 ≤ (x + α) ^ 2 :=
    (sq_le_sq₀ hz hy).2 hzy
  unfold integrand
  rw [abs_div, abs_of_pos (by positivity : 0 < 1 + (x + α) ^ 2)]
  calc
    |Real.cos x| / (1 + (x + α) ^ 2) ≤
        1 / (1 + (x + α) ^ 2) := by
      exact div_le_div_of_nonneg_right
        (abs_le.mpr ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩)
        (by positivity)
    _ ≤ 1 / (1 + (x - localRadius α₀) ^ 2) := by
      apply (div_le_div_iff₀
        (by positivity : 0 < 1 + (x + α) ^ 2)
        (by positivity : 0 < 1 + (x - localRadius α₀) ^ 2)).2
      nlinarith

theorem gap2 (α₀ : ℝ) :
    ∀ x α : ℝ, localRadius α₀ < x →
      α ∈ Set.Ioo (α₀ - 1) (α₀ + 1) →
        |deriv (fun a : ℝ => integrand a x) α| =
          |2 * (x + α) * Real.cos x / (1 + (x + α) ^ 2) ^ 2| := by
  intro x α hx hα
  rw [← parameterDerivative_eq_deriv]
  unfold parameterDerivative
  rw [show
      -(2 * (x + α) * Real.cos x) / (1 + (x + α) ^ 2) ^ 2 =
        -(2 * (x + α) * Real.cos x /
          (1 + (x + α) ^ 2) ^ 2) by ring, abs_neg]

theorem gap3 (α₀ : ℝ) :
    ∀ x α : ℝ, localRadius α₀ < x →
      α ∈ Set.Ioo (α₀ - 1) (α₀ + 1) →
        |2 * (x + α) * Real.cos x / (1 + (x + α) ^ 2) ^ 2| ≤
          2 / (1 + (x - localRadius α₀) ^ 2) := by
  intro x α hx hα
  have ha := abs_le_localRadius α₀ α hα
  have ha_lower : -(localRadius α₀) ≤ α := (abs_le.mp ha).1
  have hz : 0 ≤ x - localRadius α₀ := (sub_pos.mpr hx).le
  have hzy : x - localRadius α₀ ≤ x + α := by linarith
  have hy_nonneg : 0 ≤ x + α := hz.trans hzy
  have hsq :
      (x - localRadius α₀) ^ 2 ≤ (x + α) ^ 2 :=
    (sq_le_sq₀ hz hy_nonneg).2 hzy
  have hbasic :
      |2 * (x + α) * Real.cos x /
          (1 + (x + α) ^ 2) ^ 2| ≤
        2 / (1 + (x + α) ^ 2) := by
    have hden : 0 < 1 + (x + α) ^ 2 := by positivity
    rw [abs_div, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos (sq_pos_of_pos hden)]
    have hcos :
        |Real.cos x| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩
    have habs : |x + α| ≤ 1 + (x + α) ^ 2 := by
      nlinarith [sq_nonneg (|x + α| - 1), sq_abs (x + α)]
    have hnum :
        |x + α| * |Real.cos x| ≤ 1 + (x + α) ^ 2 :=
      (mul_le_of_le_one_right (abs_nonneg (x + α)) hcos).trans habs
    have hmul := mul_le_mul_of_nonneg_right hnum hden.le
    apply (div_le_div_iff₀ (sq_pos_of_pos hden) hden).2
    nlinarith
  calc
    |2 * (x + α) * Real.cos x /
        (1 + (x + α) ^ 2) ^ 2| ≤
        2 / (1 + (x + α) ^ 2) := hbasic
    _ ≤ 2 / (1 + (x - localRadius α₀) ^ 2) := by
      apply (div_le_div_iff₀
        (by positivity : 0 < 1 + (x + α) ^ 2)
        (by positivity : 0 < 1 + (x - localRadius α₀) ^ 2)).2
      nlinarith

theorem gap4 (α₀ : ℝ) :
    ∀ x α : ℝ, localRadius α₀ < x →
      α ∈ Set.Ioo (α₀ - 1) (α₀ + 1) →
        |deriv (fun a : ℝ => integrand a x) α| ≤
          2 / (1 + (x - localRadius α₀) ^ 2) := by
  intro x α hx hα
  rw [gap2 α₀ x α hx hα]
  exact gap3 α₀ x α hx hα

theorem gap5 (α₀ : ℝ) :
    ∃ L : ℝ,
      Tendsto
        (fun A : ℝ => ∫ x in (0 : ℝ)..A,
          1 / (1 + (x - localRadius α₀) ^ 2))
        atTop (nhds L) := by
  have hglobal :
      Integrable
        (fun x : ℝ =>
          1 / (1 + (x - localRadius α₀) ^ 2)) := by
    simpa only [div_eq_mul_inv, one_mul, sub_eq_add_neg] using
      integrable_inv_one_add_sq.comp_add_right (-(localRadius α₀))
  refine
    ⟨∫ x in Set.Ioi (0 : ℝ),
        1 / (1 + (x - localRadius α₀) ^ 2), ?_⟩
  exact intervalIntegral_tendsto_integral_Ioi
    0 hglobal.integrableOn tendsto_id

private lemma integrable_shift_kernel (α₀ : ℝ) :
    Integrable
      (fun x : ℝ =>
        1 / (1 + (x - localRadius α₀) ^ 2)) := by
  simpa only [div_eq_mul_inv, one_mul, sub_eq_add_neg] using
    integrable_inv_one_add_sq.comp_add_right (-(localRadius α₀))

private lemma shift_kernel_tail_tendsto (α₀ : ℝ) :
    Tendsto
      (fun A : ℝ =>
        ∫ x in Set.Ioi A,
          1 / (1 + (x - localRadius α₀) ^ 2))
      atTop (nhds 0) := by
  have htail (A : ℝ) :
      (∫ x in Set.Ioi A,
        1 / (1 + (x - localRadius α₀) ^ 2)) =
          Real.pi / 2 -
            Real.arctan (A - localRadius α₀) := by
    apply integral_Ioi_of_hasDerivAt_of_tendsto'
      (f := fun x : ℝ => Real.arctan (x - localRadius α₀))
      (m := Real.pi / 2)
    · intro x hx
      convert
        (Real.hasDerivAt_arctan
          (x - localRadius α₀)).comp x
            ((hasDerivAt_id x).sub_const (localRadius α₀)) using 1
      ring
    · exact (integrable_shift_kernel α₀).integrableOn
    · exact
        (tendsto_nhds_of_tendsto_nhdsWithin
          Real.tendsto_arctan_atTop).comp
        (by
          simpa only [sub_eq_add_neg] using
            tendsto_atTop_add_const_right atTop (-(localRadius α₀))
              tendsto_id)
  rw [show
      (fun A : ℝ =>
        ∫ x in Set.Ioi A,
          1 / (1 + (x - localRadius α₀) ^ 2)) =
        fun A : ℝ =>
          Real.pi / 2 -
            Real.arctan (A - localRadius α₀) by
      funext A
      exact htail A]
  convert tendsto_const_nhds.sub
    ((tendsto_nhds_of_tendsto_nhdsWithin
      Real.tendsto_arctan_atTop).comp
      (by
        simpa only [sub_eq_add_neg] using
          tendsto_atTop_add_const_right atTop (-(localRadius α₀))
            tendsto_id)) using 1 <;> ring

theorem gap6 (α₀ ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ A α : ℝ, A₀ < A →
        α ∈ Set.Ioo (α₀ - 1) (α₀ + 1) →
          |∫ x in Set.Ioi A, integrand α x| < ε := by
  have hev :
      ∀ᶠ A : ℝ in atTop,
        |∫ x in Set.Ioi A,
          1 / (1 + (x - localRadius α₀) ^ 2)| < ε := by
    have hnhds : Set.Ioo (-ε) ε ∈ nhds (0 : ℝ) :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [(shift_kernel_tail_tendsto α₀).eventually hnhds]
      with A hA
    exact abs_lt.mpr hA
  rcases (eventually_atTop.1 hev) with ⟨A₁, hA₁⟩
  let A₀ := max (max A₁ (localRadius α₀)) 0 + 1
  have hmax : 0 ≤ max (max A₁ (localRadius α₀)) 0 :=
    le_max_right _ _
  refine ⟨A₀, by dsimp [A₀]; linarith, ?_⟩
  intro A α hA hα
  have hA₁A : A₁ ≤ A := by
    dsimp [A₀] at hA
    linarith [le_max_left A₁ (localRadius α₀),
      le_max_left (max A₁ (localRadius α₀)) 0]
  have hRA : localRadius α₀ < A := by
    dsimp [A₀] at hA
    linarith [le_max_right A₁ (localRadius α₀),
      le_max_left (max A₁ (localRadius α₀)) 0]
  have hbound :
      ‖∫ x in Set.Ioi A, integrand α x‖ ≤
        ∫ x in Set.Ioi A,
          1 / (1 + (x - localRadius α₀) ^ 2) := by
    apply MeasureTheory.norm_integral_le_of_norm_le
      (μ := volume.restrict (Set.Ioi A))
      (integrable_shift_kernel α₀).integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs]
    exact gap1 α₀ x α (hRA.trans hx) hα
  rw [← Real.norm_eq_abs]
  exact lt_of_le_of_lt hbound
    (lt_of_le_of_lt (le_abs_self _)
      (hA₁ A hA₁A))

theorem gap7 (α₀ ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ A α : ℝ, A₀ < A →
        α ∈ Set.Ioo (α₀ - 1) (α₀ + 1) →
          |∫ x in Set.Ioi A, parameterDerivative α x| < ε := by
  have hehalf : 0 < ε / 2 := by linarith
  have hev :
      ∀ᶠ A : ℝ in atTop,
        |∫ x in Set.Ioi A,
          1 / (1 + (x - localRadius α₀) ^ 2)| < ε / 2 := by
    have hnhds : Set.Ioo (-(ε / 2)) (ε / 2) ∈ nhds (0 : ℝ) :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [(shift_kernel_tail_tendsto α₀).eventually hnhds]
      with A hA
    exact abs_lt.mpr hA
  rcases (eventually_atTop.1 hev) with ⟨A₁, hA₁⟩
  let A₀ := max (max A₁ (localRadius α₀)) 0 + 1
  have hmax : 0 ≤ max (max A₁ (localRadius α₀)) 0 :=
    le_max_right _ _
  refine ⟨A₀, by dsimp [A₀]; linarith, ?_⟩
  intro A α hA hα
  have hA₁A : A₁ ≤ A := by
    dsimp [A₀] at hA
    linarith [le_max_left A₁ (localRadius α₀),
      le_max_left (max A₁ (localRadius α₀)) 0]
  have hRA : localRadius α₀ < A := by
    dsimp [A₀] at hA
    linarith [le_max_right A₁ (localRadius α₀),
      le_max_left (max A₁ (localRadius α₀)) 0]
  have hmajor :
      Integrable
        (fun x : ℝ =>
          2 * (1 / (1 + (x - localRadius α₀) ^ 2))) :=
    (integrable_shift_kernel α₀).const_mul 2
  have hbound :
      ‖∫ x in Set.Ioi A, parameterDerivative α x‖ ≤
        ∫ x in Set.Ioi A,
          2 * (1 / (1 + (x - localRadius α₀) ^ 2)) := by
    apply MeasureTheory.norm_integral_le_of_norm_le
      (μ := volume.restrict (Set.Ioi A)) hmajor.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs]
    have hd := gap2 α₀ x α (hRA.trans hx) hα
    have hb := gap3 α₀ x α (hRA.trans hx) hα
    rw [parameterDerivative_eq_deriv α x, hd]
    simpa [div_eq_mul_inv] using hb
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ x in Set.Ioi A, parameterDerivative α x‖ ≤
        ∫ x in Set.Ioi A,
          2 * (1 / (1 + (x - localRadius α₀) ^ 2)) := hbound
    _ = 2 * ∫ x in Set.Ioi A,
          1 / (1 + (x - localRadius α₀) ^ 2) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ 2 * |∫ x in Set.Ioi A,
          1 / (1 + (x - localRadius α₀) ^ 2)| := by
      exact mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    _ < ε := by linarith [hA₁ A hA₁A]

private lemma hasDerivAt_F
    (α₀ α : ℝ) (hα : α ∈ Set.Ioo (α₀ - 1) (α₀ + 1)) :
    HasDerivAt F
      (∫ x in Set.Ioi (0 : ℝ), parameterDerivative α x) α := by
  let bound : ℝ → ℝ := fun x =>
    (4 * (1 + localRadius α₀ ^ 2)) * (1 + x ^ 2)⁻¹
  have hbound_int :
      Integrable bound
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
    exact
      (integrable_inv_one_add_sq.const_mul
        (4 * (1 + localRadius α₀ ^ 2))).integrableOn
  have hresult :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (F := fun a x : ℝ => integrand a x)
      (F' := fun a x : ℝ => parameterDerivative a x)
      (bound := bound)
      (s := Set.Ioo (α₀ - 1) (α₀ + 1))
      (isOpen_Ioo.mem_nhds hα)
      (by
        filter_upwards with a
        have hden_cont :
            Continuous (fun x : ℝ => 1 + (x + a) ^ 2) := by
          fun_prop
        exact
          (Real.continuous_cos.div hden_cont
            (fun x => by nlinarith [sq_nonneg (x + a)]))
            |>.aestronglyMeasurable)
      (integrableOn_integrand α₀ α hα)
      (by
        have hden_cont :
            Continuous
              (fun x : ℝ => (1 + (x + α) ^ 2) ^ 2) := by
          fun_prop
        have hnum_cont :
            Continuous
              (fun x : ℝ => -(2 * (x + α) * Real.cos x)) := by
          fun_prop
        exact
          (hnum_cont.div hden_cont
            (fun x => by
              have hp : 0 < 1 + (x + α) ^ 2 := by positivity
              exact (sq_pos_of_pos hp).ne'))
            |>.aestronglyMeasurable)
      (by
        filter_upwards with x
        intro a ha
        simpa only [bound, div_eq_mul_inv] using
          norm_parameterDerivative_le_global α₀ a x ha)
      hbound_int
      (by
        filter_upwards with x
        intro a ha
        exact hasDerivAt_integrand a x)
  simpa only [F] using hresult.2

theorem gap8 (α₀ : ℝ) :
    ContinuousOn F (Set.Ioo (α₀ - 1) (α₀ + 1)) := by
  intro α hα
  exact (hasDerivAt_F α₀ α hα).continuousAt.continuousWithinAt

theorem gap9 (α₀ : ℝ) :
    DifferentiableOn ℝ F (Set.Ioo (α₀ - 1) (α₀ + 1)) := by
  intro α hα
  exact (hasDerivAt_F α₀ α hα).differentiableAt.differentiableWithinAt

theorem gap10 :
    Continuous F := by
  rw [continuous_iff_continuousAt]
  intro α
  have hα : α ∈ Set.Ioo (α - 1) (α + 1) := by constructor <;> linarith
  exact (gap8 α).continuousAt
    (isOpen_Ioo.mem_nhds hα)

theorem gap11 :
    Differentiable ℝ F := by
  intro α
  have hα : α ∈ Set.Ioo (α - 1) (α + 1) := by constructor <;> linarith
  exact ((gap9 α) α hα).differentiableAt
    (isOpen_Ioo.mem_nhds hα)

theorem gap12 :
    Continuous F ∧ Differentiable ℝ F := by
  exact ⟨gap10, gap11⟩

end

end ProofGap.Exercise3787
