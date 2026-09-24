import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3760

noncomputable section

open Filter MeasureTheory
open scoped Interval

def dampedSinc (α x : ℝ) : ℝ :=
  Real.sin x / x * Real.exp (-(α * x))

def weight (α x : ℝ) : ℝ :=
  Real.exp (-(α * x)) / x

def primitive (α x : ℝ) : ℝ :=
  -((α * Real.sin x + Real.cos x) / (1 + α ^ 2)) *
    Real.exp (-(α * x))

def HasRemovableRightSingularity (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto f (nhdsWithin x (Set.Ioi x)) (nhds L)

private theorem abs_add (a b : ℝ) : |a + b| ≤ |a| + |b| :=
  abs_add_le a b

theorem gap1 (α : ℝ) :
    Tendsto (dampedSinc α) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hsinc : Tendsto Real.sinc (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h0 : Tendsto Real.sinc (nhds (0 : ℝ)) (nhds (Real.sinc 0)) :=
      Real.continuous_sinc.continuousAt
    have hright :
        Tendsto Real.sinc (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sinc 0)) :=
      h0.mono_left inf_le_left
    simpa [Real.sinc] using hright
  have heq :
      Real.sinc =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun x : ℝ => Real.sin x / x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    simp [Real.sinc, hx.ne']
  have hsin :
      Tendsto (fun x : ℝ => Real.sin x / x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
    hsinc.congr' heq
  have hexp :
      Tendsto (fun x : ℝ => Real.exp (-(α * x)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hc : Continuous (fun x : ℝ => Real.exp (-(α * x))) :=
      Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)
    have h0 :
        Tendsto (fun x : ℝ => Real.exp (-(α * x))) (nhds 0)
          (nhds (Real.exp (-(α * 0)))) :=
      hc.continuousAt
    have hright :
        Tendsto (fun x : ℝ => Real.exp (-(α * x)))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp (-(α * 0)))) :=
      h0.mono_left inf_le_left
    simpa using hright
  simpa [dampedSinc] using hsin.mul hexp

theorem gap2 (α : ℝ) :
    HasRemovableRightSingularity (dampedSinc α) 0 := by
  refine ⟨1, ?_⟩
  exact gap1 α

theorem gap3 (A : ℝ) :
    |∫ x in (0 : ℝ)..A, Real.sin x| = |1 - Real.cos A| := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => 1 - Real.cos y) (Real.sin x) x := by
    intro x
    convert (Real.hasDerivAt_cos x).const_sub 1 using 1 <;> ring
  have hint :
      (∫ x in (0 : ℝ)..A, Real.sin x) =
        (1 - Real.cos A) - (1 - Real.cos 0) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x) (Real.continuous_sin.intervalIntegrable 0 A)
  rw [hint]
  norm_num

theorem gap4 (A : ℝ) :
    |1 - Real.cos A| ≤ 2 := by
  rw [abs_le]
  constructor <;> nlinarith [Real.neg_one_le_cos A, Real.cos_le_one A]

theorem gap5 (A : ℝ) :
    |∫ x in (0 : ℝ)..A, Real.sin x| ≤ 2 := by
  rw [gap3 A]
  exact gap4 A

theorem gap6 (α : ℝ) (hα : 0 ≤ α) :
    AntitoneOn (weight α) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have he : Real.exp (-(α * y)) ≤ Real.exp (-(α * x)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  apply (div_le_div_iff₀ hy hx).2
  calc
    Real.exp (-(α * y)) * x ≤ Real.exp (-(α * x)) * x :=
      mul_le_mul_of_nonneg_right he (le_of_lt hx)
    _ ≤ Real.exp (-(α * x)) * y :=
      mul_le_mul_of_nonneg_left hxy (le_of_lt (Real.exp_pos _))

theorem gap7 (α x : ℝ) (hx : 0 < x) :
    0 < weight α x := by
  exact div_pos (Real.exp_pos _) hx

theorem gap8 (α x : ℝ) (hα : 0 ≤ α) (hx : 0 < x) :
    weight α x ≤ 1 / x := by
  have he : Real.exp (-(α * x)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  exact div_le_div_of_nonneg_right he (le_of_lt hx)

theorem gap9 (x : ℝ) (hx : 0 < x) :
    0 < 1 / x := by
  exact one_div_pos.mpr hx

theorem gap10 (α : ℝ) (hα : 0 ≤ α) :
    Tendsto (weight α) atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds tendsto_inv_atTop_zero ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact le_of_lt (gap7 α x hx)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simpa [one_div] using gap8 α x hα hx

theorem gap12 (A A₁ α : ℝ) (hA : 0 < A) (hAA₁ : A < A₁)
    (hα : 0 ≤ α) :
    ∃ ξ ∈ Set.Icc A A₁,
      |∫ x in A..A₁, dampedSinc α x| =
        |(1 / A) * ∫ x in A..ξ,
          Real.exp (-(α * x)) * Real.sin x| := by
  let q : ℝ → ℝ := fun x => Real.exp (-(α * x)) * Real.sin x
  let G : ℝ → ℝ := fun t => ∫ x in A..t, q x
  have hq : Continuous q := by
    dsimp [q]
    fun_prop
  have hG : Continuous G := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hq.integral_hasStrictDerivAt A x).hasDerivAt.continuousAt
  have hrecip_deriv :
      ∀ x ∈ Set.uIcc A A₁,
        HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le hAA₁.le] at hx
    have hx0 : x ≠ 0 := ne_of_gt (hA.trans_le hx.1)
    convert (hasDerivAt_const x 1).div (hasDerivAt_id x) hx0 using 1
    simp only [id_eq]
    field_simp [hx0]
    ring
  have hG_deriv :
      ∀ x ∈ Set.uIcc A A₁, HasDerivAt G (q x) x := by
    intro x _
    exact (hq.integral_hasStrictDerivAt A x).hasDerivAt
  have hrneg_int :
      IntervalIntegrable (fun x : ℝ => -1 / x ^ 2) volume A A₁ := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hAA₁.le] at hx
    have hx0 : x ≠ 0 := ne_of_gt (hA.trans_le hx.1)
    exact
      (continuousAt_const.div (continuousAt_id.pow 2)
        (pow_ne_zero 2 hx0)).continuousWithinAt
  have hq_int : IntervalIntegrable q volume A A₁ :=
    hq.intervalIntegrable A A₁
  have hip :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      hrecip_deriv hG_deriv hrneg_int hq_int
  have hr_int :
      IntervalIntegrable (fun x : ℝ => 1 / x ^ 2) volume A A₁ := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hAA₁.le] at hx
    have hx0 : x ≠ 0 := ne_of_gt (hA.trans_le hx.1)
    exact
      (continuousAt_const.div (continuousAt_id.pow 2)
        (pow_ne_zero 2 hx0)).continuousWithinAt
  have hr_nonneg :
      ∀ x ∈ Set.uIoc A A₁, 0 ≤ (1 / x ^ 2 : ℝ) := by
    intro x _
    positivity
  obtain ⟨d, hd, hmean⟩ :=
    exists_eq_const_mul_intervalIntegral_of_nonneg
      hG.continuousOn hr_int hr_nonneg
  rw [Set.uIcc_of_le hAA₁.le] at hd
  have hr_value :
      (∫ x in A..A₁, (1 / x ^ 2 : ℝ)) = 1 / A - 1 / A₁ := by
    have hderiv :
        ∀ x ∈ Set.uIcc A A₁,
          HasDerivAt (fun y : ℝ => -1 / y) (1 / x ^ 2) x := by
      intro x hx
      rw [Set.uIcc_of_le hAA₁.le] at hx
      have hx0 : x ≠ 0 := ne_of_gt (hA.trans_le hx.1)
      convert
        (hasDerivAt_const x (-1)).div (hasDerivAt_id x) hx0 using 1
      simp only [id_eq]
      field_simp [hx0]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hr_int]
    ring
  have hG_A : G A = 0 := by simp [G]
  have hparts :
      (∫ x in A..A₁, (1 / x) * q x) =
        (1 / A₁) * G A₁ + G d * (1 / A - 1 / A₁) := by
    rw [hG_A, mul_zero, sub_zero] at hip
    have hneg :
        -(∫ x in A..A₁, (-1 / x ^ 2) * G x) =
          ∫ x in A..A₁, G x * (1 / x ^ 2) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x _
      ring
    calc
      (∫ x in A..A₁, (1 / x) * q x) =
          (1 / A₁) * G A₁ -
            ∫ x in A..A₁, (-1 / x ^ 2) * G x := hip
      _ = (1 / A₁) * G A₁ +
          ∫ x in A..A₁, G x * (1 / x ^ 2) := by
        rw [sub_eq_add_neg, hneg]
      _ = (1 / A₁) * G A₁ + G d * (1 / A - 1 / A₁) := by
        rw [hmean, hr_value]
  have hA₁ : 0 < A₁ := hA.trans hAA₁
  let lam : ℝ := A / A₁
  have hlam0 : 0 ≤ lam := by
    dsimp [lam]
    positivity
  have hlam1 : lam ≤ 1 := by
    dsimp [lam]
    exact (div_le_one hA₁).2 hAA₁.le
  let T : ℝ := A * (∫ x in A..A₁, (1 / x) * q x)
  have hT :
      T = lam * G A₁ + (1 - lam) * G d := by
    dsimp [T, lam]
    rw [hparts]
    field_simp [ne_of_gt hA, ne_of_gt hA₁]
  have hT_mem : T ∈ Set.uIcc (G d) (G A₁) := by
    rw [Set.mem_uIcc]
    rw [hT]
    rcases le_total (G d) (G A₁) with h | h
    · exact Or.inl ⟨by nlinarith, by nlinarith⟩
    · exact Or.inr ⟨by nlinarith, by nlinarith⟩
  have hdA₁ : d ≤ A₁ := hd.2
  have hT_image :
      T ∈ G '' Set.Icc d A₁ := by
    have him :=
      intermediate_value_uIcc (a := d) (b := A₁) hG.continuousOn hT_mem
    rwa [Set.uIcc_of_le hdA₁] at him
  rcases hT_image with ⟨ξ, hξd, hξeq⟩
  refine ⟨ξ, ⟨hd.1.trans hξd.1, hξd.2⟩, ?_⟩
  have heq :
      (∫ x in A..A₁, (1 / x) * q x) = (1 / A) * G ξ := by
    have hAne : A ≠ 0 := ne_of_gt hA
    dsimp [T] at hξeq
    rw [hξeq]
    field_simp [hAne]
  have hdamped :
      (∫ x in A..A₁, dampedSinc α x) =
        ∫ x in A..A₁, (1 / x) * q x := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [dampedSinc, q]
    ring
  rw [hdamped, heq]

theorem gap13 (A A₁ : ℝ) (hA : 0 < A) (hAA₁ : A < A₁) :
    ∃ ξ : ℝ, A ≤ ξ := by
  exact ⟨A, le_rfl⟩

theorem gap14 (A A₁ : ℝ) (hA : 0 < A) (hAA₁ : A < A₁) :
    ∃ ξ : ℝ, ξ ≤ A₁ := by
  exact ⟨A₁, le_rfl⟩

theorem gap15 (A A₁ : ℝ) (hA : 0 < A) (hAA₁ : A < A₁) :
    A ≤ A₁ := by
  exact le_of_lt hAA₁

theorem gap16 (α x : ℝ) (hα : 0 ≤ α) (hx : 0 ≤ x) :
    |primitive α x| ≤ (α + 1) / (1 + α ^ 2) := by
  have hden : 0 < 1 + α ^ 2 := by positivity
  have hnum : |α * Real.sin x + Real.cos x| ≤ α + 1 := by
    calc
      |α * Real.sin x + Real.cos x| ≤
          |α * Real.sin x| + |Real.cos x| := abs_add _ _
      _ = α * |Real.sin x| + |Real.cos x| := by
        rw [abs_mul, abs_of_nonneg hα]
      _ ≤ α * 1 + 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one x) hα)
          (Real.abs_cos_le_one x)
      _ = α + 1 := by ring
  have hexp : Real.exp (-(α * x)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [primitive, abs_mul, abs_neg, abs_div,
    abs_of_pos hden, abs_of_pos (Real.exp_pos _)]
  calc
    |α * Real.sin x + Real.cos x| / (1 + α ^ 2) *
          Real.exp (-(α * x)) ≤
        ((α + 1) / (1 + α ^ 2)) * Real.exp (-(α * x)) := by
      apply mul_le_mul_of_nonneg_right
      · exact div_le_div_of_nonneg_right hnum (le_of_lt hden)
      · exact le_of_lt (Real.exp_pos _)
    _ ≤ ((α + 1) / (1 + α ^ 2)) * 1 := by
      apply mul_le_mul_of_nonneg_left hexp
      exact div_nonneg (by nlinarith) (le_of_lt hden)
    _ = (α + 1) / (1 + α ^ 2) := by ring

theorem gap17 (α : ℝ) :
    (α + 1) / (1 + α ^ 2) < 2 := by
  have hden : 0 < 1 + α ^ 2 := by positivity
  apply (div_lt_iff₀ hden).2
  nlinarith [sq_nonneg (α - (1 / 4 : ℝ))]

theorem gap18 (α x : ℝ) (hα : 0 ≤ α) (hx : 0 ≤ x) :
    |primitive α x| < 2 := by
  exact lt_of_le_of_lt (gap16 α x hα hx) (gap17 α)

theorem gap19 (A A₁ α : ℝ) (hA : 0 < A) (hAA₁ : A < A₁)
    (hα : 0 ≤ α) :
    |∫ x in A..A₁, dampedSinc α x| < 4 / A := by
  obtain ⟨ξ, hξ, hrep⟩ := gap12 A A₁ α hA hAA₁ hα
  have hden : 0 < 1 + α ^ 2 := by positivity
  have hderiv : ∀ y : ℝ,
      HasDerivAt (primitive α)
        (Real.exp (-(α * y)) * Real.sin y) y := by
    intro y
    have hnum : HasDerivAt
        (fun z : ℝ => α * Real.sin z + Real.cos z)
        (α * Real.cos y - Real.sin y) y := by
      convert (Real.hasDerivAt_sin y).const_mul α |>.add
        (Real.hasDerivAt_cos y) using 1 <;> ring
    have hu : HasDerivAt
        (fun z : ℝ => -((α * Real.sin z + Real.cos z) / (1 + α ^ 2)))
        (-((α * Real.cos y - Real.sin y) / (1 + α ^ 2))) y :=
      (hnum.div_const (1 + α ^ 2)).neg
    have hv : HasDerivAt
        (fun z : ℝ => Real.exp (-(α * z)))
        (-α * Real.exp (-(α * y))) y := by
      convert (Real.hasDerivAt_exp (-(α * y))).comp y
        (((hasDerivAt_id y).const_mul α).neg) using 1 <;> ring
    convert hu.mul hv using 1
    field_simp [ne_of_gt hden] <;> ring
  have hint :
      (∫ x in A..ξ, Real.exp (-(α * x)) * Real.sin x) =
        primitive α ξ - primitive α A := by
    have hg : IntervalIntegrable
        (fun x : ℝ => Real.exp (-(α * x)) * Real.sin x) volume A ξ := by
      apply Continuous.intervalIntegrable
      exact (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).neg)).mul Real.continuous_sin
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => hderiv y) hg
  have hinner :
      |∫ x in A..ξ, Real.exp (-(α * x)) * Real.sin x| < 4 := by
    rw [hint]
    calc
      |primitive α ξ - primitive α A| ≤
          |primitive α ξ| + |primitive α A| := abs_sub _ _
      _ < 2 + 2 := add_lt_add
        (gap18 α ξ hα (le_trans (le_of_lt hA) hξ.1))
        (gap18 α A hα (le_of_lt hA))
      _ = 4 := by norm_num
  rw [hrep, abs_mul, abs_of_pos (gap9 A hA)]
  have hpos : 0 < 1 / A := gap9 A hA
  calc
    (1 / A) * |∫ x in A..ξ, Real.exp (-(α * x)) * Real.sin x| <
        (1 / A) * 4 := mul_lt_mul_of_pos_left hinner hpos
    _ = 4 / A := by ring

theorem gap11 (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ A A₁ α : ℝ, A₀ < A → A < A₁ → 0 ≤ α →
        |∫ x in A..A₁, dampedSinc α x| < ε := by
  refine ⟨4 / ε, div_pos (by norm_num) hε, ?_⟩
  intro A A₁ α hA₀ hAA₁ hα
  have hA : 0 < A := lt_trans (div_pos (by norm_num) hε) hA₀
  have hbound := gap19 A A₁ α hA hAA₁ hα
  have hratio : 4 / A < ε := by
    apply (div_lt_iff₀ hA).2
    have hcross := (div_lt_iff₀ hε).1 hA₀
    nlinarith
  exact hbound.trans hratio

theorem gap20 (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ A A₁ α : ℝ, A₀ < A → A < A₁ → 0 ≤ α →
        |∫ x in A..A₁, dampedSinc α x| < ε := by
  exact gap11 ε hε

end

end ProofGap.Exercise3760
