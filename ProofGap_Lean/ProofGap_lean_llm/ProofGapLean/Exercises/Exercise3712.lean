import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3712

noncomputable section

open scoped Interval

def kernelIntegral (y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, y / (x ^ 2 + y ^ 2)

def integralFunction (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, y * f x / (x ^ 2 + y ^ 2)

def minimumValue (f : ℝ → ℝ) : ℝ :=
  sInf (f '' Set.Icc (0 : ℝ) 1)

theorem gap1 (f : ℝ → ℝ) (y : ℝ) (hy : y ≠ 0)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun x => y * f x / (x ^ 2 + y ^ 2))
      (Set.Icc (0 : ℝ) 1) := by
  apply (continuousOn_const.mul hf).div
    ((continuousOn_id.pow 2).add continuousOn_const)
  intro x hx
  have hden : 0 < x ^ 2 + y ^ 2 := by
    have hy2 : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg x]
  exact ne_of_gt hden

theorem gap2 (f : ℝ → ℝ) (y : ℝ) (hy : y ≠ 0)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    ContinuousAt (integralFunction f) y := by
  unfold integralFunction
  change Filter.Tendsto
    (fun z : ℝ => ∫ x in (0 : ℝ)..1,
      z * f x / (x ^ 2 + z ^ 2))
    (nhds y)
    (nhds (∫ x in (0 : ℝ)..1,
      y * f x / (x ^ 2 + y ^ 2)))
  simp_rw [intervalIntegral.integral_of_le
    (by norm_num : (0 : ℝ) ≤ 1)]
  have hyabs : 0 < |y| := abs_pos.mpr hy
  have hevent : ∀ᶠ z : ℝ in nhds y,
      z ∈ Metric.ball y (|y| / 2) :=
    Metric.ball_mem_nhds y (by positivity)
  have hboundInt : MeasureTheory.Integrable
      (fun x : ℝ => (2 / |y|) * |f x|)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have hc : ContinuousOn
        (fun x : ℝ => (2 / |y|) * |f x|)
        (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.mul hf.abs
    have hu : ContinuousOn
        (fun x : ℝ => (2 / |y|) * |f x|)
        (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hc
    exact hu.intervalIntegrable.1
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun x : ℝ => (2 / |y|) * |f x|) ?_ ?_ hboundInt ?_
  · filter_upwards [hevent] with z hz
    have hzy : |z - y| < |y| / 2 := by
      simpa [Real.dist_eq] using hz
    have hrev : |y| - |z| ≤ |z - y| := by
      calc
        |y| - |z| ≤ |y - z| := abs_sub_abs_le_abs_sub y z
        _ = |z - y| := abs_sub_comm y z
    have hzabs : |y| / 2 < |z| := by linarith
    have hzpos : 0 < |z| := lt_trans (by positivity) hzabs
    have hz0 : z ≠ 0 := abs_pos.mp hzpos
    have hzcont : ContinuousOn
        (fun x : ℝ => z * f x / (x ^ 2 + z ^ 2))
        (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        (gap1 f z hz0 hf)
    exact hzcont.intervalIntegrable.1.aestronglyMeasurable
  · filter_upwards [hevent] with z hz
    apply Filter.Eventually.of_forall
    intro x
    have hzy : |z - y| < |y| / 2 := by
      simpa [Real.dist_eq] using hz
    have hrev : |y| - |z| ≤ |z - y| := by
      calc
        |y| - |z| ≤ |y - z| := abs_sub_abs_le_abs_sub y z
        _ = |z - y| := abs_sub_comm y z
    have hzabs : |y| / 2 < |z| := by linarith
    have hzpos : 0 < |z| := lt_trans (by positivity) hzabs
    have hz0 : z ≠ 0 := abs_pos.mp hzpos
    have hden : 0 < x ^ 2 + z ^ 2 := by
      have hz2 : 0 < z ^ 2 := by positivity
      nlinarith [sq_nonneg x]
    have hmul := mul_lt_mul_of_pos_right hzabs hzpos
    have hratio : |z| / (x ^ 2 + z ^ 2) ≤ 2 / |y| := by
      apply (div_le_div_iff₀ hden hyabs).2
      nlinarith [sq_abs z, sq_nonneg x]
    calc
      ‖z * f x / (x ^ 2 + z ^ 2)‖ =
          (|z| / (x ^ 2 + z ^ 2)) * |f x| := by
        rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hden]
        ring
      _ ≤ (2 / |y|) * |f x| :=
        mul_le_mul_of_nonneg_right hratio (abs_nonneg (f x))
  · apply Filter.Eventually.of_forall
    intro x
    have hcnum : ContinuousAt (fun z : ℝ => z * f x) y :=
      continuousAt_id.mul continuousAt_const
    have hcden : ContinuousAt (fun z : ℝ => x ^ 2 + z ^ 2) y :=
      continuousAt_const.add (continuousAt_id.pow 2)
    have hdeny : 0 < x ^ 2 + y ^ 2 := by
      have hy2 : 0 < y ^ 2 := by positivity
      nlinarith [sq_nonneg x]
    exact (hcnum.div hcden hdeny.ne').tendsto

theorem gap3 (f : ℝ → ℝ) :
    integralFunction f 0 = 0 := by
  simp [integralFunction]

theorem gap4 (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < f x) :
    0 < minimumValue f := by
  have hcompact : IsCompact (f '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hf
  have hne : (f '' Set.Icc (0 : ℝ) 1).Nonempty := by
    refine ⟨f 0, 0, ?_, rfl⟩
    norm_num
  have hmem : sInf (f '' Set.Icc (0 : ℝ) 1) ∈
      f '' Set.Icc (0 : ℝ) 1 :=
    hcompact.isClosed.csInf_mem hne hcompact.bddBelow
  rcases hmem with ⟨x, hx, hxmin⟩
  rw [minimumValue, ← hxmin]
  exact hpos x hx

theorem gap5 (f : ℝ → ℝ) (y : ℝ) (hy : 0 < y)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < f x) :
    minimumValue f * kernelIntegral y ≤ integralFunction f y := by
  have hcompact : IsCompact (f '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hf
  have hbounded : BddBelow (f '' Set.Icc (0 : ℝ) 1) := hcompact.bddBelow
  have hleft : ContinuousOn
      (fun x : ℝ => minimumValue f * (y / (x ^ 2 + y ^ 2)))
      (Set.Icc (0 : ℝ) 1) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (gap1 (fun _ : ℝ => minimumValue f) y hy.ne'
        (continuousOn_const : ContinuousOn (fun _ : ℝ => minimumValue f)
          (Set.Icc (0 : ℝ) 1)))
  have hright := gap1 f y hy.ne' hf
  have hleftInt : IntervalIntegrable
      (fun x : ℝ => minimumValue f * (y / (x ^ 2 + y ^ 2)))
      MeasureTheory.volume 0 1 := by
    have hu : ContinuousOn
        (fun x : ℝ => minimumValue f * (y / (x ^ 2 + y ^ 2)))
        (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hleft
    exact hu.intervalIntegrable
  have hrightInt : IntervalIntegrable
      (fun x : ℝ => y * f x / (x ^ 2 + y ^ 2))
      MeasureTheory.volume 0 1 := by
    have hu : ContinuousOn
        (fun x : ℝ => y * f x / (x ^ 2 + y ^ 2))
        (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hright
    exact hu.intervalIntegrable
  rw [kernelIntegral, integralFunction,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num) hleftInt hrightInt
  intro x hx
  have hmin : minimumValue f ≤ f x := by
    unfold minimumValue
    exact csInf_le hbounded ⟨x, hx, rfl⟩
  have hden : 0 < x ^ 2 + y ^ 2 := by positivity
  have hfactor : 0 ≤ y / (x ^ 2 + y ^ 2) :=
    (div_pos hy hden).le
  calc
    minimumValue f * (y / (x ^ 2 + y ^ 2))
        ≤ f x * (y / (x ^ 2 + y ^ 2)) :=
      mul_le_mul_of_nonneg_right hmin hfactor
    _ = y * f x / (x ^ 2 + y ^ 2) := by ring

theorem gap6 (y : ℝ) (hy : 0 < y) :
    kernelIntegral y = Real.arctan (1 / y) := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun t : ℝ => Real.arctan (t / y))
        (y / (x ^ 2 + y ^ 2)) x := by
    intro x
    convert (Real.hasDerivAt_arctan (x / y)).comp x
      ((hasDerivAt_id x).div_const y) using 1
    field_simp [ne_of_gt hy]
    <;> ring
  have hcontIcc : ContinuousOn
      (fun x : ℝ => y / (x ^ 2 + y ^ 2))
      (Set.Icc (0 : ℝ) 1) := by
    simpa using
      (gap1 (fun _ : ℝ => (1 : ℝ)) y hy.ne'
        (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ))
          (Set.Icc (0 : ℝ) 1)))
  have hcont : ContinuousOn
      (fun x : ℝ => y / (x ^ 2 + y ^ 2))
      (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcontIcc
  have hftc :
      (∫ x in (0 : ℝ)..1, y / (x ^ 2 + y ^ 2)) =
        Real.arctan (1 / y) - Real.arctan (0 / y) :=
    intervalIntegral.integral_deriv_eq_sub'
      (a := (0 : ℝ)) (b := 1)
      (fun t : ℝ => Real.arctan (t / y))
      (funext fun x => (hderiv x).deriv)
      (fun x hx => (hderiv x).differentiableAt)
      hcont
  calc
    kernelIntegral y = ∫ x in (0 : ℝ)..1, y / (x ^ 2 + y ^ 2) := rfl
    _ = Real.arctan (1 / y) - Real.arctan (0 / y) := hftc
    _ = Real.arctan (1 / y) := by simp

theorem gap7 (f : ℝ → ℝ) (y : ℝ) (hy : 0 < y)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < f x) :
    minimumValue f * Real.arctan (1 / y) ≤ integralFunction f y := by
  have h := gap5 f y hy hf hpos
  rw [gap6 y hy] at h
  exact h

theorem gap8 :
    Filter.Tendsto (fun y : ℝ => Real.arctan (1 / y))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) := by
  have h := Real.tendsto_arctan_atTop.comp tendsto_inv_nhdsGT_zero
  have h' := h.mono_right inf_le_left
  simpa [one_div, Function.comp_def] using h'

theorem gap9 (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < f x)
    (y : ℕ → ℝ) (hy : ∀ n, 0 < y n)
    (hy0 : Filter.Tendsto y Filter.atTop (nhds 0))
    (L : ℝ)
    (hL : Filter.Tendsto (fun n => integralFunction f (y n))
      Filter.atTop (nhds L)) :
    minimumValue f * Real.pi / 2 ≤ L := by
  have hyWithin : Filter.Tendsto y Filter.atTop
      (nhdsWithin 0 (Set.Ioi 0)) := by
    exact tendsto_nhdsWithin_iff.2
      ⟨hy0, Filter.Eventually.of_forall (fun n => hy n)⟩
  have hatan : Filter.Tendsto
      (fun n => Real.arctan (1 / y n)) Filter.atTop
      (nhds (Real.pi / 2)) := gap8.comp hyWithin
  have hleft : Filter.Tendsto
      (fun n => minimumValue f * Real.arctan (1 / y n)) Filter.atTop
      (nhds (minimumValue f * (Real.pi / 2))) :=
    tendsto_const_nhds.mul hatan
  have hdiff : Filter.Tendsto
      (fun n => integralFunction f (y n) -
        minimumValue f * Real.arctan (1 / y n)) Filter.atTop
      (nhds (L - minimumValue f * (Real.pi / 2))) :=
    hL.sub hleft
  have hnonneg : 0 ≤ L - minimumValue f * (Real.pi / 2) := by
    exact isClosed_Ici.mem_of_tendsto hdiff
      (Filter.Eventually.of_forall (fun n =>
        sub_nonneg.mpr (gap7 f (y n) (hy n) hf hpos)))
  calc
    minimumValue f * Real.pi / 2 =
        minimumValue f * (Real.pi / 2) := by ring
    _ ≤ L := sub_nonneg.mp hnonneg

theorem gap10 (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < f x) :
    0 < minimumValue f * Real.pi / 2 := by
  exact div_pos (mul_pos (gap4 f hf hpos) Real.pi_pos)
    (by norm_num)

theorem gap11 (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < f x)
    (y : ℕ → ℝ) (hy : ∀ n, 0 < y n)
    (hy0 : Filter.Tendsto y Filter.atTop (nhds 0))
    (L : ℝ)
    (hL : Filter.Tendsto (fun n => integralFunction f (y n))
      Filter.atTop (nhds L)) :
    0 < L := by
  exact lt_of_lt_of_le (gap10 f hf hpos)
    (gap9 f hf hpos y hy hy0 L hL)

theorem gap12 (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < f x) :
    ¬ ContinuousAt (integralFunction f) 0 := by
  intro hc
  have hF : Filter.Tendsto (integralFunction f)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (integralFunction f 0)) :=
    hc.mono_left inf_le_left
  have hleft : Filter.Tendsto
      (fun y : ℝ => minimumValue f * Real.arctan (1 / y))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (minimumValue f * (Real.pi / 2))) :=
    tendsto_const_nhds.mul gap8
  have hdiff : Filter.Tendsto
      (fun y : ℝ => integralFunction f y -
        minimumValue f * Real.arctan (1 / y))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (integralFunction f 0 -
        minimumValue f * (Real.pi / 2))) :=
    hF.sub hleft
  have hevent : ∀ᶠ y in nhdsWithin 0 (Set.Ioi 0),
      0 ≤ integralFunction f y -
        minimumValue f * Real.arctan (1 / y) :=
    Filter.mem_of_superset self_mem_nhdsWithin (fun y hy =>
      sub_nonneg.mpr (gap7 f y hy hf hpos))
  have hnonneg : 0 ≤ integralFunction f 0 -
      minimumValue f * (Real.pi / 2) :=
    isClosed_Ici.mem_of_tendsto hdiff hevent
  have hpositive := gap10 f hf hpos
  rw [gap3 f] at hnonneg
  linarith

theorem gap13 (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < f x) :
    ¬ ContinuousAt (integralFunction f) 0 := by
  exact gap12 f hf hpos

end

end ProofGap.Exercise3712
