import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace ProofGap.Exercise1436

noncomputable section

def y (x : ℝ) : ℝ := x * Real.cbrt (x - 1)
def Approx (a b ε : ℝ) : Prop := |a - b| < ε

private theorem cbrt_cubed_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
    (Real.cbrt x) ^ 3 = x := by
  unfold Real.cbrt
  rw [← Real.rpow_natCast]
  calc
    (x ^ (1 / 3 : ℝ)) ^ (3 : ℝ) =
        x ^ ((1 / 3 : ℝ) * 3) := (Real.rpow_mul hx _ _).symm
    _ = x := by norm_num

private theorem cbrt_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < Real.cbrt x := by
  unfold Real.cbrt
  exact Real.rpow_pos_of_pos hx _

private theorem cbrt_pos_of_neg {x : ℝ} (hx : x < 0) :
    0 < Real.cbrt x := by
  unfold Real.cbrt
  change 0 < x ^ (1 / 3 : ℝ)
  rw [Real.rpow_def_of_neg hx]
  rw [show (1 / 3 : ℝ) * Real.pi =
    Real.pi / 3 by ring, Real.cos_pi_div_three]
  positivity

private theorem cbrt_nonneg (x : ℝ) : 0 ≤ Real.cbrt x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · exact (cbrt_pos_of_neg hx).le
  · subst x
    norm_num [Real.cbrt]
  · exact (cbrt_pos_of_pos hx).le

private theorem rpow_third_sub_one_eq {x : ℝ} (hx : 0 < x) :
    x ^ ((1 / 3 : ℝ) - 1) = 1 / (Real.cbrt x) ^ 2 := by
  have hcpos := cbrt_pos_of_pos hx
  have hcubed := cbrt_cubed_of_nonneg x hx.le
  rw [Real.rpow_sub hx, Real.rpow_one]
  change Real.cbrt x / x = 1 / (Real.cbrt x) ^ 2
  field_simp [hcpos.ne']
  nlinarith [hcubed]

private theorem cbrt_neg_of_pos {u : ℝ} (hu : 0 < u) :
    Real.cbrt (-u) = (1 / 2 : ℝ) * Real.cbrt u := by
  unfold Real.cbrt
  change (-u) ^ (1 / 3 : ℝ) =
    (1 / 2 : ℝ) * u ^ (1 / 3 : ℝ)
  rw [Real.rpow_def_of_neg (by linarith), Real.rpow_def_of_pos hu,
    Real.log_neg_eq_log]
  rw [show (1 / 3 : ℝ) * Real.pi =
    Real.pi / 3 by ring, Real.cos_pi_div_three]
  ring

private theorem rpow_neg_third_sub_one {u : ℝ} (hu : 0 < u) :
    (-u) ^ ((1 / 3 : ℝ) - 1) =
      -(1 / 2 : ℝ) * u ^ ((1 / 3 : ℝ) - 1) := by
  rw [Real.rpow_def_of_neg (by linarith), Real.rpow_def_of_pos hu,
    Real.log_neg_eq_log]
  have hcos :
      Real.cos (((1 / 3 : ℝ) - 1) * Real.pi) = -1 / 2 := by
    rw [show ((1 / 3 : ℝ) - 1) * Real.pi =
        -(2 * Real.pi / 3) by ring, Real.cos_neg]
    rw [show 2 * Real.pi / 3 =
        Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
    norm_num
  rw [hcos]
  ring

private theorem deriv_y_raw (x : ℝ) (hx : x ≠ 1) :
    deriv y x =
      Real.cbrt (x - 1) +
        x * ((1 / 3 : ℝ) * (x - 1) ^ ((1 / 3 : ℝ) - 1)) := by
  have hsub : HasDerivAt (fun z : ℝ => z - 1) 1 x :=
    (hasDerivAt_id x).sub_const 1
  have hroot :
      HasDerivAt (fun z : ℝ => (z - 1) ^ (1 / 3 : ℝ))
        ((1 / 3 : ℝ) * (x - 1) ^ ((1 / 3 : ℝ) - 1)) x := by
    simpa using hsub.rpow_const (Or.inl (sub_ne_zero.mpr hx))
  unfold y Real.cbrt
  convert ((hasDerivAt_id x).mul hroot).deriv using 1 <;>
    norm_num <;> ring

private theorem deriv_y_of_lt_one {x : ℝ} (hx : x < 1) :
    deriv y x =
      (3 - 4 * x) /
        (6 * (Real.cbrt (1 - x)) ^ 2) := by
  have hu : 0 < 1 - x := by linarith
  have hc := cbrt_pos_of_pos hu
  have hc3 := cbrt_cubed_of_nonneg (1 - x) hu.le
  rw [deriv_y_raw x (by linarith)]
  rw [show x - 1 = -(1 - x) by ring, cbrt_neg_of_pos hu,
    rpow_neg_third_sub_one hu, rpow_third_sub_one_eq hu]
  field_simp [hc.ne']
  nlinarith [hc3]

private theorem deriv_y_zero_pos : 0 < deriv y 0 := by
  rw [deriv_y_of_lt_one (by norm_num)]
  exact div_pos (by norm_num)
    (mul_pos (by norm_num)
      (sq_pos_of_pos (cbrt_pos_of_pos (by norm_num))))

private theorem deriv_y_seven_eighth_neg :
    deriv y (7 / 8) < 0 := by
  rw [deriv_y_of_lt_one (by norm_num)]
  exact div_neg_of_neg_of_pos (by norm_num)
    (mul_pos (by norm_num)
      (sq_pos_of_pos (cbrt_pos_of_pos (by norm_num))))

private theorem one_is_local_min : IsLocalMin y 1 := by
  have hone : y 1 = 0 := by
    norm_num [y, Real.cbrt]
  change ∀ᶠ x in nhds (1 : ℝ), y 1 ≤ y x
  filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
  change (0 : ℝ) < x at hx
  rw [hone]
  unfold y
  exact mul_nonneg hx.le (cbrt_nonneg (x - 1))

theorem gap1 (x : ℝ) (hx : x ≠ 1) (hgt : 1 < x) :
    deriv y x = (4 * x - 3) / (3 * (Real.cbrt (x - 1)) ^ 2) := by
  have hu : 0 < x - 1 := sub_pos.mpr hgt
  have hc := cbrt_pos_of_pos hu
  have hc3 := cbrt_cubed_of_nonneg (x - 1) hu.le
  rw [deriv_y_raw x hx, rpow_third_sub_one_eq hu]
  field_simp [hc.ne']
  nlinarith [hc3]

theorem gap2 : deriv y (3 / 4) = 0 := by
  rw [deriv_y_of_lt_one (by norm_num)]
  norm_num

theorem gap3 (x : ℝ) (hx : x < 3 / 4) : 0 < deriv y x := by
  rw [deriv_y_of_lt_one (by linarith)]
  exact div_pos (by linarith)
    (mul_pos (by norm_num)
      (sq_pos_of_pos (cbrt_pos_of_pos (by linarith))))

theorem gap4 (x : ℝ) (h₁ : 3 / 4 < x) (h₂ : x < 1) :
    deriv y x < 0 := by
  rw [deriv_y_of_lt_one h₂]
  exact div_neg_of_neg_of_pos (by linarith)
    (mul_pos (by norm_num)
      (sq_pos_of_pos (cbrt_pos_of_pos (by linarith))))

theorem gap5 : IsLocalMax y (3 / 4) := by
  have hcont : Continuous y := by
    unfold y Real.cbrt
    exact continuous_id.mul
      ((continuous_id.sub continuous_const).rpow_const
        (fun _ => Or.inr (by norm_num)))
  apply isLocalMax_of_deriv_Ioo
    (a := (0 : ℝ)) (b := (3 / 4 : ℝ)) (c := (1 : ℝ))
    (by norm_num) (by norm_num) hcont.continuousAt
  · intro x hx
    exact (differentiableAt_of_deriv_ne_zero
      (gap3 x hx.2).ne').differentiableWithinAt
  · intro x hx
    exact (differentiableAt_of_deriv_ne_zero
      (gap4 x hx.1 hx.2).ne).differentiableWithinAt
  · intro x hx
    exact le_of_lt (gap3 x hx.2)
  · intro x hx
    exact le_of_lt (gap4 x hx.1 hx.2)

theorem gap6 : y (3 / 4) = (3 / 16) * Real.cbrt 2 := by
  have hquarter : Real.cbrt (1 / 4) = (1 / 2) * Real.cbrt 2 := by
    have hq3 : (Real.cbrt (1 / 4)) ^ 3 = (1 / 4 : ℝ) :=
      cbrt_cubed_of_nonneg (1 / 4) (by norm_num)
    have h23 : (Real.cbrt 2) ^ 3 = (2 : ℝ) :=
      cbrt_cubed_of_nonneg 2 (by norm_num)
    apply (show Odd 3 by exact ⟨1, rfl⟩).pow_injective
    change (Real.cbrt (1 / 4)) ^ 3 =
      ((1 / 2 : ℝ) * Real.cbrt 2) ^ 3
    rw [hq3, mul_pow, h23]
    norm_num
  unfold y
  rw [show (3 / 4 : ℝ) - 1 = -(1 / 4) by norm_num]
  change (3 / 4 : ℝ) * Real.cbrt (-(1 / 4)) =
    (3 / 16) * Real.cbrt 2
  rw [cbrt_neg_of_pos (by norm_num), hquarter]
  ring

theorem gap7 :
    Approx ((3 / 16) * Real.cbrt 2) 0.236 0.01 := by
  have ht3 : (Real.cbrt 2) ^ 3 = (2 : ℝ) :=
    cbrt_cubed_of_nonneg 2 (by norm_num)
  have htpos : 0 < Real.cbrt 2 :=
    cbrt_pos_of_pos (by norm_num)
  have hl : (1.25 : ℝ) < Real.cbrt 2 := by
    apply lt_of_pow_lt_pow_left₀ 3 htpos.le
    rw [ht3]
    norm_num
  have hu : Real.cbrt 2 < (1.27 : ℝ) := by
    apply lt_of_pow_lt_pow_left₀ 3 (by norm_num)
    rw [ht3]
    norm_num
  unfold Approx
  rw [abs_lt]
  constructor <;> norm_num at * <;> linarith

theorem gap8 :
    Filter.Tendsto (deriv y) (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop := by
  have hsub : Filter.Tendsto (fun x : ℝ => x - 1)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun x : ℝ => x - 1) 1 := by fun_prop
      have hc' : Filter.Tendsto (fun x : ℝ => x - 1)
          (nhds (1 : ℝ)) (nhds (0 : ℝ)) := by
        convert hc.tendsto using 1 <;> norm_num
      exact hc'.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_mem_nhdsWithin] with x hx
      change (1 : ℝ) < x at hx
      exact sub_pos.mpr hx
  have hpow : Filter.Tendsto (fun x : ℝ => (x - 1) ^ (-(2 / 3 : ℝ)))
      (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (by norm_num)).comp hsub
  have hcoef : Filter.Tendsto (fun x : ℝ => (4 * x - 3) / 3)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 / 3 : ℝ)) := by
    have hc : ContinuousAt (fun x : ℝ => (4 * x - 3) / 3) 1 := by fun_prop
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> norm_num
  have hlim := hcoef.pos_mul_atTop (by norm_num : (0 : ℝ) < 1 / 3) hpow
  apply hlim.congr'
  filter_upwards [eventually_mem_nhdsWithin] with x hx
  change (1 : ℝ) < x at hx
  have hu : 0 < x - 1 := sub_pos.mpr hx
  rw [gap1 x (by linarith) hx]
  unfold Real.cbrt
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul_natCast hu.le (1 / 3 : ℝ) 2]
  rw [show -(2 / 3 : ℝ) = -((1 / 3 : ℝ) * 2) by ring,
    Real.rpow_neg hu.le]
  field_simp [(Real.rpow_pos_of_pos hu ((1 / 3 : ℝ) * 2)).ne']
  ring

theorem gap9 :
    ∃ ε > 0, ∀ x ∈ Set.Ioo 1 (1 + ε), 0 < deriv y x := by
  refine ⟨1, by norm_num, ?_⟩
  intro x hx
  rw [gap1 x (ne_of_gt hx.1) hx.1]
  exact div_pos (by linarith [hx.1])
    (mul_pos (by norm_num)
      (sq_pos_of_pos (cbrt_pos_of_pos (by linarith [hx.1]))))

theorem gap10 : ¬ IsLocalMax y 1 := by
  have hone : y 1 = 0 := by
    norm_num [y, Real.cbrt]
  intro hmax
  change {z : ℝ | y z ≤ y 1} ∈ nhds (1 : ℝ) at hmax
  rcases Metric.mem_nhds_iff.mp hmax with ⟨ε, hε, hball⟩
  let d : ℝ := min (ε / 2) (1 / 2)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (by linarith) (by norm_num)
  have hdε : d < ε :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hdball : 1 + d ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [abs_of_pos hd] using hdε
  have hle : y (1 + d) ≤ y 1 := hball hdball
  have hpos : 0 < y (1 + d) := by
    unfold y
    exact mul_pos (by linarith)
      (cbrt_pos_of_pos (by linarith))
  rw [hone] at hle
  linarith

theorem gap11 : IsLocalMin y 1 := by
  exact one_is_local_min

end
end ProofGap.Exercise1436
