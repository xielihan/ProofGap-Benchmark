import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace ProofGap.Exercise1422

noncomputable section

def y (x : ℝ) : ℝ := Real.cbrt x * (Real.cbrt (1 - x)) ^ 2

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
  have hcos :
      Real.cos ((1 / 3 : ℝ) * Real.pi) = 1 / 2 := by
    rw [show (1 / 3 : ℝ) * Real.pi =
      Real.pi / 3 by ring, Real.cos_pi_div_three]
  rw [hcos]
  positivity

private theorem rpow_third_sub_one_eq {x : ℝ} (hx : 0 < x) :
    x ^ ((1 / 3 : ℝ) - 1) = 1 / (Real.cbrt x) ^ 2 := by
  have hcpos := cbrt_pos_of_pos hx
  have hcubed := cbrt_cubed_of_nonneg x hx.le
  rw [Real.rpow_sub hx, Real.rpow_one]
  change Real.cbrt x / x = 1 / (Real.cbrt x) ^ 2
  field_simp [hcpos.ne']
  nlinarith [hcubed]

private theorem rpow_third_sub_one_neg {x : ℝ} (hx : x < 0) :
    x ^ ((1 / 3 : ℝ) - 1) < 0 := by
  rw [Real.rpow_def_of_neg hx]
  have hcos :
      Real.cos (((1 / 3 : ℝ) - 1) * Real.pi) = -1 / 2 := by
    rw [show ((1 / 3 : ℝ) - 1) * Real.pi =
        -(2 * Real.pi / 3) by ring, Real.cos_neg]
    rw [show 2 * Real.pi / 3 =
        Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
    norm_num
  rw [hcos]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) (by norm_num)

private theorem deriv_y_raw (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    deriv y x =
      (1 / 3 : ℝ) * x ^ ((1 / 3 : ℝ) - 1) *
          (Real.cbrt (1 - x)) ^ 2 +
        Real.cbrt x *
          (2 * Real.cbrt (1 - x) *
            ((1 / 3 : ℝ) * (1 - x) ^ ((1 / 3 : ℝ) - 1) * (-1))) := by
  have hxroot :
      HasDerivAt (fun z : ℝ => z ^ (1 / 3 : ℝ))
        ((1 / 3 : ℝ) * x ^ ((1 / 3 : ℝ) - 1)) x := by
    simpa using
      (hasDerivAt_id x).rpow_const (Or.inl hx0)
  have hsub : HasDerivAt (fun z : ℝ => 1 - z) (-1) x := by
    simpa using
      ((hasDerivAt_const (x : ℝ) (1 : ℝ)).sub (hasDerivAt_id x))
  have hsubroot :
      HasDerivAt (fun z : ℝ => (1 - z) ^ (1 / 3 : ℝ))
        ((1 / 3 : ℝ) * (1 - x) ^ ((1 / 3 : ℝ) - 1) * (-1)) x := by
    simpa using
      hsub.rpow_const (Or.inl (sub_ne_zero.mpr hx1.symm))
  unfold y Real.cbrt
  convert (hxroot.mul (hsubroot.fun_pow 2)).deriv using 1 <;>
    norm_num <;> ring

private theorem deriv_y_of_pos_of_lt_one {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    deriv y x =
      (1 - 3 * x) /
        (3 * (Real.cbrt x) ^ 2 * Real.cbrt (1 - x)) := by
  have hcx := cbrt_pos_of_pos hx0
  have hcu := cbrt_pos_of_pos (sub_pos.mpr hx1)
  have hcx3 := cbrt_cubed_of_nonneg x hx0.le
  have hcu3 := cbrt_cubed_of_nonneg (1 - x) (sub_nonneg.mpr hx1.le)
  rw [deriv_y_raw x hx0.ne' (by linarith),
    rpow_third_sub_one_eq hx0,
    rpow_third_sub_one_eq (sub_pos.mpr hx1)]
  field_simp [hcx.ne', hcu.ne']
  nlinarith [hcx3, hcu3]

private theorem deriv_y_neg_one_neg : deriv y (-1) < 0 := by
  have hxpow :
      (-1 : ℝ) ^ ((1 / 3 : ℝ) - 1) < 0 :=
    rpow_third_sub_one_neg (by norm_num)
  have hupow :
      (1 - (-1 : ℝ)) ^ ((1 / 3 : ℝ) - 1) > 0 :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hcx : 0 < Real.cbrt (-1) :=
    cbrt_pos_of_neg (by norm_num)
  have hcu : 0 < Real.cbrt (1 - (-1 : ℝ)) :=
    cbrt_pos_of_pos (by norm_num)
  rw [deriv_y_raw (-1) (by norm_num) (by norm_num)]
  have hleft :
      (1 / 3 : ℝ) * (-1 : ℝ) ^ ((1 / 3 : ℝ) - 1) *
          (Real.cbrt (1 - (-1 : ℝ))) ^ 2 < 0 := by
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (by norm_num) hxpow)
      (sq_pos_of_pos hcu)
  have hinner :
      (1 / 3 : ℝ) * (1 - (-1 : ℝ)) ^ ((1 / 3 : ℝ) - 1) * (-1) < 0 := by
    exact mul_neg_of_pos_of_neg
      (mul_pos (by norm_num) hupow) (by norm_num)
  have hright :
      Real.cbrt (-1) *
          (2 * Real.cbrt (1 - (-1 : ℝ)) *
            ((1 / 3 : ℝ) *
              (1 - (-1 : ℝ)) ^ ((1 / 3 : ℝ) - 1) * (-1))) < 0 := by
    exact mul_neg_of_pos_of_neg hcx
      (mul_neg_of_pos_of_neg
        (mul_pos (by norm_num) hcu) hinner)
  linarith

private theorem cbrt_nonneg (x : ℝ) : 0 ≤ Real.cbrt x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · exact (cbrt_pos_of_neg hx).le
  · subst x
    norm_num [Real.cbrt]
  · exact (cbrt_pos_of_pos hx).le

private theorem zero_is_local_min : IsLocalMin y 0 := by
  have hzero : y 0 = 0 := by
    norm_num [y, Real.cbrt]
  change ∀ᶠ x in nhds (0 : ℝ), y 0 ≤ y x
  exact Filter.Eventually.of_forall fun x => by
    rw [hzero]
    unfold y
    exact mul_nonneg (cbrt_nonneg x) (sq_nonneg _)

theorem gap1 (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hxpos : 0 < x) (hxlt : x < 1) :
    deriv y x = (1 - 3 * x) / (3 * Real.cbrt (x ^ 2 * (1 - x))) := by
  have hcprod :
      Real.cbrt (x ^ 2 * (1 - x)) =
        (Real.cbrt x) ^ 2 * Real.cbrt (1 - x) := by
    unfold Real.cbrt
    simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow (sq_nonneg x) (sub_nonneg.mpr hxlt.le)]
    congr 1
    calc
      (x ^ 2) ^ (1 / 3 : ℝ) =
          x ^ ((2 : ℝ) * (1 / 3 : ℝ)) :=
        (Real.rpow_natCast_mul hxpos.le 2 (1 / 3 : ℝ)).symm
      _ = x ^ ((1 / 3 : ℝ) * (2 : ℝ)) := by ring
      _ = (x ^ (1 / 3 : ℝ)) ^ 2 :=
        Real.rpow_mul_natCast hxpos.le (1 / 3 : ℝ) 2
  rw [deriv_y_of_pos_of_lt_one hxpos hxlt, hcprod]
  ring

theorem gap2 : deriv y (1 / 3) = 0 := by
  rw [deriv_y_of_pos_of_lt_one (by norm_num) (by norm_num)]
  norm_num

theorem gap3 (x : ℝ) (hx : x < 0) : deriv y x < 0 := by
  have hxpow : x ^ ((1 / 3 : ℝ) - 1) < 0 :=
    rpow_third_sub_one_neg hx
  have hupow : 0 < (1 - x) ^ ((1 / 3 : ℝ) - 1) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hcx : 0 < Real.cbrt x := cbrt_pos_of_neg hx
  have hcu : 0 < Real.cbrt (1 - x) := cbrt_pos_of_pos (by linarith)
  rw [deriv_y_raw x (by linarith) (by linarith)]
  have hleft :
      (1 / 3 : ℝ) * x ^ ((1 / 3 : ℝ) - 1) *
          (Real.cbrt (1 - x)) ^ 2 < 0 := by
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (by norm_num) hxpow)
      (sq_pos_of_pos hcu)
  have hinner :
      (1 / 3 : ℝ) * (1 - x) ^ ((1 / 3 : ℝ) - 1) * (-1) < 0 := by
    exact mul_neg_of_pos_of_neg
      (mul_pos (by norm_num) hupow) (by norm_num)
  have hright :
      Real.cbrt x *
          (2 * Real.cbrt (1 - x) *
            ((1 / 3 : ℝ) * (1 - x) ^ ((1 / 3 : ℝ) - 1) * (-1))) < 0 := by
    exact mul_neg_of_pos_of_neg hcx
      (mul_neg_of_pos_of_neg (mul_pos (by norm_num) hcu) hinner)
  linarith

theorem gap4 (x : ℝ) (h₁ : 0 < x) (h₂ : x < 1 / 3) :
    0 < deriv y x := by
  rw [deriv_y_of_pos_of_lt_one h₁ (by linarith)]
  have hden :
      0 < 3 * (Real.cbrt x) ^ 2 * Real.cbrt (1 - x) := by
    exact mul_pos
      (mul_pos (by norm_num) (sq_pos_of_pos (cbrt_pos_of_pos h₁)))
      (cbrt_pos_of_pos (by linarith))
  exact div_pos (by linarith) hden

theorem gap5 (x : ℝ) (h₁ : 1 / 3 < x) (h₂ : x < 1) :
    deriv y x < 0 := by
  rw [deriv_y_of_pos_of_lt_one (by linarith) h₂]
  have hden :
      0 < 3 * (Real.cbrt x) ^ 2 * Real.cbrt (1 - x) := by
    exact mul_pos
      (mul_pos (by norm_num)
        (sq_pos_of_pos (cbrt_pos_of_pos (by linarith))))
      (cbrt_pos_of_pos (by linarith))
  exact div_neg_of_neg_of_pos (by linarith) hden

theorem gap6 (x : ℝ) (hx : 1 < x) : 0 < deriv y x := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x ≠ 1 := by linarith
  have hcx : 0 < Real.cbrt x :=
    cbrt_pos_of_pos (by linarith)
  have hcu : 0 < Real.cbrt (1 - x) :=
    cbrt_pos_of_neg (by linarith)
  have hxpow :
      0 < x ^ ((1 / 3 : ℝ) - 1) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hupow :
      (1 - x) ^ ((1 / 3 : ℝ) - 1) < 0 :=
    rpow_third_sub_one_neg (by linarith)
  rw [deriv_y_raw x hx0 hx1]
  have hleft :
      0 < (1 / 3 : ℝ) * x ^ ((1 / 3 : ℝ) - 1) *
          (Real.cbrt (1 - x)) ^ 2 := by
    exact mul_pos
      (mul_pos (by norm_num) hxpow)
      (sq_pos_of_pos hcu)
  have hinner :
      0 < (1 / 3 : ℝ) * (1 - x) ^ ((1 / 3 : ℝ) - 1) * (-1) := by
    exact mul_pos_of_neg_of_neg
      (mul_neg_of_pos_of_neg (by norm_num) hupow)
      (by norm_num)
  have hright :
      0 < Real.cbrt x *
          (2 * Real.cbrt (1 - x) *
            ((1 / 3 : ℝ) * (1 - x) ^ ((1 / 3 : ℝ) - 1) * (-1))) := by
    exact mul_pos hcx
      (mul_pos (mul_pos (by norm_num) hcu) hinner)
  linarith

theorem gap7 : ¬ IsLocalMax y 0 := by
  have hzero : y 0 = 0 := by
    norm_num [y, Real.cbrt]
  intro hmax
  change {z : ℝ | y z ≤ y 0} ∈ nhds (0 : ℝ) at hmax
  rcases Metric.mem_nhds_iff.mp hmax with ⟨ε, hε, hball⟩
  let d : ℝ := min (ε / 2) (1 / 2)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (by linarith) (by norm_num)
  have hdε : d < ε :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hdhalf : d ≤ (1 : ℝ) / 2 := min_le_right _ _
  have hdball : d ∈ Metric.ball (0 : ℝ) ε := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hd] using hdε
  have hle : y d ≤ y 0 := hball hdball
  have hpos : 0 < y d := by
    unfold y
    exact mul_pos (cbrt_pos_of_pos hd)
      (sq_pos_of_pos (cbrt_pos_of_pos (by linarith)))
  rw [hzero] at hle
  linarith

theorem gap8 : IsLocalMin y 0 := by
  exact zero_is_local_min

theorem gap9 : IsLocalMax y (1 / 3) := by
  have hcont : Continuous y := by
    unfold y Real.cbrt
    exact
      (Real.continuous_rpow_const (by norm_num)).mul
        (((continuous_const.sub continuous_id).rpow_const
          (fun _ => Or.inr (by norm_num))).pow 2)
  apply isLocalMax_of_deriv_Ioo
    (a := (0 : ℝ)) (b := (1 / 3 : ℝ)) (c := (1 : ℝ))
    (by norm_num) (by norm_num) hcont.continuousAt
  · intro x hx
    exact
      (differentiableAt_of_deriv_ne_zero
        (gap4 x hx.1 hx.2).ne').differentiableWithinAt
  · intro x hx
    exact
      (differentiableAt_of_deriv_ne_zero
        (gap5 x hx.1 hx.2).ne).differentiableWithinAt
  · intro x hx
    exact le_of_lt (gap4 x hx.1 hx.2)
  · intro x hx
    exact le_of_lt (gap5 x hx.1 hx.2)

theorem gap10 : y (1 / 3) = (1 / 3) * Real.cbrt 4 := by
  have h13 : (Real.cbrt (1 / 3)) ^ 3 = (1 / 3 : ℝ) :=
    cbrt_cubed_of_nonneg (1 / 3) (by norm_num)
  have h23 : (Real.cbrt (2 / 3)) ^ 3 = (2 / 3 : ℝ) :=
    cbrt_cubed_of_nonneg (2 / 3) (by norm_num)
  have h43 : (Real.cbrt 4) ^ 3 = (4 : ℝ) :=
    cbrt_cubed_of_nonneg 4 (by norm_num)
  apply (show Odd 3 by exact ⟨1, rfl⟩).pow_injective
  change (y (1 / 3)) ^ 3 =
    ((1 / 3 : ℝ) * Real.cbrt 4) ^ 3
  unfold y
  norm_num
  change
    (Real.cbrt (1 / 3) * (Real.cbrt (2 / 3)) ^ 2) ^ 3 =
      ((1 / 3 : ℝ) * Real.cbrt 4) ^ 3
  calc
    (Real.cbrt (1 / 3) * (Real.cbrt (2 / 3)) ^ 2) ^ 3 =
        (Real.cbrt (1 / 3)) ^ 3 *
          ((Real.cbrt (2 / 3)) ^ 3) ^ 2 := by ring
    _ = (1 / 3 : ℝ) * (2 / 3) ^ 2 := by rw [h13, h23]
    _ = ((1 / 3 : ℝ) * Real.cbrt 4) ^ 3 := by
      rw [mul_pow, h43]
      norm_num

theorem gap11 :
    Approx ((1 / 3) * Real.cbrt 4) 0.529 0.001 := by
  have ht3 : (Real.cbrt 4) ^ 3 = (4 : ℝ) :=
    cbrt_cubed_of_nonneg 4 (by norm_num)
  have htpos : 0 < Real.cbrt 4 :=
    cbrt_pos_of_pos (by norm_num)
  have hl : (1.584 : ℝ) < Real.cbrt 4 := by
    apply lt_of_pow_lt_pow_left₀ 3 htpos.le
    rw [ht3]
    norm_num
  have hu : Real.cbrt 4 < (1.590 : ℝ) := by
    apply lt_of_pow_lt_pow_left₀ 3 (by norm_num)
    rw [ht3]
    norm_num
  unfold Approx
  rw [abs_lt]
  constructor <;> norm_num at * <;> linarith

theorem gap12 : IsLocalMin y 1 := by
  have hone : y 1 = 0 := by
    norm_num [y, Real.cbrt]
  change ∀ᶠ x in nhds (1 : ℝ), y 1 ≤ y x
  filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
  rw [hone]
  unfold y Real.cbrt
  exact mul_nonneg
    (Real.rpow_nonneg (le_of_lt hx) _)
    (sq_nonneg _)

theorem gap13 : y 1 = 0 := by
  norm_num [y, Real.cbrt]

end
end ProofGap.Exercise1422
