import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise3857

noncomputable section

open MeasureTheory
open scoped Interval

def betaFn (x y : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1,
    Real.rpow u (x - 1) * Real.rpow (1 - u) (y - 1)

private theorem sin_image_Ioo_zero_pi_div_two :
    Real.sin '' Set.Ioo (0 : ℝ) (Real.pi / 2) = Set.Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxpi : x < Real.pi := hx.2.trans (by linarith [Real.pi_pos])
    have hxmem :
        x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨(neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans hx.1.le,
        hx.2.le⟩
    have hend :
        Real.pi / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], le_rfl⟩
    exact ⟨Real.sin_pos_of_pos_of_lt_pi hx.1 hxpi,
      by simpa using Real.strictMonoOn_sin hxmem hend hx.2⟩
  · intro hy
    refine ⟨Real.arcsin y,
      ⟨Real.arcsin_pos.2 hy.1, Real.arcsin_lt_pi_div_two.2 hy.2⟩, ?_⟩
    exact Real.sin_arcsin (by linarith [hy.1]) hy.2.le

private theorem tan_rpow_eq_sin_mul_cos_neg (n x : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Real.rpow (Real.tan x) n =
      Real.rpow (Real.sin x) n * Real.rpow (Real.cos x) (-n) := by
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1
      (hx.2.trans (by linarith [Real.pi_pos]))
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo
      ⟨(neg_neg_of_pos (by positivity : 0 < Real.pi / 2)).trans hx.1,
        hx.2⟩
  rw [Real.tan_eq_sin_div_cos]
  change Real.rpow (Real.sin x / Real.cos x) n =
    Real.rpow (Real.sin x) n * Real.rpow (Real.cos x) (-n)
  rw [div_eq_mul_inv]
  have hmul :
      Real.rpow (Real.sin x * (Real.cos x)⁻¹) n =
        Real.rpow (Real.sin x) n *
          Real.rpow ((Real.cos x)⁻¹) n :=
    Real.mul_rpow hsin.le (inv_nonneg.mpr hcos.le)
  rw [hmul]
  have hinv :
      Real.rpow ((Real.cos x)⁻¹) n =
        (Real.rpow (Real.cos x) n)⁻¹ :=
    Real.inv_rpow hcos.le n
  rw [hinv]
  have hneg :
      Real.rpow (Real.cos x) (-n) =
        (Real.rpow (Real.cos x) n)⁻¹ :=
    by
      simpa only [← Real.rpow_eq_pow] using
        (Real.rpow_neg hcos.le n)
  rw [hneg]

private theorem tan_change_integrand (n x : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |Real.cos x| *
        (Real.rpow (Real.sin x) n *
          Real.rpow (1 - Real.sin x ^ 2) (-(n + 1) / 2)) =
      Real.rpow (Real.tan x) n := by
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo
      ⟨(neg_neg_of_pos (by positivity : 0 < Real.pi / 2)).trans hx.1,
        hx.2⟩
  have hsq : 1 - Real.sin x ^ 2 = Real.cos x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [abs_of_pos hcos, hsq]
  have hpow :
      Real.rpow (Real.cos x ^ 2) (-(n + 1) / 2) =
        Real.rpow (Real.cos x) (-n - 1) := by
    have hnat :
        Real.rpow (Real.cos x) (2 : ℝ) = Real.cos x ^ (2 : ℕ) :=
      Real.rpow_natCast _ 2
    rw [← hnat]
    have hmul :
        Real.rpow (Real.rpow (Real.cos x) 2) (-(n + 1) / 2) =
          Real.rpow (Real.cos x) (2 * (-(n + 1) / 2)) :=
      (Real.rpow_mul hcos.le 2 (-(n + 1) / 2)).symm
    rw [hmul]
    congr 1
    ring
  rw [hpow]
  have hadd :
      Real.cos x * Real.rpow (Real.cos x) (-n - 1) =
        Real.rpow (Real.cos x) (-n) := by
    have hone : Real.rpow (Real.cos x) 1 = Real.cos x :=
      Real.rpow_one _
    calc
      Real.cos x * Real.rpow (Real.cos x) (-n - 1) =
          Real.rpow (Real.cos x) 1 *
            Real.rpow (Real.cos x) (-n - 1) := by rw [hone]
      _ = Real.rpow (Real.cos x) (1 + (-n - 1)) :=
        (Real.rpow_add hcos 1 (-n - 1)).symm
      _ = Real.rpow (Real.cos x) (-n) := by congr 1 <;> ring
  rw [show Real.cos x *
      (Real.rpow (Real.sin x) n *
        Real.rpow (Real.cos x) (-n - 1)) =
      Real.rpow (Real.sin x) n *
        (Real.cos x * Real.rpow (Real.cos x) (-n - 1)) by ring,
    hadd, tan_rpow_eq_sin_mul_cos_neg n x hx]

theorem gap1 (n : ℝ) (hn : |n| < 1) :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.rpow (Real.tan x) n) =
      ∫ t in (0 : ℝ)..1,
        Real.rpow t n *
          Real.rpow (1 - t ^ 2) (-(n + 1) / 2) := by
  let g : ℝ → ℝ := fun t =>
    Real.rpow t n * Real.rpow (1 - t ^ 2) (-(n + 1) / 2)
  have hinj :
      Set.InjOn Real.sin (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    apply Real.injOn_sin.mono
    intro x hx
    exact
      ⟨(neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans hx.1.le,
        hx.2.le⟩
  have hchange :=
    integral_image_eq_integral_abs_deriv_smul
      (s := Set.Ioo (0 : ℝ) (Real.pi / 2))
      measurableSet_Ioo
      (fun x hx => (Real.hasDerivAt_sin x).hasDerivWithinAt)
      hinj g
  rw [sin_image_Ioo_zero_pi_div_two] at hchange
  rw [intervalIntegral.integral_of_le (by positivity),
    integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo]
  rw [hchange]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  change Real.rpow (Real.tan x) n =
    |Real.cos x| *
      (Real.rpow (Real.sin x) n *
        Real.rpow (1 - Real.sin x ^ 2) (-(n + 1) / 2))
  exact (tan_change_integrand n x hx).symm

private theorem square_image_Ioo_zero_one :
    (fun t : ℝ => t ^ 2) '' Set.Ioo (0 : ℝ) 1 = Set.Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    change 0 < t ^ 2 ∧ t ^ 2 < 1
    constructor
    · exact sq_pos_of_pos ht0
    · simpa using (sq_lt_sq₀ ht0.le (by norm_num : (0 : ℝ) ≤ 1)).2 ht1
  · rintro ⟨hy0, hy1⟩
    refine ⟨Real.sqrt y, ?_, ?_⟩
    · exact ⟨Real.sqrt_pos.2 hy0,
        (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2 (by simpa using hy1)⟩
    · exact Real.sq_sqrt hy0.le

private theorem square_change_integrand (n t : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (1 / 2 : ℝ) *
        (|2 * t| *
          (Real.rpow (t ^ 2) ((n - 1) / 2) *
            Real.rpow (1 - t ^ 2) (-(n + 1) / 2))) =
      Real.rpow t n * Real.rpow (1 - t ^ 2) (-(n + 1) / 2) := by
  have hpow :
      Real.rpow (t ^ 2) ((n - 1) / 2) =
        Real.rpow t (n - 1) := by
    have hnat : Real.rpow t (2 : ℝ) = t ^ (2 : ℕ) :=
      Real.rpow_natCast _ 2
    rw [← hnat]
    have hmul :
        Real.rpow (Real.rpow t 2) ((n - 1) / 2) =
          Real.rpow t (2 * ((n - 1) / 2)) :=
      (Real.rpow_mul ht.1.le 2 ((n - 1) / 2)).symm
    rw [hmul]
    congr 1
    ring
  rw [abs_of_pos (mul_pos (by norm_num) ht.1), hpow]
  have hadd :
      t * Real.rpow t (n - 1) = Real.rpow t n := by
    have hone : Real.rpow t 1 = t := Real.rpow_one _
    calc
      t * Real.rpow t (n - 1) =
          Real.rpow t 1 * Real.rpow t (n - 1) := by rw [hone]
      _ = Real.rpow t (1 + (n - 1)) :=
        (Real.rpow_add ht.1 1 (n - 1)).symm
      _ = Real.rpow t n := by congr 1 <;> ring
  rw [show (1 / 2 : ℝ) * (2 * t *
      (Real.rpow t (n - 1) *
        Real.rpow (1 - t ^ 2) (-(n + 1) / 2))) =
      (t * Real.rpow t (n - 1)) *
        Real.rpow (1 - t ^ 2) (-(n + 1) / 2) by ring, hadd]

theorem gap2 (n : ℝ) (hn : |n| < 1) :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.rpow (Real.tan x) n) =
      (1 / 2 : ℝ) *
        ∫ u in (0 : ℝ)..1,
          Real.rpow u ((n - 1) / 2) *
            Real.rpow (1 - u) (-(n + 1) / 2) := by
  rw [gap1 n hn]
  let g : ℝ → ℝ := fun u =>
    Real.rpow u ((n - 1) / 2) *
      Real.rpow (1 - u) (-(n + 1) / 2)
  have hinj :
      Set.InjOn (fun t : ℝ => t ^ 2) (Set.Ioo (0 : ℝ) 1) := by
    rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ hxy
    change x ^ 2 = y ^ 2 at hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (ne_of_lt ((sq_lt_sq₀ hx0.le hy0.le).2 hlt)) hxy
    · exact (ne_of_gt ((sq_lt_sq₀ hy0.le hx0.le).2 hgt)) hxy
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivWithinAt (fun s : ℝ => s ^ 2) (2 * t)
          (Set.Ioo (0 : ℝ) 1) t := by
    intro t ht
    simpa [mul_comm] using ((hasDerivAt_id t).pow 2).hasDerivWithinAt
  have hchange :=
    integral_image_eq_integral_abs_deriv_smul
      (s := Set.Ioo (0 : ℝ) 1)
      measurableSet_Ioo hderiv hinj g
  rw [square_image_Ioo_zero_one] at hchange
  simp only [smul_eq_mul] at hchange
  rw [intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo]
  calc
    (∫ t in Set.Ioo (0 : ℝ) 1,
        Real.rpow t n * Real.rpow (1 - t ^ 2) (-(n + 1) / 2)) =
      ∫ t in Set.Ioo (0 : ℝ) 1,
        (1 / 2 : ℝ) *
          (|2 * t| *
            (Real.rpow (t ^ 2) ((n - 1) / 2) *
              Real.rpow (1 - t ^ 2) (-(n + 1) / 2))) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro t ht
        exact (square_change_integrand n t ht).symm
    _ = (1 / 2 : ℝ) *
        ∫ t in Set.Ioo (0 : ℝ) 1,
          |2 * t| *
            (Real.rpow (t ^ 2) ((n - 1) / 2) *
              Real.rpow (1 - t ^ 2) (-(n + 1) / 2)) := by
        rw [MeasureTheory.integral_const_mul]
    _ = (1 / 2 : ℝ) *
        ∫ u in Set.Ioo (0 : ℝ) 1,
          Real.rpow u ((n - 1) / 2) *
            Real.rpow (1 - u) (-(n + 1) / 2) := by
        rw [hchange]

theorem gap3 (n : ℝ) (hn : |n| < 1) :
    (1 / 2 : ℝ) *
        (∫ u in (0 : ℝ)..1,
          Real.rpow u ((n - 1) / 2) *
            Real.rpow (1 - u) (-(n + 1) / 2)) =
      (1 / 2 : ℝ) *
        betaFn ((n + 1) / 2) ((1 - n) / 2) := by
  unfold betaFn
  ring_nf

theorem gap4 (n : ℝ) (hn : |n| < 1) :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.rpow (Real.tan x) n) =
      (1 / 2 : ℝ) *
        betaFn ((n + 1) / 2) ((1 - n) / 2) := by
  rw [gap2 n hn]
  exact gap3 n hn

private theorem betaFn_eq_Gamma_mul_div (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    betaFn a b = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have hcoe : ((betaFn a b : ℝ) : ℂ) = Complex.betaIntegral a b := by
    unfold betaFn Complex.betaIntegral
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    change
      ((Real.rpow x (a - 1) * Real.rpow (1 - x) (b - 1) : ℝ) : ℂ) =
        (x : ℂ) ^ ((a : ℂ) - 1) *
          (1 - (x : ℂ)) ^ ((b : ℂ) - 1)
    rw [Complex.ofReal_mul, Real.rpow_eq_pow, Real.rpow_eq_pow,
      Complex.ofReal_cpow hx.1,
      Complex.ofReal_cpow (sub_nonneg.mpr hx.2)]
    push_cast
    rfl
  apply Complex.ofReal_injective
  rw [hcoe, Complex.ofReal_div, Complex.ofReal_mul,
    ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal,
    ← Complex.Gamma_ofReal]
  simpa only [Complex.ofReal_add] using
    (Complex.betaIntegral_eq_Gamma_mul_div (a : ℂ) (b : ℂ)
      (by simpa using ha) (by simpa using hb))

theorem gap5 (n : ℝ) (hn : |n| < 1) :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.rpow (Real.tan x) n) =
      (1 / 2 : ℝ) *
        (Real.Gamma ((n + 1) / 2) *
            Real.Gamma (1 - (n + 1) / 2) /
          Real.Gamma 1) := by
  rw [gap4 n hn]
  have hn' := abs_lt.mp hn
  have ha : 0 < (n + 1) / 2 := by linarith
  have hb : 0 < (1 - n) / 2 := by linarith
  rw [betaFn_eq_Gamma_mul_div _ _ ha hb]
  congr 3 <;> ring

theorem gap6 (n : ℝ) (hn : |n| < 1) :
    (1 / 2 : ℝ) *
        (Real.Gamma ((n + 1) / 2) *
            Real.Gamma (1 - (n + 1) / 2) /
          Real.Gamma 1) =
      (1 / 2 : ℝ) *
        (Real.pi / Real.sin (((n + 1) / 2) * Real.pi)) := by
  rw [Real.Gamma_one, div_one,
    Real.Gamma_mul_Gamma_one_sub]
  congr 3
  ring

theorem gap7 (n : ℝ) (hn : |n| < 1) :
    (1 / 2 : ℝ) *
        (Real.pi / Real.sin (((n + 1) / 2) * Real.pi)) =
      Real.pi / (2 * Real.cos (n * Real.pi / 2)) := by
  rw [show ((n + 1) / 2) * Real.pi =
    n * Real.pi / 2 + Real.pi / 2 by ring,
    Real.sin_add_pi_div_two]
  ring

theorem gap8 (n : ℝ) (hn : |n| < 1) :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.rpow (Real.tan x) n) =
      Real.pi / (2 * Real.cos (n * Real.pi / 2)) := by
  rw [gap5 n hn, gap6 n hn, gap7 n hn]

theorem gap9 (n : ℝ) :
    0 < (n + 1) / 2 ∧ 0 < (1 - n) / 2 ↔
      |n| < 1 := by
  rw [abs_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

end

end ProofGap.Exercise3857
