import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise3858

noncomputable section

open MeasureTheory
open scoped Interval

def betaFn (x y : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1,
    Real.rpow u (x - 1) * Real.rpow (1 - u) (y - 1)

def xOfT (k t : ℝ) : ℝ :=
  2 * Real.arctan
    (Real.sqrt ((1 + k) / (1 - k)) * Real.tan (t / 2))

def mainIntegrand (k n x : ℝ) : ℝ :=
  Real.rpow (Real.sin x) (n - 1) /
    Real.rpow (1 + k * Real.cos x) n

theorem gap1 (k t : ℝ)
    (hk₀ : 0 < |k|) (hk : |k| < 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Real.tan (xOfT k t / 2) =
      Real.sqrt ((1 + k) / (1 - k)) * Real.tan (t / 2) := by
  simp [xOfT, Real.tan_arctan]

private theorem sqrt_ratio_pos (k : ℝ) (hk : |k| < 1) :
    0 < Real.sqrt ((1 + k) / (1 - k)) := by
  have hk' := abs_lt.mp hk
  exact Real.sqrt_pos.2 (div_pos (by linarith) (by linarith))

private theorem sqrt_one_sub_sq_eq (k : ℝ) (hk : |k| < 1) :
    Real.sqrt (1 - k ^ 2) =
      Real.sqrt ((1 + k) / (1 - k)) * (1 - k) := by
  have hk' := abs_lt.mp hk
  have hsub : 0 < 1 - k := by linarith
  have hsum : 0 < 1 + k := by linarith
  have hquad : 0 ≤ 1 - k ^ 2 := by nlinarith
  have hratio : 0 ≤ (1 + k) / (1 - k) :=
    (div_pos hsum hsub).le
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hsub.le)).mp
  rw [Real.sq_sqrt hquad, mul_pow, Real.sq_sqrt hratio]
  field_simp [hsub.ne']
  ring

private theorem cos_ne_neg_one_of_mem_Ioo_zero_pi {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Real.cos t ≠ -1 := by
  have hmem : t ∈ Set.Icc (0 : ℝ) Real.pi := ⟨ht.1.le, ht.2.le⟩
  have hpi : Real.pi ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨Real.pi_pos.le, le_rfl⟩
  have hlt := Real.strictAntiOn_cos hmem hpi ht.2
  simpa using ne_of_gt hlt

private theorem xOfT_mem_Ioo (k t : ℝ) (hk : |k| < 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) Real.pi) :
    xOfT k t ∈ Set.Ioo (0 : ℝ) Real.pi := by
  have htHalf :
      t / 2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    exact ⟨half_pos ht.1, (div_lt_div_iff_of_pos_right (by norm_num)).2 ht.2⟩
  have htan : 0 < Real.tan (t / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two htHalf.1 htHalf.2
  have harg :
      0 < Real.sqrt ((1 + k) / (1 - k)) * Real.tan (t / 2) :=
    mul_pos (sqrt_ratio_pos k hk) htan
  unfold xOfT
  have harctanPos :
      0 < Real.arctan
        (Real.sqrt ((1 + k) / (1 - k)) * Real.tan (t / 2)) :=
    Real.arctan_pos.2 harg
  have harctanLt :
      Real.arctan
          (Real.sqrt ((1 + k) / (1 - k)) * Real.tan (t / 2)) <
        Real.pi / 2 :=
    (Real.arctan_lt_pi_div_two _)
  constructor <;> linarith

theorem gap2 (k t : ℝ)
    (hk₀ : 0 < |k|) (hk : |k| < 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Real.sin (xOfT k t) =
      Real.sqrt (1 - k ^ 2) * Real.sin t /
        (1 - k * Real.cos t) := by
  have hxt := xOfT_mem_Ioo k t hk ht
  have hct : Real.cos t ≠ -1 := cos_ne_neg_one_of_mem_Ioo_zero_pi ht
  rw [Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq,
    gap1 k t hk₀ hk ht,
    Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq,
    Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq t hct,
    sqrt_one_sub_sq_eq k hk]
  have hs :
      Real.sqrt ((1 + k) / (1 - k)) ^ 2 =
        (1 + k) / (1 - k) :=
    Real.sq_sqrt (div_nonneg (by linarith [abs_lt.mp hk])
      (by linarith [abs_lt.mp hk]))
  rw [mul_pow, hs]
  have hkden : 1 - k ≠ 0 := by linarith [abs_lt.mp hk]
  have htanDen : 1 + Real.tan (t / 2) ^ 2 ≠ 0 := by positivity
  field_simp [hkden, htanDen]
  ring

theorem gap3 (k t : ℝ)
    (hk₀ : 0 < |k|) (hk : |k| < 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Real.cos (xOfT k t) =
      (Real.cos t - k) / (1 - k * Real.cos t) := by
  have hxt := xOfT_mem_Ioo k t hk ht
  have hcx : Real.cos (xOfT k t) ≠ -1 :=
    cos_ne_neg_one_of_mem_Ioo_zero_pi hxt
  have hct : Real.cos t ≠ -1 := cos_ne_neg_one_of_mem_Ioo_zero_pi ht
  rw [Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq _ hcx,
    gap1 k t hk₀ hk ht,
    Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq t hct]
  have hs :
      Real.sqrt ((1 + k) / (1 - k)) ^ 2 =
        (1 + k) / (1 - k) :=
    Real.sq_sqrt (div_nonneg (by linarith [abs_lt.mp hk])
      (by linarith [abs_lt.mp hk]))
  rw [mul_pow, hs]
  have hkden : 1 - k ≠ 0 := by linarith [abs_lt.mp hk]
  have htanDen : 1 + Real.tan (t / 2) ^ 2 ≠ 0 := by positivity
  field_simp [hkden, htanDen]
  ring

theorem gap4 (k t : ℝ)
    (hk₀ : 0 < |k|) (hk : |k| < 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) Real.pi) :
    1 + k * Real.cos (xOfT k t) =
      (1 - k ^ 2) / (1 - k * Real.cos t) := by
  rw [gap3 k t hk₀ hk ht]
  have hden : 1 - k * Real.cos t ≠ 0 := by
    have hcos : |Real.cos t| ≤ 1 := Real.abs_cos_le_one t
    have hprod : k * Real.cos t < 1 := by
      calc
        k * Real.cos t ≤ |k * Real.cos t| := le_abs_self _
        _ = |k| * |Real.cos t| := abs_mul _ _
        _ ≤ |k| * 1 := mul_le_mul_of_nonneg_left hcos (abs_nonneg k)
        _ < 1 := by simpa using hk
    linarith
  field_simp [hden]
  ring

theorem gap5 (k t : ℝ)
    (hk₀ : 0 < |k|) (hk : |k| < 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) Real.pi) :
    HasDerivAt (xOfT k)
      (Real.sqrt (1 - k ^ 2) / (1 - k * Real.cos t)) t := by
  have htHalf :
      t / 2 ∈ Set.Ioo (-(Real.pi / 2) : ℝ) (Real.pi / 2) := by
    constructor
    · have := ht.1
      linarith [Real.pi_pos]
    · exact (div_lt_div_iff_of_pos_right (by norm_num)).2 ht.2
  have hcos : Real.cos (t / 2) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo htHalf).ne'
  let a : ℝ := Real.sqrt ((1 + k) / (1 - k))
  have htan :
      HasDerivAt (fun s : ℝ => Real.tan (s / 2))
        ((1 / Real.cos (t / 2) ^ 2) * (1 / 2)) t :=
    by
      simpa only [Function.comp_apply, id_eq] using
        (Real.hasDerivAt_tan hcos).comp t
          ((hasDerivAt_id t).div_const 2)
  have hinner :
      HasDerivAt (fun s : ℝ => a * Real.tan (s / 2))
        (a * ((1 / Real.cos (t / 2) ^ 2) * (1 / 2))) t :=
    htan.const_mul a
  have hall :
      HasDerivAt
        (fun s : ℝ => 2 * Real.arctan (a * Real.tan (s / 2)))
        (2 * (1 / (1 + (a * Real.tan (t / 2)) ^ 2) *
          (a * ((1 / Real.cos (t / 2) ^ 2) * (1 / 2))))) t :=
    hinner.arctan.const_mul 2
  change HasDerivAt
    (fun s : ℝ =>
      2 * Real.arctan
        (Real.sqrt ((1 + k) / (1 - k)) * Real.tan (s / 2)))
    _ t
  convert hall using 1
  · dsimp [a]
    have hs :
        Real.sqrt ((1 + k) / (1 - k)) ^ 2 =
          (1 + k) / (1 - k) :=
      Real.sq_sqrt (div_nonneg (by linarith [abs_lt.mp hk])
        (by linarith [abs_lt.mp hk]))
    have hkden : 1 - k ≠ 0 := by linarith [abs_lt.mp hk]
    have hcosden : Real.cos (t / 2) ≠ 0 := hcos
    have htanEq :
        Real.tan (t / 2) = Real.sin (t / 2) / Real.cos (t / 2) :=
      Real.tan_eq_sin_div_cos _
    have hsin2 :
        Real.sin (t / 2) ^ 2 + Real.cos (t / 2) ^ 2 = 1 := by
      simpa [add_comm] using Real.sin_sq_add_cos_sq (t / 2)
    have hcost :
        Real.cos t =
          Real.cos (t / 2) ^ 2 - Real.sin (t / 2) ^ 2 := by
      calc
        Real.cos t = Real.cos (2 * (t / 2)) := by congr 1 <;> ring
        _ = Real.cos (t / 2) ^ 2 - Real.sin (t / 2) ^ 2 := by
          rw [Real.cos_two_mul]
          nlinarith
    have hdenEq :
        1 - k * (Real.cos (t / 2) ^ 2 - Real.sin (t / 2) ^ 2) =
          (1 - k) * Real.cos (t / 2) ^ 2 +
            (1 + k) * Real.sin (t / 2) ^ 2 := by
      nlinarith
    rw [mul_pow, hs, htanEq, div_pow]
    rw [sqrt_one_sub_sq_eq k hk, hcost]
    rw [hdenEq]
    field_simp [hkden, hcosden]

private theorem sqrt_ratio_mul_neg_eq_one (k : ℝ) (hk : |k| < 1) :
    Real.sqrt ((1 + k) / (1 - k)) *
        Real.sqrt ((1 - k) / (1 + k)) = 1 := by
  have hk' := abs_lt.mp hk
  have h₁ : 0 ≤ (1 + k) / (1 - k) :=
    (div_pos (by linarith) (by linarith)).le
  have h₂ : 0 ≤ (1 - k) / (1 + k) :=
    (div_pos (by linarith) (by linarith)).le
  have hk₁ : 1 - k ≠ 0 := by linarith
  have hk₂ : 1 + k ≠ 0 := by linarith
  have hprod :
      (Real.sqrt ((1 + k) / (1 - k)) *
          Real.sqrt ((1 - k) / (1 + k))) ^ 2 = 1 := by
    rw [mul_pow, Real.sq_sqrt h₁, Real.sq_sqrt h₂]
    field_simp [hk₁, hk₂]
  have hnonneg :
      0 ≤ Real.sqrt ((1 + k) / (1 - k)) *
        Real.sqrt ((1 - k) / (1 + k)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  apply (sq_eq_sq₀ hnonneg (by norm_num)).mp
  simpa using hprod

private theorem xOfT_neg_involutive (k t : ℝ) (hk : |k| < 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) Real.pi) :
    xOfT k (xOfT (-k) t) = t := by
  have htHalf :
      t / 2 ∈ Set.Ioo (-(Real.pi / 2) : ℝ) (Real.pi / 2) := by
    exact
      ⟨by linarith [ht.1, Real.pi_pos],
        (div_lt_div_iff_of_pos_right (by norm_num)).2 ht.2⟩
  unfold xOfT
  rw [show
      (2 * Real.arctan
        (Real.sqrt ((1 + -k) / (1 - -k)) * Real.tan (t / 2))) / 2 =
        Real.arctan
          (Real.sqrt ((1 - k) / (1 + k)) * Real.tan (t / 2)) by
      congr 1 <;> ring]
  rw [Real.tan_arctan]
  have hmul :
      Real.sqrt ((1 + k) / (1 - k)) *
          (Real.sqrt ((1 - k) / (1 + k)) * Real.tan (t / 2)) =
        Real.tan (t / 2) := by
    rw [← mul_assoc, sqrt_ratio_mul_neg_eq_one k hk, one_mul]
  rw [hmul, Real.arctan_tan htHalf.1 htHalf.2]
  ring

private theorem xOfT_image_Ioo (k : ℝ) (hk : |k| < 1) :
    xOfT k '' Set.Ioo (0 : ℝ) Real.pi =
      Set.Ioo (0 : ℝ) Real.pi := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact xOfT_mem_Ioo k t hk ht
  · intro hx
    refine ⟨xOfT (-k) x, ?_, ?_⟩
    · apply xOfT_mem_Ioo
      · simpa only [abs_neg] using hk
      · exact hx
    · exact xOfT_neg_involutive k x hk hx

private theorem xOfT_injOn (k : ℝ) (hk : |k| < 1) :
    Set.InjOn (xOfT k) (Set.Ioo (0 : ℝ) Real.pi) := by
  intro x hx y hy hxy
  have h := congrArg (xOfT (-k)) hxy
  have hxinv : xOfT (-k) (xOfT k x) = x := by
    simpa only [neg_neg] using
      xOfT_neg_involutive (-k) x (by simpa only [abs_neg] using hk) hx
  have hyinv : xOfT (-k) (xOfT k y) = y := by
    simpa only [neg_neg] using
      xOfT_neg_involutive (-k) y (by simpa only [abs_neg] using hk) hy
  rw [hxinv, hyinv] at h
  exact h

private theorem transformed_rpow_identity (A D s n : ℝ)
    (hA : 0 < A) (hD : 0 < D) (hs : 0 < s) :
    |Real.sqrt A / D| *
        (Real.rpow (Real.sqrt A * s / D) (n - 1) /
          Real.rpow (A / D) n) =
      Real.rpow A (-n / 2) * Real.rpow s (n - 1) := by
  have hS : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hSA : Real.sqrt A = Real.rpow A (1 / 2) :=
    Real.sqrt_eq_rpow A
  have hSr :
      Real.rpow (Real.sqrt A) (n - 1) =
        Real.rpow A ((n - 1) / 2) := by
    rw [hSA]
    calc
      Real.rpow (Real.rpow A (1 / 2)) (n - 1) =
          Real.rpow A ((1 / 2) * (n - 1)) :=
        (Real.rpow_mul hA.le (1 / 2) (n - 1)).symm
      _ = Real.rpow A ((n - 1) / 2) := by congr 1 <;> ring
  have hSprod :
      Real.sqrt A * Real.rpow (Real.sqrt A) (n - 1) =
        Real.rpow A (n / 2) := by
    calc
      Real.sqrt A * Real.rpow (Real.sqrt A) (n - 1) =
          Real.rpow A (1 / 2) * Real.rpow A ((n - 1) / 2) := by
        rw [hSr, hSA]
      _ = Real.rpow A (1 / 2 + (n - 1) / 2) :=
        (Real.rpow_add hA (1 / 2) ((n - 1) / 2)).symm
      _ = Real.rpow A (n / 2) := by congr 1 <;> ring
  have hDprod :
      D * Real.rpow D (n - 1) = Real.rpow D n := by
    calc
      D * Real.rpow D (n - 1) =
          Real.rpow D 1 * Real.rpow D (n - 1) := by
        exact congrArg (fun z => z * Real.rpow D (n - 1))
          (Real.rpow_one D).symm
      _ = Real.rpow D (1 + (n - 1)) :=
        (Real.rpow_add hD 1 (n - 1)).symm
      _ = Real.rpow D n := by congr 1 <;> ring
  have hAprod :
      Real.rpow A (-n / 2) * Real.rpow A n =
        Real.rpow A (n / 2) := by
    calc
      Real.rpow A (-n / 2) * Real.rpow A n =
          Real.rpow A (-n / 2 + n) :=
        (Real.rpow_add hA (-n / 2) n).symm
      _ = Real.rpow A (n / 2) := by congr 1 <;> ring
  rw [abs_of_pos (div_pos hS hD)]
  have hdiv₁ :
      Real.rpow (Real.sqrt A * s / D) (n - 1) =
        Real.rpow (Real.sqrt A * s) (n - 1) /
          Real.rpow D (n - 1) :=
    Real.div_rpow (mul_nonneg hS.le hs.le) hD.le (n - 1)
  have hmul₁ :
      Real.rpow (Real.sqrt A * s) (n - 1) =
        Real.rpow (Real.sqrt A) (n - 1) *
          Real.rpow s (n - 1) :=
    Real.mul_rpow hS.le hs.le
  have hdiv₂ :
      Real.rpow (A / D) n =
        Real.rpow A n / Real.rpow D n :=
    Real.div_rpow hA.le hD.le n
  rw [hdiv₁, hmul₁, hdiv₂]
  have hDn : Real.rpow D n ≠ 0 := (Real.rpow_pos_of_pos hD _).ne'
  have hDnm : Real.rpow D (n - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hD _).ne'
  have hAn : Real.rpow A n ≠ 0 := (Real.rpow_pos_of_pos hA _).ne'
  have hneg :
      Real.rpow A (-n / 2) = Real.rpow A (-(n / 2)) := by
    congr 1 <;> ring
  field_simp [hDn, hDnm, hAn]
  calc
    Real.sqrt A * Real.rpow (Real.sqrt A) (n - 1) *
          Real.rpow s (n - 1) * Real.rpow D n =
        Real.rpow A (n / 2) * Real.rpow s (n - 1) *
          Real.rpow D n := by rw [hSprod]
    _ = (D * Real.rpow D (n - 1)) * Real.rpow s (n - 1) *
          (Real.rpow A (-n / 2) * Real.rpow A n) := by
      rw [hDprod, hAprod]
      ring
    _ = D * Real.rpow s (n - 1) * Real.rpow D (n - 1) *
          Real.rpow A n * Real.rpow A (-(n / 2)) := by
      rw [← hneg]
      ring

private theorem one_sub_k_cos_pos (k t : ℝ) (hk : |k| < 1) :
    0 < 1 - k * Real.cos t := by
  have hcos : |Real.cos t| ≤ 1 := Real.abs_cos_le_one t
  have hprod : k * Real.cos t < 1 := by
    calc
      k * Real.cos t ≤ |k * Real.cos t| := le_abs_self _
      _ = |k| * |Real.cos t| := abs_mul _ _
      _ ≤ |k| * 1 := mul_le_mul_of_nonneg_left hcos (abs_nonneg k)
      _ < 1 := by simpa using hk
  linarith

private theorem transformed_mainIntegrand (k n t : ℝ)
    (hk₀ : 0 < |k|) (hk : |k| < 1)
    (ht : t ∈ Set.Ioo (0 : ℝ) Real.pi) :
    |Real.sqrt (1 - k ^ 2) / (1 - k * Real.cos t)| *
        mainIntegrand k n (xOfT k t) =
      Real.rpow (1 - k ^ 2) (-n / 2) *
        Real.rpow (Real.sin t) (n - 1) := by
  have hk' := abs_lt.mp hk
  have hA : 0 < 1 - k ^ 2 := by nlinarith
  have hD : 0 < 1 - k * Real.cos t := one_sub_k_cos_pos k t hk
  have hs : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  unfold mainIntegrand
  rw [gap2 k t hk₀ hk ht, gap4 k t hk₀ hk ht]
  exact transformed_rpow_identity
    (1 - k ^ 2) (1 - k * Real.cos t) (Real.sin t) n hA hD hs

theorem gap6 (k n : ℝ)
    (hk₀ : 0 < |k|) (hk : |k| < 1) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..Real.pi, mainIntegrand k n x) =
      Real.rpow (1 - k ^ 2) (-n / 2) *
        ∫ t in (0 : ℝ)..Real.pi,
          Real.rpow (Real.sin t) (n - 1) := by
  let f' : ℝ → ℝ := fun t =>
    Real.sqrt (1 - k ^ 2) / (1 - k * Real.cos t)
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) Real.pi,
        HasDerivWithinAt (xOfT k) (f' t)
          (Set.Ioo (0 : ℝ) Real.pi) t := by
    intro t ht
    exact (gap5 k t hk₀ hk ht).hasDerivWithinAt
  have hchange :=
    integral_image_eq_integral_abs_deriv_smul
      (s := Set.Ioo (0 : ℝ) Real.pi)
      measurableSet_Ioo hderiv (xOfT_injOn k hk) (mainIntegrand k n)
  rw [xOfT_image_Ioo k hk] at hchange
  simp only [smul_eq_mul] at hchange
  rw [intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_Ioc_eq_integral_Ioo]
  rw [hchange, ← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  exact transformed_mainIntegrand k n t hk₀ hk ht

private theorem sin_rpow_eq_half_product (n t : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Real.rpow (Real.sin t) (n - 1) =
      Real.rpow 2 (n - 1) *
        (Real.rpow (Real.sin (t / 2)) (n - 1) *
          Real.rpow (Real.cos (t / 2)) (n - 1)) := by
  have htHalf : 0 < t / 2 :=
    half_pos ht.1
  have htHalfPi : t / 2 < Real.pi :=
    ((div_lt_div_iff_of_pos_right (by norm_num)).2 ht.2).trans
      (half_lt_self Real.pi_pos)
  have hsin : 0 ≤ Real.sin (t / 2) :=
    (Real.sin_pos_of_pos_of_lt_pi htHalf htHalfPi).le
  have hhalfIoo :
      t / 2 ∈ Set.Ioo (-(Real.pi / 2) : ℝ) (Real.pi / 2) :=
    ⟨by linarith [ht.1, Real.pi_pos],
      (div_lt_div_iff_of_pos_right (by norm_num)).2 ht.2⟩
  have hcos : 0 ≤ Real.cos (t / 2) :=
    (Real.cos_pos_of_mem_Ioo hhalfIoo).le
  have hsinEq :
      Real.sin t =
        2 * (Real.sin (t / 2) * Real.cos (t / 2)) := by
    calc
      Real.sin t = Real.sin (2 * (t / 2)) := by congr 1 <;> ring
      _ = 2 * Real.sin (t / 2) * Real.cos (t / 2) :=
        Real.sin_two_mul _
      _ = 2 * (Real.sin (t / 2) * Real.cos (t / 2)) := by ring
  have hmul₁ :
      Real.rpow
          (2 * (Real.sin (t / 2) * Real.cos (t / 2))) (n - 1) =
        Real.rpow 2 (n - 1) *
          Real.rpow (Real.sin (t / 2) * Real.cos (t / 2)) (n - 1) :=
    Real.mul_rpow (by norm_num) (mul_nonneg hsin hcos)
  have hmul₂ :
      Real.rpow (Real.sin (t / 2) * Real.cos (t / 2)) (n - 1) =
        Real.rpow (Real.sin (t / 2)) (n - 1) *
          Real.rpow (Real.cos (t / 2)) (n - 1) :=
    Real.mul_rpow hsin hcos
  rw [hsinEq, hmul₁, hmul₂]

theorem gap7 (k n : ℝ)
    (hk₀ : 0 < |k|) (hk : |k| < 1) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..Real.pi, mainIntegrand k n x) =
      Real.rpow 2 (n - 1) * Real.rpow (1 - k ^ 2) (-n / 2) *
        ∫ t in (0 : ℝ)..Real.pi,
          Real.rpow (Real.sin (t / 2)) (n - 1) *
            Real.rpow (Real.cos (t / 2)) (n - 1) := by
  have hint :
      (∫ t in (0 : ℝ)..Real.pi,
          Real.rpow (Real.sin t) (n - 1)) =
        Real.rpow 2 (n - 1) *
          ∫ t in (0 : ℝ)..Real.pi,
            Real.rpow (Real.sin (t / 2)) (n - 1) *
              Real.rpow (Real.cos (t / 2)) (n - 1) := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le,
      integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le Real.pi_pos.le,
      integral_Ioc_eq_integral_Ioo,
      ← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    exact sin_rpow_eq_half_product n t ht
  rw [gap6 k n hk₀ hk hn, hint]
  ring

private theorem sin_half_image_Ioo :
    (fun t : ℝ => Real.sin (t / 2)) '' Set.Ioo (0 : ℝ) Real.pi =
      Set.Ioo (0 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    have htHalf :
        t / 2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨half_pos ht.1,
        (div_lt_div_iff_of_pos_right (by norm_num)).2 ht.2⟩
    have hmem :
        t / 2 ∈ Set.Icc (-(Real.pi / 2) : ℝ) (Real.pi / 2) :=
      ⟨(by linarith [htHalf.1, Real.pi_pos]), htHalf.2.le⟩
    have hend :
        Real.pi / 2 ∈ Set.Icc (-(Real.pi / 2) : ℝ) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], le_rfl⟩
    exact
      ⟨Real.sin_pos_of_pos_of_lt_pi htHalf.1
          (htHalf.2.trans (half_lt_self Real.pi_pos)),
        by simpa using Real.strictMonoOn_sin hmem hend htHalf.2⟩
  · intro hy
    refine ⟨2 * Real.arcsin y, ?_, ?_⟩
    · exact
        ⟨mul_pos (by norm_num) (Real.arcsin_pos.2 hy.1),
          by linarith [Real.arcsin_lt_pi_div_two.2 hy.2]⟩
    · change Real.sin ((2 * Real.arcsin y) / 2) = y
      rw [show (2 * Real.arcsin y) / 2 = Real.arcsin y by ring]
      exact Real.sin_arcsin (by linarith [hy.1]) hy.2.le

private theorem sin_half_injOn :
    Set.InjOn (fun t : ℝ => Real.sin (t / 2))
      (Set.Ioo (0 : ℝ) Real.pi) := by
  intro x hx y hy hxy
  have hxmem :
      x / 2 ∈ Set.Icc (-(Real.pi / 2) : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hx.1, Real.pi_pos],
      ((div_lt_div_iff_of_pos_right (by norm_num)).2 hx.2).le⟩
  have hymem :
      y / 2 ∈ Set.Icc (-(Real.pi / 2) : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hy.1, Real.pi_pos],
      ((div_lt_div_iff_of_pos_right (by norm_num)).2 hy.2).le⟩
  have hhalf : x / 2 = y / 2 :=
    Real.injOn_sin hxmem hymem hxy
  linarith

private theorem sin_half_change_integrand (n t : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) Real.pi) :
    |Real.cos (t / 2) * (1 / 2)| *
        (2 * Real.rpow (Real.sin (t / 2)) (n - 1) *
          Real.rpow (1 - Real.sin (t / 2) ^ 2) ((n - 2) / 2)) =
      Real.rpow (Real.sin (t / 2)) (n - 1) *
        Real.rpow (Real.cos (t / 2)) (n - 1) := by
  have hhalf :
      t / 2 ∈ Set.Ioo (-(Real.pi / 2) : ℝ) (Real.pi / 2) :=
    ⟨by linarith [ht.1, Real.pi_pos],
      (div_lt_div_iff_of_pos_right (by norm_num)).2 ht.2⟩
  have hcos : 0 < Real.cos (t / 2) :=
    Real.cos_pos_of_mem_Ioo hhalf
  have hsq :
      1 - Real.sin (t / 2) ^ 2 = Real.cos (t / 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
  have hpow :
      Real.rpow (Real.cos (t / 2) ^ 2) ((n - 2) / 2) =
        Real.rpow (Real.cos (t / 2)) (n - 2) := by
    have hnat :
        Real.rpow (Real.cos (t / 2)) (2 : ℝ) =
          Real.cos (t / 2) ^ (2 : ℕ) :=
      Real.rpow_natCast _ 2
    rw [← hnat]
    calc
      Real.rpow (Real.rpow (Real.cos (t / 2)) 2) ((n - 2) / 2) =
          Real.rpow (Real.cos (t / 2)) (2 * ((n - 2) / 2)) :=
        (Real.rpow_mul hcos.le 2 ((n - 2) / 2)).symm
      _ = Real.rpow (Real.cos (t / 2)) (n - 2) := by
        congr 1 <;> ring
  have hmul :
      Real.cos (t / 2) *
          Real.rpow (Real.cos (t / 2)) (n - 2) =
        Real.rpow (Real.cos (t / 2)) (n - 1) := by
    calc
      Real.cos (t / 2) *
          Real.rpow (Real.cos (t / 2)) (n - 2) =
        Real.rpow (Real.cos (t / 2)) 1 *
          Real.rpow (Real.cos (t / 2)) (n - 2) := by
            exact congrArg
              (fun z => z * Real.rpow (Real.cos (t / 2)) (n - 2))
              (Real.rpow_one (Real.cos (t / 2))).symm
      _ = Real.rpow (Real.cos (t / 2)) (1 + (n - 2)) :=
        (Real.rpow_add hcos 1 (n - 2)).symm
      _ = Real.rpow (Real.cos (t / 2)) (n - 1) := by
        congr 1 <;> ring
  rw [abs_of_pos (mul_pos hcos (by norm_num)), hsq, hpow]
  rw [show
      Real.cos (t / 2) * (1 / 2) *
          (2 * Real.rpow (Real.sin (t / 2)) (n - 1) *
            Real.rpow (Real.cos (t / 2)) (n - 2)) =
        Real.rpow (Real.sin (t / 2)) (n - 1) *
          (Real.cos (t / 2) *
            Real.rpow (Real.cos (t / 2)) (n - 2)) by ring,
    hmul]

theorem gap8 (k n : ℝ)
    (hk₀ : 0 < |k|) (hk : |k| < 1) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..Real.pi, mainIntegrand k n x) =
      Real.rpow 2 (n - 1) * Real.rpow (1 - k ^ 2) (-n / 2) *
        ∫ u in (0 : ℝ)..1,
          2 * Real.rpow u (n - 1) *
            Real.rpow (1 - u ^ 2) ((n - 2) / 2) := by
  rw [gap7 k n hk₀ hk hn]
  let g : ℝ → ℝ := fun u =>
    2 * Real.rpow u (n - 1) *
      Real.rpow (1 - u ^ 2) ((n - 2) / 2)
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) Real.pi,
        HasDerivWithinAt (fun s : ℝ => Real.sin (s / 2))
          (Real.cos (t / 2) * (1 / 2))
          (Set.Ioo (0 : ℝ) Real.pi) t := by
    intro t ht
    simpa only [Function.comp_apply, id_eq] using
      ((Real.hasDerivAt_sin (t / 2)).comp t
        ((hasDerivAt_id t).div_const 2)).hasDerivWithinAt
  have hchange :=
    integral_image_eq_integral_abs_deriv_smul
      (s := Set.Ioo (0 : ℝ) Real.pi)
      measurableSet_Ioo hderiv sin_half_injOn g
  rw [sin_half_image_Ioo] at hchange
  simp only [smul_eq_mul] at hchange
  have hint :
      (∫ t in (0 : ℝ)..Real.pi,
          Real.rpow (Real.sin (t / 2)) (n - 1) *
            Real.rpow (Real.cos (t / 2)) (n - 1)) =
        ∫ u in (0 : ℝ)..1, g u := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le,
      integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le (by norm_num),
      integral_Ioc_eq_integral_Ioo,
      hchange]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    exact (sin_half_change_integrand n t ht).symm
  rw [hint]

private theorem square_image_Ioo_zero_one :
    (fun u : ℝ => u ^ 2) '' Set.Ioo (0 : ℝ) 1 =
      Set.Ioo (0 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact
      ⟨sq_pos_of_pos hu.1,
        by simpa using (sq_lt_sq₀ hu.1.le (by norm_num : (0 : ℝ) ≤ 1)).2 hu.2⟩
  · intro hy
    refine ⟨Real.sqrt y, ?_, ?_⟩
    · exact
        ⟨Real.sqrt_pos.2 hy.1,
          (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
            (by simpa using hy.2)⟩
    · exact Real.sq_sqrt hy.1.le

private theorem square_injOn_Ioo_zero_one :
    Set.InjOn (fun u : ℝ => u ^ 2) (Set.Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  exact (sq_eq_sq_iff_eq_or_eq_neg).mp hxy |>.resolve_right
    (by intro hneg; nlinarith [hx.1, hy.1])

private theorem square_change_integrand_3858 (n u : ℝ)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    |2 * u| *
        (Real.rpow (u ^ 2) ((n - 2) / 2) *
          Real.rpow (1 - u ^ 2) ((n - 2) / 2)) =
      2 * Real.rpow u (n - 1) *
        Real.rpow (1 - u ^ 2) ((n - 2) / 2) := by
  have hpow :
      Real.rpow (u ^ 2) ((n - 2) / 2) =
        Real.rpow u (n - 2) := by
    have hnat : Real.rpow u (2 : ℝ) = u ^ (2 : ℕ) :=
      Real.rpow_natCast _ 2
    rw [← hnat]
    calc
      Real.rpow (Real.rpow u 2) ((n - 2) / 2) =
          Real.rpow u (2 * ((n - 2) / 2)) :=
        (Real.rpow_mul hu.1.le 2 ((n - 2) / 2)).symm
      _ = Real.rpow u (n - 2) := by congr 1 <;> ring
  have hmul :
      u * Real.rpow u (n - 2) = Real.rpow u (n - 1) := by
    calc
      u * Real.rpow u (n - 2) =
          Real.rpow u 1 * Real.rpow u (n - 2) := by
        exact congrArg (fun z => z * Real.rpow u (n - 2))
          (Real.rpow_one u).symm
      _ = Real.rpow u (1 + (n - 2)) :=
        (Real.rpow_add hu.1 1 (n - 2)).symm
      _ = Real.rpow u (n - 1) := by congr 1 <;> ring
  rw [abs_of_pos (mul_pos (by norm_num) hu.1), hpow]
  rw [show
      2 * u *
          (Real.rpow u (n - 2) *
            Real.rpow (1 - u ^ 2) ((n - 2) / 2)) =
        2 * (u * Real.rpow u (n - 2)) *
          Real.rpow (1 - u ^ 2) ((n - 2) / 2) by ring,
    hmul]

theorem gap9 (k n : ℝ)
    (hk₀ : 0 < |k|) (hk : |k| < 1) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..Real.pi, mainIntegrand k n x) =
      Real.rpow 2 (n - 1) * Real.rpow (1 - k ^ 2) (-n / 2) *
        ∫ y in (0 : ℝ)..1,
          Real.rpow y ((n - 2) / 2) *
            Real.rpow (1 - y) ((n - 2) / 2) := by
  rw [gap8 k n hk₀ hk hn]
  let g : ℝ → ℝ := fun y =>
    Real.rpow y ((n - 2) / 2) *
      Real.rpow (1 - y) ((n - 2) / 2)
  have hderiv :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivWithinAt (fun s : ℝ => s ^ 2) (2 * u)
          (Set.Ioo (0 : ℝ) 1) u := by
    intro u hu
    simpa [mul_comm] using ((hasDerivAt_id u).pow 2).hasDerivWithinAt
  have hchange :=
    integral_image_eq_integral_abs_deriv_smul
      (s := Set.Ioo (0 : ℝ) 1)
      measurableSet_Ioo hderiv square_injOn_Ioo_zero_one g
  rw [square_image_Ioo_zero_one] at hchange
  simp only [smul_eq_mul] at hchange
  have hint :
      (∫ u in (0 : ℝ)..1,
          2 * Real.rpow u (n - 1) *
            Real.rpow (1 - u ^ 2) ((n - 2) / 2)) =
        ∫ y in (0 : ℝ)..1, g y := by
    rw [intervalIntegral.integral_of_le (by norm_num),
      integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le (by norm_num),
      integral_Ioc_eq_integral_Ioo,
      hchange]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    exact (square_change_integrand_3858 n u hu).symm
  rw [hint]

theorem gap10 (k n : ℝ)
    (hk₀ : 0 < |k|) (hk : |k| < 1) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..Real.pi, mainIntegrand k n x) =
      Real.rpow 2 (n - 1) * Real.rpow (1 - k ^ 2) (-n / 2) *
        betaFn (n / 2) (n / 2) := by
  rw [gap9 k n hk₀ hk hn]
  unfold betaFn
  ring_nf

theorem gap11 (n : ℝ) (hn : 0 < n) :
    0 < n := by
  exact hn

end

end ProofGap.Exercise3858
