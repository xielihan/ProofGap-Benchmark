import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise3856

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

private theorem trig_change_integrand (m n x : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |Real.cos x| *
        (Real.rpow (Real.sin x) m *
          Real.rpow (1 - Real.sin x ^ 2) ((n - 1) / 2)) =
      Real.rpow (Real.sin x) m * Real.rpow (Real.cos x) n := by
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo
      ⟨(neg_neg_of_pos (by positivity : 0 < Real.pi / 2)).trans hx.1,
        hx.2⟩
  have hcos0 : 0 ≤ Real.cos x := hcos.le
  have hsq : 1 - Real.sin x ^ 2 = Real.cos x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [abs_of_pos hcos, hsq]
  have hpow :
      Real.rpow (Real.cos x ^ 2) ((n - 1) / 2) =
        Real.rpow (Real.cos x) (n - 1) := by
    have hnat :
        Real.rpow (Real.cos x) (2 : ℝ) = Real.cos x ^ (2 : ℕ) :=
      Real.rpow_natCast _ 2
    rw [← hnat]
    have hmul :
        Real.rpow (Real.rpow (Real.cos x) 2) ((n - 1) / 2) =
          Real.rpow (Real.cos x) (2 * ((n - 1) / 2)) :=
      (Real.rpow_mul hcos0 2 ((n - 1) / 2)).symm
    rw [hmul]
    congr 1
    ring
  rw [hpow]
  have hadd :
      Real.rpow (Real.cos x) (n - 1) * Real.cos x =
        Real.rpow (Real.cos x) n := by
    have hone : Real.rpow (Real.cos x) 1 = Real.cos x :=
      Real.rpow_one _
    calc
      Real.rpow (Real.cos x) (n - 1) * Real.cos x =
          Real.rpow (Real.cos x) (n - 1) *
            Real.rpow (Real.cos x) 1 := by rw [hone]
      _ = Real.rpow (Real.cos x) ((n - 1) + 1) :=
        (Real.rpow_add hcos (n - 1) 1).symm
      _ = Real.rpow (Real.cos x) n := by congr 1 <;> ring
  calc
    Real.cos x *
        (Real.rpow (Real.sin x) m * Real.rpow (Real.cos x) (n - 1)) =
      Real.rpow (Real.sin x) m *
        (Real.rpow (Real.cos x) (n - 1) * Real.cos x) := by ring
    _ = Real.rpow (Real.sin x) m * Real.rpow (Real.cos x) n := by
      rw [hadd]

theorem gap1 (m n : ℝ) (hm : -1 < m) (hn : -1 < n) :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        Real.rpow (Real.sin x) m * Real.rpow (Real.cos x) n) =
      ∫ t in (0 : ℝ)..1,
        Real.rpow t m *
          Real.rpow (1 - t ^ 2) ((n - 1) / 2) := by
  let g : ℝ → ℝ := fun t =>
    Real.rpow t m * Real.rpow (1 - t ^ 2) ((n - 1) / 2)
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
  change
    Real.rpow (Real.sin x) m * Real.rpow (Real.cos x) n =
      |Real.cos x| *
        (Real.rpow (Real.sin x) m *
          Real.rpow (1 - Real.sin x ^ 2) ((n - 1) / 2))
  exact (trig_change_integrand m n x hx).symm

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

private theorem square_change_integrand (m n t : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (1 / 2 : ℝ) *
        (|2 * t| *
          (Real.rpow (t ^ 2) ((m - 1) / 2) *
            Real.rpow (1 - t ^ 2) ((n - 1) / 2))) =
      Real.rpow t m * Real.rpow (1 - t ^ 2) ((n - 1) / 2) := by
  have ht0 : 0 ≤ t := ht.1.le
  have hpow :
      Real.rpow (t ^ 2) ((m - 1) / 2) =
        Real.rpow t (m - 1) := by
    have hnat : Real.rpow t (2 : ℝ) = t ^ (2 : ℕ) :=
      Real.rpow_natCast _ 2
    rw [← hnat]
    have hmul :
        Real.rpow (Real.rpow t 2) ((m - 1) / 2) =
          Real.rpow t (2 * ((m - 1) / 2)) :=
      (Real.rpow_mul ht0 2 ((m - 1) / 2)).symm
    rw [hmul]
    congr 1
    ring
  rw [abs_of_pos (mul_pos (by norm_num) ht.1), hpow]
  have hadd :
      t * Real.rpow t (m - 1) = Real.rpow t m := by
    have hone : Real.rpow t 1 = t := Real.rpow_one _
    calc
      t * Real.rpow t (m - 1) =
          Real.rpow t 1 * Real.rpow t (m - 1) := by rw [hone]
      _ = Real.rpow t (1 + (m - 1)) :=
        (Real.rpow_add ht.1 1 (m - 1)).symm
      _ = Real.rpow t m := by congr 1 <;> ring
  rw [show (1 / 2 : ℝ) * (2 * t *
      (Real.rpow t (m - 1) *
        Real.rpow (1 - t ^ 2) ((n - 1) / 2))) =
      (t * Real.rpow t (m - 1)) *
        Real.rpow (1 - t ^ 2) ((n - 1) / 2) by ring, hadd]

theorem gap2 (m n : ℝ) (hm : -1 < m) (hn : -1 < n) :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        Real.rpow (Real.sin x) m * Real.rpow (Real.cos x) n) =
      (1 / 2 : ℝ) *
        ∫ u in (0 : ℝ)..1,
          Real.rpow u ((m - 1) / 2) *
            Real.rpow (1 - u) ((n - 1) / 2) := by
  rw [gap1 m n hm hn]
  let g : ℝ → ℝ := fun u =>
    Real.rpow u ((m - 1) / 2) *
      Real.rpow (1 - u) ((n - 1) / 2)
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
      measurableSet_Ioo
      hderiv
      hinj g
  rw [square_image_Ioo_zero_one] at hchange
  simp only [smul_eq_mul] at hchange
  rw [intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo]
  calc
    (∫ t in Set.Ioo (0 : ℝ) 1,
        Real.rpow t m * Real.rpow (1 - t ^ 2) ((n - 1) / 2)) =
      ∫ t in Set.Ioo (0 : ℝ) 1,
        (1 / 2 : ℝ) *
          (|2 * t| *
            (Real.rpow (t ^ 2) ((m - 1) / 2) *
              Real.rpow (1 - t ^ 2) ((n - 1) / 2))) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro t ht
        exact (square_change_integrand m n t ht).symm
    _ = (1 / 2 : ℝ) *
        ∫ t in Set.Ioo (0 : ℝ) 1,
          |2 * t| *
            (Real.rpow (t ^ 2) ((m - 1) / 2) *
              Real.rpow (1 - t ^ 2) ((n - 1) / 2)) := by
        rw [MeasureTheory.integral_const_mul]
    _ = (1 / 2 : ℝ) *
        ∫ u in Set.Ioo (0 : ℝ) 1,
          Real.rpow u ((m - 1) / 2) *
            Real.rpow (1 - u) ((n - 1) / 2) := by
        rw [hchange]

theorem gap3 (m n : ℝ) (hm : -1 < m) (hn : -1 < n) :
    (1 / 2 : ℝ) *
        (∫ u in (0 : ℝ)..1,
          Real.rpow u ((m - 1) / 2) *
            Real.rpow (1 - u) ((n - 1) / 2)) =
      (1 / 2 : ℝ) * betaFn ((m + 1) / 2) ((n + 1) / 2) := by
  unfold betaFn
  ring_nf

theorem gap4 (m n : ℝ) (hm : -1 < m) (hn : -1 < n) :
    (∫ x in (0 : ℝ)..Real.pi / 2,
        Real.rpow (Real.sin x) m * Real.rpow (Real.cos x) n) =
      (1 / 2 : ℝ) *
        betaFn ((m + 1) / 2) ((n + 1) / 2) := by
  calc
    (∫ x in (0 : ℝ)..Real.pi / 2,
        Real.rpow (Real.sin x) m * Real.rpow (Real.cos x) n) =
        (1 / 2 : ℝ) *
          ∫ u in (0 : ℝ)..1,
            Real.rpow u ((m - 1) / 2) *
              Real.rpow (1 - u) ((n - 1) / 2) := gap2 m n hm hn
    _ = (1 / 2 : ℝ) * betaFn ((m + 1) / 2) ((n + 1) / 2) :=
      gap3 m n hm hn

theorem gap5 (m : ℝ) (hm : -1 < m) :
    -1 < m := by
  exact hm

theorem gap6 (n : ℝ) (hn : -1 < n) :
    -1 < n := by
  exact hn

end

end ProofGap.Exercise3856
