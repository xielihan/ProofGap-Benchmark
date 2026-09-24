import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace ProofGap.Exercise3873

noncomputable section

open Filter MeasureTheory
open scoped Interval

def HasImproperIntegral (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds L)

def improperIntegral (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | HasImproperIntegral a f L}

def gammaIntegrand (q t : ℝ) : ℝ :=
  Real.rpow t (q - 1) * Real.exp (-t)

def stretchedIntegrand (m n x : ℝ) : ℝ :=
  Real.rpow x m * Real.exp (-Real.rpow x n)

private theorem improperIntegral_eq_integral_Ioi {f : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Ioi 0)) :
    improperIntegral 0 f = ∫ x in Set.Ioi 0, f x := by
  have hlim : HasImproperIntegral 0 f (∫ x in Set.Ioi 0, f x) :=
    intervalIntegral_tendsto_integral_Ioi 0 hf tendsto_id
  have hset :
      {L : ℝ | HasImproperIntegral 0 f L} =
        {(∫ x in Set.Ioi 0, f x)} := by
    ext L
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hL
      exact tendsto_nhds_unique hL hlim
    · rintro rfl
      exact hlim
  rw [improperIntegral, hset, csInf_singleton]

private theorem gamma_integrable {q : ℝ} (hq : 0 < q) :
    IntegrableOn (gammaIntegrand q) (Set.Ioi 0) := by
  refine (Real.GammaIntegral_convergent hq).congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp [gammaIntegrand, mul_comm]

private theorem stretched_eq_change (m n x : ℝ) (hn : 0 < n)
    (hx : x ∈ Set.Ioi (0 : ℝ)) :
    stretchedIntegrand m n x =
      (1 / n) *
        ((n * x ^ (n - 1)) *
          gammaIntegrand ((m + 1) / n) (x ^ n)) := by
  have hx0 : 0 ≤ x := le_of_lt hx
  rw [stretchedIntegrand, gammaIntegrand]
  field_simp [hn.ne']
  have hrpow :
      Real.rpow (Real.rpow x n) ((m + 1 - n) / n) =
        Real.rpow x (n * ((m + 1 - n) / n)) :=
    (Real.rpow_mul hx0 n ((m + 1 - n) / n)).symm
  change Real.rpow x m * Real.exp (-Real.rpow x n) =
    Real.rpow x (n - 1) *
      Real.rpow (Real.rpow x n) ((m + 1 - n) / n) *
        Real.exp (-Real.rpow x n)
  rw [hrpow]
  have hrpow_add :
      Real.rpow x (n - 1) *
          Real.rpow x (n * ((m + 1 - n) / n)) =
        Real.rpow x ((n - 1) + n * ((m + 1 - n) / n)) :=
    (Real.rpow_add hx (n - 1) (n * ((m + 1 - n) / n))).symm
  rw [hrpow_add]
  congr 2
  field_simp
  ring

theorem gap1 (m n : ℝ) (hn : 0 < n) (hq : 0 < (m + 1) / n) :
    improperIntegral 0 (stretchedIntegrand m n) =
      1 / n *
        improperIntegral 0 (gammaIntegrand ((m + 1) / n)) := by
  let q := (m + 1) / n
  have hgamma : IntegrableOn (gammaIntegrand q) (Set.Ioi 0) :=
    gamma_integrable hq
  have hchanged :
      IntegrableOn
        (fun x : ℝ =>
          (n * x ^ (n - 1)) * gammaIntegrand q (x ^ n))
        (Set.Ioi 0) := by
    simpa [abs_of_pos hn, smul_eq_mul] using
      (integrableOn_Ioi_comp_rpow_iff (gammaIntegrand q) hn.ne').mpr hgamma
  have hstretched :
      IntegrableOn (stretchedIntegrand m n) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun
      (hchanged.const_mul (1 / n)) ?_ measurableSet_Ioi
    intro x hx
    exact (stretched_eq_change m n x hn hx).symm
  rw [improperIntegral_eq_integral_Ioi hstretched,
    improperIntegral_eq_integral_Ioi hgamma]
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun x hx => stretched_eq_change m n x hn hx)]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  simpa [smul_eq_mul] using
    (MeasureTheory.integral_comp_rpow_Ioi_of_pos
      (g := gammaIntegrand q) hn)

theorem gap2 (n m : ℝ) (hn : 0 < n) (hq : 0 < (m + 1) / n) :
    1 / n *
        improperIntegral 0 (gammaIntegrand ((m + 1) / n)) =
      1 / n * Real.Gamma ((m + 1) / n) := by
  have hgamma :
      IntegrableOn (gammaIntegrand ((m + 1) / n)) (Set.Ioi 0) :=
    gamma_integrable hq
  rw [improperIntegral_eq_integral_Ioi hgamma]
  rw [Real.Gamma_eq_integral hq]
  apply congrArg (fun z : ℝ => (1 / n) * z)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp [gammaIntegrand, mul_comm]

theorem gap3 (m n : ℝ) (hn : 0 < n) (hq : 0 < (m + 1) / n) :
    improperIntegral 0 (stretchedIntegrand m n) =
      1 / n * Real.Gamma ((m + 1) / n) := by
  rw [gap1 m n hn hq]
  exact gap2 n m hn hq

theorem gap4 :
    improperIntegral 0 (fun x => Real.exp (-x ^ 4)) *
        improperIntegral 0 (fun x => x ^ 2 * Real.exp (-x ^ 4)) =
      (1 / 4 : ℝ) * Real.Gamma (1 / 4) *
        ((1 / 4 : ℝ) * Real.Gamma (3 / 4)) := by
  have h0 :=
    gap3 (m := (0 : ℝ)) (n := (4 : ℝ)) (by norm_num) (by norm_num)
  have h2 :=
    gap3 (m := (2 : ℝ)) (n := (4 : ℝ)) (by norm_num) (by norm_num)
  norm_num at h0 h2
  have hf0 :
      (fun x : ℝ => Real.exp (-x ^ 4)) = stretchedIntegrand 0 4 := by
    funext x
    simp [stretchedIntegrand]
  have hf2 :
      (fun x : ℝ => x ^ 2 * Real.exp (-x ^ 4)) =
        stretchedIntegrand 2 4 := by
    funext x
    simp [stretchedIntegrand]
  rw [hf0, hf2, h0, h2]

theorem gap5 :
    (1 / 4 : ℝ) * Real.Gamma (1 / 4) *
        ((1 / 4 : ℝ) * Real.Gamma (3 / 4)) =
      1 / (4 : ℝ) ^ 2 *
        (Real.pi / Real.sin (Real.pi / 4)) := by
  have href := Real.Gamma_mul_Gamma_one_sub (1 / 4 : ℝ)
  have href' :
      Real.Gamma (1 / 4) * Real.Gamma (3 / 4) =
        Real.pi / Real.sin (Real.pi / 4) := by
    rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num,
      show Real.pi * (1 / 4) = Real.pi / 4 by ring] at href
    exact href
  calc
    (1 / 4 : ℝ) * Real.Gamma (1 / 4) *
          ((1 / 4 : ℝ) * Real.Gamma (3 / 4)) =
        (1 / 16 : ℝ) *
          (Real.Gamma (1 / 4) * Real.Gamma (3 / 4)) := by ring
    _ = (1 / 16 : ℝ) * (Real.pi / Real.sin (Real.pi / 4)) := by
      rw [href']
    _ = 1 / (4 : ℝ) ^ 2 *
          (Real.pi / Real.sin (Real.pi / 4)) := by norm_num

theorem gap6 :
    1 / (4 : ℝ) ^ 2 *
        (Real.pi / Real.sin (Real.pi / 4)) =
      Real.pi / (8 * Real.sqrt 2) := by
  rw [Real.sin_pi_div_four]
  have hs : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hs]
  ring

theorem gap7 :
    improperIntegral 0 (fun x => Real.exp (-x ^ 4)) *
        improperIntegral 0 (fun x => x ^ 2 * Real.exp (-x ^ 4)) =
      Real.pi / (8 * Real.sqrt 2) := by
  rw [gap4, gap5, gap6]

theorem gap8 :
    improperIntegral 0 (fun x => Real.exp (-x ^ 4)) *
        improperIntegral 0 (fun x => x ^ 2 * Real.exp (-x ^ 4)) =
      Real.pi / (8 * Real.sqrt 2) := by
  exact gap7

end

end ProofGap.Exercise3873
