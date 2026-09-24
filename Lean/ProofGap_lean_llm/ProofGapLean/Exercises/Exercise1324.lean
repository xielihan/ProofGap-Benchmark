import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1324

noncomputable section
open Filter
open scoped Topology

def punctured (x₀ : ℝ) := nhdsWithin x₀ ({x₀} : Set ℝ)ᶜ
def cubeRoot (x : ℝ) := Real.rpow x (1 / 3 : ℝ)
def original (x : ℝ) :=
  (cubeRoot (Real.tan x) - 1) / (2 * Real.sin x ^ 2 - 1)
def derivativeStage (x : ℝ) :=
  ((1 / (3 * cubeRoot (Real.tan x ^ 2))) * (1 / Real.cos x) ^ 2) /
    (4 * Real.sin x * Real.cos x)

private theorem exercise1324_limits :
    Tendsto original (punctured (Real.pi / 4)) (nhds (1 / 3 : ℝ)) ∧
      Tendsto derivativeStage (punctured (Real.pi / 4)) (nhds (1 / 3 : ℝ)) := by
  let a : ℝ := Real.pi / 4
  let F : ℝ → ℝ := fun x =>
    Real.exp (Real.log (Real.tan x) * (1 / 3 : ℝ)) - 1
  let G : ℝ → ℝ := fun x => 2 * Real.sin x ^ 2 - 1
  have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := by
    positivity
  have hcos : Real.cos a ≠ 0 := by
    dsimp [a]
    rw [Real.cos_pi_div_four]
    positivity
  have htan_lim :
      Tendsto Real.tan (punctured a) (nhds (1 : ℝ)) := by
    have ht : Tendsto Real.tan (punctured a) (nhds (Real.tan a)) := by
      simpa only [punctured] using
        ((Real.hasDerivAt_tan hcos).continuousAt.tendsto.mono_left
          (show nhdsWithin a ({a} : Set ℝ)ᶜ ≤ nhds a from inf_le_left))
    simpa [a, Real.tan_pi_div_four] using ht
  have htan_pos : ∀ᶠ x in punctured a, 0 < Real.tan x := by
    apply htan_lim
    exact isOpen_Ioi.mem_nhds (by norm_num)
  have htan_deriv : HasDerivAt Real.tan 2 a := by
    convert Real.hasDerivAt_tan hcos using 1
    dsimp [a]
    rw [Real.cos_pi_div_four]
    field_simp [hsqrt_ne] <;> nlinarith [hsqrt_sq]
  have hlogtan :
      HasDerivAt (fun x => Real.log (Real.tan x)) 2 a := by
    convert
      (Real.hasDerivAt_log
        (by simpa [a, Real.tan_pi_div_four] using (one_ne_zero : (1 : ℝ) ≠ 0))).comp
        a htan_deriv using 1 <;>
      norm_num [a, Real.tan_pi_div_four]
  have hscaled :
      HasDerivAt
        (fun x => Real.log (Real.tan x) * (1 / 3 : ℝ))
        (2 / 3 : ℝ) a := by
    convert hlogtan.mul_const (1 / 3 : ℝ) using 1 <;> norm_num
  have hexp :
      HasDerivAt
        (fun x => Real.exp (Real.log (Real.tan x) * (1 / 3 : ℝ)))
        (2 / 3 : ℝ) a := by
    convert
      (Real.hasDerivAt_exp
        (Real.log (Real.tan a) * (1 / 3 : ℝ))).comp a hscaled using 1 <;>
      norm_num [a, Real.tan_pi_div_four]
  have hF : HasDerivAt F (2 / 3 : ℝ) a := by
    simpa [F] using hexp.sub_const 1
  have hsin_square :
      HasDerivAt (fun x => Real.sin x ^ 2) 1 a := by
    convert (Real.hasDerivAt_sin a).pow 2 using 1
    dsimp [a]
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    norm_num
    nlinarith [hsqrt_sq]
  have hG : HasDerivAt G 2 a := by
    simpa [G] using (hsin_square.const_mul 2).sub_const 1
  have hFa : F a = 0 := by
    simp [F, a, Real.tan_pi_div_four]
  have hGa : G a = 0 := by
    dsimp [G, a]
    rw [Real.sin_pi_div_four]
    nlinarith [hsqrt_sq]
  constructor
  · have hFslope :
        Tendsto (fun x => (F x - F a) / (x - a))
          (punctured a) (nhds (2 / 3 : ℝ)) := by
      simpa [punctured, div_eq_inv_mul] using
        (hasDerivAt_iff_tendsto_slope.mp hF)
    have hGslope :
        Tendsto (fun x => (G x - G a) / (x - a))
          (punctured a) (nhds (2 : ℝ)) := by
      simpa [punctured, div_eq_inv_mul] using
        (hasDerivAt_iff_tendsto_slope.mp hG)
    have hratio :
        Tendsto
          (fun x => ((F x - F a) / (x - a)) /
            ((G x - G a) / (x - a)))
          (punctured a) (nhds (1 / 3 : ℝ)) := by
      convert hFslope.div hGslope (by norm_num : (2 : ℝ) ≠ 0) using 1 <;>
        norm_num
    have hne : ∀ᶠ x in punctured a, x ≠ a := by
      rw [punctured]
      filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using hx
    have hquot :
        Tendsto (fun x => F x / G x) (punctured a) (nhds (1 / 3 : ℝ)) := by
      apply hratio.congr'
      filter_upwards [hne] with x hx
      rw [hFa, hGa]
      by_cases hgx : G x = 0
      · simp [hgx]
      · have hxa : x - a ≠ 0 := sub_ne_zero.mpr hx
        field_simp [hxa, hgx] <;> ring
    apply hquot.congr'
    filter_upwards [htan_pos] with x hx
    simp only [original, cubeRoot, F, G]
    have hrpow :
        Real.exp (Real.log (Real.tan x) * (1 / 3 : ℝ)) =
          Real.rpow (Real.tan x) (1 / 3 : ℝ) :=
      (Real.rpow_def_of_pos hx (1 / 3 : ℝ)).symm
    exact congrArg
      (fun y : ℝ => (y - 1) / (2 * Real.sin x ^ 2 - 1)) hrpow
  · have hsin_lim :
        Tendsto Real.sin (punctured a) (nhds (Real.sin a)) := by
      simpa [punctured] using
        ((Real.hasDerivAt_sin a).continuousAt.tendsto.mono_left
          (show nhdsWithin a ({a} : Set ℝ)ᶜ ≤ nhds a from inf_le_left))
    have hcos_lim :
        Tendsto Real.cos (punctured a) (nhds (Real.cos a)) := by
      simpa [punctured] using
        ((Real.hasDerivAt_cos a).continuousAt.tendsto.mono_left
          (show nhdsWithin a ({a} : Set ℝ)ᶜ ≤ nhds a from inf_le_left))
    have hsq :
        Tendsto (fun x => Real.tan x ^ 2) (punctured a) (nhds (1 : ℝ)) := by
      simpa using htan_lim.pow 2
    have hlog :
        Tendsto (fun x => Real.log (Real.tan x ^ 2))
          (punctured a) (nhds (0 : ℝ)) := by
      have ht :=
        (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).continuousAt.tendsto.comp hsq
      simpa only [Function.comp_apply, Real.log_one] using ht
    have hscaled_lim :
        Tendsto
          (fun x => Real.log (Real.tan x ^ 2) * (1 / 3 : ℝ))
          (punctured a) (nhds (0 : ℝ)) := by
      convert hlog.mul_const (1 / 3 : ℝ) using 1 <;> norm_num
    have hcube_exp :
        Tendsto
          (fun x => Real.exp
            (Real.log (Real.tan x ^ 2) * (1 / 3 : ℝ)))
          (punctured a) (nhds (1 : ℝ)) := by
      convert (Real.hasDerivAt_exp 0).continuousAt.tendsto.comp hscaled_lim using 1 <;>
        norm_num
    have hcube :
        Tendsto (fun x => cubeRoot (Real.tan x ^ 2))
          (punctured a) (nhds (1 : ℝ)) := by
      apply hcube_exp.congr'
      filter_upwards [htan_pos] with x hx
      simp only [cubeRoot]
      exact (Real.rpow_def_of_pos (pow_pos hx 2) (1 / 3 : ℝ)).symm
    have hone :
        Tendsto (fun _ : ℝ => (1 : ℝ)) (punctured a) (nhds (1 : ℝ)) :=
      tendsto_const_nhds
    have hthree :
        Tendsto (fun x => 3 * cubeRoot (Real.tan x ^ 2))
          (punctured a) (nhds (3 : ℝ)) := by
      convert (tendsto_const_nhds.mul hcube) using 1 <;> norm_num
    have hA :
        Tendsto (fun x => 1 / (3 * cubeRoot (Real.tan x ^ 2)))
          (punctured a) (nhds (1 / 3 : ℝ)) := by
      exact hone.div hthree (by norm_num)
    have hB :
        Tendsto (fun x => (1 / Real.cos x) ^ 2)
          (punctured a) (nhds ((1 / Real.cos a) ^ 2)) := by
      exact (hone.div hcos_lim hcos).pow 2
    have hfour :
        Tendsto (fun _ : ℝ => (4 : ℝ)) (punctured a) (nhds (4 : ℝ)) :=
      tendsto_const_nhds
    have hC :
        Tendsto (fun x => 4 * Real.sin x * Real.cos x)
          (punctured a) (nhds (4 * Real.sin a * Real.cos a)) := by
      exact (hfour.mul hsin_lim).mul hcos_lim
    have hden_ne : 4 * Real.sin a * Real.cos a ≠ 0 := by
      dsimp [a]
      rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
      positivity
    have hstage := (hA.mul hB).div hC hden_ne
    have hlimitval :
        ((1 / 3 : ℝ) * (1 / Real.cos a) ^ 2) /
            (4 * Real.sin a * Real.cos a) = 1 / 3 := by
      dsimp [a]
      rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
      field_simp [hsqrt_ne] <;> nlinarith [hsqrt_sq]
    simpa only [derivativeStage, hlimitval] using hstage

theorem gap1 :
    Tendsto original (punctured (Real.pi / 4)) (nhds (1 / 3 : ℝ)) := by
  exact exercise1324_limits.1
theorem gap2 :
    Tendsto derivativeStage (punctured (Real.pi / 4)) (nhds (1 / 3 : ℝ)) := by
  exact exercise1324_limits.2
theorem gap3 :
    Tendsto original (punctured (Real.pi / 4)) (nhds (1 / 3 : ℝ)) := by
  exact gap1

end
end ProofGap.Exercise1324
