import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1401

noncomputable section
open Filter
open scoped Topology

def sixthRoot (x : ℝ) := Real.rpow x (1 / 6 : ℝ)
def original (x : ℝ) :=
  sixthRoot (x ^ 6 + x ^ 5) - sixthRoot (x ^ 6 - x ^ 5)
def normalized (x : ℝ) :=
  x * (Real.rpow (1 + 1 / x) (1 / 6 : ℝ) -
    Real.rpow (1 - 1 / x) (1 / 6 : ℝ))
def leadingStage (x : ℝ) := (1 / 3 : ℝ) + 1 / x

private theorem reciprocalAtTop1401 :
    Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
  simpa [one_div] using
    (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0))

private theorem reciprocalAtTopPunctured1401 :
    Tendsto (fun x : ℝ => 1 / x) atTop (𝓝[≠] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨reciprocalAtTop1401, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp [hx.ne']

private theorem normalizedTendsto1401 :
    Tendsto normalized atTop (nhds (1 / 3 : ℝ)) := by
  have hf : HasDerivAt
      (fun u : ℝ => Real.rpow u (1 / 6 : ℝ)) (1 / 6 : ℝ) 1 := by
    simpa using
      (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := (1 / 6 : ℝ))
        (Or.inl (by norm_num : (1 : ℝ) ≠ 0)))
  have hp : HasDerivAt (fun t : ℝ => 1 + t) 1 0 := by
    simpa using
      (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add
        (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ))
  have hm : HasDerivAt (fun t : ℝ => 1 - t) (-1) 0 := by
    simpa using
      (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub
        (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ))
  have hfplus : HasDerivAt
      (fun u : ℝ => Real.rpow u (1 / 6 : ℝ)) (1 / 6 : ℝ)
        ((fun t : ℝ => 1 + t) 0) := by
    simpa using hf
  have hfminus : HasDerivAt
      (fun u : ℝ => Real.rpow u (1 / 6 : ℝ)) (1 / 6 : ℝ)
        ((fun t : ℝ => 1 - t) 0) := by
    simpa using hf
  have hdp : HasDerivAt
      (fun t : ℝ => Real.rpow (1 + t) (1 / 6 : ℝ)) (1 / 6 : ℝ) 0 := by
    simpa [Function.comp_def] using hfplus.comp 0 hp
  have hdm : HasDerivAt
      (fun t : ℝ => Real.rpow (1 - t) (1 / 6 : ℝ)) (-(1 / 6 : ℝ)) 0 := by
    simpa [Function.comp_def] using hfminus.comp 0 hm
  have hd : HasDerivAt
      (fun t : ℝ =>
        Real.rpow (1 + t) (1 / 6 : ℝ) -
          Real.rpow (1 - t) (1 / 6 : ℝ))
      (1 / 3 : ℝ) 0 := by
    convert hdp.sub hdm using 1 <;> norm_num
  have hs := hd.tendsto_slope_zero.comp reciprocalAtTopPunctured1401
  change Tendsto
    (fun x : ℝ => x *
      (Real.rpow (1 + 1 / x) (1 / 6 : ℝ) -
        Real.rpow (1 - 1 / x) (1 / 6 : ℝ)))
    atTop (nhds (1 / 3 : ℝ))
  simpa [Function.comp_def, one_div] using hs

private theorem originalEventuallyEqNormalized1401 :
    original =ᶠ[atTop] normalized := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hxpos : 0 < x := lt_trans (by norm_num) hx
  have hx0 : 0 ≤ x := hxpos.le
  have hxne : x ≠ 0 := hxpos.ne'
  have hp : 0 < 1 + 1 / x := by
    have hi : 0 < 1 / x := one_div_pos.mpr hxpos
    nlinarith
  have hm : 0 < 1 - 1 / x := by
    have hi : 1 / x < 1 := (div_lt_one hxpos).mpr hx
    nlinarith
  have hadd : x ^ 6 + x ^ 5 = x ^ 6 * (1 + 1 / x) := by
    field_simp [hxne]
  have hsub : x ^ 6 - x ^ 5 = x ^ 6 * (1 - 1 / x) := by
    field_simp [hxne]
  have hroot : Real.rpow (x ^ 6) (1 / 6 : ℝ) = x := by
    change (x ^ 6) ^ (1 / 6 : ℝ) = x
    rw [Real.rpow_def_of_pos (pow_pos hxpos 6)]
    rw [Real.log_pow]
    convert Real.exp_log hxpos using 1 <;> ring
  have hradd :
      Real.rpow (x ^ 6 * (1 + 1 / x)) (1 / 6 : ℝ) =
        Real.rpow (x ^ 6) (1 / 6 : ℝ) *
          Real.rpow (1 + 1 / x) (1 / 6 : ℝ) := by
    change (x ^ 6 * (1 + 1 / x)) ^ (1 / 6 : ℝ) =
      (x ^ 6) ^ (1 / 6 : ℝ) * (1 + 1 / x) ^ (1 / 6 : ℝ)
    exact Real.mul_rpow (pow_nonneg hx0 6) hp.le
  have hrsub :
      Real.rpow (x ^ 6 * (1 - 1 / x)) (1 / 6 : ℝ) =
        Real.rpow (x ^ 6) (1 / 6 : ℝ) *
          Real.rpow (1 - 1 / x) (1 / 6 : ℝ) := by
    change (x ^ 6 * (1 - 1 / x)) ^ (1 / 6 : ℝ) =
      (x ^ 6) ^ (1 / 6 : ℝ) * (1 - 1 / x) ^ (1 / 6 : ℝ)
    exact Real.mul_rpow (pow_nonneg hx0 6) hm.le
  simp only [original, normalized, sixthRoot]
  rw [hadd, hsub, hradd, hrsub, hroot]
  ring

theorem gap1 : Tendsto original atTop (nhds (1 / 3 : ℝ)) := by
  apply normalizedTendsto1401.congr'
  exact originalEventuallyEqNormalized1401.symm
theorem gap2 : Tendsto normalized atTop (nhds (1 / 3 : ℝ)) := by
  exact normalizedTendsto1401
theorem gap3 : Tendsto leadingStage atTop (nhds (1 / 3 : ℝ)) := by
  change Tendsto (fun x : ℝ => (1 / 3 : ℝ) + 1 / x) atTop (nhds (1 / 3 : ℝ))
  have hc : Tendsto (fun _ : ℝ => (1 / 3 : ℝ)) atTop (nhds (1 / 3 : ℝ)) :=
    tendsto_const_nhds
  simpa [one_div] using hc.add reciprocalAtTop1401
theorem gap4 : Tendsto leadingStage atTop (nhds (1 / 3 : ℝ)) := by
  exact gap3
theorem gap5 : Tendsto original atTop (nhds (1 / 3 : ℝ)) := by
  exact gap1

end
end ProofGap.Exercise1401
