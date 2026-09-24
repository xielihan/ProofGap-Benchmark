import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1402

noncomputable section
open Filter
open scoped Topology

def original (x : ℝ) :=
  (x ^ 3 - x ^ 2 + x / 2) * Real.exp (1 / x) -
    Real.sqrt (x ^ 6 + 1)
def leadingStage (x : ℝ) := (1 / 6 : ℝ) + 1 / x

private theorem original_limit :
    Tendsto original atTop (nhds (1 / 6 : ℝ)) := by
  let f : ℝ → ℝ := fun t =>
    (1 - t + t * t / 2) * Real.exp t - 1
  have hf (t : ℝ) :
      HasDerivAt f (t * t / 2 * Real.exp t) t := by
    dsimp only [f]
    convert
      (((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
          (((hasDerivAt_id t).mul (hasDerivAt_id t)).div_const 2)).mul
          (Real.hasDerivAt_exp t)).sub_const 1) using 1 <;>
      simp <;> ring
  have sandwich (t : ℝ) (ht : 0 ≤ t) :
      t ^ 3 / 6 ≤ f t ∧
        f t ≤ Real.exp t * t ^ 3 / 6 := by
    let g : ℝ → ℝ := fun u => f u - u * u * u / 6
    have hg (u : ℝ) :
        HasDerivAt g (u * u / 2 * (Real.exp u - 1)) u := by
      dsimp only [g]
      convert
        (hf u).sub
          ((((hasDerivAt_id u).mul (hasDerivAt_id u)).mul
            (hasDerivAt_id u)).div_const 6) using 1 <;>
        simp <;> ring
    have hgmono : MonotoneOn g (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) ?_ ?_ ?_
      · intro u hu
        exact (hg u).continuousAt.continuousWithinAt
      · intro u hu
        exact (hg u).differentiableAt.differentiableWithinAt
      · intro u hu
        rw [(hg u).deriv]
        have hu0 : 0 ≤ u := interior_subset hu
        have he : 1 ≤ Real.exp u := Real.one_le_exp hu0
        exact mul_nonneg (by positivity) (sub_nonneg.mpr he)
    have hgl :=
      hgmono (by simp : (0 : ℝ) ∈ Set.Ici 0)
        (by simpa : t ∈ Set.Ici 0) ht
    have hf0 : f 0 = 0 := by
      norm_num [f]
    have hl : t ^ 3 / 6 ≤ f t := by
      dsimp only [g] at hgl
      rw [hf0] at hgl
      norm_num at hgl
      nlinarith [hgl]
    let h : ℝ → ℝ := fun u =>
      Real.exp u * (u * u * u) / 6 - f u
    have hh (u : ℝ) :
        HasDerivAt h (Real.exp u * (u * u * u) / 6) u := by
      dsimp only [h]
      convert
        (((Real.hasDerivAt_exp u).mul
          ((((hasDerivAt_id u).mul (hasDerivAt_id u)).mul
            (hasDerivAt_id u)).div_const 6)).sub (hf u)) using 1
      · funext v
        simp <;> ring
      · simp [id]
        ring
    have hhmono : MonotoneOn h (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) ?_ ?_ ?_
      · intro u hu
        exact (hh u).continuousAt.continuousWithinAt
      · intro u hu
        exact (hh u).differentiableAt.differentiableWithinAt
      · intro u hu
        rw [(hh u).deriv]
        have hu0 : 0 ≤ u := interior_subset hu
        positivity
    have hhu :=
      hhmono (by simp : (0 : ℝ) ∈ Set.Ici 0)
        (by simpa : t ∈ Set.Ici 0) ht
    have hu : f t ≤ Real.exp t * t ^ 3 / 6 := by
      dsimp only [h] at hhu
      rw [hf0] at hhu
      norm_num at hhu
      nlinarith [hhu]
    exact ⟨hl, hu⟩
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0))
  let main : ℝ → ℝ := fun x =>
    (x ^ 3 - x ^ 2 + x / 2) * Real.exp (1 / x) - x ^ 3
  have hmain_bounds : ∀ᶠ x : ℝ in atTop,
      (1 / 6 : ℝ) ≤ main x ∧
        main x ≤ Real.exp (1 / x) / 6 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hx3 : 0 ≤ x ^ 3 := by positivity
    have ht : 0 ≤ (1 / x : ℝ) := by positivity
    have hs := sandwich (1 / x) ht
    have hmain_eq :
        main x = x ^ 3 * f (1 / x) := by
      dsimp [main, f]
      field_simp [hxne]
    have hl := mul_le_mul_of_nonneg_left hs.1 hx3
    have hu := mul_le_mul_of_nonneg_left hs.2 hx3
    have hl_id :
        x ^ 3 * ((1 / x : ℝ) ^ 3 / 6) = (1 / 6 : ℝ) := by
      field_simp [hxne]
    have hu_id :
        x ^ 3 * (Real.exp (1 / x) * (1 / x : ℝ) ^ 3 / 6) =
          Real.exp (1 / x) / 6 := by
      field_simp [hxne]
    rw [hl_id] at hl
    rw [hu_id] at hu
    rw [hmain_eq]
    exact ⟨hl, hu⟩
  have hexp :
      Tendsto (fun x : ℝ => Real.exp (1 / x) / 6) atTop
        (nhds (1 / 6 : ℝ)) := by
    have he :
        Tendsto (fun x : ℝ => Real.exp (1 / x)) atTop
          (nhds (Real.exp 0)) :=
      Real.continuous_exp.continuousAt.tendsto.comp hinv
    simpa using he.div_const 6
  have hmain : Tendsto main atTop (nhds (1 / 6 : ℝ)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (1 / 6 : ℝ)) atTop (nhds (1 / 6 : ℝ)))
      hexp
    · exact hmain_bounds.mono (fun _ h => h.1)
    · exact hmain_bounds.mono (fun _ h => h.2)
  let correction : ℝ → ℝ := fun x =>
    Real.sqrt (x ^ 6 + 1) - x ^ 3
  have hcorr_bounds : ∀ᶠ x : ℝ in atTop,
      0 ≤ correction x ∧ correction x ≤ 1 / x ^ 3 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hx3pos : 0 < x ^ 3 := by positivity
    have hsnonneg : 0 ≤ Real.sqrt (x ^ 6 + 1) := Real.sqrt_nonneg _
    have harg : 0 ≤ x ^ 6 + 1 := by positivity
    have hsq : (Real.sqrt (x ^ 6 + 1)) ^ 2 = x ^ 6 + 1 :=
      Real.sq_sqrt harg
    have hpow : (x ^ 3) ^ 2 = x ^ 6 := by ring
    have hsge : x ^ 3 ≤ Real.sqrt (x ^ 6 + 1) := by
      nlinarith
    have hc0 : 0 ≤ correction x := by
      dsimp only [correction]
      linarith
    have hprod :
        correction x * (Real.sqrt (x ^ 6 + 1) + x ^ 3) = 1 := by
      dsimp only [correction]
      nlinarith
    have hmul : correction x * x ^ 3 ≤ 1 := by
      have hden :
          x ^ 3 ≤ Real.sqrt (x ^ 6 + 1) + x ^ 3 := by
        nlinarith
      have hm := mul_le_mul_of_nonneg_left hden hc0
      nlinarith
    have hinv_id : x ^ 3 * (1 / x ^ 3) = 1 := by
      field_simp [hxne]
    have hcu : correction x ≤ 1 / x ^ 3 := by
      nlinarith
    exact ⟨hc0, hcu⟩
  have hupper :
      Tendsto (fun x : ℝ => 1 / x ^ 3) atTop (nhds 0) := by
    have hp := hinv.pow 3
    simpa [div_pow] using hp
  have hcorr : Tendsto correction atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0))
      hupper
    · exact hcorr_bounds.mono (fun _ h => h.1)
    · exact hcorr_bounds.mono (fun _ h => h.2)
  have hfinal := hmain.sub hcorr
  have heq : (fun x : ℝ => main x - correction x) = original := by
    funext x
    dsimp [main, correction, original]
    ring
  rw [← heq]
  simpa using hfinal

theorem gap1 : Tendsto original atTop (nhds (1 / 6 : ℝ)) := by
  exact original_limit
theorem gap2 : Tendsto leadingStage atTop (nhds (1 / 6 : ℝ)) := by
  change Tendsto (fun x : ℝ => (1 / 6 : ℝ) + 1 / x) atTop
    (nhds (1 / 6 : ℝ))
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0))
  have hc :
      Tendsto (fun _ : ℝ => (1 / 6 : ℝ)) atTop
        (nhds (1 / 6 : ℝ)) :=
    tendsto_const_nhds
  simpa using hc.add hinv
theorem gap3 : Tendsto original atTop (nhds (1 / 6 : ℝ)) := by
  exact gap1

end
end ProofGap.Exercise1402
