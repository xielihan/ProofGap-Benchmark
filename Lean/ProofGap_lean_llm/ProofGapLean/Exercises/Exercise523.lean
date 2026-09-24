import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise523

noncomputable section

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def original (x : ℝ) : ℝ := Real.rpow (Real.sin x) (Real.tan x)
def rewritten (x : ℝ) : ℝ :=
  Real.rpow (1 + cot x ^ 2) (-Real.tan x / 2)
def exponentialForm (x : ℝ) : ℝ :=
  Real.rpow (1 + cot x ^ 2)
    ((1 / cot x ^ 2) * (-cot x / 2))
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_523/1.txt`. -/
private theorem tendsto_of_eventually_eq
    {α β : Type*} {f g : α → β} {l : Filter α} {l' : Filter β}
    (h : f =ᶠ[l] g) (hf : Filter.Tendsto f l l') :
    Filter.Tendsto g l l' := by
  rw [Filter.tendsto_def] at hf ⊢
  intro s hs
  filter_upwards [hf s hs, h] with x hfx hx
  change g x ∈ s
  change f x ∈ s at hfx
  exact hx ▸ hfx

private theorem tendsto_iff_of_eventually_eq
    {α β : Type*} {f g : α → β} {l : Filter α} {l' : Filter β}
    (h : f =ᶠ[l] g) :
    Filter.Tendsto f l l' ↔ Filter.Tendsto g l l' := by
  constructor
  · exact tendsto_of_eventually_eq h
  · exact tendsto_of_eventually_eq h.symm

private theorem sin_pos_near_pi_div_two :
    ∀ᶠ x in nhds (Real.pi / 2), 0 < Real.sin x := by
  have hleft : (0 : ℝ) < Real.pi / 2 := by
    linarith [Real.pi_pos]
  have hright : Real.pi / 2 < Real.pi := by
    linarith [Real.pi_pos]
  have hinterval :
      Set.Ioo (0 : ℝ) Real.pi ∈ nhds (Real.pi / 2) :=
    isOpen_Ioo.mem_nhds ⟨hleft, hright⟩
  filter_upwards [hinterval] with x hx
  exact Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2

private theorem original_eq_rewritten_of_sin_pos {x : ℝ}
    (hx : 0 < Real.sin x) : original x = rewritten x := by
  have hsne : Real.sin x ≠ 0 := ne_of_gt hx
  have hbase :
      1 + cot x ^ 2 = (Real.sin x ^ 2)⁻¹ := by
    unfold cot
    field_simp [hsne]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hbasePos : 0 < 1 + cot x ^ 2 := by
    positivity
  have hlog :
      Real.log (1 + cot x ^ 2) = -2 * Real.log (Real.sin x) := by
    rw [hbase, Real.log_inv, Real.log_pow]
    norm_num
  have horiginal :
      Real.rpow (Real.sin x) (Real.tan x) =
        Real.exp (Real.log (Real.sin x) * Real.tan x) := by
    exact Real.rpow_def_of_pos hx (Real.tan x)
  have hrewritten :
      Real.rpow (1 + cot x ^ 2) (-Real.tan x / 2) =
        Real.exp
          (Real.log (1 + cot x ^ 2) * (-Real.tan x / 2)) := by
    exact Real.rpow_def_of_pos hbasePos (-Real.tan x / 2)
  unfold original rewritten
  rw [horiginal, hrewritten, hlog]
  congr 1
  ring

private theorem rewritten_eq_exponential_of_sin_pos {x : ℝ}
    (hx : 0 < Real.sin x) : rewritten x = exponentialForm x := by
  have hsne : Real.sin x ≠ 0 := ne_of_gt hx
  have hexponent :
      (1 / cot x ^ 2) * (-cot x / 2) = -Real.tan x / 2 := by
    unfold cot
    rw [Real.tan_eq_sin_div_cos]
    by_cases hc : Real.cos x = 0
    · simp [hc]
    · field_simp [hsne, hc]
  unfold rewritten exponentialForm
  rw [hexponent]

private def logQuadraticSlope (t : ℝ) : ℝ :=
  Real.log (1 + t ^ 2) / t

private theorem logQuadraticSlope_tendsto_zero :
    Filter.Tendsto logQuadraticSlope (nhds 0) (nhds 0) := by
  have hpoly :
      HasDerivAt (fun t : ℝ => 1 + t ^ 2) 0 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add
        ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).pow 2) using 1 <;>
      norm_num
  have hlogAt :
      HasDerivAt Real.log 1 (1 + (0 : ℝ) ^ 2) := by
    convert
      Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
      using 1 <;> norm_num
  have hderiv :
      HasDerivAt (fun t : ℝ => Real.log (1 + t ^ 2)) 0 0 := by
    convert hlogAt.comp 0 hpoly using 1 <;> norm_num
  have hpunc :
      Filter.Tendsto logQuadraticSlope
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have hslopeEq :
        (fun t : ℝ => t⁻¹ * Real.log (1 + t ^ 2)) =
          logQuadraticSlope := by
      funext t
      unfold logQuadraticSlope
      rw [div_eq_mul_inv]
      exact mul_comm _ _
    rw [← hslopeEq]
    simpa using hderiv.tendsto_slope_zero
  rw [Filter.tendsto_def] at hpunc ⊢
  intro s hs
  have hs0 : (0 : ℝ) ∈ s := mem_of_mem_nhds hs
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hpunc s hs) with
    ⟨u, hu, hus⟩
  refine Filter.mem_of_superset hu ?_
  intro x hx
  by_cases hzero : x = 0
  · subst x
    simpa [logQuadraticSlope] using hs0
  · exact hus ⟨hx, by simp [hzero]⟩

private theorem exponentialForm_eq_exp_slope (x : ℝ) :
    exponentialForm x = Real.exp (-logQuadraticSlope (cot x) / 2) := by
  have hbasePos : 0 < 1 + cot x ^ 2 := by
    positivity
  have hrpow :
      Real.rpow (1 + cot x ^ 2)
          ((1 / cot x ^ 2) * (-cot x / 2)) =
        Real.exp
          (Real.log (1 + cot x ^ 2) *
            ((1 / cot x ^ 2) * (-cot x / 2))) := by
    exact Real.rpow_def_of_pos hbasePos
      ((1 / cot x ^ 2) * (-cot x / 2))
  unfold exponentialForm
  rw [hrpow]
  congr 1
  unfold logQuadraticSlope
  by_cases hcot : cot x = 0
  · simp [hcot]
  · field_simp [hcot] <;> ring

theorem gap1 (L : ℝ) :
    HasLimitAt original (Real.pi / 2) L ↔
      HasLimitAt rewritten (Real.pi / 2) L := by
  have heqFull : original =ᶠ[nhds (Real.pi / 2)] rewritten := by
    filter_upwards [sin_pos_near_pi_div_two] with x hx
    exact original_eq_rewritten_of_sin_pos hx
  have heq :
      original =ᶠ[nhdsWithin (Real.pi / 2) ({Real.pi / 2} : Set ℝ)ᶜ]
        rewritten :=
    heqFull.filter_mono inf_le_left
  unfold HasLimitAt
  exact tendsto_iff_of_eventually_eq heq

/-- Source: `proof_gap/exercise_523/2.txt`. -/
theorem gap2 (L : ℝ) :
    HasLimitAt original (Real.pi / 2) L ↔
      HasLimitAt exponentialForm (Real.pi / 2) L := by
  rw [gap1]
  have heqFull : rewritten =ᶠ[nhds (Real.pi / 2)] exponentialForm := by
    filter_upwards [sin_pos_near_pi_div_two] with x hx
    exact rewritten_eq_exponential_of_sin_pos hx
  have heq :
      rewritten =ᶠ[nhdsWithin (Real.pi / 2) ({Real.pi / 2} : Set ℝ)ᶜ]
        exponentialForm :=
    heqFull.filter_mono inf_le_left
  unfold HasLimitAt
  exact tendsto_iff_of_eventually_eq heq

/-- Source: `proof_gap/exercise_523/3.txt`. -/
theorem gap3 : HasLimitAt exponentialForm (Real.pi / 2) (Real.exp 0) := by
  unfold HasLimitAt
  have hcot :
      Filter.Tendsto cot (nhds (Real.pi / 2)) (nhds 0) := by
    have hcont :
        Filter.Tendsto (fun x : ℝ => Real.cos x / Real.sin x)
          (nhds (Real.pi / 2))
          (nhds (Real.cos (Real.pi / 2) / Real.sin (Real.pi / 2))) :=
      Real.continuous_cos.continuousAt.div
        Real.continuous_sin.continuousAt
        (by simp)
    simpa [cot] using hcont
  have hslope := logQuadraticSlope_tendsto_zero.comp hcot
  have hinner :
      Filter.Tendsto
        (fun x : ℝ => -logQuadraticSlope (cot x) / 2)
        (nhds (Real.pi / 2)) (nhds 0) := by
    simpa using hslope.neg.div_const 2
  have hexp :
      Filter.Tendsto Real.exp (nhds 0) (nhds (Real.exp 0)) :=
    Real.continuous_exp.continuousAt
  have hfun :
      exponentialForm =
        (fun x : ℝ => Real.exp (-logQuadraticSlope (cot x) / 2)) := by
    funext x
    exact exponentialForm_eq_exp_slope x
  have hfull :
      Filter.Tendsto exponentialForm (nhds (Real.pi / 2))
        (nhds (Real.exp 0)) := by
    rw [hfun]
    simpa only [Function.comp_apply] using hexp.comp hinner
  exact hfull.mono_left inf_le_left

/-- Source: `proof_gap/exercise_523/4.txt`. -/
theorem gap4 : Real.exp 0 = 1 := by
  exact Real.exp_zero

/-- Source: `proof_gap/exercise_523/5.txt`. -/
theorem gap5 : HasLimitAt original (Real.pi / 2) 1 := by
  apply (gap2 1).mpr
  simpa [gap4] using gap3

end

end ProofGap.Exercise523
