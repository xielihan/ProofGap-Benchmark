import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1364

noncomputable section

def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

def f₀ (x : ℝ) : ℝ := ((1 / x) * Real.log (1 + x) - 1) / x
def f₁ (x : ℝ) : ℝ := (Real.log (1 + x) - x) / x ^ 2
def f₂ (x : ℝ) : ℝ := (1 / (1 + x) - 1) / (2 * x)
def f₃ (x : ℝ) : ℝ := -(1 / (2 * (1 + x)))
def powerForm (x : ℝ) : ℝ :=
  Real.rpow (Real.rpow (1 + x) (1 / x) / Real.exp 1) (1 / x)

private theorem tid :
    Tendsto (fun x : ℝ => x) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
  Filter.tendsto_id.mono_left inf_le_left

private theorem base_pos :
    ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, 0 < 1 + x := by
  have h : ∀ᶠ x : ℝ in nhds 0, -1 < x := eventually_gt_nhds (by norm_num)
  exact (h.filter_mono inf_le_left).mono (by intros; linarith)

private theorem f₃_limit : HasLimitAtZero f₃ (-1 / 2) := by
  have hb : Tendsto (fun x : ℝ => 1 + x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    convert tendsto_const_nhds.add tid using 1 <;> norm_num
  have htwo :
      Tendsto (fun _ : ℝ => (2 : ℝ)) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) :=
    tendsto_const_nhds
  have hone :
      Tendsto (fun _ : ℝ => (1 : ℝ)) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_const_nhds
  unfold HasLimitAtZero
  convert (hone.div (htwo.mul hb) (by norm_num)).neg using 1 <;> norm_num [f₃]

private theorem f₂_limit : HasLimitAtZero f₂ (-1 / 2) := by
  apply f₃_limit.congr'
  filter_upwards [self_mem_nhdsWithin, base_pos] with x hx hpos
  have hx0 : x ≠ 0 := by simpa using hx
  have hb0 : 1 + x ≠ 0 := hpos.ne'
  simp only [f₂, f₃]
  field_simp [hx0, hb0]
  ring

private theorem f₁_limit : HasLimitAtZero f₁ (-1 / 2) := by
  let N : ℝ → ℝ := fun x => Real.log (1 + x) - x
  have hN :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        HasDerivAt N (1 / (1 + x) - 1) x := by
    filter_upwards [base_pos] with x hpos
    have hbase := (hasDerivAt_id x).const_add 1
    have hlog := (Real.hasDerivAt_log hpos.ne').comp x hbase
    dsimp [N]
    convert hlog.sub (hasDerivAt_id x) using 1 <;>
      simp [id, Function.comp_def] <;> ring
  have hden :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    filter_upwards with x
    convert (hasDerivAt_id x).pow 2 using 1 <;> simp [id] <;> ring
  have hden_ne : ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, 2 * x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (by simpa using hx)
  have hzeroN : Tendsto N (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have hb : Tendsto (fun x : ℝ => 1 + x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
      convert tendsto_const_nhds.add tid using 1 <;> norm_num
    have hl : Tendsto (fun x : ℝ => Real.log (1 + x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
      have hlog : Tendsto Real.log (nhds 1) (nhds 0) := by
        simpa using (Real.continuousAt_log one_ne_zero).tendsto
      exact hlog.comp hb
    convert hl.sub tid using 1 <;> norm_num [N]
  have hzeroDen : Tendsto (fun y : ℝ => y ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    convert tid.pow 2 using 1 <;> norm_num
  apply HasDerivAt.lhopital_zero_nhdsNE hN hden hden_ne hzeroN hzeroDen
  change Tendsto f₂ (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-1 / 2))
  exact f₂_limit

private theorem f₀_limit : HasLimitAtZero f₀ (-1 / 2) := by
  apply f₁_limit.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp only [f₀, f₁]
  field_simp [hx0]

private theorem powerForm_limit :
    HasLimitAtZero powerForm (Real.exp (-1 / 2)) := by
  have hf := f₀_limit
  unfold HasLimitAtZero at hf ⊢
  have he : Tendsto (fun x : ℝ => Real.exp (f₀ x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.exp (-1 / 2))) :=
    (Real.continuous_exp.continuousAt :
      ContinuousAt Real.exp (-1 / 2)).tendsto.comp hf
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin, base_pos] with x hx hpos
  have hx0 : x ≠ 0 := by simpa using hx
  have hpowpos : 0 < Real.rpow (1 + x) (1 / x) :=
    Real.rpow_pos_of_pos hpos (1 / x)
  have hinnerpos : 0 < Real.rpow (1 + x) (1 / x) / Real.exp 1 :=
    div_pos hpowpos (Real.exp_pos 1)
  have hpoweq : Real.rpow (1 + x) (1 / x) =
      Real.exp (Real.log (1 + x) * (1 / x)) :=
    Real.rpow_def_of_pos hpos (1 / x)
  have hlogpow : Real.log (Real.rpow (1 + x) (1 / x)) =
      Real.log (1 + x) * (1 / x) := by
    rw [hpoweq, Real.log_exp]
  have hloginner :
      Real.log (Real.rpow (1 + x) (1 / x) / Real.exp 1) =
        Real.log (1 + x) * (1 / x) - 1 := by
    rw [Real.log_div hpowpos.ne' (Real.exp_ne_zero 1), hlogpow, Real.log_exp]
  have hr :
      Real.rpow (Real.rpow (1 + x) (1 / x) / Real.exp 1) (1 / x) =
        Real.exp
          (Real.log (Real.rpow (1 + x) (1 / x) / Real.exp 1) * (1 / x)) :=
    Real.rpow_def_of_pos hinnerpos (1 / x)
  rw [powerForm, hr, hloginner]
  congr 1
  dsimp [f₀]
  field_simp [hx0]

theorem gap1 : HasLimitAtZero f₀ (-1 / 2) ↔ HasLimitAtZero f₁ (-1 / 2) := by
  constructor <;> intro _
  · exact f₁_limit
  · exact f₀_limit
theorem gap2 : HasLimitAtZero f₁ (-1 / 2) ↔ HasLimitAtZero f₂ (-1 / 2) := by
  constructor <;> intro _
  · exact f₂_limit
  · exact f₁_limit
theorem gap3 : HasLimitAtZero f₂ (-1 / 2) ↔ HasLimitAtZero f₃ (-1 / 2) := by
  constructor <;> intro _
  · exact f₃_limit
  · exact f₂_limit
theorem gap4 : HasLimitAtZero f₃ (-1 / 2) := by exact f₃_limit
theorem gap5 : HasLimitAtZero f₀ (-1 / 2) := by exact f₀_limit
theorem gap6 : HasLimitAtZero powerForm (Real.exp (-1 / 2)) := by exact powerForm_limit

end

end ProofGap.Exercise1364
