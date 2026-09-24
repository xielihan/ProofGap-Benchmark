import ProofGapLean.Prelude.Analysis
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1362

noncomputable section

def HasLimitAtTop (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

def f₀ (x : ℝ) : ℝ := x * Real.log (Real.tanh x)
def f₁ (x : ℝ) : ℝ := Real.log (Real.tanh x) / (1 / x)
def f₂ (x : ℝ) : ℝ :=
  (1 / (Real.tanh x * Real.cosh x ^ 2)) / (-1 / x ^ 2)
def f₃ (x : ℝ) : ℝ := -2 * (x ^ 2 / Real.sinh (2 * x))
def f₄ (x : ℝ) : ℝ := -2 * ((2 * x) / (2 * Real.cosh (2 * x)))
def f₅ (x : ℝ) : ℝ := -2 * (1 / (2 * Real.sinh (2 * x)))
def powerForm (x : ℝ) : ℝ := Real.rpow (Real.tanh x) x

private theorem exercise1362_eventually_pos :
    ∀ᶠ x : ℝ in Filter.atTop, 0 < x := by
  apply Filter.eventually_atTop.2
  refine ⟨1, ?_⟩
  intro x hx
  linarith

private theorem exercise1362_sinh_pos {x : ℝ} (hx : 0 < x) : 0 < Real.sinh x := by
  have he : Real.exp (-x) < Real.exp x :=
    Real.exp_lt_exp.mpr (by linarith)
  rw [Real.sinh_eq]
  linarith

private theorem exercise1362_tanh_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (exercise1362_sinh_pos hx) (Real.cosh_pos x)

private theorem exercise1362_tendsto_exp_neg :
    Filter.Tendsto (fun x : ℝ => Real.exp (-x)) Filter.atTop (nhds 0) := by
  simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0)

private theorem exercise1362_tendsto_exp_neg_two :
    Filter.Tendsto (fun x : ℝ => Real.exp (-2 * x)) Filter.atTop (nhds 0) := by
  have h := exercise1362_tendsto_exp_neg.mul exercise1362_tendsto_exp_neg
  have heq :
      (fun x : ℝ => Real.exp (-x) * Real.exp (-x)) =ᶠ[Filter.atTop]
        (fun x : ℝ => Real.exp (-2 * x)) :=
    Filter.Eventually.of_forall (fun x => by
      change Real.exp (-x) * Real.exp (-x) = Real.exp (-2 * x)
      rw [← Real.exp_add]
      congr 1 <;> ring)
  simpa using h.congr' heq

private theorem exercise1362_tendsto_exp_neg_four :
    Filter.Tendsto (fun x : ℝ => Real.exp (-4 * x)) Filter.atTop (nhds 0) := by
  have h := exercise1362_tendsto_exp_neg_two.mul exercise1362_tendsto_exp_neg_two
  have heq :
      (fun x : ℝ => Real.exp (-2 * x) * Real.exp (-2 * x)) =ᶠ[Filter.atTop]
        (fun x : ℝ => Real.exp (-4 * x)) :=
    Filter.Eventually.of_forall (fun x => by
      change Real.exp (-2 * x) * Real.exp (-2 * x) = Real.exp (-4 * x)
      rw [← Real.exp_add]
      congr 1 <;> ring)
  simpa using h.congr' heq

private theorem exercise1362_tendsto_pow_exp_neg_two (n : ℕ) :
    Filter.Tendsto (fun x : ℝ => x ^ n * Real.exp (-2 * x))
      Filter.atTop (nhds 0) := by
  have h :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).mul
      exercise1362_tendsto_exp_neg
  have heq :
      (fun x : ℝ => (x ^ n * Real.exp (-x)) * Real.exp (-x)) =ᶠ[Filter.atTop]
        (fun x : ℝ => x ^ n * Real.exp (-2 * x)) :=
    Filter.Eventually.of_forall (fun x => by
      change (x ^ n * Real.exp (-x)) * Real.exp (-x) =
        x ^ n * Real.exp (-2 * x)
      rw [mul_assoc, ← Real.exp_add]
      congr 2 <;> ring)
  simpa using h.congr' heq

private theorem exercise1362_tendsto_pow_div_sinh_two (n : ℕ) :
    Filter.Tendsto (fun x : ℝ => x ^ n / Real.sinh (2 * x))
      Filter.atTop (nhds 0) := by
  have hc : Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) Filter.atTop (nhds 2) :=
    tendsto_const_nhds
  have hd :
      Filter.Tendsto (fun x : ℝ => 1 - Real.exp (-4 * x))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub exercise1362_tendsto_exp_neg_four
  have hm :
      Filter.Tendsto
        (fun x : ℝ => 2 * (x ^ n * Real.exp (-2 * x)) /
          (1 - Real.exp (-4 * x))) Filter.atTop (nhds 0) := by
    simpa using
      (hc.mul (exercise1362_tendsto_pow_exp_neg_two n)).div hd
        (by norm_num : (1 : ℝ) ≠ 0)
  apply hm.congr'
  filter_upwards [exercise1362_eventually_pos] with x hx
  change 2 * (x ^ n * Real.exp (-2 * x)) / (1 - Real.exp (-4 * x)) =
    x ^ n / Real.sinh (2 * x)
  have hsub : Real.exp (2 * x) - Real.exp (-2 * x) ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith)))
  have hden : 1 - Real.exp (-4 * x) ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr ((Real.exp_lt_one_iff).2 (by linarith)))
  have hp : Real.exp (-2 * x) * Real.exp (2 * x) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hs : Real.exp (-2 * x) * Real.exp (-2 * x) = Real.exp (-4 * x) := by
    rw [← Real.exp_add]
    congr 1 <;> ring
  have hcore :
      Real.exp (-2 * x) * (Real.exp (2 * x) - Real.exp (-2 * x)) =
        1 - Real.exp (-4 * x) := by
    rw [mul_sub, hp, hs]
  have hfrac :
      1 / (Real.exp (2 * x) - Real.exp (-2 * x)) =
        Real.exp (-2 * x) / (1 - Real.exp (-4 * x)) := by
    apply (div_eq_div_iff hsub hden).2
    simpa using hcore.symm
  symm
  rw [Real.sinh_eq]
  rw [show -(2 * x) = -2 * x by ring]
  calc
    x ^ n / ((Real.exp (2 * x) - Real.exp (-2 * x)) / 2) =
        2 * x ^ n / (Real.exp (2 * x) - Real.exp (-2 * x)) := by
          field_simp [hsub] <;> ring
    _ = 2 * x ^ n * (1 / (Real.exp (2 * x) - Real.exp (-2 * x))) := by
          simp [div_eq_mul_inv]
    _ = 2 * (x ^ n * Real.exp (-2 * x)) /
        (1 - Real.exp (-4 * x)) := by
          rw [hfrac]
          ring

private theorem exercise1362_tendsto_pow_div_cosh_two (n : ℕ) :
    Filter.Tendsto (fun x : ℝ => x ^ n / Real.cosh (2 * x))
      Filter.atTop (nhds 0) := by
  have hc : Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) Filter.atTop (nhds 2) :=
    tendsto_const_nhds
  have hd :
      Filter.Tendsto (fun x : ℝ => 1 + Real.exp (-4 * x))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add exercise1362_tendsto_exp_neg_four
  have hm :
      Filter.Tendsto
        (fun x : ℝ => 2 * (x ^ n * Real.exp (-2 * x)) /
          (1 + Real.exp (-4 * x))) Filter.atTop (nhds 0) := by
    simpa using
      (hc.mul (exercise1362_tendsto_pow_exp_neg_two n)).div hd
        (by norm_num : (1 : ℝ) ≠ 0)
  apply hm.congr'
  filter_upwards with x
  change 2 * (x ^ n * Real.exp (-2 * x)) / (1 + Real.exp (-4 * x)) =
    x ^ n / Real.cosh (2 * x)
  have hsum : Real.exp (2 * x) + Real.exp (-2 * x) ≠ 0 := by
    positivity
  have hden : 1 + Real.exp (-4 * x) ≠ 0 := by
    positivity
  have hp : Real.exp (-2 * x) * Real.exp (2 * x) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hs : Real.exp (-2 * x) * Real.exp (-2 * x) = Real.exp (-4 * x) := by
    rw [← Real.exp_add]
    congr 1 <;> ring
  have hcore :
      Real.exp (-2 * x) * (Real.exp (2 * x) + Real.exp (-2 * x)) =
        1 + Real.exp (-4 * x) := by
    rw [mul_add, hp, hs]
  have hfrac :
      1 / (Real.exp (2 * x) + Real.exp (-2 * x)) =
        Real.exp (-2 * x) / (1 + Real.exp (-4 * x)) := by
    apply (div_eq_div_iff hsum hden).2
    simpa using hcore.symm
  symm
  rw [Real.cosh_eq]
  rw [show -(2 * x) = -2 * x by ring]
  calc
    x ^ n / ((Real.exp (2 * x) + Real.exp (-2 * x)) / 2) =
        2 * x ^ n / (Real.exp (2 * x) + Real.exp (-2 * x)) := by
          field_simp [hsum] <;> ring
    _ = 2 * x ^ n * (1 / (Real.exp (2 * x) + Real.exp (-2 * x))) := by
          simp [div_eq_mul_inv]
    _ = 2 * (x ^ n * Real.exp (-2 * x)) /
        (1 + Real.exp (-4 * x)) := by
          rw [hfrac]
          ring

private theorem exercise1362_limit_f₃ : HasLimitAtTop f₃ 0 := by
  unfold HasLimitAtTop
  have hc : Filter.Tendsto (fun _ : ℝ => (-2 : ℝ)) Filter.atTop (nhds (-2)) :=
    tendsto_const_nhds
  have h :
      Filter.Tendsto (fun x : ℝ => -2 * (x ^ 2 / Real.sinh (2 * x)))
        Filter.atTop (nhds 0) := by
    simpa using hc.mul (exercise1362_tendsto_pow_div_sinh_two 2)
  change Filter.Tendsto (fun x : ℝ => -2 * (x ^ 2 / Real.sinh (2 * x)))
    Filter.atTop (nhds 0)
  exact h

private theorem exercise1362_limit_f₄ : HasLimitAtTop f₄ 0 := by
  unfold HasLimitAtTop
  have hc : Filter.Tendsto (fun _ : ℝ => (-2 : ℝ)) Filter.atTop (nhds (-2)) :=
    tendsto_const_nhds
  have h :
      Filter.Tendsto (fun x : ℝ => -2 * (x / Real.cosh (2 * x)))
        Filter.atTop (nhds 0) := by
    simpa using hc.mul (exercise1362_tendsto_pow_div_cosh_two 1)
  apply h.congr'
  filter_upwards with x
  change -2 * (x / Real.cosh (2 * x)) = f₄ x
  rw [f₄]
  have hcosh : Real.cosh (2 * x) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  field_simp [hcosh] <;> ring

private theorem exercise1362_limit_f₅ : HasLimitAtTop f₅ 0 := by
  unfold HasLimitAtTop
  have hc : Filter.Tendsto (fun _ : ℝ => (-1 : ℝ)) Filter.atTop (nhds (-1)) :=
    tendsto_const_nhds
  have h :
      Filter.Tendsto (fun x : ℝ => -1 * (x ^ 0 / Real.sinh (2 * x)))
        Filter.atTop (nhds 0) := by
    simpa using hc.mul (exercise1362_tendsto_pow_div_sinh_two 0)
  apply h.congr'
  filter_upwards [exercise1362_eventually_pos] with x hx
  change -1 * (x ^ 0 / Real.sinh (2 * x)) = f₅ x
  have hsinh : Real.sinh (2 * x) ≠ 0 :=
    ne_of_gt (exercise1362_sinh_pos (by linarith))
  rw [f₅]
  field_simp [hsinh] <;> ring

private theorem exercise1362_limit_f₂ : HasLimitAtTop f₂ 0 := by
  unfold HasLimitAtTop at *
  apply exercise1362_limit_f₃.congr'
  filter_upwards [exercise1362_eventually_pos] with x hx
  change f₃ x = f₂ x
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hsinh : Real.sinh x ≠ 0 := ne_of_gt (exercise1362_sinh_pos hx)
  have hcosh : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  rw [f₂, f₃, Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul]
  field_simp [hx0, hsinh, hcosh] <;> ring

private theorem exercise1362_tendsto_tanh_log_bound :
    Filter.Tendsto
      (fun x : ℝ => x * ((1 - Real.tanh x) / Real.tanh x))
      Filter.atTop (nhds 0) := by
  have hc : Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) Filter.atTop (nhds 2) :=
    tendsto_const_nhds
  have hd :
      Filter.Tendsto (fun x : ℝ => 1 - Real.exp (-2 * x))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub exercise1362_tendsto_exp_neg_two
  have hm :
      Filter.Tendsto
        (fun x : ℝ => 2 * (x * Real.exp (-2 * x)) /
          (1 - Real.exp (-2 * x))) Filter.atTop (nhds 0) := by
    simpa using
      (hc.mul (exercise1362_tendsto_pow_exp_neg_two 1)).div hd
        (by norm_num : (1 : ℝ) ≠ 0)
  apply hm.congr'
  filter_upwards [exercise1362_eventually_pos] with x hx
  change 2 * (x * Real.exp (-2 * x)) / (1 - Real.exp (-2 * x)) =
    x * ((1 - Real.tanh x) / Real.tanh x)
  have hsub : Real.exp x - Real.exp (-x) ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith)))
  have hsum : Real.exp x + Real.exp (-x) ≠ 0 := by
    positivity
  have hden : 1 - Real.exp (-2 * x) ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr ((Real.exp_lt_one_iff).2 (by linarith)))
  have hca : Real.exp (-2 * x) * Real.exp x = Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1 <;> ring
  have hcore :
      Real.exp (-x) * (1 - Real.exp (-2 * x)) =
        Real.exp (-2 * x) * (Real.exp x - Real.exp (-x)) := by
    rw [mul_sub, mul_one, mul_sub, hca] <;> ring
  have hfrac :
      Real.exp (-x) / (Real.exp x - Real.exp (-x)) =
        Real.exp (-2 * x) / (1 - Real.exp (-2 * x)) := by
    exact (div_eq_div_iff hsub hden).2 hcore
  have htform :
      (1 - Real.tanh x) / Real.tanh x =
        2 * (Real.exp (-x) / (Real.exp x - Real.exp (-x))) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    field_simp [hsub, hsum] <;> ring
  rw [htform, hfrac]
  ring

private theorem exercise1362_limit_f₀ : HasLimitAtTop f₀ 0 := by
  unfold HasLimitAtTop
  have hl :
      Filter.Tendsto
        (fun x : ℝ => -(x * ((1 - Real.tanh x) / Real.tanh x)))
        Filter.atTop (nhds 0) := by
    simpa using exercise1362_tendsto_tanh_log_bound.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hl exercise1362_tendsto_tanh_log_bound
  · filter_upwards [exercise1362_eventually_pos] with x hx
    have htpos : 0 < Real.tanh x := exercise1362_tanh_pos hx
    have htlt : Real.tanh x < 1 := Real.tanh_lt_one x
    have hlogneg : Real.log (Real.tanh x) < 0 := Real.log_neg htpos htlt
    have hlogbound :
        |Real.log (Real.tanh x)| ≤ (1 - Real.tanh x) / Real.tanh x := by
      calc
        |Real.log (Real.tanh x)| = -Real.log (Real.tanh x) :=
          abs_of_neg hlogneg
        _ = Real.log (Real.tanh x)⁻¹ := by rw [Real.log_inv]
        _ ≤ (Real.tanh x)⁻¹ - 1 :=
          Real.log_le_sub_one_of_pos (inv_pos.mpr htpos)
        _ = (1 - Real.tanh x) / Real.tanh x := by
          field_simp [ne_of_gt htpos] <;> ring
    have hb : |f₀ x| ≤ x * ((1 - Real.tanh x) / Real.tanh x) := by
      rw [f₀, abs_mul, abs_of_pos hx]
      exact mul_le_mul_of_nonneg_left hlogbound hx.le
    exact (neg_le_neg hb).trans (neg_abs_le (f₀ x))
  · filter_upwards [exercise1362_eventually_pos] with x hx
    have htpos : 0 < Real.tanh x := exercise1362_tanh_pos hx
    have htlt : Real.tanh x < 1 := Real.tanh_lt_one x
    have hlogneg : Real.log (Real.tanh x) < 0 := Real.log_neg htpos htlt
    have hlogbound :
        |Real.log (Real.tanh x)| ≤ (1 - Real.tanh x) / Real.tanh x := by
      calc
        |Real.log (Real.tanh x)| = -Real.log (Real.tanh x) :=
          abs_of_neg hlogneg
        _ = Real.log (Real.tanh x)⁻¹ := by rw [Real.log_inv]
        _ ≤ (Real.tanh x)⁻¹ - 1 :=
          Real.log_le_sub_one_of_pos (inv_pos.mpr htpos)
        _ = (1 - Real.tanh x) / Real.tanh x := by
          field_simp [ne_of_gt htpos] <;> ring
    have hb : |f₀ x| ≤ x * ((1 - Real.tanh x) / Real.tanh x) := by
      rw [f₀, abs_mul, abs_of_pos hx]
      exact mul_le_mul_of_nonneg_left hlogbound hx.le
    exact (le_abs_self (f₀ x)).trans hb

private theorem exercise1362_limit_f₁ : HasLimitAtTop f₁ 0 := by
  unfold HasLimitAtTop at *
  apply exercise1362_limit_f₀.congr'
  filter_upwards [exercise1362_eventually_pos] with x hx
  change f₀ x = f₁ x
  rw [f₀, f₁]
  field_simp [ne_of_gt hx] <;> ring

private theorem exercise1362_limit_powerForm :
    HasLimitAtTop powerForm (Real.exp 0) := by
  unfold HasLimitAtTop at *
  have he :
      Filter.Tendsto (fun x : ℝ => Real.exp (f₀ x)) Filter.atTop
        (nhds (Real.exp 0)) :=
    Real.continuous_exp.continuousAt.tendsto.comp exercise1362_limit_f₀
  apply he.congr'
  filter_upwards [exercise1362_eventually_pos] with x hx
  have htpos : 0 < Real.tanh x := exercise1362_tanh_pos hx
  change Real.exp (f₀ x) = Real.rpow (Real.tanh x) x
  calc
    Real.exp (f₀ x) = Real.exp (Real.log (Real.tanh x) * x) := by
      congr 1
      rw [f₀]
      ring
    _ = Real.rpow (Real.tanh x) x := by
      symm
      exact Real.rpow_def_of_pos htpos x

theorem gap1 : HasLimitAtTop f₀ 0 ↔ HasLimitAtTop f₁ 0 := by
  exact ⟨fun _ => exercise1362_limit_f₁, fun _ => exercise1362_limit_f₀⟩
theorem gap2 : HasLimitAtTop f₁ 0 ↔ HasLimitAtTop f₂ 0 := by
  exact ⟨fun _ => exercise1362_limit_f₂, fun _ => exercise1362_limit_f₁⟩
theorem gap3 : HasLimitAtTop f₂ 0 ↔ HasLimitAtTop f₃ 0 := by
  exact ⟨fun _ => exercise1362_limit_f₃, fun _ => exercise1362_limit_f₂⟩
theorem gap4 : HasLimitAtTop f₃ 0 ↔ HasLimitAtTop f₄ 0 := by
  exact ⟨fun _ => exercise1362_limit_f₄, fun _ => exercise1362_limit_f₃⟩
theorem gap5 : HasLimitAtTop f₄ 0 ↔ HasLimitAtTop f₅ 0 := by
  exact ⟨fun _ => exercise1362_limit_f₅, fun _ => exercise1362_limit_f₄⟩
theorem gap6 : HasLimitAtTop f₅ 0 := by
  exact exercise1362_limit_f₅
theorem gap7 : HasLimitAtTop f₀ 0 := by
  exact gap1.mpr (gap2.mpr (gap3.mpr (gap4.mpr (gap5.mpr gap6))))
theorem gap8 : HasLimitAtTop powerForm (Real.exp 0) := by
  exact exercise1362_limit_powerForm
theorem gap9 : Real.exp 0 = 1 := by
  exact Real.exp_zero
theorem gap10 : HasLimitAtTop powerForm 1 := by
  simpa using gap8

end

end ProofGap.Exercise1362
