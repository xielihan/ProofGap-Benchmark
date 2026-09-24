import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1367

noncomputable section

def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

def rootPower (m x : ℝ) : ℝ := Real.rpow (Real.cosh x) (1 / m)
def f₀ (m n x : ℝ) : ℝ :=
  Real.log (Real.cosh x) / (rootPower m x - rootPower n x)
def f₁ (m n x : ℝ) : ℝ :=
  Real.tanh x /
    (Real.sinh x *
      ((1 / m) * Real.rpow (Real.cosh x) (1 / m - 1) -
        (1 / n) * Real.rpow (Real.cosh x) (1 / n - 1)))
def target (m n : ℝ) : ℝ := m * n / (n - m)

private theorem reciprocal_difference_ne_zero
    (m n : ℝ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ≠ n) :
    1 / m - 1 / n ≠ 0 := by
  intro h
  have hcalc : m * n * (1 / m - 1 / n) = n - m := by
    field_simp [hm, hn]
  rw [h, mul_zero] at hcalc
  apply hmn
  linarith

private theorem reciprocal_eq_target
    (m n : ℝ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ≠ n) :
    1 / (1 / m - 1 / n) = target m n := by
  have hnm : n - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hmn)
  unfold target
  field_simp [hm, hn, hnm]

private theorem rpow_eq_exp_log (x p : ℝ) (hx : 0 < x) :
    Real.rpow x p = Real.exp (Real.log x * p) := by
  change x ^ p = Real.exp (Real.log x * p)
  exact Real.rpow_def_of_pos hx p

private theorem sinh_ne_zero_of_ne_zero (x : ℝ) (hx : x ≠ 0) :
    Real.sinh x ≠ 0 := by
  intro hs
  apply hx
  rw [Real.sinh_eq] at hs
  have he : Real.exp x = Real.exp (-x) := by
    linarith
  have hxeq : x = -x := Real.exp_injective he
  linarith

private theorem one_lt_cosh_of_ne_zero (x : ℝ) (hx : x ≠ 0) :
    1 < Real.cosh x := by
  have hs : Real.sinh x ≠ 0 := sinh_ne_zero_of_ne_zero x hx
  have hspos : 0 < Real.sinh x * Real.sinh x := mul_self_pos.mpr hs
  have hid := Real.cosh_sq_sub_sinh_sq x
  have hcpos := Real.cosh_pos x
  by_contra h
  have hcle : Real.cosh x ≤ 1 := le_of_not_gt h
  have hcplus : 0 ≤ Real.cosh x + 1 := by linarith
  have hprod : (Real.cosh x - 1) * (Real.cosh x + 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcle) hcplus
  nlinarith

private theorem log_cosh_tendsto_zero :
    Filter.Tendsto (fun x : ℝ => Real.log (Real.cosh x)) (nhds 0) (nhds 0) := by
  have hcosh0 : ContinuousAt Real.cosh 0 :=
    Real.continuous_cosh.continuousAt
  have hcosh : Filter.Tendsto Real.cosh (nhds 0) (nhds 1) := by
    convert hcosh0.tendsto using 1 <;> norm_num [Real.cosh]
  have hlog1 : ContinuousAt Real.log 1 :=
    Real.continuousAt_log (by norm_num)
  have hlog : Filter.Tendsto Real.log (nhds 1) (nhds 0) := by
    convert hlog1.tendsto using 1 <;> norm_num
  exact hlog.comp hcosh

private theorem log_cosh_tendsto_punctured :
    Filter.Tendsto (fun x : ℝ => Real.log (Real.cosh x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
  let y : ℝ → ℝ := fun x => Real.log (Real.cosh x)
  have hy : Filter.Tendsto y (nhds 0) (nhds 0) := by
    simpa [y] using log_cosh_tendsto_zero
  refine tendsto_nhdsWithin_iff.mpr ⟨hy.mono_left inf_le_left, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  have hcosh : 1 < Real.cosh x := one_lt_cosh_of_ne_zero x hx0
  exact Set.mem_compl_singleton_iff.mpr (ne_of_gt (Real.log_pos hcosh))

private theorem f₀_hasLimitAtZero
    (m n : ℝ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ≠ n) :
    HasLimitAtZero (f₀ m n) (1 / (1 / m - 1 / n)) := by
  let c : ℝ := 1 / m - 1 / n
  let B : ℝ → ℝ := fun t => Real.exp (t / m) - Real.exp (t / n)
  let y : ℝ → ℝ := fun x => Real.log (Real.cosh x)
  have hc : c ≠ 0 := by
    simpa [c] using reciprocal_difference_ne_zero m n hm hn hmn
  have hBm : HasDerivAt (fun t : ℝ => Real.exp (t / m)) (1 / m) 0 := by
    simpa using
      ((Real.hasDerivAt_exp (0 / m)).comp 0 ((hasDerivAt_id 0).div_const m))
  have hBn : HasDerivAt (fun t : ℝ => Real.exp (t / n)) (1 / n) 0 := by
    simpa using
      ((Real.hasDerivAt_exp (0 / n)).comp 0 ((hasDerivAt_id 0).div_const n))
  have hB : HasDerivAt B c 0 := by
    simpa [B, c] using hBm.sub hBn
  have hSlope :
      Filter.Tendsto (fun t : ℝ => B t / t) (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds c) := by
    simpa [B, div_eq_mul_inv, mul_comm] using hB.tendsto_slope_zero
  have hRatio :
      Filter.Tendsto (fun t : ℝ => t / B t) (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds (1 / c)) := by
    simpa [one_div] using hSlope.inv₀ hc
  have hy :
      Filter.Tendsto y (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    simpa [y] using log_cosh_tendsto_punctured
  have hcomp := hRatio.comp hy
  unfold HasLimitAtZero
  convert hcomp using 1
  · funext x
    simp only [f₀, rootPower, y, B, Function.comp_apply]
    rw [rpow_eq_exp_log (Real.cosh x) (1 / m) (Real.cosh_pos x),
      rpow_eq_exp_log (Real.cosh x) (1 / n) (Real.cosh_pos x)]
    simp [div_eq_mul_inv]

private theorem f₁_hasLimitAtZero
    (m n : ℝ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ≠ n) :
    HasLimitAtZero (f₁ m n) (1 / (1 / m - 1 / n)) := by
  let c : ℝ := 1 / m - 1 / n
  let y : ℝ → ℝ := fun x => Real.log (Real.cosh x)
  let D : ℝ → ℝ := fun x =>
    (1 / m) * Real.exp (y x * (1 / m - 1)) -
      (1 / n) * Real.exp (y x * (1 / n - 1))
  let E : ℝ → ℝ := fun x => 1 / (Real.cosh x * D x)
  have hc : c ≠ 0 := by
    simpa [c] using reciprocal_difference_ne_zero m n hm hn hmn
  have hy : Filter.Tendsto y (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    exact (show Filter.Tendsto y (nhds 0) (nhds 0) by
      simpa [y] using log_cosh_tendsto_zero).mono_left inf_le_left
  have hcosh0 : ContinuousAt Real.cosh 0 :=
    Real.continuous_cosh.continuousAt
  have hcosh :
      Filter.Tendsto Real.cosh (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have h : Filter.Tendsto Real.cosh
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.cosh 0)) :=
      hcosh0.tendsto.mono_left inf_le_left
    convert h using 1 <;> norm_num [Real.cosh]
  have hpowm :
      Filter.Tendsto (fun x => Real.exp (y x * (1 / m - 1)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have harg := hy.mul_const (1 / m - 1)
    have hexp := Real.continuous_exp.continuousAt.tendsto.comp harg
    simpa using hexp
  have hpown :
      Filter.Tendsto (fun x => Real.exp (y x * (1 / n - 1)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have harg := hy.mul_const (1 / n - 1)
    have hexp := Real.continuous_exp.continuousAt.tendsto.comp harg
    simpa using hexp
  have hmterm :
      Filter.Tendsto
        (fun x : ℝ => (1 / m) * Real.exp (y x * (1 / m - 1)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds ((1 / m) * 1)) := by
    exact
      (show Filter.Tendsto (fun _ : ℝ => (1 / m : ℝ))
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / m)) from
        tendsto_const_nhds).mul hpowm
  have hnterm :
      Filter.Tendsto
        (fun x : ℝ => (1 / n) * Real.exp (y x * (1 / n - 1)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds ((1 / n) * 1)) := by
    exact
      (show Filter.Tendsto (fun _ : ℝ => (1 / n : ℝ))
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / n)) from
        tendsto_const_nhds).mul hpown
  have hD : Filter.Tendsto D (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds c) := by
    simpa [D, c] using hmterm.sub hnterm
  have hE : Filter.Tendsto E (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / c)) := by
    have hden := hcosh.mul hD
    have hden0 : (1 : ℝ) * c ≠ 0 := by simpa using hc
    simpa [E, one_div] using hden.inv₀ hden0
  have heq : f₁ m n =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] E := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    have hsinh : Real.sinh x ≠ 0 := sinh_ne_zero_of_ne_zero x hx0
    have hcosh0 : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
    simp only [f₁, E, D, y]
    rw [rpow_eq_exp_log (Real.cosh x) (1 / m - 1) (Real.cosh_pos x),
      rpow_eq_exp_log (Real.cosh x) (1 / n - 1) (Real.cosh_pos x),
      Real.tanh_eq_sinh_div_cosh]
    let q : ℝ :=
      (1 / m) * Real.exp (Real.log (Real.cosh x) * (1 / m - 1)) -
        (1 / n) * Real.exp (Real.log (Real.cosh x) * (1 / n - 1))
    change (Real.sinh x / Real.cosh x) / (Real.sinh x * q) =
      1 / (Real.cosh x * q)
    by_cases hq : q = 0
    · simp [hq]
    · field_simp [hsinh, hcosh0, hq]
  unfold HasLimitAtZero
  simpa [c] using hE.congr' heq.symm

theorem gap1 (m n : ℝ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ≠ n) :
    HasLimitAtZero (f₀ m n) (target m n) ↔
      HasLimitAtZero (f₁ m n) (target m n) := by
  rw [← reciprocal_eq_target m n hm hn hmn]
  constructor
  · intro _
    exact f₁_hasLimitAtZero m n hm hn hmn
  · intro _
    exact f₀_hasLimitAtZero m n hm hn hmn

theorem gap2 (m n : ℝ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ≠ n) :
    HasLimitAtZero (f₁ m n) (1 / (1 / m - 1 / n)) := by
  exact f₁_hasLimitAtZero m n hm hn hmn

theorem gap3 (m n : ℝ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ≠ n) :
    1 / (1 / m - 1 / n) = target m n := by
  exact reciprocal_eq_target m n hm hn hmn

theorem gap4 (m n : ℝ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ≠ n) :
    HasLimitAtZero (f₀ m n) (target m n) := by
  rw [← reciprocal_eq_target m n hm hn hmn]
  exact f₀_hasLimitAtZero m n hm hn hmn

end

end ProofGap.Exercise1367
