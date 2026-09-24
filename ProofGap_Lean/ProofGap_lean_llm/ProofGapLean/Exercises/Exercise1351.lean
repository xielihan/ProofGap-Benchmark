import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1351

noncomputable section

def HasLimitAtTop (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

def angle (x : ℝ) : ℝ := Real.pi * x / (2 * x + 1)
def doubleAngle (x : ℝ) : ℝ := 2 * Real.pi * x / (2 * x + 1)
def f₀ (x : ℝ) : ℝ := (1 / x) * Real.log (Real.tan (angle x))
def f₁ (x : ℝ) : ℝ :=
  (Real.pi / (1 + 2 * x) ^ 2) /
    (Real.tan (angle x) * Real.cos (angle x) ^ 2)
def f₂ (x : ℝ) : ℝ :=
  2 * Real.pi * ((1 / (1 + 2 * x) ^ 2) / Real.sin (doubleAngle x))
def f₃ (x : ℝ) : ℝ :=
  2 * Real.pi *
    ((-4 / (1 + 2 * x) ^ 3) /
      ((2 * Real.pi / (1 + 2 * x) ^ 2) * Real.cos (doubleAngle x)))
def f₄ (x : ℝ) : ℝ := -4 * (1 / ((1 + 2 * x) * Real.cos (doubleAngle x)))
def powerForm (x : ℝ) : ℝ := Real.rpow (Real.tan (angle x)) (1 / x)

private theorem baseLimits :
    HasLimitAtTop f₀ 0 ∧ HasLimitAtTop f₁ 0 ∧ HasLimitAtTop f₂ 0 ∧
      HasLimitAtTop f₃ 0 ∧ HasLimitAtTop f₄ 0 ∧
        HasLimitAtTop powerForm (Real.exp 0) := by
  let z : ℝ → ℝ := fun x => 1 / (2 * x + 1)
  let u : ℝ → ℝ := fun x => Real.pi * z x / 2
  let v : ℝ → ℝ := fun x => Real.pi * z x
  let r : ℝ → ℝ := fun x => Real.tan (angle x) / x

  have hinv : Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
  have hden : Filter.Tendsto (fun x : ℝ => 2 + 1 / x) Filter.atTop (nhds 2) := by
    simpa using
      ((tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) Filter.atTop (nhds 2)).add hinv)
  have hzRaw :
      Filter.Tendsto (fun x : ℝ => (1 / x) / (2 + 1 / x))
        Filter.atTop (nhds 0) := by
    simpa using hinv.div hden (by norm_num : (2 : ℝ) ≠ 0)
  have hz : Filter.Tendsto z Filter.atTop (nhds 0) := by
    refine hzRaw.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    have hd0 : 2 * x + 1 ≠ 0 := by linarith
    dsimp [z]
    field_simp [hx0, hd0]
    <;> ring
  have hhalfRaw :
      Filter.Tendsto
        ((fun _ : ℝ => (1 : ℝ)) / (fun x : ℝ => 2 + 1 / x))
        Filter.atTop (nhds (1 / 2 : ℝ)) := by
    exact
      (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1)).div
        hden (by norm_num : (2 : ℝ) ≠ 0)
  have hhalf :
      Filter.Tendsto (fun x : ℝ => x * z x) Filter.atTop (nhds (1 / 2 : ℝ)) := by
    refine hhalfRaw.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    have hd0 : 2 * x + 1 ≠ 0 := by linarith
    dsimp [z]
    field_simp [hx0, hd0]
    <;> ring_nf
  have hu : Filter.Tendsto u Filter.atTop (nhds 0) := by
    have h :=
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ => Real.pi / 2) Filter.atTop
          (nhds (Real.pi / 2))).mul hz
    convert h using 1
    · funext x
      dsimp [u]
      ring
    · ring
  have hv : Filter.Tendsto v Filter.atTop (nhds 0) := by
    have h :=
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ => Real.pi) Filter.atTop
          (nhds Real.pi)).mul hz
    simpa [v] using h
  have hux :
      Filter.Tendsto (fun x : ℝ => u x * x) Filter.atTop
        (nhds (Real.pi / 4)) := by
    have h :=
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ => Real.pi / 2) Filter.atTop
          (nhds (Real.pi / 2))).mul hhalf
    convert h using 1
    · funext x
      dsimp [u]
      ring
    · ring
  have hcosu :
      Filter.Tendsto (fun x => Real.cos (u x)) Filter.atTop (nhds 1) := by
    simpa using Real.continuous_cos.continuousAt.tendsto.comp hu
  have hcosv :
      Filter.Tendsto (fun x => Real.cos (v x)) Filter.atTop (nhds 1) := by
    simpa using Real.continuous_cos.continuousAt.tendsto.comp hv
  have hsincu :
      Filter.Tendsto (fun x => Real.sinc (u x)) Filter.atTop (nhds 1) := by
    simpa using Real.continuous_sinc.continuousAt.tendsto.comp hu
  have hsincv :
      Filter.Tendsto (fun x => Real.sinc (v x)) Filter.atTop (nhds 1) := by
    simpa using Real.continuous_sinc.continuousAt.tendsto.comp hv
  have hgeom : ∀ᶠ x : ℝ in Filter.atTop,
      0 < x ∧ 0 < z x ∧ 0 < u x ∧ 0 < v x := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hd : 0 < 2 * x + 1 := by linarith
    have hzpos : 0 < z x := by
      dsimp [z]
      exact one_div_pos.mpr hd
    have hupos : 0 < u x := by
      dsimp [u]
      exact div_pos (mul_pos Real.pi_pos hzpos) (by norm_num)
    have hvpos : 0 < v x := by
      dsimp [v]
      exact mul_pos Real.pi_pos hzpos
    exact ⟨by linarith, hzpos, hupos, hvpos⟩
  have hcosuPos : ∀ᶠ x : ℝ in Filter.atTop, 0 < Real.cos (u x) :=
    (tendsto_order.1 hcosu).1 0 zero_lt_one
  have hcosvPos : ∀ᶠ x : ℝ in Filter.atTop, 0 < Real.cos (v x) :=
    (tendsto_order.1 hcosv).1 0 zero_lt_one
  have hsincuPos : ∀ᶠ x : ℝ in Filter.atTop, 0 < Real.sinc (u x) :=
    (tendsto_order.1 hsincu).1 0 zero_lt_one
  have hsincvPos : ∀ᶠ x : ℝ in Filter.atTop, 0 < Real.sinc (v x) :=
    (tendsto_order.1 hsincv).1 0 zero_lt_one

  have hrSimple :
      Filter.Tendsto
        (fun x : ℝ => Real.cos (u x) / ((u x * x) * Real.sinc (u x)))
        Filter.atTop (nhds (4 / Real.pi)) := by
    have h := hcosu.div (hux.mul hsincu) (by
      have hp : Real.pi ≠ 0 := Real.pi_ne_zero
      norm_num [hp])
    convert h using 1 <;> field_simp [Real.pi_ne_zero] <;> ring
  have hr : Filter.Tendsto r Filter.atTop (nhds (4 / Real.pi)) := by
    refine hrSimple.congr' ?_
    filter_upwards [hgeom, hcosuPos, hsincuPos] with x hx hcu hsu
    rcases hx with ⟨hx, hz, hu0, hv0⟩
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hd0 : 2 * x + 1 ≠ 0 := by linarith
    have ha : angle x = Real.pi / 2 - u x := by
      dsimp [angle, u, z]
      field_simp [hd0]
      <;> ring
    have hsincEq : Real.sinc (u x) = Real.sin (u x) / u x := by
      simp [Real.sinc, ne_of_gt hu0]
    dsimp [r]
    rw [ha, Real.tan_eq_sin_div_cos]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    rw [hsincEq]
    field_simp [hx0, ne_of_gt hu0, ne_of_gt hcu, ne_of_gt hsu]
    <;> dsimp [u, z]
    <;> field_simp [hd0]
    <;> ring
  have hcpos : 0 < 4 / Real.pi := div_pos (by norm_num) Real.pi_pos
  have hrpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < r x :=
    (tendsto_order.1 hr).1 0 hcpos
  have hlogr :
      Filter.Tendsto (fun x => Real.log (r x)) Filter.atTop
        (nhds (Real.log (4 / Real.pi))) := by
    exact (Real.continuousAt_log (ne_of_gt hcpos)).tendsto.comp hr
  have hlogdiv :
      Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
    simpa only [id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hf0Simple :
      Filter.Tendsto
        (fun x : ℝ => Real.log x / x + (1 / x) * Real.log (r x))
        Filter.atTop (nhds 0) := by
    simpa using hlogdiv.add (hinv.mul hlogr)
  have hf0 : HasLimitAtTop f₀ 0 := by
    unfold HasLimitAtTop
    refine hf0Simple.congr' ?_
    filter_upwards [hgeom, hrpos] with x hx hrx
    rcases hx with ⟨hx, hz, hu0, hv0⟩
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hr0 : r x ≠ 0 := ne_of_gt hrx
    have htan : Real.tan (angle x) = x * r x := by
      dsimp [r]
      field_simp [hx0]
    rw [f₀, htan, Real.log_mul hx0 hr0]
    ring

  have hf1Simple :
      Filter.Tendsto
        (fun x : ℝ => (2 * z x) / (Real.cos (u x) * Real.sinc (u x)))
        Filter.atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds.mul hz).div (hcosu.mul hsincu)
        (by norm_num : (1 : ℝ) * 1 ≠ 0))
  have hf1 : HasLimitAtTop f₁ 0 := by
    unfold HasLimitAtTop
    refine hf1Simple.congr' ?_
    filter_upwards [hgeom, hcosuPos, hsincuPos] with x hx hcu hsu
    rcases hx with ⟨hx, hz, hu0, hv0⟩
    have hd0 : 2 * x + 1 ≠ 0 := by linarith
    have hd1 : 1 + 2 * x ≠ 0 := by linarith
    have ha : angle x = Real.pi / 2 - u x := by
      dsimp [angle, u, z]
      field_simp [hd0]
      <;> ring
    have hsincEq : Real.sinc (u x) = Real.sin (u x) / u x := by
      simp [Real.sinc, ne_of_gt hu0]
    rw [f₁, ha, Real.tan_eq_sin_div_cos]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    rw [hsincEq]
    field_simp [hd0, hd1, ne_of_gt hu0, ne_of_gt hcu, ne_of_gt hsu,
      Real.pi_ne_zero]
    <;> dsimp [u, z]
    <;> field_simp [hd0, hd1]
    <;> ring

  have hf2Simple :
      Filter.Tendsto (fun x : ℝ => (2 * z x) / Real.sinc (v x))
        Filter.atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds.mul hz).div hsincv (by norm_num : (1 : ℝ) ≠ 0))
  have hf2 : HasLimitAtTop f₂ 0 := by
    unfold HasLimitAtTop
    refine hf2Simple.congr' ?_
    filter_upwards [hgeom, hsincvPos] with x hx hsv
    rcases hx with ⟨hx, hz, hu0, hv0⟩
    have hd0 : 2 * x + 1 ≠ 0 := by linarith
    have hd1 : 1 + 2 * x ≠ 0 := by linarith
    have hda : doubleAngle x = Real.pi - v x := by
      dsimp [doubleAngle, v, z]
      field_simp [hd0]
      <;> ring
    have hsincEq : Real.sinc (v x) = Real.sin (v x) / v x := by
      simp [Real.sinc, ne_of_gt hv0]
    rw [f₂, hda, Real.sin_pi_sub, hsincEq]
    field_simp [hd0, hd1, ne_of_gt hv0, ne_of_gt hsv, Real.pi_ne_zero]
    <;> dsimp [v, z]
    <;> field_simp [hd0, hd1]
    <;> ring

  have hf4Simple :
      Filter.Tendsto (fun x : ℝ => (4 * z x) / Real.cos (v x))
        Filter.atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds.mul hz).div hcosv (by norm_num : (1 : ℝ) ≠ 0))
  have hf4 : HasLimitAtTop f₄ 0 := by
    unfold HasLimitAtTop
    refine hf4Simple.congr' ?_
    filter_upwards [hgeom, hcosvPos] with x hx hcv
    rcases hx with ⟨hx, hz, hu0, hv0⟩
    have hd0 : 2 * x + 1 ≠ 0 := by linarith
    have hd1 : 1 + 2 * x ≠ 0 := by linarith
    have hda : doubleAngle x = Real.pi - v x := by
      dsimp [doubleAngle, v, z]
      field_simp [hd0]
      <;> ring
    rw [f₄, hda, Real.cos_pi_sub]
    field_simp [hd0, hd1, ne_of_gt hcv]
    <;> dsimp [z]
    <;> field_simp [hd0, hd1]
    <;> ring

  have hf3 : HasLimitAtTop f₃ 0 := by
    unfold HasLimitAtTop
    refine hf4Simple.congr' ?_
    filter_upwards [hgeom, hcosvPos] with x hx hcv
    rcases hx with ⟨hx, hz, hu0, hv0⟩
    have hd0 : 1 + 2 * x ≠ 0 := by linarith
    have hd0' : 2 * x + 1 ≠ 0 := by linarith
    have hda : doubleAngle x = Real.pi - v x := by
      dsimp [doubleAngle, v, z]
      field_simp [hd0']
      <;> ring
    rw [f₃, hda, Real.cos_pi_sub]
    field_simp [hd0, hd0', ne_of_gt hcv, Real.pi_ne_zero]
    <;> dsimp [z]
    <;> field_simp [hd0, hd0']
    <;> ring

  have htanpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < Real.tan (angle x) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), hrpos] with x hx hrx
    have hxpos : 0 < x := by linarith
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have htan : Real.tan (angle x) = x * r x := by
      dsimp [r]
      field_simp [hx0]
    rw [htan]
    exact mul_pos hxpos hrx
  have hpowEq :
      (fun x => powerForm x) =ᶠ[Filter.atTop]
        (fun x => Real.exp (f₀ x)) := by
    filter_upwards [htanpos] with x hx
    have hpowdef :
        Real.rpow (Real.tan (angle x)) (1 / x) =
          Real.exp (Real.log (Real.tan (angle x)) * (1 / x)) := by
      exact Real.rpow_def_of_pos hx (1 / x)
    rw [powerForm]
    calc
      Real.rpow (Real.tan (angle x)) (1 / x) =
          Real.exp (Real.log (Real.tan (angle x)) * (1 / x)) := hpowdef
      _ = Real.exp (f₀ x) := by
        congr 1
        rw [f₀]
        ring
  have hpow : HasLimitAtTop powerForm (Real.exp 0) := by
    unfold HasLimitAtTop
    have he := Real.continuous_exp.continuousAt.tendsto.comp hf0
    exact he.congr' hpowEq.symm
  exact ⟨hf0, hf1, hf2, hf3, hf4, hpow⟩

theorem gap1 : HasLimitAtTop f₀ 0 ↔ HasLimitAtTop f₁ 0 := by
  constructor
  · intro _
    exact baseLimits.2.1
  · intro _
    exact baseLimits.1
theorem gap2 : HasLimitAtTop f₀ 0 ↔ HasLimitAtTop f₂ 0 := by
  constructor
  · intro _
    exact baseLimits.2.2.1
  · intro _
    exact baseLimits.1
theorem gap3 : HasLimitAtTop f₂ 0 ↔ HasLimitAtTop f₃ 0 := by
  constructor
  · intro _
    exact baseLimits.2.2.2.1
  · intro _
    exact baseLimits.2.2.1
theorem gap4 : HasLimitAtTop f₀ 0 ↔ HasLimitAtTop f₃ 0 := by
  exact gap2.trans gap3
theorem gap5 : HasLimitAtTop f₀ 0 ↔ HasLimitAtTop f₄ 0 := by
  constructor
  · intro _
    exact baseLimits.2.2.2.2.1
  · intro _
    exact baseLimits.1
theorem gap6 : HasLimitAtTop f₄ 0 := by
  exact baseLimits.2.2.2.2.1
theorem gap7 : HasLimitAtTop f₀ 0 := by
  exact gap5.mpr gap6
theorem gap8 : HasLimitAtTop powerForm (Real.exp 0) := by
  exact baseLimits.2.2.2.2.2
theorem gap9 : Real.exp 0 = 1 := by
  exact Real.exp_zero
theorem gap10 : HasLimitAtTop powerForm 1 := by
  simpa [gap9] using gap8

end

end ProofGap.Exercise1351
