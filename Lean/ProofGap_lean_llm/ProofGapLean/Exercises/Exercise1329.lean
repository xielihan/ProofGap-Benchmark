import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise1329

noncomputable section
open Filter
open scoped Topology

def punctured (x₀ : ℝ) := nhdsWithin x₀ ({x₀} : Set ℝ)ᶜ
def apow (a x : ℝ) := Real.rpow a x
def original (a x : ℝ) := (apow a x - apow a (Real.sin x)) / x ^ 3
def firstStage (a x : ℝ) :=
  ((apow a x - apow a (Real.sin x) * Real.cos x) * Real.log a) /
    (3 * x ^ 2)
def secondStage (a x : ℝ) :=
  (Real.log a / 3) *
    ((apow a x * Real.log a +
      apow a (Real.sin x) * Real.sin x -
      apow a (Real.sin x) * Real.log a * Real.cos x ^ 2) / (2 * x))
def finalStage (a x : ℝ) :=
  (Real.log a / 6) *
    (apow a x * Real.log a ^ 2 +
      apow a (Real.sin x) * Real.cos x +
      apow a (Real.sin x) * Real.log a * Real.sin x * Real.cos x +
      apow a (Real.sin x) * Real.log a * Real.sin (2 * x) -
      apow a (Real.sin x) * Real.log a ^ 2 * Real.cos x ^ 3)

private theorem tendsto_id_punctured :
    Tendsto (fun x : ℝ => x) (punctured 0) (nhds 0) :=
  tendsto_id.mono_left inf_le_left

private theorem finalStage_limit (a : ℝ) (ha : 0 < a) :
    Tendsto (finalStage a) (punctured 0) (nhds (Real.log a / 6)) := by
  have hid := tendsto_id_punctured
  have hsin : Tendsto Real.sin (punctured 0) (nhds 0) := by
    simpa [punctured] using
      ((Real.continuous_sin.continuousAt : ContinuousAt Real.sin 0).tendsto).mono_left
        inf_le_left
  have hcos : Tendsto Real.cos (punctured 0) (nhds 1) := by
    simpa using
      ((Real.continuous_cos.continuousAt : ContinuousAt Real.cos 0).tendsto).mono_left
        inf_le_left
  have hsin2 : Tendsto (fun x : ℝ => Real.sin (2 * x)) (punctured 0) (nhds 0) := by
    have htwo : Tendsto (fun x : ℝ => 2 * x) (punctured 0) (nhds 0) := by
      convert tendsto_const_nhds.mul hid using 1 <;> norm_num
    simpa [Function.comp_def] using
      (Real.continuous_sin.continuousAt : ContinuousAt Real.sin 0).tendsto.comp htwo
  have hpow : Tendsto (apow a) (punctured 0) (nhds 1) := by
    have hd := (hasDerivAt_id (0 : ℝ)).const_rpow ha
    simpa [apow] using hd.continuousAt.tendsto.mono_left inf_le_left
  have hpowsin : Tendsto (fun x : ℝ => apow a (Real.sin x))
      (punctured 0) (nhds 1) := by
    have hd := (hasDerivAt_id (0 : ℝ)).const_rpow ha
    simpa [Function.comp_def, apow] using hd.continuousAt.tendsto.comp hsin
  have hlog :
      Tendsto (fun _ : ℝ => Real.log a) (punctured 0) (nhds (Real.log a)) :=
    tendsto_const_nhds
  have hlog2 :
      Tendsto (fun _ : ℝ => Real.log a ^ 2) (punctured 0) (nhds (Real.log a ^ 2)) :=
    tendsto_const_nhds
  have ht1 := hpow.mul hlog2
  have ht2 := hpowsin.mul hcos
  have ht3 := ((hpowsin.mul hlog).mul hsin).mul hcos
  have ht4 := (hpowsin.mul hlog).mul hsin2
  have ht5 := (hpowsin.mul hlog2).mul (hcos.pow 3)
  have hbracket := (((ht1.add ht2).add ht3).add ht4).sub ht5
  convert tendsto_const_nhds.mul hbracket using 1 <;>
    norm_num [finalStage] <;> ring

private theorem secondStage_limit (a : ℝ) (ha : 0 < a) :
    Tendsto (secondStage a) (punctured 0) (nhds (Real.log a / 6)) := by
  let N : ℝ → ℝ := fun x =>
    apow a x * Real.log a +
      apow a (Real.sin x) * Real.sin x -
      apow a (Real.sin x) * Real.log a * Real.cos x ^ 2
  have hA : HasDerivAt (apow a) (Real.log a) 0 := by
    simpa [apow] using (hasDerivAt_id (0 : ℝ)).const_rpow ha
  have hs : HasDerivAt Real.sin 1 0 := by
    simpa using Real.hasDerivAt_sin 0
  have hc : HasDerivAt Real.cos 0 0 := by
    simpa using Real.hasDerivAt_cos 0
  have hB : HasDerivAt (fun x : ℝ => apow a (Real.sin x)) (Real.log a) 0 := by
    simpa [apow] using hs.const_rpow ha
  have hN : HasDerivAt N 1 0 := by
    have hraw := (hA.const_mul (Real.log a)).add (hB.mul hs) |>.sub
      (((hB.const_mul (Real.log a)).mul (hc.pow 2)))
    convert hraw using 1
    · funext y
      dsimp [N]
      ring
    · norm_num [apow]
  have hslope : Tendsto (slope N 0) (punctured 0) (nhds 1) :=
    hasDerivAt_iff_tendsto_slope.mp hN
  have hlim :
      Tendsto (fun x : ℝ => (Real.log a / 6) * slope N 0 x)
        (punctured 0) (nhds (Real.log a / 6)) := by
    convert tendsto_const_nhds.mul hslope using 1 <;> ring
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp only [slope_def_field]
  simp [N, secondStage, apow]
  field_simp [hx0]
  ring

private theorem firstStage_limit (a : ℝ) (ha : 0 < a) :
    Tendsto (firstStage a) (punctured 0) (nhds (Real.log a / 6)) := by
  let M : ℝ → ℝ := fun x =>
    (apow a x - apow a (Real.sin x) * Real.cos x) * Real.log a
  let N : ℝ → ℝ := fun x =>
    apow a x * Real.log a +
      apow a (Real.sin x) * Real.sin x -
      apow a (Real.sin x) * Real.log a * Real.cos x ^ 2
  have hM :
      ∀ᶠ x : ℝ in punctured 0,
        HasDerivAt M (Real.log a * N x) x := by
    filter_upwards with x
    have hA : HasDerivAt (apow a) (Real.log a * apow a x) x := by
      simpa [apow] using (hasDerivAt_id x).const_rpow ha
    have hs := Real.hasDerivAt_sin x
    have hc := Real.hasDerivAt_cos x
    have hB :
        HasDerivAt (fun y : ℝ => apow a (Real.sin y))
          (Real.log a * Real.cos x * apow a (Real.sin x)) x := by
      simpa [apow] using hs.const_rpow ha
    have hraw := (hA.sub (hB.mul hc)).const_mul (Real.log a)
    convert hraw using 1
    · funext y
      dsimp [M]
      ring
    · dsimp [N]
      ring
  have hden :
      ∀ᶠ x : ℝ in punctured 0,
        HasDerivAt (fun y : ℝ => 3 * y ^ 2) (6 * x) x := by
    filter_upwards with x
    convert ((hasDerivAt_id x).pow 2).const_mul 3 using 1 <;>
      simp [id] <;> ring
  have hden_ne : ∀ᶠ x : ℝ in punctured 0, 6 * x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (by simpa using hx)
  have hzeroM : Tendsto M (punctured 0) (nhds 0) := by
    have hA : Tendsto (apow a) (nhds 0) (nhds 1) := by
      simpa [apow] using
        ((hasDerivAt_id (0 : ℝ)).const_rpow ha).continuousAt.tendsto
    have hs : Tendsto Real.sin (nhds 0) (nhds 0) := by
      simpa using
        (Real.continuous_sin.continuousAt : ContinuousAt Real.sin 0).tendsto
    have hB : Tendsto (fun x : ℝ => apow a (Real.sin x)) (nhds 0) (nhds 1) :=
      by simpa [Function.comp_def] using hA.comp hs
    have hc : Tendsto Real.cos (nhds 0) (nhds 1) := by
      simpa using
        (Real.continuous_cos.continuousAt : ContinuousAt Real.cos 0).tendsto
    have hlog :
        Tendsto (fun _ : ℝ => Real.log a) (nhds 0) (nhds (Real.log a)) :=
      tendsto_const_nhds
    have hm := (hA.sub (hB.mul hc)).mul hlog
    simpa [M] using hm.mono_left inf_le_left
  have hzeroDen : Tendsto (fun y : ℝ => 3 * y ^ 2) (punctured 0) (nhds 0) := by
    convert tendsto_const_nhds.mul (tendsto_id_punctured.pow 2) using 1 <;>
      norm_num
  apply HasDerivAt.lhopital_zero_nhdsNE hM hden hden_ne hzeroM hzeroDen
  have hsecond := secondStage_limit a ha
  apply hsecond.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  dsimp [N, secondStage]
  field_simp [hx0]
  ring

private theorem original_limit (a : ℝ) (ha : 0 < a) :
    Tendsto (original a) (punctured 0) (nhds (Real.log a / 6)) := by
  let F : ℝ → ℝ := fun x => apow a x - apow a (Real.sin x)
  let M : ℝ → ℝ := fun x =>
    (apow a x - apow a (Real.sin x) * Real.cos x) * Real.log a
  have hF :
      ∀ᶠ x : ℝ in punctured 0, HasDerivAt F (M x) x := by
    filter_upwards with x
    have hA : HasDerivAt (apow a) (Real.log a * apow a x) x := by
      simpa [apow] using (hasDerivAt_id x).const_rpow ha
    have hs := Real.hasDerivAt_sin x
    have hB :
        HasDerivAt (fun y : ℝ => apow a (Real.sin y))
          (Real.log a * Real.cos x * apow a (Real.sin x)) x := by
      simpa [apow] using hs.const_rpow ha
    have hraw := hA.sub hB
    convert hraw using 1
    dsimp [M]
    ring
  have hden :
      ∀ᶠ x : ℝ in punctured 0,
        HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    filter_upwards with x
    simpa [id, mul_comm] using (hasDerivAt_id x).pow 3
  have hden_ne : ∀ᶠ x : ℝ in punctured 0, 3 * x ^ 2 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hx0)
  have hzeroF : Tendsto F (punctured 0) (nhds 0) := by
    have hA : Tendsto (apow a) (nhds 0) (nhds 1) := by
      simpa [apow] using
        ((hasDerivAt_id (0 : ℝ)).const_rpow ha).continuousAt.tendsto
    have hs : Tendsto Real.sin (nhds 0) (nhds 0) := by
      simpa using
        (Real.continuous_sin.continuousAt : ContinuousAt Real.sin 0).tendsto
    have hB : Tendsto (fun x : ℝ => apow a (Real.sin x)) (nhds 0) (nhds 1) :=
      by simpa [Function.comp_def] using hA.comp hs
    simpa [F] using (hA.sub hB).mono_left inf_le_left
  have hzeroDen : Tendsto (fun y : ℝ => y ^ 3) (punctured 0) (nhds 0) := by
    convert tendsto_id_punctured.pow 3 using 1 <;> norm_num
  apply HasDerivAt.lhopital_zero_nhdsNE hF hden hden_ne hzeroF hzeroDen
  simpa [M, firstStage] using firstStage_limit a ha

theorem gap1 (a : ℝ) (ha : 0 < a) :
    Tendsto (original a) (punctured 0) (nhds (Real.log a / 6)) := by exact original_limit a ha
theorem gap2 (a : ℝ) (ha : 0 < a) :
    Tendsto (secondStage a) (punctured 0) (nhds (Real.log a / 6)) := by exact secondStage_limit a ha
theorem gap3 (a : ℝ) (ha : 0 < a) :
    Tendsto (finalStage a) (punctured 0) (nhds (Real.log a / 6)) := by exact finalStage_limit a ha
theorem gap4 (a : ℝ) (ha : 0 < a) :
    Tendsto (finalStage a) (punctured 0) (nhds (Real.log a / 6)) := by exact finalStage_limit a ha
theorem gap5 (a : ℝ) (ha : 0 < a) :
    Tendsto (original a) (punctured 0) (nhds (Real.log a / 6)) := by exact original_limit a ha

end
end ProofGap.Exercise1329
