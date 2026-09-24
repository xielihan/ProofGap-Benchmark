import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1322

noncomputable section
open Filter
open scoped Topology

def punctured (x₀ : ℝ) := nhdsWithin x₀ ({x₀} : Set ℝ)ᶜ
def sec (x : ℝ) := 1 / Real.cos x
def original (x : ℝ) := Real.tan (3 * x) / Real.tan x
def firstStage (x : ℝ) := 3 * sec (3 * x) ^ 2 / sec x ^ 2
def cosineStage (x : ℝ) := 3 * (Real.cos x / Real.cos (3 * x)) ^ 2
def sineStage (x : ℝ) := 3 * (Real.sin x / (3 * Real.sin (3 * x))) ^ 2

private theorem tripleFormulas (x : ℝ) :
    Real.sin (3 * x) = Real.sin x * (4 * Real.cos x ^ 2 - 1) ∧
      Real.cos (3 * x) = Real.cos x * (4 * Real.cos x ^ 2 - 3) := by
  constructor
  · rw [show 3 * x = x + (x + x) by ring, Real.sin_add,
      Real.cos_add, Real.sin_add]
    calc
      _ = Real.sin x * (3 * Real.cos x ^ 2 - Real.sin x ^ 2) := by ring
      _ = Real.sin x * (4 * Real.cos x ^ 2 - 1) := by
        congr 1
        linarith [Real.sin_sq_add_cos_sq x]
  · rw [show 3 * x = x + (x + x) by ring, Real.cos_add,
      Real.cos_add, Real.sin_add]
    calc
      _ = Real.cos x * (Real.cos x ^ 2 - 3 * Real.sin x ^ 2) := by ring
      _ = Real.cos x * (4 * Real.cos x ^ 2 - 3) := by
        congr 1
        linarith [Real.sin_sq_add_cos_sq x]

private theorem eventuallyCosNeZero :
    ∀ᶠ x in punctured (Real.pi / 2), Real.cos x ≠ 0 := by
  let c : ℝ := Real.pi / 2
  have hle : punctured c ≤ nhds c := by
    exact inf_le_left
  have hid : Tendsto (fun x : ℝ => x) (punctured c) (nhds c) :=
    tendsto_id.mono_left hle
  have hsub : Tendsto (fun x : ℝ => x - c) (punctured c) (nhds 0) := by
    convert hid.sub_const c using 1 <;> ring
  have hsinc : Tendsto (fun x : ℝ => Real.sinc (x - c))
      (punctured c) (nhds 1) := by
    simpa using Real.continuous_sinc.continuousAt.tendsto.comp hsub
  have hsincpos : ∀ᶠ x in punctured c, 0 < Real.sinc (x - c) :=
    hsinc.eventually (isOpen_Ioi.mem_nhds (by norm_num))
  have hne : ∀ᶠ x in punctured c, x ≠ c := by
    change ∀ᶠ x in nhdsWithin c ({c} : Set ℝ)ᶜ, x ≠ c
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  change ∀ᶠ x in punctured c, Real.cos x ≠ 0
  filter_upwards [hne, hsincpos] with x hx hpos
  have ht : x - c ≠ 0 := sub_ne_zero.mpr hx
  have hsin : Real.sin (x - c) ≠ 0 := by
    intro hs
    have hz : Real.sinc (x - c) = 0 := by
      simp [Real.sinc, ht, hs]
    linarith
  rw [show x = (x - c) + c by ring, Real.cos_add]
  simp only [c, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero,
    mul_one]
  simpa only [zero_sub] using (neg_ne_zero.mpr hsin)

private theorem originalLimit :
    Tendsto original (punctured (Real.pi / 2)) (nhds (1 / 3 : ℝ)) := by
  let l := punctured (Real.pi / 2)
  have hle : l ≤ nhds (Real.pi / 2) := by
    exact inf_le_left
  have hid : Tendsto (fun x : ℝ => x) l (nhds (Real.pi / 2)) :=
    tendsto_id.mono_left hle
  have hcos : Tendsto (fun x : ℝ => Real.cos x) l (nhds 0) := by
    simpa using Real.continuous_cos.continuousAt.tendsto.comp hid
  have hsin : Tendsto (fun x : ℝ => Real.sin x) l (nhds 1) := by
    simpa using Real.continuous_sin.continuousAt.tendsto.comp hid
  have hfour : Tendsto (fun _ : ℝ => (4 : ℝ)) l (nhds 4) := tendsto_const_nhds
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) l (nhds 1) := tendsto_const_nhds
  have hthree : Tendsto (fun _ : ℝ => (3 : ℝ)) l (nhds 3) := tendsto_const_nhds
  have hN : Tendsto (fun x : ℝ => 4 * Real.cos x ^ 2 - 1) l (nhds (-1)) := by
    convert (hfour.mul (hcos.pow 2)).sub hone using 1 <;> norm_num
  have hD : Tendsto (fun x : ℝ => 4 * Real.cos x ^ 2 - 3) l (nhds (-3)) := by
    convert (hfour.mul (hcos.pow 2)).sub hthree using 1 <;> norm_num
  have hrat : Tendsto
      (fun x : ℝ => (4 * Real.cos x ^ 2 - 1) /
        (4 * Real.cos x ^ 2 - 3)) l (nhds (1 / 3 : ℝ)) := by
    convert hN.div hD (by norm_num : (-3 : ℝ) ≠ 0) using 1 <;> norm_num
  have hsinpos : ∀ᶠ x in l, 0 < Real.sin x :=
    hsin.eventually (isOpen_Ioi.mem_nhds (by norm_num))
  have hDneg : ∀ᶠ x in l, 4 * Real.cos x ^ 2 - 3 < 0 :=
    hD.eventually (isOpen_Iio.mem_nhds (by norm_num))
  apply hrat.congr'
  filter_upwards [eventuallyCosNeZero, hsinpos, hDneg] with x hcx hsx hdx
  have hsne : Real.sin x ≠ 0 := ne_of_gt hsx
  have hdne : 4 * Real.cos x ^ 2 - 3 ≠ 0 := ne_of_lt hdx
  change (4 * Real.cos x ^ 2 - 1) / (4 * Real.cos x ^ 2 - 3) = original x
  rw [original, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos,
    (tripleFormulas x).1, (tripleFormulas x).2]
  field_simp [hcx, hsne, hdne] <;> ring

private theorem cosineLimit :
    Tendsto cosineStage (punctured (Real.pi / 2)) (nhds (1 / 3 : ℝ)) := by
  let l := punctured (Real.pi / 2)
  have hle : l ≤ nhds (Real.pi / 2) := by
    exact inf_le_left
  have hid : Tendsto (fun x : ℝ => x) l (nhds (Real.pi / 2)) :=
    tendsto_id.mono_left hle
  have hcos : Tendsto (fun x : ℝ => Real.cos x) l (nhds 0) := by
    simpa using Real.continuous_cos.continuousAt.tendsto.comp hid
  have hfour : Tendsto (fun _ : ℝ => (4 : ℝ)) l (nhds 4) := tendsto_const_nhds
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) l (nhds 1) := tendsto_const_nhds
  have hthree : Tendsto (fun _ : ℝ => (3 : ℝ)) l (nhds 3) := tendsto_const_nhds
  have hD : Tendsto (fun x : ℝ => 4 * Real.cos x ^ 2 - 3) l (nhds (-3)) := by
    convert (hfour.mul (hcos.pow 2)).sub hthree using 1 <;> norm_num
  have hinv : Tendsto (fun x : ℝ => 1 / (4 * Real.cos x ^ 2 - 3))
      l (nhds (-1 / 3 : ℝ)) := by
    convert hone.div hD (by norm_num : (-3 : ℝ) ≠ 0) using 1 <;> norm_num
  have hbase : Tendsto
      (fun x : ℝ => 3 * (1 / (4 * Real.cos x ^ 2 - 3)) ^ 2)
      l (nhds (1 / 3 : ℝ)) := by
    convert hthree.mul (hinv.pow 2) using 1 <;> norm_num
  apply hbase.congr'
  filter_upwards [eventuallyCosNeZero] with x hcx
  change 3 * (1 / (4 * Real.cos x ^ 2 - 3)) ^ 2 = cosineStage x
  rw [cosineStage, (tripleFormulas x).2]
  by_cases hd : 4 * Real.cos x ^ 2 - 3 = 0
  · simp [hd]
  · field_simp [hcx, hd] <;> ring

private theorem sineLimit :
    Tendsto sineStage (punctured (Real.pi / 2)) (nhds (1 / 3 : ℝ)) := by
  let l := punctured (Real.pi / 2)
  have hle : l ≤ nhds (Real.pi / 2) := by
    exact inf_le_left
  have hid : Tendsto (fun x : ℝ => x) l (nhds (Real.pi / 2)) :=
    tendsto_id.mono_left hle
  have hcos : Tendsto (fun x : ℝ => Real.cos x) l (nhds 0) := by
    simpa using Real.continuous_cos.continuousAt.tendsto.comp hid
  have hsin : Tendsto (fun x : ℝ => Real.sin x) l (nhds 1) := by
    simpa using Real.continuous_sin.continuousAt.tendsto.comp hid
  have hfour : Tendsto (fun _ : ℝ => (4 : ℝ)) l (nhds 4) := tendsto_const_nhds
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) l (nhds 1) := tendsto_const_nhds
  have hthree : Tendsto (fun _ : ℝ => (3 : ℝ)) l (nhds 3) := tendsto_const_nhds
  have hN : Tendsto (fun x : ℝ => 4 * Real.cos x ^ 2 - 1) l (nhds (-1)) := by
    convert (hfour.mul (hcos.pow 2)).sub hone using 1 <;> norm_num
  have hprod : Tendsto
      (fun x : ℝ => Real.sin x * (4 * Real.cos x ^ 2 - 1))
      l (nhds (-1)) := by
    convert hsin.mul hN using 1 <;> norm_num
  have hsin3 : Tendsto (fun x : ℝ => Real.sin (3 * x)) l (nhds (-1)) := by
    apply hprod.congr'
    exact Filter.Eventually.of_forall (fun x => (tripleFormulas x).1.symm)
  have hden : Tendsto (fun x : ℝ => 3 * Real.sin (3 * x)) l (nhds (-3)) := by
    convert hthree.mul hsin3 using 1 <;> norm_num
  have hquot : Tendsto
      (fun x : ℝ => Real.sin x / (3 * Real.sin (3 * x)))
      l (nhds (-1 / 3 : ℝ)) := by
    convert hsin.div hden (by norm_num : (-3 : ℝ) ≠ 0) using 1 <;> norm_num
  have hout := hthree.mul (hquot.pow 2)
  have hval : 3 * (-1 / 3 : ℝ) ^ 2 = 1 / 3 := by norm_num
  simpa only [sineStage, hval] using hout

theorem gap1 : Tendsto original (punctured (Real.pi / 2)) (nhds (1 / 3 : ℝ)) := by
  exact originalLimit
theorem gap2 : Tendsto firstStage (punctured (Real.pi / 2)) (nhds (1 / 3 : ℝ)) := by
  apply cosineLimit.congr'
  filter_upwards [eventuallyCosNeZero] with x hcx
  change cosineStage x = firstStage x
  simp only [cosineStage, firstStage, sec]
  rw [(tripleFormulas x).2]
  by_cases hd : 4 * Real.cos x ^ 2 - 3 = 0
  · simp [hd]
  · field_simp [hcx, hd] <;> ring
theorem gap3 : Tendsto cosineStage (punctured (Real.pi / 2)) (nhds (1 / 3 : ℝ)) := by
  exact cosineLimit
theorem gap4 : Tendsto sineStage (punctured (Real.pi / 2)) (nhds (1 / 3 : ℝ)) := by
  exact sineLimit
theorem gap5 : Tendsto original (punctured (Real.pi / 2)) (nhds (1 / 3 : ℝ)) := by
  exact originalLimit

end
end ProofGap.Exercise1322
