import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace ProofGap.Exercise1327

noncomputable section
open Filter
open scoped Topology

def punctured (x₀ : ℝ) := nhdsWithin x₀ ({x₀} : Set ℝ)ᶜ
def original (x : ℝ) :=
  (Real.arcsin (2 * x) - 2 * Real.arcsin x) / x ^ 3
def firstStage (x : ℝ) :=
  (2 / Real.sqrt (1 - 4 * x ^ 2) - 2 / Real.sqrt (1 - x ^ 2)) /
    (3 * x ^ 2)
def secondStage (x : ℝ) :=
  2 * (4 * x / Real.rpow (1 - 4 * x ^ 2) (3 / 2 : ℝ) -
    x / Real.rpow (1 - x ^ 2) (3 / 2 : ℝ)) / (6 * x)
def finalStage (x : ℝ) :=
  (1 / 3 : ℝ) * (4 / Real.rpow (1 - 4 * x ^ 2) (3 / 2 : ℝ) -
    1 / Real.rpow (1 - x ^ 2) (3 / 2 : ℝ))

private theorem tendsto_id_punctured :
    Tendsto (fun x : ℝ => x) (punctured 0) (nhds 0) := by
  exact tendsto_id.mono_left inf_le_left

private theorem finalStage_limit :
    Tendsto finalStage (punctured 0) (nhds 1) := by
  have hid := tendsto_id_punctured
  have hu4 : Tendsto (fun x : ℝ => 1 - 4 * x ^ 2) (punctured 0) (nhds 1) := by
    convert tendsto_const_nhds.sub (tendsto_const_nhds.mul (hid.pow 2)) using 1 <;>
      norm_num
  have hu1 : Tendsto (fun x : ℝ => 1 - x ^ 2) (punctured 0) (nhds 1) := by
    convert tendsto_const_nhds.sub (hid.pow 2) using 1 <;> norm_num
  have hr4 := hu4.rpow_const (p := (3 / 2 : ℝ)) (Or.inl one_ne_zero)
  have hr1 := hu1.rpow_const (p := (3 / 2 : ℝ)) (Or.inl one_ne_zero)
  have h4 :
      Tendsto (fun x : ℝ => 4 / Real.rpow (1 - 4 * x ^ 2) (3 / 2 : ℝ))
        (punctured 0) (nhds 4) := by
    simpa using (tendsto_const_nhds.div hr4 (by norm_num) :
      Tendsto (fun x : ℝ => 4 / Real.rpow (1 - 4 * x ^ 2) (3 / 2 : ℝ))
        (punctured 0) (nhds (4 / Real.rpow 1 (3 / 2 : ℝ))))
  have h1 :
      Tendsto (fun x : ℝ => 1 / Real.rpow (1 - x ^ 2) (3 / 2 : ℝ))
        (punctured 0) (nhds 1) := by
    simpa only [one_div, Real.one_rpow, inv_one] using hr1.inv₀ (by norm_num)
  convert tendsto_const_nhds.mul (h4.sub h1) using 1 <;>
    norm_num [finalStage]

private theorem secondStage_limit :
    Tendsto secondStage (punctured 0) (nhds 1) := by
  apply finalStage_limit.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  let q : ℝ :=
    4 / Real.rpow (1 - 4 * x ^ 2) (3 / 2 : ℝ) -
      1 / Real.rpow (1 - x ^ 2) (3 / 2 : ℝ)
  have hfactor :
      4 * x / Real.rpow (1 - 4 * x ^ 2) (3 / 2 : ℝ) -
          x / Real.rpow (1 - x ^ 2) (3 / 2 : ℝ) =
        x * q := by
    dsimp [q]
    ring
  rw [secondStage, finalStage, hfactor]
  symm
  change 2 * (x * q) / (6 * x) = (1 / 3 : ℝ) * q
  field_simp [hx0]
  ring

private theorem square_to_punctured :
    Tendsto (fun x : ℝ => x ^ 2) (punctured 0) (punctured 0) := by
  unfold punctured
  rw [tendsto_nhdsWithin_iff]
  constructor
  · convert tendsto_id_punctured.pow 2 using 1 <;> norm_num
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
    exact pow_ne_zero 2 hx

private theorem four_square_to_punctured :
    Tendsto (fun x : ℝ => 4 * x ^ 2) (punctured 0) (punctured 0) := by
  unfold punctured
  rw [tendsto_nhdsWithin_iff]
  constructor
  · convert tendsto_const_nhds.mul (tendsto_id_punctured.pow 2) using 1 <;>
      norm_num
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)

private theorem firstStage_limit :
    Tendsto firstStage (punctured 0) (nhds 1) := by
  let h : ℝ → ℝ := fun y => 2 / Real.sqrt (1 - y)
  have hinner : HasDerivAt (fun y : ℝ => 1 - y) (-1) 0 := by
    convert hasDerivAt_const (x := 0) (c := (1 : ℝ)) |>.sub (hasDerivAt_id 0) using 1 <;>
      norm_num
  have hsqrt : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y)) (-1 / 2) 0 := by
    convert hinner.sqrt (by norm_num) using 1 <;> norm_num
  have hh : HasDerivAt h 1 0 := by
    dsimp [h]
    convert (hasDerivAt_const (x := 0) (c := (2 : ℝ))).div hsqrt (by norm_num) using 1 <;>
      norm_num
  have hslope : Tendsto (slope h 0) (punctured 0) (nhds 1) :=
    hasDerivAt_iff_tendsto_slope.mp hh
  have hs4 := hslope.comp four_square_to_punctured
  have hs1 := hslope.comp square_to_punctured
  have hlim :
      Tendsto (fun x : ℝ => (4 / 3 : ℝ) * slope h 0 (4 * x ^ 2) -
        (1 / 3 : ℝ) * slope h 0 (x ^ 2)) (punctured 0) (nhds 1) := by
    convert tendsto_const_nhds.mul hs4 |>.sub (tendsto_const_nhds.mul hs1) using 1 <;>
      norm_num
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp only [slope_def_field]
  dsimp [h, firstStage]
  field_simp [hx0]
  ring

private theorem original_limit :
    Tendsto original (punctured 0) (nhds 1) := by
  have hsmall : ∀ᶠ x : ℝ in punctured 0, |x| < (1 / 4 : ℝ) := by
    have hnhds : ∀ᶠ x : ℝ in nhds 0, |x| < (1 / 4 : ℝ) := by
      apply Metric.eventually_nhds_iff.mpr
      refine ⟨1 / 4, by norm_num, ?_⟩
      intro y hy
      simpa [Real.dist_eq] using hy
    exact hnhds.filter_mono inf_le_left
  have hnum :
      ∀ᶠ x : ℝ in punctured 0,
        HasDerivAt (fun y : ℝ => Real.arcsin (2 * y) - 2 * Real.arcsin y)
          (2 / Real.sqrt (1 - 4 * x ^ 2) -
            2 / Real.sqrt (1 - x ^ 2)) x := by
    filter_upwards [hsmall] with x hx
    rw [abs_lt] at hx
    have h2m : 2 * x ≠ -1 := by linarith
    have h2p : 2 * x ≠ 1 := by linarith
    have hxm : x ≠ -1 := by linarith
    have hxp : x ≠ 1 := by linarith
    have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      convert (hasDerivAt_id x).const_mul 2 using 1 <;> ring
    have ha2 := (Real.hasDerivAt_arcsin h2m h2p).comp x hlin
    have ha1 := Real.hasDerivAt_arcsin hxm hxp
    convert ha2.sub (ha1.const_mul 2) using 1 <;> ring
  have hden :
      ∀ᶠ x : ℝ in punctured 0,
        HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    filter_upwards with x
    simpa [id, mul_comm] using (hasDerivAt_id x).pow 3
  have hden_ne : ∀ᶠ x : ℝ in punctured 0, 3 * x ^ 2 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hx0)
  have hzero_num :
      Tendsto (fun y : ℝ => Real.arcsin (2 * y) - 2 * Real.arcsin y)
        (punctured 0) (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => (2 : ℝ)) (nhds 0) (nhds 2) :=
      tendsto_const_nhds
    have hlin : Tendsto (fun y : ℝ => 2 * y) (nhds 0) (nhds 0) := by
      convert hconst.mul (tendsto_id : Tendsto (fun y : ℝ => y) (nhds 0) (nhds 0))
        using 1 <;> norm_num
    have harc : Tendsto Real.arcsin (nhds 0) (nhds 0) := by
      simpa using (Real.continuousAt_arcsin (x := (0 : ℝ))).tendsto
    have ha2 : Tendsto (fun y : ℝ => Real.arcsin (2 * y)) (nhds 0) (nhds 0) :=
      harc.comp hlin
    have ha1 : Tendsto (fun y : ℝ => 2 * Real.arcsin y) (nhds 0) (nhds 0) := by
      convert hconst.mul harc using 1 <;> norm_num
    simpa [punctured] using (ha2.sub ha1).mono_left inf_le_left
  have hzero_den : Tendsto (fun y : ℝ => y ^ 3) (punctured 0) (nhds 0) := by
    convert tendsto_id_punctured.pow 3 using 1 <;> norm_num
  apply HasDerivAt.lhopital_zero_nhdsNE hnum hden hden_ne hzero_num hzero_den
  simpa [firstStage] using firstStage_limit

theorem gap1 : Tendsto original (punctured 0) (nhds 1) := by exact original_limit
theorem gap2 : Tendsto firstStage (punctured 0) (nhds 1) := by exact firstStage_limit
theorem gap3 : Tendsto secondStage (punctured 0) (nhds 1) := by exact secondStage_limit
theorem gap4 : Tendsto finalStage (punctured 0) (nhds 1) := by exact finalStage_limit
theorem gap5 : Tendsto finalStage (punctured 0) (nhds 1) := by exact finalStage_limit
theorem gap6 : Tendsto original (punctured 0) (nhds 1) := by exact original_limit

end
end ProofGap.Exercise1327
