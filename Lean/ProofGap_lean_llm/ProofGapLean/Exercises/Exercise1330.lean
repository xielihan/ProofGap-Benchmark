import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace ProofGap.Exercise1330

noncomputable section
open Filter
open scoped Topology

def punctured (x₀ : ℝ) := nhdsWithin x₀ ({x₀} : Set ℝ)ᶜ
def xx (x : ℝ) := Real.rpow x x
def original (x : ℝ) := (xx x - x) / (Real.log x - x + 1)
def firstStage (x : ℝ) :=
  (xx x * (Real.log x + 1) - 1) / (1 / x - 1)
def secondStage (x : ℝ) :=
  (xx x * (Real.log x + 1) ^ 2 + Real.rpow x (x - 1)) /
    (-(1 / x ^ 2))

private theorem tendsto_id_punctured :
    Tendsto (fun x : ℝ => x) (punctured 1) (nhds 1) :=
  tendsto_id.mono_left inf_le_left

private theorem eventually_pos : ∀ᶠ x : ℝ in punctured 1, 0 < x := by
  have h : ∀ᶠ x : ℝ in nhds 1, 0 < x := eventually_gt_nhds (by norm_num)
  exact h.filter_mono inf_le_left

private theorem hasDerivAt_xx {x : ℝ} (hx : 0 < x) :
    HasDerivAt xx (xx x * (Real.log x + 1)) x := by
  have hraw := (hasDerivAt_id x).rpow (hasDerivAt_id x) hx
  convert hraw using 1
  simp only [id_eq]
  rw [Real.rpow_sub_one hx.ne' x]
  dsimp [xx]
  field_simp [hx.ne']
  ring

private theorem secondStage_limit :
    Tendsto secondStage (punctured 1) (nhds (-2)) := by
  have hxx : Tendsto xx (punctured 1) (nhds 1) := by
    simpa [xx] using (hasDerivAt_xx (x := 1) (by norm_num)).continuousAt.tendsto.mono_left
      inf_le_left
  have hlog : Tendsto Real.log (punctured 1) (nhds 0) := by
    simpa using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.mono_left
      inf_le_left
  have hsub : Tendsto (fun x : ℝ => x - 1) (punctured 1) (nhds 0) := by
    convert tendsto_id_punctured.sub tendsto_const_nhds using 1 <;> norm_num
  have hrpow : Tendsto (fun x : ℝ => Real.rpow x (x - 1))
      (punctured 1) (nhds 1) := by
    have hd := (hasDerivAt_id (1 : ℝ)).rpow
      ((hasDerivAt_id (1 : ℝ)).sub_const 1) (by norm_num)
    simpa using hd.continuousAt.tendsto.mono_left inf_le_left
  have hden : Tendsto (fun x : ℝ => -(1 / x ^ 2)) (punctured 1) (nhds (-1)) := by
    have hp := tendsto_id_punctured.pow 2
    have hone :
        Tendsto (fun _ : ℝ => (1 : ℝ)) (punctured 1) (nhds 1) :=
      tendsto_const_nhds
    have hi := hone.div hp (by norm_num)
    simpa using hi.neg
  have hone :
      Tendsto (fun _ : ℝ => (1 : ℝ)) (punctured 1) (nhds 1) :=
    tendsto_const_nhds
  have hnum := (hxx.mul ((hlog.add hone).pow 2)).add hrpow
  convert hnum.div hden (by norm_num) using 1 <;>
    norm_num [secondStage]

private theorem firstStage_limit :
    Tendsto firstStage (punctured 1) (nhds (-2)) := by
  let M : ℝ → ℝ := fun x => xx x * (Real.log x + 1) - 1
  have hM :
      ∀ᶠ x : ℝ in punctured 1,
        HasDerivAt M
          (xx x * (Real.log x + 1) ^ 2 + Real.rpow x (x - 1)) x := by
    filter_upwards [eventually_pos] with x hx
    have hxx := hasDerivAt_xx hx
    have hlog := (Real.hasDerivAt_log hx.ne').const_add 1
    have hraw := (hxx.mul hlog).sub_const 1
    convert hraw using 1
    · funext y
      dsimp [M]
      ring
    · have hr : Real.rpow x (x - 1) = Real.rpow x x / x :=
        Real.rpow_sub_one hx.ne' x
      rw [hr]
      dsimp [xx]
      simp only [div_eq_mul_inv]
      ring
  have hden :
      ∀ᶠ x : ℝ in punctured 1,
        HasDerivAt (fun y : ℝ => 1 / y - 1) (-(1 / x ^ 2)) x := by
    filter_upwards [eventually_pos] with x hx
    have hi := (hasDerivAt_const (x := x) (c := (1 : ℝ))).div (hasDerivAt_id x) hx.ne'
    convert hi.sub_const 1 using 1 <;> simp [id] <;> field_simp [hx.ne'] <;> ring
  have hden_ne : ∀ᶠ x : ℝ in punctured 1, -(1 / x ^ 2) ≠ 0 := by
    filter_upwards [eventually_pos] with x hx
    exact neg_ne_zero.mpr (div_ne_zero one_ne_zero (pow_ne_zero 2 hx.ne'))
  have hzeroM : Tendsto M (punctured 1) (nhds 0) := by
    have hxx : Tendsto xx (punctured 1) (nhds 1) := by
      simpa [xx] using
        (hasDerivAt_xx (x := 1) (by norm_num)).continuousAt.tendsto.mono_left inf_le_left
    have hlog : Tendsto Real.log (punctured 1) (nhds 0) := by
      simpa using
        (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.mono_left inf_le_left
    convert (hxx.mul (hlog.add tendsto_const_nhds)).sub tendsto_const_nhds using 1 <;>
      norm_num [M]
  have hzeroDen : Tendsto (fun y : ℝ => 1 / y - 1) (punctured 1) (nhds 0) := by
    have hone :
        Tendsto (fun _ : ℝ => (1 : ℝ)) (punctured 1) (nhds 1) :=
      tendsto_const_nhds
    have hi := hone.div tendsto_id_punctured (by norm_num)
    convert hi.sub hone using 1 <;> norm_num
  apply HasDerivAt.lhopital_zero_nhdsNE hM hden hden_ne hzeroM hzeroDen
  change Tendsto secondStage (punctured 1) (nhds (-2))
  exact secondStage_limit

private theorem original_limit :
    Tendsto original (punctured 1) (nhds (-2)) := by
  let F : ℝ → ℝ := fun x => xx x - x
  let M : ℝ → ℝ := fun x => Real.log x - x + 1
  have hF :
      ∀ᶠ x : ℝ in punctured 1,
        HasDerivAt F (xx x * (Real.log x + 1) - 1) x := by
    filter_upwards [eventually_pos] with x hx
    dsimp [F]
    convert (hasDerivAt_xx hx).sub (hasDerivAt_id x) using 1 <;> ring
  have hM :
      ∀ᶠ x : ℝ in punctured 1,
        HasDerivAt M (1 / x - 1) x := by
    filter_upwards [eventually_pos] with x hx
    have hraw := (Real.hasDerivAt_log hx.ne').sub (hasDerivAt_id x) |>.const_add 1
    convert hraw using 1
    · funext y
      dsimp [M]
      ring
    · simp only [one_div]
  have hM_ne : ∀ᶠ x : ℝ in punctured 1, 1 / x - 1 ≠ 0 := by
    filter_upwards [eventually_pos, self_mem_nhdsWithin] with x hx hne
    have hx1 : x ≠ 1 := by simpa using hne
    intro h
    have : x = 1 := by
      field_simp [hx.ne'] at h
      linarith
    exact hx1 this
  have hzeroF : Tendsto F (punctured 1) (nhds 0) := by
    have hxx : Tendsto xx (punctured 1) (nhds 1) := by
      simpa [xx] using
        (hasDerivAt_xx (x := 1) (by norm_num)).continuousAt.tendsto.mono_left inf_le_left
    simpa [F] using hxx.sub tendsto_id_punctured
  have hzeroM : Tendsto M (punctured 1) (nhds 0) := by
    have hlog : Tendsto Real.log (punctured 1) (nhds 0) := by
      simpa using
        (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.mono_left inf_le_left
    convert (hlog.sub tendsto_id_punctured).add tendsto_const_nhds using 1 <;>
      norm_num [M]
  apply HasDerivAt.lhopital_zero_nhdsNE hF hM hM_ne hzeroF hzeroM
  change Tendsto firstStage (punctured 1) (nhds (-2))
  exact firstStage_limit

theorem gap1 : Tendsto original (punctured 1) (nhds (-2)) := by exact original_limit
theorem gap2 : Tendsto firstStage (punctured 1) (nhds (-2)) := by exact firstStage_limit
theorem gap3 : Tendsto secondStage (punctured 1) (nhds (-2)) := by exact secondStage_limit
theorem gap4 : Tendsto original (punctured 1) (nhds (-2)) := by exact original_limit

end
end ProofGap.Exercise1330
