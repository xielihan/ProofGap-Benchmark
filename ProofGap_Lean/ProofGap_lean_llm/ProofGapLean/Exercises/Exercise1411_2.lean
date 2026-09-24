import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1411_2

noncomputable section
open Filter
open scoped Topology

def punctured := nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ
def cubeRoot (x : ℝ) := Real.rpow x (1 / 3 : ℝ)
def target (x : ℝ) :=
  cubeRoot ((1 + x) / (1 - x)) -
    cubeRoot ((1 - x) / (1 + x))
def rationalModel (x : ℝ) := 4 * x / (3 * (1 - x ^ 2))
def linearModel (x : ℝ) := (4 / 3 : ℝ) * x

private theorem hasDerivAt_cubeRoot_one :
    HasDerivAt cubeRoot (1 / 3 : ℝ) 1 := by
  unfold cubeRoot
  convert
    (Real.hasDerivAt_rpow_const (p := (1 / 3 : ℝ))
      (show (1 : ℝ) ≠ 0 ∨ 1 ≤ (1 / 3 : ℝ) by
        left
        norm_num)) using 1 <;> norm_num

private theorem hasDerivAt_target_zero :
    HasDerivAt target (4 / 3 : ℝ) 0 := by
  have hc : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 :=
    hasDerivAt_const 0 1
  have hi : HasDerivAt (fun x : ℝ => x) 1 0 := hasDerivAt_id 0
  have hu :
      HasDerivAt (fun x : ℝ => (1 + x) / (1 - x)) 2 0 := by
    convert (hc.add hi).div (hc.sub hi) (by norm_num) using 1 <;> norm_num
  have hv :
      HasDerivAt (fun x : ℝ => (1 - x) / (1 + x)) (-2) 0 := by
    convert (hc.sub hi).div (hc.add hi) (by norm_num) using 1 <;> norm_num
  have houteru :
      HasDerivAt cubeRoot (1 / 3 : ℝ)
        ((1 + (0 : ℝ)) / (1 - (0 : ℝ))) := by
    convert hasDerivAt_cubeRoot_one using 1 <;> norm_num
  have houterv :
      HasDerivAt cubeRoot (1 / 3 : ℝ)
        ((1 - (0 : ℝ)) / (1 + (0 : ℝ))) := by
    convert hasDerivAt_cubeRoot_one using 1 <;> norm_num
  have hcu :
      HasDerivAt (fun x : ℝ => cubeRoot ((1 + x) / (1 - x)))
        (2 / 3 : ℝ) 0 := by
    convert houteru.comp 0 hu using 1 <;> norm_num
  have hcv :
      HasDerivAt (fun x : ℝ => cubeRoot ((1 - x) / (1 + x)))
        (-2 / 3 : ℝ) 0 := by
    convert houterv.comp 0 hv using 1 <;> norm_num
  unfold target
  convert hcu.sub hcv using 1 <;> norm_num

private theorem hasDerivAt_rational_zero :
    HasDerivAt rationalModel (4 / 3 : ℝ) 0 := by
  have hi : HasDerivAt (fun x : ℝ => x) 1 0 := hasDerivAt_id 0
  have hfour : HasDerivAt (fun _ : ℝ => (4 : ℝ)) 0 0 :=
    hasDerivAt_const 0 4
  have hthree : HasDerivAt (fun _ : ℝ => (3 : ℝ)) 0 0 :=
    hasDerivAt_const 0 3
  have hone : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 :=
    hasDerivAt_const 0 1
  have hnum : HasDerivAt (fun x : ℝ => 4 * x) 4 0 := by
    convert hfour.mul hi using 1 <;> norm_num
  have hden :
      HasDerivAt (fun x : ℝ => 3 * (1 - x ^ 2)) 0 0 := by
    convert hthree.mul (hone.sub (hi.pow 2)) using 1 <;> norm_num
  unfold rationalModel
  convert hnum.div hden (by norm_num) using 1 <;> norm_num

private theorem hasDerivAt_linear_zero :
    HasDerivAt linearModel (4 / 3 : ℝ) 0 := by
  have hc :
      HasDerivAt (fun _ : ℝ => (4 / 3 : ℝ)) 0 0 :=
    hasDerivAt_const 0 (4 / 3 : ℝ)
  have hi : HasDerivAt (fun x : ℝ => x) 1 0 := hasDerivAt_id 0
  unfold linearModel
  convert hc.mul hi using 1 <;> norm_num

private theorem equivalent_of_common_nonzero_derivative
    (f g : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hf : HasDerivAt f c 0) (hf0 : f 0 = 0)
    (hg : HasDerivAt g c 0) (hg0 : g 0 = 0) :
    Asymptotics.IsEquivalent punctured f g := by
  have hne : ∀ᶠ x in punctured, x ≠ 0 := by
    unfold punctured
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  have hfs :
      Tendsto (slope f 0) punctured (𝓝 c) := by
    simpa [punctured] using
      (hasDerivAt_iff_tendsto_slope.mp hf)
  have hgs :
      Tendsto (slope g 0) punctured (𝓝 c) := by
    simpa [punctured] using
      (hasDerivAt_iff_tendsto_slope.mp hg)
  have hslope_ne : ∀ᶠ x in punctured, slope g 0 x ≠ 0 := by
    exact hgs.eventually (eventually_ne_nhds hc)
  have hgne : ∀ᶠ x in punctured, g x ≠ 0 := by
    filter_upwards [hslope_ne] with x hx
    intro hgx
    apply hx
    rw [show slope g 0 x = x⁻¹ * g x by simp [slope, hg0]]
    simp [hgx]
  rw [Asymptotics.isEquivalent_iff_tendsto_one hgne]
  have hquot :
      Tendsto
        (fun x : ℝ => slope f 0 x / slope g 0 x)
        punctured (𝓝 (c / c)) :=
    hfs.div hgs hc
  have heq :
      (fun x : ℝ => slope f 0 x / slope g 0 x) =ᶠ[punctured]
        (fun x : ℝ => f x / g x) := by
    filter_upwards [hne] with x hx
    rw [show slope f 0 x = x⁻¹ * f x by simp [slope, hf0]]
    rw [show slope g 0 x = x⁻¹ * g x by simp [slope, hg0]]
    calc
      (x⁻¹ * f x) / (x⁻¹ * g x)
          = x⁻¹ * x * (f x / g x) := by
              simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
              ring
      _ = f x / g x := by simp [hx]
  have ht := hquot.congr' heq
  simpa [div_self hc] using ht

theorem gap1 (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    target x =
      Real.rpow (1 + 2 * x / (1 - x)) (1 / 3 : ℝ) -
      Real.rpow (1 - 2 * x / (1 + x)) (1 / 3 : ℝ) := by
  have hminus : 1 - x ≠ 0 := by
    intro h
    linarith [hx.2]
  have hplus : 1 + x ≠ 0 := by
    intro h
    linarith [hx.1]
  have ha : (1 + x) / (1 - x) = 1 + 2 * x / (1 - x) := by
    field_simp [hminus]
    <;> ring
  have hb : (1 - x) / (1 + x) = 1 - 2 * x / (1 + x) := by
    field_simp [hplus]
    <;> ring
  unfold target cubeRoot
  rw [ha, hb]
theorem gap2 :
    Asymptotics.IsEquivalent punctured target rationalModel := by
  refine equivalent_of_common_nonzero_derivative target rationalModel (4 / 3 : ℝ)
    (by norm_num) hasDerivAt_target_zero ?_ hasDerivAt_rational_zero ?_
  · simp [target]
  · simp [rationalModel]
theorem gap3 (x : ℝ) (hx : x ≠ 1) (hxn : x ≠ -1) :
    1 + 2 * x / (3 * (1 - x)) -
        (1 - 2 * x / (3 * (1 + x))) =
      rationalModel x := by
  have hminus : 1 - x ≠ 0 := by
    intro h
    apply hx
    linarith
  have hplus : 1 + x ≠ 0 := by
    intro h
    apply hxn
    linarith
  have hsquare : 1 - x ^ 2 ≠ 0 := by
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]
    exact mul_ne_zero hminus hplus
  unfold rationalModel
  field_simp [hminus, hplus, hsquare]
  <;> ring
theorem gap4 :
    Asymptotics.IsEquivalent punctured rationalModel linearModel := by
  refine equivalent_of_common_nonzero_derivative rationalModel linearModel
    (4 / 3 : ℝ) (by norm_num) hasDerivAt_rational_zero ?_
    hasDerivAt_linear_zero ?_
  · simp [rationalModel]
  · simp [linearModel]
theorem gap5 :
    Asymptotics.IsEquivalent punctured target linearModel := by
  exact gap2.trans gap4

end
end ProofGap.Exercise1411_2
