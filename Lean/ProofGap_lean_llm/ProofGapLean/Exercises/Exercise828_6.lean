import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise828_6

noncomputable section

def y (x : ℝ) : ℝ := Real.tan x
def sec (x : ℝ) : ℝ := 1 / Real.cos x
def quotient (x h : ℝ) : ℝ := (Real.tan (x + h) - Real.tan x) / h
def transformed (x h : ℝ) : ℝ :=
  Real.tan h * sec x ^ 2 / (h * (1 - Real.tan x * Real.tan h))

private theorem eventually_ne_zero_of_tendsto_one (f : ℝ → ℝ)
    (hf : Filter.Tendsto f (nhds 0) (nhds 1)) :
    ∀ᶠ h in nhdsWithin 0 ({0}ᶜ : Set ℝ), f h ≠ 0 := by
  have hmem : ({0}ᶜ : Set ℝ) ∈ nhds (1 : ℝ) := by
    exact isClosed_singleton.isOpen_compl.mem_nhds (by simp)
  have hev : ∀ᶠ h in nhds 0, f h ∈ ({0}ᶜ : Set ℝ) :=
    hf.eventually hmem
  have hev' : ∀ᶠ h in nhdsWithin 0 ({0}ᶜ : Set ℝ),
      f h ∈ ({0}ᶜ : Set ℝ) :=
    hev.filter_mono inf_le_left
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hev'

theorem gap1 (x h Δy : ℝ) (hΔy : Δy = y (x + h) - y x) :
    Δy / h = quotient x h := by
  rw [hΔy]
  rfl
theorem gap2 (x h : ℝ) (hcos : Real.cos x ≠ 0) (hcos' : Real.cos h ≠ 0)
    (hden : 1 - Real.tan x * Real.tan h ≠ 0) :
    quotient x h =
      ((Real.tan x + Real.tan h) / (1 - Real.tan x * Real.tan h) -
        Real.tan x) / h := by
  have hden' :
      1 - (Real.sin x / Real.cos x) * (Real.sin h / Real.cos h) ≠ 0 := by
    simpa only [Real.tan_eq_sin_div_cos] using hden
  have hsum :
      Real.cos x * Real.cos h - Real.sin x * Real.sin h ≠ 0 := by
    intro hz
    apply hden'
    field_simp [hcos, hcos']
    nlinarith [hz]
  have htadd :
      Real.tan (x + h) =
        (Real.tan x + Real.tan h) /
          (1 - Real.tan x * Real.tan h) := by
    simp only [Real.tan_eq_sin_div_cos, Real.sin_add, Real.cos_add]
    field_simp [hcos, hcos', hden', hsum]
  unfold quotient
  rw [htadd]
theorem gap3 (x h : ℝ) (hden : 1 - Real.tan x * Real.tan h ≠ 0) :
    ((Real.tan x + Real.tan h) / (1 - Real.tan x * Real.tan h) -
      Real.tan x) / h =
      Real.tan h * (1 + Real.tan x ^ 2) /
        (h * (1 - Real.tan x * Real.tan h)) := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  · field_simp [hh, hden] <;> ring
theorem gap4 (x h : ℝ) (hcos : Real.cos x ≠ 0) :
    Real.tan h * (1 + Real.tan x ^ 2) /
      (h * (1 - Real.tan x * Real.tan h)) = transformed x h := by
  have hident : 1 + Real.tan x ^ 2 = (1 / Real.cos x) ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos]
    nlinarith [Real.sin_sq_add_cos_sq x]
  unfold transformed sec
  rw [hident]
theorem gap5 (x h Δy : ℝ) (hΔy : Δy = y (x + h) - y x)
    (hcos : Real.cos x ≠ 0) (hcos' : Real.cos h ≠ 0)
    (hden : 1 - Real.tan x * Real.tan h ≠ 0) :
    Δy / h = transformed x h := by
  calc
    Δy / h = quotient x h := gap1 x h Δy hΔy
    _ = ((Real.tan x + Real.tan h) /
          (1 - Real.tan x * Real.tan h) - Real.tan x) / h :=
      gap2 x h hcos hcos' hden
    _ = Real.tan h * (1 + Real.tan x ^ 2) /
          (h * (1 - Real.tan x * Real.tan h)) := gap3 x h hden
    _ = transformed x h := gap4 x h hcos
theorem gap6 (x : ℝ) (hx : Real.cos x ≠ 0) :
    HasDerivAt y (sec x ^ 2) x := by
  unfold y sec
  have hval :
      (Real.cos x * Real.cos x - Real.sin x * -Real.sin x) /
          Real.cos x ^ 2 =
        (1 / Real.cos x) ^ 2 := by
    field_simp [hx]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hderiv :=
    (Real.hasDerivAt_sin x).div (Real.hasDerivAt_cos x) hx
  simpa only [Real.tan_eq_sin_div_cos, hval] using hderiv
theorem gap7 (x : ℝ) (hx : Real.cos x ≠ 0) :
    Filter.Tendsto (quotient x) (nhdsWithin 0 {0}ᶜ) (nhds (sec x ^ 2)) := by
  have hslope := (gap6 x hx).tendsto_slope_zero
  apply hslope.congr'
  filter_upwards [] with h
  change h⁻¹ * (Real.tan (x + h) - Real.tan x) =
    (Real.tan (x + h) - Real.tan x) / h
  rw [div_eq_inv_mul]
theorem gap8 (x : ℝ) (hx : Real.cos x ≠ 0) :
    Filter.Tendsto (transformed x) (nhdsWithin 0 {0}ᶜ) (nhds (sec x ^ 2)) := by
  have hcos_tend :
      Filter.Tendsto Real.cos (nhds 0) (nhds 1) := by
    have hc :
        Filter.Tendsto Real.cos (nhds 0) (nhds (Real.cos 0)) :=
      Real.continuous_cos.continuousAt
    rw [Real.cos_zero] at hc
    exact hc
  have htan : ContinuousAt Real.tan 0 := by
    simpa only [y] using (gap6 0 (by simp)).continuousAt
  have hden_tend :
      Filter.Tendsto (fun h => 1 - Real.tan x * Real.tan h)
        (nhds 0) (nhds 1) := by
    have hc : ContinuousAt
        (fun h => 1 - Real.tan x * Real.tan h) 0 :=
      continuousAt_const.sub (continuousAt_const.mul htan)
    have ht :
        Filter.Tendsto (fun h => 1 - Real.tan x * Real.tan h)
          (nhds 0)
          (nhds ((fun h => 1 - Real.tan x * Real.tan h) 0)) := hc
    change Filter.Tendsto (fun h => 1 - Real.tan x * Real.tan h)
      (nhds 0) (nhds (1 - Real.tan x * Real.tan 0)) at ht
    simpa only [Real.tan_zero, mul_zero, sub_zero] using ht
  have hcos_ev := eventually_ne_zero_of_tendsto_one Real.cos hcos_tend
  have hden_ev := eventually_ne_zero_of_tendsto_one
    (fun h => 1 - Real.tan x * Real.tan h) hden_tend
  apply (gap7 x hx).congr'
  filter_upwards [hcos_ev, hden_ev] with h hhcos hhden
  exact (gap2 x h hx hhcos hhden).trans
    ((gap3 x h hhden).trans (gap4 x h hx))
theorem gap9 (x : ℝ) : sec x ^ 2 = 1 / Real.cos x ^ 2 := by
  simp [sec]
theorem gap10 (x : ℝ) (hx : Real.cos x ≠ 0) :
    HasDerivAt y (1 / Real.cos x ^ 2) x := by
  rw [← gap9 x]
  exact gap6 x hx

end
end ProofGap.Exercise828_6
