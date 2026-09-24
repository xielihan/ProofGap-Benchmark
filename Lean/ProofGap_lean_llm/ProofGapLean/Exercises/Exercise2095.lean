import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.IntermediateValue

namespace ProofGap.Exercise2095
noncomputable section

def f (x : ℝ) := Real.exp (2 * x) / (x ^ 2 - 3 * x + 2)
def mode (c x : ℝ) := Real.exp (2 * x) / (x - c)
def shiftedMode (c x : ℝ) := Real.exp (2 * (x - c)) / (x - c)
def Family (U : Set ℝ) (g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (g x) x}
def Split (U : Set ℝ) := {F : ℝ → ℝ |
  ∃ A ∈ Family U (mode 2), ∃ B ∈ Family U (mode 1),
  ∃ C, ∀ x ∈ U, F x = A x - B x + C}
def Shifted (U : Set ℝ) := {F : ℝ → ℝ |
  ∃ A ∈ Family U (shiftedMode 2), ∃ B ∈ Family U (shiftedMode 1),
  ∃ C, ∀ x ∈ U,
    F x = Real.exp 4 * A x - Real.exp 2 * B x + C}
def LiForm (U : Set ℝ) := {F : ℝ → ℝ |
  ∃ L₂ ∈ Family U (shiftedMode 2), ∃ L₁ ∈ Family U (shiftedMode 1),
  ∃ C, ∀ x ∈ U,
    F x = Real.exp 4 * L₂ x - Real.exp 2 * L₁ x + C}
def Regular (U : Set ℝ) :=
  IsOpen U ∧ IsPreconnected U ∧ ∀ x ∈ U, x ≠ 1 ∧ x ≠ 2

private theorem partial_fraction (x : ℝ) (h1 : x ≠ 1) (h2 : x ≠ 2) :
    Real.exp (2 * x) / ((x - 2) * (x - 1)) = mode 2 x - mode 1 x := by
  unfold mode
  field_simp [sub_ne_zero.mpr h1, sub_ne_zero.mpr h2]
  <;> ring

private theorem mode_eq_scaled_shifted (c x : ℝ) :
    mode c x = Real.exp (2 * c) * shiftedMode c x := by
  unfold mode shiftedMode
  rw [← mul_div_assoc, ← Real.exp_add]
  congr 1
  ring

private theorem exists_mode_primitive
    (U : Set ℝ) (hU : Regular U) (c : ℝ)
    (hc : ∀ x ∈ U, x ≠ c) :
    ∃ A, A ∈ Family U (mode c) := by
  classical
  by_cases hne : U.Nonempty
  · rcases hne with ⟨a, ha⟩
    let A : ℝ → ℝ := fun x => ∫ t in a..x, mode c t
    have hnum : Continuous (fun y : ℝ => Real.exp (2 * y)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hden : Continuous (fun y : ℝ => y - c) :=
      continuous_id.sub continuous_const
    have hcont : ContinuousOn (mode c) U := by
      intro x hx
      apply ContinuousAt.continuousWithinAt
      simpa only [mode] using
        hnum.continuousAt.div hden.continuousAt
          (sub_ne_zero.mpr (hc x hx))
    refine ⟨A, ?_⟩
    change ∀ x ∈ U, HasDerivAt A (mode c x) x
    intro x hx
    have hca : ContinuousAt (mode c) x :=
      hcont.continuousAt (hU.1.mem_nhds hx)
    have hseg : Set.uIcc a x ⊆ U :=
      hU.2.1.ordConnected.uIcc_subset ha hx
    have hint : IntervalIntegrable (mode c) MeasureTheory.volume a x :=
      (hcont.mono hseg).intervalIntegrable
    have hopen : IsOpen U := hU.1
    have hcaU : ∀ y ∈ U, ContinuousAt (mode c) y := by
      intro y hy
      exact hcont.continuousAt (hopen.mem_nhds hy)
    have hsm : StronglyMeasurableAtFilter (mode c) (nhds x)
        MeasureTheory.volume := by
      apply ContinuousAt.stronglyMeasurableAtFilter (s := U) <;> assumption
    simpa [A] using
      (intervalIntegral.integral_hasDerivAt_right hint hsm hca)
  · refine ⟨fun _ => 0, ?_⟩
    change ∀ x ∈ U, HasDerivAt (fun _ : ℝ => 0) (mode c x) x
    intro x hx
    exact (hne ⟨x, hx⟩).elim

private theorem split_eq_shifted (U : Set ℝ) : Split U = Shifted U := by
  ext F
  constructor
  · rintro ⟨A, hA, B, hB, C, hF⟩
    change ∀ x ∈ U, HasDerivAt A (mode 2 x) x at hA
    change ∀ x ∈ U, HasDerivAt B (mode 1 x) x at hB
    let L₂ : ℝ → ℝ := fun x => A x / Real.exp 4
    let L₁ : ℝ → ℝ := fun x => B x / Real.exp 2
    change ∃ L₂ ∈ Family U (shiftedMode 2),
      ∃ L₁ ∈ Family U (shiftedMode 1), ∃ C, ∀ x ∈ U,
        F x = Real.exp 4 * L₂ x - Real.exp 2 * L₁ x + C
    refine ⟨L₂, ?_, L₁, ?_, C, ?_⟩
    · change ∀ x ∈ U, HasDerivAt L₂ (shiftedMode 2 x) x
      intro x hx
      have hs : mode 2 x = Real.exp 4 * shiftedMode 2 x := by
        convert mode_eq_scaled_shifted 2 x using 1 <;> norm_num
      have hc : mode 2 x / Real.exp 4 = shiftedMode 2 x := by
        rw [hs]
        field_simp [Real.exp_ne_zero]
      simpa [L₂, hc] using (hA x hx).div_const (Real.exp 4)
    · change ∀ x ∈ U, HasDerivAt L₁ (shiftedMode 1 x) x
      intro x hx
      have hs : mode 1 x = Real.exp 2 * shiftedMode 1 x := by
        convert mode_eq_scaled_shifted 1 x using 1 <;> norm_num
      have hc : mode 1 x / Real.exp 2 = shiftedMode 1 x := by
        rw [hs]
        field_simp [Real.exp_ne_zero]
      simpa [L₁, hc] using (hB x hx).div_const (Real.exp 2)
    · intro x hx
      dsimp [L₂, L₁]
      rw [hF x hx]
      field_simp [Real.exp_ne_zero]
      <;> ring
  · rintro ⟨L₂, hL₂, L₁, hL₁, C, hF⟩
    change ∀ x ∈ U, HasDerivAt L₂ (shiftedMode 2 x) x at hL₂
    change ∀ x ∈ U, HasDerivAt L₁ (shiftedMode 1 x) x at hL₁
    let A : ℝ → ℝ := fun x => Real.exp 4 * L₂ x
    let B : ℝ → ℝ := fun x => Real.exp 2 * L₁ x
    change ∃ A ∈ Family U (mode 2), ∃ B ∈ Family U (mode 1),
      ∃ C, ∀ x ∈ U, F x = A x - B x + C
    refine ⟨A, ?_, B, ?_, C, ?_⟩
    · change ∀ x ∈ U, HasDerivAt A (mode 2 x) x
      intro x hx
      have hs : Real.exp 4 * shiftedMode 2 x = mode 2 x := by
        symm
        convert mode_eq_scaled_shifted 2 x using 1 <;> norm_num
      simpa [A, hs] using (hL₂ x hx).const_mul (Real.exp 4)
    · change ∀ x ∈ U, HasDerivAt B (mode 1 x) x
      intro x hx
      have hs : Real.exp 2 * shiftedMode 1 x = mode 1 x := by
        symm
        convert mode_eq_scaled_shifted 1 x using 1 <;> norm_num
      simpa [B, hs] using (hL₁ x hx).const_mul (Real.exp 2)
    · intro x hx
      simpa [A, B] using hF x hx

theorem gap1 (U : Set ℝ) (hU : Regular U) :
    Family U f =
      Family U (fun x => Real.exp (2 * x) / ((x - 2) * (x - 1))) := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ U, HasDerivAt F (f x) x at hF
    change ∀ x ∈ U,
      HasDerivAt F (Real.exp (2 * x) / ((x - 2) * (x - 1))) x
    intro x hx
    have hden : x ^ 2 - 3 * x + 2 = (x - 2) * (x - 1) := by ring
    simpa [f, hden] using hF x hx
  · intro hF
    change ∀ x ∈ U,
      HasDerivAt F (Real.exp (2 * x) / ((x - 2) * (x - 1))) x at hF
    change ∀ x ∈ U, HasDerivAt F (f x) x
    intro x hx
    have hden : x ^ 2 - 3 * x + 2 = (x - 2) * (x - 1) := by ring
    simpa [f, hden] using hF x hx
theorem gap2 (U : Set ℝ) (hU : Regular U) :
    Family U (fun x => Real.exp (2 * x) / ((x - 2) * (x - 1))) =
      Split U := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ U,
      HasDerivAt F (Real.exp (2 * x) / ((x - 2) * (x - 1))) x at hF
    rcases exists_mode_primitive U hU 1 (fun x hx => (hU.2.2 x hx).1) with
      ⟨B, hB⟩
    change ∀ x ∈ U, HasDerivAt B (mode 1 x) x at hB
    let A : ℝ → ℝ := fun x => F x + B x
    change ∃ A ∈ Family U (mode 2), ∃ B ∈ Family U (mode 1),
      ∃ C, ∀ x ∈ U, F x = A x - B x + C
    refine ⟨A, ?_, B, ?_, 0, ?_⟩
    · change ∀ x ∈ U, HasDerivAt A (mode 2 x) x
      intro x hx
      have hp := partial_fraction x (hU.2.2 x hx).1 (hU.2.2 x hx).2
      have hc :
          Real.exp (2 * x) / ((x - 2) * (x - 1)) + mode 1 x =
            mode 2 x := by
        rw [hp]
        ring
      simpa [A, hc] using (hF x hx).add (hB x hx)
    · exact hB
    · intro x hx
      dsimp [A]
      ring
  · rintro ⟨A, hA, B, hB, C, hEq⟩
    change ∀ x ∈ U, HasDerivAt A (mode 2 x) x at hA
    change ∀ x ∈ U, HasDerivAt B (mode 1 x) x at hB
    change ∀ x ∈ U,
      HasDerivAt F (Real.exp (2 * x) / ((x - 2) * (x - 1))) x
    intro x hx
    have hd := ((hA x hx).sub (hB x hx)).add_const C
    have hmem : ∀ᶠ y in nhds x, y ∈ U := hU.1.mem_nhds hx
    have heq : F =ᶠ[nhds x] (fun y => (A - B) y + C) := by
      filter_upwards [hmem] with y hy
      change F y = A y - B y + C
      exact hEq y hy
    have hdF := hd.congr_of_eventuallyEq heq
    have hp := partial_fraction x (hU.2.2 x hx).1 (hU.2.2 x hx).2
    simpa only [hp] using hdF
theorem gap3 (U : Set ℝ) (hU : Regular U) :
    Family U f = Split U := by
  calc
    Family U f =
        Family U (fun x => Real.exp (2 * x) / ((x - 2) * (x - 1))) :=
      gap1 U hU
    _ = Split U := gap2 U hU
theorem gap4 (U : Set ℝ) (hU : Regular U) :
    Family U f = Shifted U := by
  calc
    Family U f = Split U := gap3 U hU
    _ = Shifted U := split_eq_shifted U
theorem gap5 (U : Set ℝ) (hU : Regular U) :
    Shifted U = LiForm U := by
  rfl
theorem gap6 (U : Set ℝ) (hU : Regular U) :
    Family U f = LiForm U := by
  calc
    Family U f = Shifted U := gap4 U hU
    _ = LiForm U := gap5 U hU

end
end ProofGap.Exercise2095
