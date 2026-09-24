import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1256

noncomputable section

open Filter

def LittleOAtTop (f : ℝ → ℝ) : Prop :=
  Tendsto (fun x => f x / x) atTop (nhds 0)

theorem gap1 (f : ℝ → ℝ)
    (hlim : Tendsto (deriv f) atTop (nhds 0)) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₁, 0 < X₁ ∧ ∀ x > X₁, |deriv f x| < ε / 2 := by
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨X, hX⟩ := hlim (ε / 2) (by linarith)
  refine ⟨max X 1, by linarith [le_max_right X 1], ?_⟩
  intro x hx
  have h := hX x (le_trans (le_max_left X 1) (le_of_lt hx))
  simpa [Real.dist_eq] using h

theorem gap2 (f : ℝ → ℝ) (x₀ X₁ a x : ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioi x₀))
    (hX₁ : x₀ < X₁) (ha : X₁ < a) (hxa : a < x) :
    ∃ ξ ∈ Set.Ioo a x,
      |f x - f a| = |x - a| * |deriv f ξ| := by
  have hdiffIcc : DifferentiableOn ℝ f (Set.Icc a x) :=
    hf.mono (by
      intro y hy
      exact lt_of_lt_of_le (lt_trans hX₁ ha) hy.1)
  have hcont : ContinuousOn f (Set.Icc a x) := hdiffIcc.continuousOn
  have hdiffIoo : DifferentiableOn ℝ f (Set.Ioo a x) :=
    hf.mono (by
      intro y hy
      exact lt_trans (lt_trans hX₁ ha) hy.1)
  obtain ⟨ξ, hξ, hderiv⟩ :=
    exists_deriv_eq_slope (f := f) hxa hcont hdiffIoo
  refine ⟨ξ, hξ, ?_⟩
  have hne : x - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hxa)
  have hmul : deriv f ξ * (x - a) = f x - f a :=
    (eq_div_iff hne).mp hderiv
  have heq : f x - f a = (x - a) * deriv f ξ := by
    calc
      f x - f a = deriv f ξ * (x - a) := hmul.symm
      _ = (x - a) * deriv f ξ := mul_comm _ _
  rw [heq, abs_mul]

theorem gap3 (f : ℝ → ℝ) (X₁ a x ε : ℝ)
    (hε : 0 < ε) (ha : X₁ < a) (hxa : a < x)
    (hbound : ∀ z > X₁, |deriv f z| < ε / 2)
    (hf : DifferentiableOn ℝ f (Set.Ioi X₁)) :
    |f x - f a| < ε / 2 * |x - a| := by
  let Y := (X₁ + a) / 2
  have hX₁Y : X₁ < Y := by
    dsimp [Y]
    linarith
  have hYa : Y < a := by
    dsimp [Y]
    linarith
  obtain ⟨ξ, hξ, heq⟩ :=
    gap2 f X₁ Y a x hf hX₁Y hYa hxa
  have hξX₁ : X₁ < ξ := lt_trans ha hξ.1
  have hb := hbound ξ hξX₁
  have hpos : 0 < |x - a| := abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hxa))
  calc
    |f x - f a| = |x - a| * |deriv f ξ| := heq
    _ < |x - a| * (ε / 2) := mul_lt_mul_of_pos_left hb hpos
    _ = ε / 2 * |x - a| := mul_comm _ _

theorem gap4 (f : ℝ → ℝ) (X₁ a x ε : ℝ)
    (hε : 0 < ε) (ha : X₁ < a) (hxa : a < x)
    (hbound : ∀ z > X₁, |deriv f z| < ε / 2)
    (hf : DifferentiableOn ℝ f (Set.Ioi X₁)) :
    |f x - f a| < ε / 2 * |x - a| := by
  exact gap3 f X₁ a x ε hε ha hxa hbound hf

theorem gap5 (f : ℝ → ℝ) (a x : ℝ) :
    |f x| - |f a| ≤ |f x - f a| := by
  have h := abs_add_le (f x - f a) (f a)
  rw [sub_add_cancel] at h
  linarith

theorem gap6 (f : ℝ → ℝ) (a x ε : ℝ)
    (hε : 0 < ε) (hxa : a < x)
    (hdiff : |f x - f a| < ε / 2 * |x - a|) :
    |f x| ≤ |f a| + ε / 2 * |x - a| := by
  have htriangle := gap5 f a x
  linarith

theorem gap7 (f : ℝ → ℝ) (a ε : ℝ) (hε : 0 < ε) :
    ∃ X₂ > a, |f a| / X₂ < ε / 2 := by
  let X₂ := max (a + 1) (2 * |f a| / ε + 1)
  refine ⟨X₂, ?_, ?_⟩
  · have hle : a + 1 ≤ X₂ := by
      exact le_max_left _ _
    linarith
  · have hratio_nonneg : 0 ≤ 2 * |f a| / ε :=
      div_nonneg (mul_nonneg (by linarith) (abs_nonneg _)) (le_of_lt hε)
    have hX₂pos : 0 < X₂ := by
      have hle : 2 * |f a| / ε + 1 ≤ X₂ := le_max_right _ _
      linarith
    apply (div_lt_iff₀ hX₂pos).2
    have hle : 2 * |f a| / ε + 1 ≤ X₂ := le_max_right _ _
    have hdiv : 2 * |f a| / ε < X₂ := by linarith
    have hmul : 2 * |f a| < X₂ * ε := (div_lt_iff₀ hε).mp hdiv
    nlinarith

theorem gap8 (f : ℝ → ℝ) (a x ε : ℝ) (hε : 0 < ε)
    (hx : 0 < x)
    (hbound : |f x| ≤ |f a| + ε / 2 * |x - a|) :
    |f x / x| ≤ |f a| / x + ε / 2 * (|x - a| / x) := by
  rw [abs_div, abs_of_pos hx]
  have hdiv := (div_le_div_iff_of_pos_right hx).2 hbound
  calc
    |f x| / x ≤ (|f a| + ε / 2 * |x - a|) / x := hdiv
    _ = |f a| / x + ε / 2 * (|x - a| / x) := by ring

theorem gap9 (f : ℝ → ℝ) (a X₂ x ε : ℝ)
    (hε : 0 < ε) (ha : 0 ≤ a) (hX₂ : a < X₂) (hx : X₂ < x) :
    |f a| / x + ε / 2 * (|x - a| / x) ≤
      |f a| / X₂ + ε / 2 := by
  have hX₂pos : 0 < X₂ := lt_of_le_of_lt ha hX₂
  have hxpos : 0 < x := lt_trans hX₂pos hx
  have hfa : |f a| / x ≤ |f a| / X₂ := by
    apply (div_le_div_iff₀ hxpos hX₂pos).2
    exact mul_le_mul_of_nonneg_left (le_of_lt hx) (abs_nonneg _)
  have hax : a < x := lt_trans hX₂ hx
  have hratio : |x - a| / x ≤ 1 := by
    rw [abs_of_pos (sub_pos.mpr hax)]
    apply (div_le_iff₀ hxpos).2
    nlinarith
  have hscaled : ε / 2 * (|x - a| / x) ≤ ε / 2 := by
    have := mul_le_mul_of_nonneg_left hratio (by linarith : 0 ≤ ε / 2)
    simpa using this
  exact add_le_add hfa hscaled

theorem gap10 (f : ℝ → ℝ) (a X₂ ε : ℝ)
    (hε : 0 < ε) (hsmall : |f a| / X₂ < ε / 2) :
    |f a| / X₂ + ε / 2 < ε / 2 + ε / 2 := by
  linarith

theorem gap11 (ε : ℝ) :
    ε / 2 + ε / 2 = ε := by
  ring

theorem gap12 (f : ℝ → ℝ) (x₀ : ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioi x₀))
    (hlim : Tendsto (deriv f) atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ X, ∀ x > X, |f x / x| < ε := by
  obtain ⟨B, hBpos, hBbound⟩ := gap1 f hlim ε hε
  let X₁ := max B (x₀ + 1)
  have hBX₁ : B ≤ X₁ := le_max_left _ _
  have hX₁pos : 0 < X₁ := lt_of_lt_of_le hBpos hBX₁
  have hx₀X₁ : x₀ < X₁ := by
    have hle : x₀ + 1 ≤ X₁ := le_max_right _ _
    linarith
  have hbound : ∀ z > X₁, |deriv f z| < ε / 2 := by
    intro z hz
    exact hBbound z (lt_of_le_of_lt hBX₁ hz)
  have hf₁ : DifferentiableOn ℝ f (Set.Ioi X₁) :=
    hf.mono (by
      intro z hz
      exact lt_trans hx₀X₁ hz)
  let a := X₁ + 1
  have ha : X₁ < a := by
    dsimp [a]
    linarith
  have ha0 : 0 ≤ a := by
    dsimp [a]
    linarith
  obtain ⟨X₂, hX₂, hsmall⟩ := gap7 f a ε hε
  refine ⟨X₂, ?_⟩
  intro x hx
  have hax : a < x := lt_trans hX₂ hx
  have hxpos : 0 < x := lt_of_le_of_lt ha0 hax
  have hdiff := gap3 f X₁ a x ε hε ha hax hbound hf₁
  have habs := gap6 f a x ε hε hax hdiff
  calc
    |f x / x| ≤ |f a| / x + ε / 2 * (|x - a| / x) :=
      gap8 f a x ε hε hxpos habs
    _ ≤ |f a| / X₂ + ε / 2 := gap9 f a X₂ x ε hε ha0 hX₂ hx
    _ < ε / 2 + ε / 2 := gap10 f a X₂ ε hε hsmall
    _ = ε := gap11 ε

theorem gap13 (f : ℝ → ℝ) (x₀ : ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioi x₀))
    (hlim : Tendsto (deriv f) atTop (nhds 0)) :
    Tendsto (fun x => f x / x) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨X, hX⟩ := gap12 f x₀ hf hlim ε hε
  refine ⟨X + 1, ?_⟩
  intro x hx
  rw [Real.dist_eq, sub_zero]
  exact hX x (by linarith)

theorem gap14 (f : ℝ → ℝ) (x₀ : ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioi x₀))
    (hlim : Tendsto (deriv f) atTop (nhds 0)) :
    LittleOAtTop f := by
  simpa [LittleOAtTop] using gap13 f x₀ hf hlim

theorem gap15 (f : ℝ → ℝ) (x₀ : ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioi x₀))
    (hlim : Tendsto (deriv f) atTop (nhds 0)) :
    Tendsto (fun x => f x / x) atTop (nhds 0) := by
  exact gap13 f x₀ hf hlim

end

end ProofGap.Exercise1256
