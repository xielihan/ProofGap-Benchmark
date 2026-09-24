import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1009

open Filter

noncomputable section

def f (x : ℝ) : ℝ :=
  if x = 0 then 0 else x * Real.sin (1 / x)

def model (x : ℝ) : ℝ := x * Real.sin (1 / x)
def dq (g : ℝ → ℝ) (a h : ℝ) : ℝ := (g (a + h) - g a) / h
def HasLeftDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Iio 0)) (nhds g')
def HasRightDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Ioi 0)) (nhds g')
def LeftDifferentiableAt (g : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ g', HasLeftDerivAt g g' a
def RightDifferentiableAt (g : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ g', HasRightDerivAt g g' a

private theorem no_sin_tendsto_atTop (L : ℝ) :
    ¬ Tendsto Real.sin atTop (nhds L) := by
  intro h
  have he : ∀ᶠ x : ℝ in atTop,
      dist (Real.sin x) L < (1 / 4 : ℝ) :=
    (Metric.tendsto_nhds.mp h) (1 / 4) (by norm_num)
  rw [eventually_atTop] at he
  rcases he with ⟨a, ha⟩
  have hpi : 0 < Real.pi := Real.pi_pos
  have h0 : |Real.sin a - L| < (1 / 4 : ℝ) := by
    simpa [Real.dist_eq] using ha a le_rfl
  have h1 : |-Real.sin a - L| < (1 / 4 : ℝ) := by
    have hle : a ≤ a + Real.pi := by linarith
    simpa [Real.dist_eq, Real.sin_add] using ha (a + Real.pi) hle
  have h2 : |Real.cos a - L| < (1 / 4 : ℝ) := by
    have hle : a ≤ a + Real.pi / 2 := by linarith
    simpa [Real.dist_eq, Real.sin_add] using ha (a + Real.pi / 2) hle
  have h3 : |-Real.cos a - L| < (1 / 4 : ℝ) := by
    have hle : a ≤ (a + Real.pi / 2) + Real.pi := by linarith
    simpa [Real.dist_eq, Real.sin_add] using
      ha ((a + Real.pi / 2) + Real.pi) hle
  rcases abs_lt.mp h0 with ⟨h0l, h0u⟩
  rcases abs_lt.mp h1 with ⟨h1l, h1u⟩
  rcases abs_lt.mp h2 with ⟨h2l, h2u⟩
  rcases abs_lt.mp h3 with ⟨h3l, h3u⟩
  have hslo : -(1 / 4 : ℝ) < Real.sin a := by linarith
  have hshi : Real.sin a < (1 / 4 : ℝ) := by linarith
  have hclo : -(1 / 4 : ℝ) < Real.cos a := by linarith
  have hchi : Real.cos a < (1 / 4 : ℝ) := by linarith
  have hsprod :
      0 < ((1 / 4 : ℝ) - Real.sin a) * ((1 / 4 : ℝ) + Real.sin a) :=
    mul_pos (sub_pos.mpr hshi) (by linarith)
  have hcprod :
      0 < ((1 / 4 : ℝ) - Real.cos a) * ((1 / 4 : ℝ) + Real.cos a) :=
    mul_pos (sub_pos.mpr hchi) (by linarith)
  nlinarith [hsprod, hcprod, Real.sin_sq_add_cos_sq a]

theorem gap1 (L : ℝ) :
    Tendsto f (nhds 0) (nhds L) ↔
      Tendsto model (nhds 0) (nhds L) := by
  have hfm : f = model := by
    funext x
    by_cases hx : x = 0 <;> simp [f, model, hx]
  simp [hfm]

theorem gap2 :
    Tendsto model (nhds 0) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with x hx
  have hxe : dist x 0 < ε := Metric.mem_ball.mp hx
  calc
    dist (model x) 0 = |x * Real.sin (1 / x)| := by simp [model, Real.dist_eq]
    _ = |x| * |Real.sin (1 / x)| := abs_mul _ _
    _ ≤ |x| * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (1 / x)) (abs_nonneg x)
    _ = |x| := by ring
    _ < ε := by simpa [Real.dist_eq] using hxe

theorem gap3 :
    (0 : ℝ) = f 0 := by
  simp [f]

theorem gap4 :
    Tendsto f (nhds 0) (nhds (f 0)) := by
  simpa [f] using (gap1 0).2 gap2

theorem gap5 :
    ContinuousAt f 0 := by
  exact gap4

theorem gap6 (h : ℝ) (hh : h ≠ 0) :
    dq f 0 h = Real.sin (1 / h) := by
  simp [dq, f, hh]

theorem gap7 :
    ¬ ∃ L : ℝ,
      Tendsto (fun h : ℝ => Real.sin (1 / h))
        (nhdsWithin 0 (Set.Iio 0)) (nhds L) := by
  rintro ⟨L, hL⟩
  have hinv0 : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hinv :
      Tendsto (fun x : ℝ => -(x⁻¹)) atTop
        (nhdsWithin 0 (Set.Iio 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using hinv0.neg
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact neg_lt_zero.mpr (inv_pos.mpr hx)
  have hc := hL.comp hinv
  have hfun :
      (fun h : ℝ => Real.sin (1 / h)) ∘ (fun x : ℝ => -(x⁻¹)) =
        (fun x : ℝ => -Real.sin x) := by
    funext x
    simp [Function.comp_apply, one_div]
  rw [hfun] at hc
  have hs : Tendsto Real.sin atTop (nhds (-L)) := by
    simpa only [neg_neg] using hc.neg
  exact no_sin_tendsto_atTop (-L) hs

theorem gap8 :
    ¬ ∃ L : ℝ,
      Tendsto (fun h : ℝ => Real.sin (1 / h))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  rintro ⟨L, hL⟩
  have hinv0 : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hinv :
      Tendsto (fun x : ℝ => x⁻¹) atTop
        (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hinv0, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact inv_pos.mpr hx
  have hc := hL.comp hinv
  have hfun :
      (fun h : ℝ => Real.sin (1 / h)) ∘ (fun x : ℝ => x⁻¹) =
        Real.sin := by
    funext x
    simp [Function.comp_apply, one_div]
  rw [hfun] at hc
  exact no_sin_tendsto_atTop L hc

theorem gap9 :
    ¬ LeftDifferentiableAt f 0 := by
  rintro ⟨L, hL⟩
  apply gap7
  refine ⟨L, hL.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact gap6 h (ne_of_lt hh)

theorem gap10 :
    ¬ RightDifferentiableAt f 0 := by
  rintro ⟨L, hL⟩
  apply gap8
  refine ⟨L, hL.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact gap6 h (ne_of_gt hh)

theorem gap11 :
    ContinuousAt f 0 ∧
      ¬ LeftDifferentiableAt f 0 ∧
      ¬ RightDifferentiableAt f 0 := by
  exact ⟨gap5, gap9, gap10⟩

end

end ProofGap.Exercise1009
