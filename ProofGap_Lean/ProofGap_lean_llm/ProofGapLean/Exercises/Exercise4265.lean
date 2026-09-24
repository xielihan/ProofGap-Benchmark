import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4265

noncomputable section

open scoped Interval

abbrev Point := ℝ × ℝ

def field (φ ψ : ℝ → ℝ) (z : Point) : Point :=
  (φ z.1, ψ z.2)

def potential (F G : ℝ → ℝ) (z : Point) : ℝ :=
  F z.1 + G z.2

def coordinateDifferential (V v : Point) : ℝ :=
  V.1 * v.1 + V.2 * v.2

def separatedDifferential (F G : ℝ → ℝ) (z v : Point) : ℝ :=
  deriv F z.1 * v.1 + deriv G z.2 * v.2

def differential (U : Point → ℝ) (z v : Point) : ℝ :=
  deriv (fun x => U (x, z.2)) z.1 * v.1 +
    deriv (fun y => U (z.1, y)) z.2 * v.2

def AdmissiblePath (γ : ℝ → Point) (start finish : Point) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = start ∧ γ 1 = finish

def lineIntegral (φ ψ : ℝ → ℝ) (γ : ℝ → Point) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    φ (γ t).1 * deriv (fun s => (γ s).1) t +
      ψ (γ t).2 * deriv (fun s => (γ s).2) t

private theorem lineIntegral_endpoint
    (φ ψ F G : ℝ → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hF : ∀ x, HasDerivAt F (φ x) x)
    (hG : ∀ y, HasDerivAt G (ψ y) y)
    (x₁ y₁ x₂ y₂ : ℝ) (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (x₁, y₁) (x₂, y₂)) :
    lineIntegral φ ψ γ =
      potential F G (x₂, y₂) -
        potential F G (x₁, y₁) := by
  have hcx : ContDiff ℝ 1 (fun t => (γ t).1) :=
    hγ.1.fst
  have hcy : ContDiff ℝ 1 (fun t => (γ t).2) :=
    hγ.1.snd
  have hdx :
      Continuous
        (fun t => deriv (fun s => (γ s).1) t) :=
    (contDiff_one_iff_deriv.mp hcx).2
  have hdy :
      Continuous
        (fun t => deriv (fun s => (γ s).2) t) :=
    (contDiff_one_iff_deriv.mp hcy).2
  have hdiffx :
      Differentiable ℝ (fun t => (γ t).1) :=
    (contDiff_one_iff_deriv.mp hcx).1
  have hdiffy :
      Differentiable ℝ (fun t => (γ t).2) :=
    (contDiff_one_iff_deriv.mp hcy).1
  have hpot (t : ℝ) :
      HasDerivAt (fun s => potential F G (γ s))
        (φ (γ t).1 *
            deriv (fun s => (γ s).1) t +
          ψ (γ t).2 *
            deriv (fun s => (γ s).2) t) t := by
    have h₁ :=
      (hF (γ t).1).comp t
        (hdiffx t).hasDerivAt
    have h₂ :=
      (hG (γ t).2).comp t
        (hdiffy t).hasDerivAt
    simpa [potential, Function.comp_def] using h₁.add h₂
  have hint :
      Continuous
        (fun t =>
          φ (γ t).1 *
              deriv (fun s => (γ s).1) t +
            ψ (γ t).2 *
              deriv (fun s => (γ s).2) t) :=
    ((hφ.comp hcx.continuous).mul hdx).add
      ((hψ.comp hcy.continuous).mul hdy)
  unfold lineIntegral
  calc
    _ = potential F G (γ 1) -
          potential F G (γ 0) := by
      exact
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t ht => hpot t)
          (hint.intervalIntegrable 0 1)
    _ = potential F G (x₂, y₂) -
          potential F G (x₁, y₁) := by
      rw [hγ.2.2, hγ.2.1]

theorem gap1 (φ ψ F G : ℝ → ℝ)
    (hF : ∀ x, HasDerivAt F (φ x) x)
    (hG : ∀ y, HasDerivAt G (ψ y) y)
    (z v : Point) :
    coordinateDifferential (field φ ψ z) v =
      separatedDifferential F G z v := by
  unfold coordinateDifferential field separatedDifferential
  rw [(hF z.1).deriv, (hG z.2).deriv]

theorem gap2 (F G : ℝ → ℝ) (z v : Point) :
    separatedDifferential F G z v =
      differential (potential F G) z v := by
  unfold separatedDifferential differential potential
  simp only [Prod.fst, Prod.snd]
  rw [deriv_add_const, deriv_const_add]

theorem gap3 (φ ψ F G : ℝ → ℝ)
    (hF : ∀ x, HasDerivAt F (φ x) x)
    (hG : ∀ y, HasDerivAt G (ψ y) y)
    (z v : Point) :
    coordinateDifferential (field φ ψ z) v =
      differential (potential F G) z v := by
  rw [gap1 φ ψ F G hF hG z v,
    gap2 F G z v]

theorem gap4 (φ ψ F G : ℝ → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hF : ∀ x, HasDerivAt F (φ x) x)
    (hG : ∀ y, HasDerivAt G (ψ y) y)
    (x₁ y₁ x₂ y₂ : ℝ) (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (x₁, y₁) (x₂, y₂)) :
    lineIntegral φ ψ γ =
      potential F G (x₂, y₂) - potential F G (x₁, y₁) := by
  exact
    lineIntegral_endpoint φ ψ F G hφ hψ hF hG
      x₁ y₁ x₂ y₂ γ hγ

theorem gap5 (F G : ℝ → ℝ) (x₁ y₁ x₂ y₂ : ℝ) :
    potential F G (x₂, y₂) - potential F G (x₁, y₁) =
      F x₂ + G y₂ - (F x₁ + G y₁) := by
  rfl

theorem gap6 (φ ψ F G : ℝ → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hF : ∀ x, HasDerivAt F (φ x) x)
    (hG : ∀ y, HasDerivAt G (ψ y) y)
    (x₁ y₁ x₂ y₂ : ℝ) :
    F x₂ + G y₂ - (F x₁ + G y₁) =
      (∫ u in x₁..x₂, φ u) + ∫ v in y₁..y₂, ψ v := by
  have h₁ :
      (∫ u in x₁..x₂, φ u) = F x₂ - F x₁ := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => hF u)
      (hφ.intervalIntegrable x₁ x₂)
  have h₂ :
      (∫ v in y₁..y₂, ψ v) = G y₂ - G y₁ := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v hv => hG v)
      (hψ.intervalIntegrable y₁ y₂)
  rw [h₁, h₂]
  ring

theorem gap7 (φ ψ F G : ℝ → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hF : ∀ x, HasDerivAt F (φ x) x)
    (hG : ∀ y, HasDerivAt G (ψ y) y)
    (x₁ y₁ x₂ y₂ : ℝ) (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (x₁, y₁) (x₂, y₂)) :
    lineIntegral φ ψ γ =
      (∫ u in x₁..x₂, φ u) + ∫ v in y₁..y₂, ψ v := by
  calc
    lineIntegral φ ψ γ =
        potential F G (x₂, y₂) -
          potential F G (x₁, y₁) :=
      gap4 φ ψ F G hφ hψ hF hG
        x₁ y₁ x₂ y₂ γ hγ
    _ = F x₂ + G y₂ - (F x₁ + G y₁) :=
      gap5 F G x₁ y₁ x₂ y₂
    _ = _ :=
      gap6 φ ψ F G hφ hψ hF hG
        x₁ y₁ x₂ y₂

end

end ProofGap.Exercise4265
