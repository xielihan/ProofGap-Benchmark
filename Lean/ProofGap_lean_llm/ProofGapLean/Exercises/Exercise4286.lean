import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise4286

noncomputable section

open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def squaredNorm (p : Point3) : ℝ :=
  p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2

def radius (p : Point3) : ℝ :=
  Real.sqrt (squaredNorm p)

def radialField (p : Point3) : Point3 :=
  (p.1 / radius p, p.2.1 / radius p, p.2.2 / radius p)

def lineIntegral (γ : ℝ → Point3) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    (radialField (γ t)).1 * deriv (fun s => (γ s).1) t +
      (radialField (γ t)).2.1 * deriv (fun s => (γ s).2.1) t +
      (radialField (γ t)).2.2 * deriv (fun s => (γ s).2.2) t

def AdmissiblePath (γ : ℝ → Point3) (start finish : Point3) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = start ∧ γ 1 = finish ∧
    ∀ t, t ∈ Set.Icc (0 : ℝ) 1 → γ t ≠ (0, 0, 0)

private theorem squaredNorm_pos_of_ne_zero (p : Point3)
    (hp : p ≠ (0, 0, 0)) : 0 < squaredNorm p := by
  rcases p with ⟨x, y, z⟩
  unfold squaredNorm
  have hcoord : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 := by
    by_cases hx : x = 0
    · by_cases hy : y = 0
      · by_cases hz : z = 0
        · exact (hp (by simp [hx, hy, hz])).elim
        · exact Or.inr (Or.inr hz)
      · exact Or.inr (Or.inl hy)
    · exact Or.inl hx
  rcases hcoord with hx | hy | hz
  · have hxpos : 0 < x ^ 2 := by
      simpa [pow_two] using (mul_self_pos.mpr hx)
    nlinarith [sq_nonneg y, sq_nonneg z]
  · have hypos : 0 < y ^ 2 := by
      simpa [pow_two] using (mul_self_pos.mpr hy)
    nlinarith [sq_nonneg x, sq_nonneg z]
  · have hzpos : 0 < z ^ 2 := by
      simpa [pow_two] using (mul_self_pos.mpr hz)
    nlinarith [sq_nonneg x, sq_nonneg y]

theorem gap1 (p q : Point3) (a b : ℝ)
    (hp : squaredNorm p = a ^ 2)
    (hq : squaredNorm q = b ^ 2) (ha : 0 < a) (hb : 0 < b) :
    squaredNorm p = a ^ 2 := by
  exact hp

theorem gap2 (p q : Point3) (a b : ℝ)
    (hp : squaredNorm p = a ^ 2)
    (hq : squaredNorm q = b ^ 2) (ha : 0 < a) (hb : 0 < b) :
    squaredNorm q = b ^ 2 := by
  exact hq

theorem gap3 (p q : Point3) (γ : ℝ → Point3)
    (hγ : AdmissiblePath γ p q) :
    lineIntegral γ = radius q - radius p := by
  rcases hγ with ⟨hcd, hstart, hfinish, hne⟩
  have hcdx : ContDiff ℝ 1 (fun t => (γ t).1) := hcd.fst
  have hcdy : ContDiff ℝ 1 (fun t => (γ t).2.1) := hcd.snd.fst
  have hcdz : ContDiff ℝ 1 (fun t => (γ t).2.2) := hcd.snd.snd
  have hscont : Continuous (fun t => squaredNorm (γ t)) := by
    simpa [squaredNorm] using
      (((hcdx.continuous.pow 2).add (hcdy.continuous.pow 2)).add
        (hcdz.continuous.pow 2))
  have hrcont : Continuous (fun t => radius (γ t)) := by
    unfold radius
    exact Real.continuous_sqrt.comp hscont
  have hrne : ∀ t ∈ Set.Icc (0 : ℝ) 1, radius (γ t) ≠ 0 := by
    intro t ht
    unfold radius
    exact ne_of_gt (Real.sqrt_pos.2 (squaredNorm_pos_of_ne_zero (γ t) (hne t ht)))
  have hdxcont : Continuous (fun t => deriv (fun s => (γ s).1) t) := by
    simpa only [deriv] using
      ((hcdx.continuous_fderiv one_ne_zero).clm_apply
        (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))))
  have hdycont : Continuous (fun t => deriv (fun s => (γ s).2.1) t) := by
    simpa only [deriv] using
      ((hcdy.continuous_fderiv one_ne_zero).clm_apply
        (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))))
  have hdzcont : Continuous (fun t => deriv (fun s => (γ s).2.2) t) := by
    simpa only [deriv] using
      ((hcdz.continuous_fderiv one_ne_zero).clm_apply
        (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))))
  have htx : ContinuousOn
      (fun t => (γ t).1 / radius (γ t) * deriv (fun s => (γ s).1) t)
      (Set.Icc (0 : ℝ) 1) :=
    (hcdx.continuous.continuousOn.div hrcont.continuousOn hrne).mul
      hdxcont.continuousOn
  have hty : ContinuousOn
      (fun t => (γ t).2.1 / radius (γ t) * deriv (fun s => (γ s).2.1) t)
      (Set.Icc (0 : ℝ) 1) :=
    (hcdy.continuous.continuousOn.div hrcont.continuousOn hrne).mul
      hdycont.continuousOn
  have htz : ContinuousOn
      (fun t => (γ t).2.2 / radius (γ t) * deriv (fun s => (γ s).2.2) t)
      (Set.Icc (0 : ℝ) 1) :=
    (hcdz.continuous.continuousOn.div hrcont.continuousOn hrne).mul
      hdzcont.continuousOn
  have hgcontIcc : ContinuousOn
      (fun t =>
        (γ t).1 / radius (γ t) * deriv (fun s => (γ s).1) t +
          (γ t).2.1 / radius (γ t) * deriv (fun s => (γ s).2.1) t +
          (γ t).2.2 / radius (γ t) * deriv (fun s => (γ s).2.2) t)
      (Set.Icc (0 : ℝ) 1) :=
    (htx.add hty).add htz
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have hgcont : ContinuousOn
      (fun t =>
        (γ t).1 / radius (γ t) * deriv (fun s => (γ s).1) t +
          (γ t).2.1 / radius (γ t) * deriv (fun s => (γ s).2.1) t +
          (γ t).2.2 / radius (γ t) * deriv (fun s => (γ s).2.2) t)
      (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le h01] using hgcontIcc
  have hradIcc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => radius (γ s))
        ((γ t).1 / radius (γ t) * deriv (fun s => (γ s).1) t +
          (γ t).2.1 / radius (γ t) * deriv (fun s => (γ s).2.1) t +
          (γ t).2.2 / radius (γ t) * deriv (fun s => (γ s).2.2) t) t := by
    intro t ht
    have hpos : 0 < squaredNorm (γ t) :=
      squaredNorm_pos_of_ne_zero (γ t) (hne t ht)
    have hsqrtne : Real.sqrt (squaredNorm (γ t)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hpos)
    have hx : HasDerivAt (fun s => (γ s).1)
        (deriv (fun s => (γ s).1) t) t :=
      (hcdx.differentiable one_ne_zero).differentiableAt.hasDerivAt
    have hy : HasDerivAt (fun s => (γ s).2.1)
        (deriv (fun s => (γ s).2.1) t) t :=
      (hcdy.differentiable one_ne_zero).differentiableAt.hasDerivAt
    have hz : HasDerivAt (fun s => (γ s).2.2)
        (deriv (fun s => (γ s).2.2) t) t :=
      (hcdz.differentiable one_ne_zero).differentiableAt.hasDerivAt
    have hs : HasDerivAt (fun s => squaredNorm (γ s))
        (2 * (γ t).1 * deriv (fun s => (γ s).1) t +
          2 * (γ t).2.1 * deriv (fun s => (γ s).2.1) t +
          2 * (γ t).2.2 * deriv (fun s => (γ s).2.2) t) t := by
      simpa [squaredNorm, pow_two] using
        (((hx.pow 2).add (hy.pow 2)).add (hz.pow 2))
    unfold radius
    convert (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp t hs using 1
    field_simp [hsqrtne]
    <;> ring
  have hrad : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => radius (γ s))
        ((γ t).1 / radius (γ t) * deriv (fun s => (γ s).1) t +
          (γ t).2.1 / radius (γ t) * deriv (fun s => (γ s).2.1) t +
          (γ t).2.2 / radius (γ t) * deriv (fun s => (γ s).2.2) t) t := by
    intro t ht
    apply hradIcc t
    simpa [Set.uIcc_of_le h01] using ht
  rw [← hfinish, ← hstart]
  unfold lineIntegral radialField
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hrad hgcont.intervalIntegrable

theorem gap4 (p q : Point3) :
    radius q - radius p =
      Real.sqrt (squaredNorm q) - Real.sqrt (squaredNorm p) := by
  rfl

theorem gap5 (p q : Point3) (a b : ℝ)
    (hp : squaredNorm p = a ^ 2)
    (hq : squaredNorm q = b ^ 2) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (squaredNorm q) - Real.sqrt (squaredNorm p) = b - a := by
  rw [hq, hp, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    abs_of_pos hb, abs_of_pos ha]

theorem gap6 (p q : Point3) (a b : ℝ) (γ : ℝ → Point3)
    (hp : squaredNorm p = a ^ 2)
    (hq : squaredNorm q = b ^ 2) (ha : 0 < a) (hb : 0 < b)
    (hγ : AdmissiblePath γ p q) :
    lineIntegral γ = b - a := by
  calc
    lineIntegral γ = radius q - radius p := gap3 p q γ hγ
    _ = Real.sqrt (squaredNorm q) - Real.sqrt (squaredNorm p) := gap4 p q
    _ = b - a := gap5 p q a b hp hq ha hb

end

end ProofGap.Exercise4286
