import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4268

noncomputable section

open scoped Interval

abbrev Point := ℝ × ℝ

def P (x y : ℝ) : ℝ :=
  1 - y ^ 2 / x ^ 2 * Real.cos (y / x)

def Q (x y : ℝ) : ℝ :=
  Real.sin (y / x) + y / x * Real.cos (y / x)

def field (z : Point) : Point :=
  (P z.1 z.2, Q z.1 z.2)

def potential (z : Point) : ℝ :=
  z.1 - 1 + z.2 * Real.sin (z.2 / z.1)

def InDomain (z : Point) : Prop :=
  0 < z.1

def HasCoordinateGradientAt
    (U : Point → ℝ) (V : Point) (z : Point) : Prop :=
  HasDerivAt (fun x => U (x, z.2)) V.1 z.1 ∧
    HasDerivAt (fun y => U (z.1, y)) V.2 z.2

def AdmissiblePath (γ : ℝ → Point) (start finish : Point) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = start ∧ γ 1 = finish ∧
    ∀ t, t ∈ Set.Icc (0 : ℝ) 1 → InDomain (γ t)

def lineIntegral (γ : ℝ → Point) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    P (γ t).1 (γ t).2 * deriv (fun s => (γ s).1) t +
      Q (γ t).1 (γ t).2 * deriv (fun s => (γ s).2) t

def mixedDerivativeValue (x y : ℝ) : ℝ :=
  -(2 * y / x ^ 2) * Real.cos (y / x) +
    y ^ 2 / x ^ 3 * Real.sin (y / x)

def constructedPotential (x y : ℝ) : ℝ :=
  (∫ s in (1 : ℝ)..x, P s y) +
    ∫ t in Real.pi..y, Real.sin t + t * Real.cos t

private theorem potential_coordinate_gradient_aux
    (x y : ℝ) (hx : 0 < x) :
    HasDerivAt (fun s => potential (s, y)) (P x y) x ∧
      HasDerivAt (fun t => potential (x, t)) (Q x y) y := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  constructor
  · have hquot : HasDerivAt (fun s : ℝ => y / s) (-y / x ^ 2) x := by
      convert (hasDerivAt_const x y).div (hasDerivAt_id x) hx0 using 1 <;>
        (try simp only [id_eq]) <;>
        (try field_simp [hx0]) <;>
        ring_nf
    unfold potential P
    convert ((hasDerivAt_id x).sub_const 1).add
      ((hasDerivAt_const x y).mul hquot.sin) using 1 <;>
      (try simp only [id_eq]) <;>
      (try field_simp [hx0]) <;>
      ring_nf
  · have hquot : HasDerivAt (fun t : ℝ => t / x) (1 / x) y := by
      convert (hasDerivAt_id y).div_const x using 1 <;>
        (try simp only [id_eq]) <;>
        ring_nf
    unfold potential Q
    convert (hasDerivAt_const y (x - 1)).add
      ((hasDerivAt_id y).mul hquot.sin) using 1 <;>
      (try simp only [id_eq]) <;>
      (try field_simp [hx0]) <;>
      ring_nf

theorem gap1 (x y : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => P x t) (mixedDerivativeValue x y) y := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hlin : HasDerivAt (fun t : ℝ => t / x) (1 / x) y := by
    convert (hasDerivAt_id y).div_const x using 1 <;>
      (try simp only [id_eq]) <;>
      ring_nf
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2 / x ^ 2)
      (2 * y / x ^ 2) y := by
    convert ((hasDerivAt_id y).pow 2).div_const (x ^ 2) using 1 <;>
      (try simp only [id_eq]) <;>
      ring_nf
  unfold P mixedDerivativeValue
  convert (hasDerivAt_const y (1 : ℝ)).sub (hsq.mul hlin.cos) using 1 <;>
    (try simp only [id_eq]) <;>
    (try field_simp [hx0]) <;>
    ring_nf

theorem gap2 (x y : ℝ) (hx : 0 < x) :
    HasDerivAt (fun s => Q s y)
      (-(y / x ^ 2) * Real.cos (y / x) -
        (y / x ^ 2) * Real.cos (y / x) +
        y ^ 2 / x ^ 3 * Real.sin (y / x)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hquot : HasDerivAt (fun s : ℝ => y / s) (-y / x ^ 2) x := by
    convert (hasDerivAt_const x y).div (hasDerivAt_id x) hx0 using 1 <;>
      (try simp only [id_eq]) <;>
      (try field_simp [hx0]) <;>
      ring_nf
  unfold Q
  convert hquot.sin.add (hquot.mul hquot.cos) using 1 <;>
    (try simp only [id_eq]) <;>
    (try field_simp [hx0]) <;>
    ring_nf

theorem gap3 (x y : ℝ) (hx : 0 < x) :
    deriv (fun s => Q s y) x = deriv (fun t => P x t) y := by
  rw [(gap2 x y hx).deriv, (gap1 x y hx).deriv]
  unfold mixedDerivativeValue
  ring

theorem gap4 :
    ∃ U : Point → ℝ, ∀ z, InDomain z →
      HasCoordinateGradientAt U (field z) z := by
  refine ⟨potential, ?_⟩
  rintro ⟨x, y⟩ hz
  change 0 < x at hz
  simpa [HasCoordinateGradientAt, field] using
    potential_coordinate_gradient_aux x y hz

theorem gap5 (x y : ℝ) (hx : 0 < x) :
    constructedPotential x y = x - 1 + y * Real.sin (y / x) := by
  have hpos : ∀ s ∈ Set.uIcc (1 : ℝ) x, 0 < s := by
    intro s hs
    rcases (Set.mem_uIcc.mp hs) with hs | hs
    · exact lt_of_lt_of_le zero_lt_one hs.1
    · exact lt_of_lt_of_le hx hs.1
  have hfirst :
      (∫ s in (1 : ℝ)..x, P s y) =
        potential (x, y) - potential (1, y) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro s hs
      exact (potential_coordinate_gradient_aux s y (hpos s hs)).1
    · have hPcont : ContinuousOn (fun s : ℝ => P s y)
          (Set.uIcc (1 : ℝ) x) := by
        intro s hs
        have hs0 : s ≠ 0 := ne_of_gt (hpos s hs)
        have hone : ContinuousAt (fun _ : ℝ => (1 : ℝ)) s := continuousAt_const
        have hyc : ContinuousAt (fun _ : ℝ => y) s := continuousAt_const
        have hic : ContinuousAt (fun r : ℝ => r) s := continuousAt_id
        have hcos : ContinuousAt (fun r : ℝ => Real.cos (y / r)) s := by
          simpa only [Function.comp_apply] using
            Real.continuous_cos.continuousAt.comp (hyc.div hic hs0)
        unfold P
        exact (hone.sub
          (((hyc.pow 2).div (hic.pow 2) (pow_ne_zero 2 hs0)).mul
            hcos)).continuousWithinAt
      exact hPcont.intervalIntegrable
  have hsecond :
      (∫ t in Real.pi..y, Real.sin t + t * Real.cos t) =
        y * Real.sin y - Real.pi * Real.sin Real.pi := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _
      convert (hasDerivAt_id t).mul (Real.hasDerivAt_sin t) using 1 <;>
        simp only [id_eq] <;>
        ring_nf
    · exact (Real.continuous_sin.add
        (continuous_id.mul Real.continuous_cos)).intervalIntegrable _ _
  unfold constructedPotential
  rw [hfirst, hsecond]
  simp [potential, Real.sin_pi] <;> ring

theorem gap6 (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (1, Real.pi) (2, Real.pi)) :
    lineIntegral γ = potential (2, Real.pi) - potential (1, Real.pi) := by
  rcases hγ with ⟨hcd, hstart, hfinish, hdomain⟩
  have hcd1 : ContDiff ℝ 1 (fun t => (γ t).1) := hcd.fst
  have hcd2 : ContDiff ℝ 1 (fun t => (γ t).2) := hcd.snd
  have hdiff1 : Differentiable ℝ (fun t => (γ t).1) :=
    (contDiff_one_iff_deriv.mp hcd1).1
  have hdiff2 : Differentiable ℝ (fun t => (γ t).2) :=
    (contDiff_one_iff_deriv.mp hcd2).1
  have hcder1 : Continuous (fun t => deriv (fun s => (γ s).1) t) :=
    (contDiff_one_iff_deriv.mp hcd1).2
  have hcder2 : Continuous (fun t => deriv (fun s => (γ s).2) t) :=
    (contDiff_one_iff_deriv.mp hcd2).2
  have hpos : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 0 < (γ t).1 := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc] using ht
    simpa [InDomain] using hdomain t ht'
  have hlineCont : ContinuousOn
      (fun t =>
        P (γ t).1 (γ t).2 * deriv (fun s => (γ s).1) t +
          Q (γ t).1 (γ t).2 * deriv (fun s => (γ s).2) t)
      (Set.uIcc (0 : ℝ) 1) := by
    intro t ht
    have hx0 : (γ t).1 ≠ 0 := ne_of_gt (hpos t ht)
    have hc1 : ContinuousAt (fun s => (γ s).1) t :=
      hcd1.continuous.continuousAt
    have hc2 : ContinuousAt (fun s => (γ s).2) t :=
      hcd2.continuous.continuousAt
    have hratio : ContinuousAt
        (fun s => (γ s).2 / (γ s).1) t :=
      hc2.div hc1 hx0
    have hsqratio : ContinuousAt
        (fun s => (γ s).2 ^ 2 / (γ s).1 ^ 2) t :=
      (hc2.pow 2).div (hc1.pow 2) (pow_ne_zero 2 hx0)
    have hcosratio : ContinuousAt
        (fun s => Real.cos ((γ s).2 / (γ s).1)) t := by
      simpa only [Function.comp_apply] using
        Real.continuous_cos.continuousAt.comp hratio
    have hsinratio : ContinuousAt
        (fun s => Real.sin ((γ s).2 / (γ s).1)) t := by
      simpa only [Function.comp_apply] using
        Real.continuous_sin.continuousAt.comp hratio
    have hone : ContinuousAt (fun _ : ℝ => (1 : ℝ)) t := continuousAt_const
    have hPcont : ContinuousAt
        (fun s => P (γ s).1 (γ s).2) t := by
      unfold P
      exact hone.sub (hsqratio.mul hcosratio)
    have hQcont : ContinuousAt
        (fun s => Q (γ s).1 (γ s).2) t := by
      unfold Q
      exact hsinratio.add (hratio.mul hcosratio)
    exact ((hPcont.mul hcder1.continuousAt).add
      (hQcont.mul hcder2.continuousAt)).continuousWithinAt
  calc
    lineIntegral γ = potential (γ 1) - potential (γ 0) := by
      unfold lineIntegral
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t => potential (γ t))
        (f' := fun t =>
          P (γ t).1 (γ t).2 * deriv (fun s => (γ s).1) t +
            Q (γ t).1 (γ t).2 * deriv (fun s => (γ s).2) t) ?_
        hlineCont.intervalIntegrable
      intro t ht
      have hx0 : (γ t).1 ≠ 0 := ne_of_gt (hpos t ht)
      have hxder : HasDerivAt (fun s => (γ s).1)
          (deriv (fun s => (γ s).1) t) t :=
        (hdiff1 t).hasDerivAt
      have hyder : HasDerivAt (fun s => (γ s).2)
          (deriv (fun s => (γ s).2) t) t :=
        (hdiff2 t).hasDerivAt
      have hquot : HasDerivAt
          (fun s => (γ s).2 / (γ s).1)
          ((deriv (fun r => (γ r).2) t * (γ t).1 -
              (γ t).2 * deriv (fun r => (γ r).1) t) /
            (γ t).1 ^ 2) t :=
        hyder.div hxder hx0
      unfold potential P Q
      convert (hxder.sub_const 1).add (hyder.mul hquot.sin) using 1 <;>
        simp only [id_eq] <;>
        field_simp [hx0] <;>
        ring_nf
    _ = potential (2, Real.pi) - potential (1, Real.pi) := by
      rw [hfinish, hstart]

theorem gap7 (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (1, Real.pi) (2, Real.pi)) :
    lineIntegral γ = Real.pi + 1 := by
  rw [gap6 γ hγ]
  simp [potential, Real.sin_pi, Real.sin_pi_div_two] <;> ring

end

end ProofGap.Exercise4268
