import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise4287

noncomputable section

open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def field (φ ψ χ : ℝ → ℝ) (p : Point3) : Point3 :=
  (φ p.1, ψ p.2.1, χ p.2.2)

def potential (φ ψ χ : ℝ → ℝ) (base p : Point3) : ℝ :=
  (∫ u in base.1..p.1, φ u) +
    (∫ v in base.2.1..p.2.1, ψ v) +
      ∫ w in base.2.2..p.2.2, χ w

def HasCoordinateGradientAt
    (U : Point3 → ℝ) (V : Point3) (p : Point3) : Prop :=
  HasDerivAt (fun x => U (x, p.2.1, p.2.2)) V.1 p.1 ∧
    HasDerivAt (fun y => U (p.1, y, p.2.2)) V.2.1 p.2.1 ∧
      HasDerivAt (fun z => U (p.1, p.2.1, z)) V.2.2 p.2.2

def lineIntegral (φ ψ χ : ℝ → ℝ) (γ : ℝ → Point3) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    φ (γ t).1 * deriv (fun s => (γ s).1) t +
      ψ (γ t).2.1 * deriv (fun s => (γ s).2.1) t +
      χ (γ t).2.2 * deriv (fun s => (γ s).2.2) t

def AdmissiblePath (γ : ℝ → Point3) (start finish : Point3) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = start ∧ γ 1 = finish

theorem gap1 (φ ψ χ : ℝ → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ) (hχ : Continuous χ)
    (base p : Point3) :
    HasCoordinateGradientAt (potential φ ψ χ base)
      (field φ ψ χ p) p := by
  unfold HasCoordinateGradientAt
  dsimp [field, potential]
  refine ⟨?_, ?_, ?_⟩
  · simpa using
      (((intervalIntegral.integral_hasDerivAt_right
          (hφ.intervalIntegrable base.1 p.1)
            (hφ.stronglyMeasurableAtFilter MeasureTheory.volume (nhds p.1))
            hφ.continuousAt).add_const
              (∫ v in base.2.1..p.2.1, ψ v)).add_const
                (∫ w in base.2.2..p.2.2, χ w))
  · simpa using
      (((intervalIntegral.integral_hasDerivAt_right
          (hψ.intervalIntegrable base.2.1 p.2.1)
            (hψ.stronglyMeasurableAtFilter MeasureTheory.volume (nhds p.2.1))
            hψ.continuousAt).const_add
              (∫ u in base.1..p.1, φ u)).add_const
                (∫ w in base.2.2..p.2.2, χ w))
  · simpa using
      ((intervalIntegral.integral_hasDerivAt_right
          (hχ.intervalIntegrable base.2.2 p.2.2)
            (hχ.stronglyMeasurableAtFilter MeasureTheory.volume (nhds p.2.2))
            hχ.continuousAt).const_add
              ((∫ u in base.1..p.1, φ u) +
                ∫ v in base.2.1..p.2.1, ψ v))

theorem gap2 (φ ψ χ : ℝ → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ) (hχ : Continuous χ)
    (start finish : Point3) (γ : ℝ → Point3)
    (hγ : AdmissiblePath γ start finish) :
    lineIntegral φ ψ χ γ =
      potential φ ψ χ start finish - potential φ ψ χ start start := by
  rcases hγ with ⟨hγcd, hγ0, hγ1⟩
  have hγx : ContDiff ℝ 1 (fun t : ℝ => (γ t).1) :=
    ContDiff.fst hγcd
  have hγyz : ContDiff ℝ 1 (fun t : ℝ => (γ t).2) :=
    ContDiff.snd hγcd
  have hγy : ContDiff ℝ 1 (fun t : ℝ => (γ t).2.1) :=
    ContDiff.fst hγyz
  have hγz : ContDiff ℝ 1 (fun t : ℝ => (γ t).2.2) :=
    ContDiff.snd hγyz
  have hγx_deriv : Continuous (fun t : ℝ => deriv (fun s : ℝ => (γ s).1) t) := by
    simpa only [deriv] using
      ((hγx.continuous_fderiv (n := 1) one_ne_zero).clm_apply
        (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))))
  have hγy_deriv : Continuous (fun t : ℝ => deriv (fun s : ℝ => (γ s).2.1) t) := by
    simpa only [deriv] using
      ((hγy.continuous_fderiv (n := 1) one_ne_zero).clm_apply
        (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))))
  have hγz_deriv : Continuous (fun t : ℝ => deriv (fun s : ℝ => (γ s).2.2) t) := by
    simpa only [deriv] using
      ((hγz.continuous_fderiv (n := 1) one_ne_zero).clm_apply
        (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))))
  let P : ℝ → ℝ := fun t => potential φ ψ χ start (γ t)
  have hP (t : ℝ) :
      HasDerivAt P
        (φ (γ t).1 * deriv (fun s : ℝ => (γ s).1) t +
          ψ (γ t).2.1 * deriv (fun s : ℝ => (γ s).2.1) t +
            χ (γ t).2.2 * deriv (fun s : ℝ => (γ s).2.2) t) t := by
    have hdx : HasDerivAt (fun s : ℝ => (γ s).1)
        (deriv (fun s : ℝ => (γ s).1) t) t :=
      ((hγx.differentiable one_ne_zero).differentiableAt).hasDerivAt
    have hdy : HasDerivAt (fun s : ℝ => (γ s).2.1)
        (deriv (fun s : ℝ => (γ s).2.1) t) t :=
      ((hγy.differentiable one_ne_zero).differentiableAt).hasDerivAt
    have hdz : HasDerivAt (fun s : ℝ => (γ s).2.2)
        (deriv (fun s : ℝ => (γ s).2.2) t) t :=
      ((hγz.differentiable one_ne_zero).differentiableAt).hasDerivAt
    have hx :=
      (intervalIntegral.integral_hasDerivAt_right
        (hφ.intervalIntegrable start.1 (γ t).1)
          (hφ.stronglyMeasurableAtFilter MeasureTheory.volume (nhds (γ t).1))
          hφ.continuousAt).comp t hdx
    have hy :=
      (intervalIntegral.integral_hasDerivAt_right
        (hψ.intervalIntegrable start.2.1 (γ t).2.1)
          (hψ.stronglyMeasurableAtFilter MeasureTheory.volume (nhds (γ t).2.1))
          hψ.continuousAt).comp t hdy
    have hz :=
      (intervalIntegral.integral_hasDerivAt_right
        (hχ.intervalIntegrable start.2.2 (γ t).2.2)
          (hχ.stronglyMeasurableAtFilter MeasureTheory.volume (nhds (γ t).2.2))
          hχ.continuousAt).comp t hdz
    simpa [P, potential] using (hx.add hy).add hz
  have hI : Continuous
      (fun t : ℝ =>
        φ (γ t).1 * deriv (fun s : ℝ => (γ s).1) t +
          ψ (γ t).2.1 * deriv (fun s : ℝ => (γ s).2.1) t +
            χ (γ t).2.2 * deriv (fun s : ℝ => (γ s).2.2) t) :=
    (((hφ.comp hγx.continuous).mul hγx_deriv).add
      ((hψ.comp hγy.continuous).mul hγy_deriv)).add
        ((hχ.comp hγz.continuous).mul hγz_deriv)
  have hFTC :
      (∫ t in (0 : ℝ)..1,
        φ (γ t).1 * deriv (fun s : ℝ => (γ s).1) t +
          ψ (γ t).2.1 * deriv (fun s : ℝ => (γ s).2.1) t +
            χ (γ t).2.2 * deriv (fun s : ℝ => (γ s).2.2) t) =
        P 1 - P 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hP t) (hI.intervalIntegrable 0 1)
  simpa [lineIntegral, P, hγ0, hγ1] using hFTC

theorem gap3 (φ ψ χ : ℝ → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ) (hχ : Continuous χ)
    (start finish : Point3) (γ : ℝ → Point3)
    (hγ : AdmissiblePath γ start finish) :
    lineIntegral φ ψ χ γ =
      (∫ u in start.1..finish.1, φ u) +
        (∫ v in start.2.1..finish.2.1, ψ v) +
          ∫ w in start.2.2..finish.2.2, χ w := by
  simpa [potential] using
    (gap2 φ ψ χ hφ hψ hχ start finish γ hγ)

end

end ProofGap.Exercise4287
