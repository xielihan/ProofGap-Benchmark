import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4262

noncomputable section

open scoped Interval

abbrev Point := ℝ × ℝ

def potential (f : ℝ → ℝ) (z : Point) : ℝ :=
  ∫ u in (0 : ℝ)..z.1 + z.2, f u

def field (f : ℝ → ℝ) (z : Point) : Point :=
  (f (z.1 + z.2), f (z.1 + z.2))

def HasCoordinateGradientAt
    (U : Point → ℝ) (V : Point) (z : Point) : Prop :=
  HasDerivAt (fun x => U (x, z.2)) V.1 z.1 ∧
    HasDerivAt (fun y => U (z.1, y)) V.2 z.2

def coordinateDifferential (V v : Point) : ℝ :=
  V.1 * v.1 + V.2 * v.2

def differential (U : Point → ℝ) (z v : Point) : ℝ :=
  deriv (fun x => U (x, z.2)) z.1 * v.1 +
    deriv (fun y => U (z.1, y)) z.2 * v.2

def form (f : ℝ → ℝ) (z v : Point) : ℝ :=
  f (z.1 + z.2) * (v.1 + v.2)

def AdmissiblePath (γ : ℝ → Point) (start finish : Point) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = start ∧ γ 1 = finish

def lineIntegral (f : ℝ → ℝ) (γ : ℝ → Point) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    f ((γ t).1 + (γ t).2) *
      (deriv (fun s => (γ s).1) t + deriv (fun s => (γ s).2) t)

theorem gap1 (f : ℝ → ℝ) (hf : Continuous f) (x y : ℝ) :
    HasDerivAt (fun s => potential f (s, y)) (f (x + y)) x := by
  have hI :
      HasDerivAt (fun b : ℝ => ∫ u in (0 : ℝ)..b, f u)
        (f (x + y)) (x + y) :=
    intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable _ _)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuousAt
  have hs : HasDerivAt (fun s : ℝ => s + y) 1 x := by
    simpa using (hasDerivAt_id x).add_const y
  simpa [potential] using hI.comp x hs

theorem gap2 (f : ℝ → ℝ) (hf : Continuous f) (x y : ℝ) :
    HasDerivAt (fun t => potential f (x, t)) (f (x + y)) y := by
  have hI :
      HasDerivAt (fun b : ℝ => ∫ u in (0 : ℝ)..b, f u)
        (f (x + y)) (x + y) :=
    intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable _ _)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuousAt
  have hs : HasDerivAt (fun t : ℝ => x + t) 1 y := by
    simpa using (hasDerivAt_const y x).add (hasDerivAt_id y)
  simpa [potential] using hI.comp y hs

theorem gap3 (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (fun z : Point => (field f z).1) := by
  simpa [field] using hf.comp (continuous_fst.add continuous_snd)

theorem gap4 (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (fun z : Point => (field f z).2) := by
  simpa [field] using hf.comp (continuous_fst.add continuous_snd)

theorem gap5 (f : ℝ → ℝ) (hf : Continuous f) (z v : Point) :
    differential (potential f) z v =
      coordinateDifferential (field f z) v := by
  have hx := (gap1 f hf z.1 z.2).deriv
  have hy := (gap2 f hf z.1 z.2).deriv
  simp only [differential, coordinateDifferential, field]
  rw [hx, hy]

theorem gap6 (f : ℝ → ℝ) (z v : Point) :
    coordinateDifferential (field f z) v = form f z v := by
  simp only [coordinateDifferential, field, form]
  ring

theorem gap7 (f : ℝ → ℝ) (hf : Continuous f) (z v : Point) :
    differential (potential f) z v = form f z v := by
  rw [gap5 f hf z v, gap6 f z v]

theorem gap8 (f : ℝ → ℝ) (hf : Continuous f)
    (a b : ℝ) (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (0, 0) (a, b)) :
    lineIntegral f γ = potential f (a, b) - potential f (0, 0) := by
  rcases hγ with ⟨hγdiff, hγ0, hγ1⟩
  have hcx : ContDiff ℝ 1 (fun t : ℝ => (γ t).1) := by
    simpa only using (contDiff_fst.comp hγdiff)
  have hcy : ContDiff ℝ 1 (fun t : ℝ => (γ t).2) := by
    simpa only using (contDiff_snd.comp hγdiff)
  have hsumcd : ContDiff ℝ 1 (fun t : ℝ => (γ t).1 + (γ t).2) :=
    hcx.add hcy
  have hc : Continuous (fun t : ℝ => f ((γ t).1 + (γ t).2)) :=
    hf.comp hsumcd.continuous
  have hds :
      Continuous (deriv (fun s : ℝ => (γ s).1 + (γ s).2)) := by
    unfold deriv
    fun_prop
  have hs (t : ℝ) :
      HasDerivAt (fun s : ℝ => (γ s).1 + (γ s).2)
        (deriv (fun s : ℝ => (γ s).1) t +
          deriv (fun s : ℝ => (γ s).2) t) t := by
    exact
      (hcx.differentiable (by norm_num) t).hasDerivAt.add
        (hcy.differentiable (by norm_num) t).hasDerivAt
  have hcurve (t : ℝ) :
      HasDerivAt (fun s : ℝ => potential f (γ s))
        (f ((γ t).1 + (γ t).2) *
          (deriv (fun s : ℝ => (γ s).1) t +
            deriv (fun s : ℝ => (γ s).2) t)) t := by
    have hout :
        HasDerivAt (fun c : ℝ => ∫ u in (0 : ℝ)..c, f u)
          (f ((γ t).1 + (γ t).2)) ((γ t).1 + (γ t).2) :=
      intervalIntegral.integral_hasDerivAt_right
        (hf.intervalIntegrable _ _)
        hf.stronglyMeasurable.stronglyMeasurableAtFilter
        hf.continuousAt
    simpa [potential] using hout.comp t (hs t)
  have heq :
      (fun t : ℝ =>
        f ((γ t).1 + (γ t).2) *
          (deriv (fun s => (γ s).1) t +
            deriv (fun s => (γ s).2) t)) =
      (fun t : ℝ =>
        f ((γ t).1 + (γ t).2) *
          deriv (fun s : ℝ => (γ s).1 + (γ s).2) t) := by
    funext t
    rw [(hs t).deriv]
  have hint :
      IntervalIntegrable
        (fun t : ℝ =>
          f ((γ t).1 + (γ t).2) *
            (deriv (fun s => (γ s).1) t +
              deriv (fun s => (γ s).2) t))
        MeasureTheory.volume 0 1 := by
    rw [heq]
    simpa only [Pi.mul_apply] using
      (hc.mul hds).intervalIntegrable
        (μ := MeasureTheory.volume) (0 : ℝ) (1 : ℝ)
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := (1 : ℝ)) (fun t _ => hcurve t) hint
  simpa [lineIntegral, hγ0, hγ1] using hFTC

theorem gap9 (f : ℝ → ℝ) (a b : ℝ) :
    potential f (a, b) - potential f (0, 0) =
      ∫ u in (0 : ℝ)..a + b, f u := by
  simp [potential]

theorem gap10 (f : ℝ → ℝ) (hf : Continuous f)
    (a b : ℝ) (γ : ℝ → Point)
    (hγ : AdmissiblePath γ (0, 0) (a, b)) :
    lineIntegral f γ = ∫ u in (0 : ℝ)..a + b, f u := by
  rw [gap8 f hf a b γ hγ, gap9 f a b]

end

end ProofGap.Exercise4262
