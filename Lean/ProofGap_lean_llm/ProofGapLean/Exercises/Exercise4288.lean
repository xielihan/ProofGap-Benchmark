import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4288

noncomputable section

open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def coordinateSum (p : Point3) : ℝ :=
  p.1 + p.2.1 + p.2.2

def potential (f : ℝ → ℝ) (p : Point3) : ℝ :=
  ∫ u in (0 : ℝ)..coordinateSum p, f u

def field (f : ℝ → ℝ) (p : Point3) : Point3 :=
  (f (coordinateSum p), f (coordinateSum p), f (coordinateSum p))

def coordinateDifferential (V v : Point3) : ℝ :=
  V.1 * v.1 + V.2.1 * v.2.1 + V.2.2 * v.2.2

def differential (F : Point3 → ℝ) (p v : Point3) : ℝ :=
  deriv (fun x => F (x, p.2.1, p.2.2)) p.1 * v.1 +
    deriv (fun y => F (p.1, y, p.2.2)) p.2.1 * v.2.1 +
      deriv (fun z => F (p.1, p.2.1, z)) p.2.2 * v.2.2

def lineIntegral (f : ℝ → ℝ) (γ : ℝ → Point3) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    coordinateDifferential (field f (γ t))
      (deriv (fun s => (γ s).1) t,
        deriv (fun s => (γ s).2.1) t,
        deriv (fun s => (γ s).2.2) t)

def AdmissiblePath (γ : ℝ → Point3) (start finish : Point3) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = start ∧ γ 1 = finish

theorem gap1 (f : ℝ → ℝ) (hf : Continuous f) (p : Point3) :
    HasDerivAt (fun x => potential f (x, p.2.1, p.2.2))
      (f (coordinateSum p)) p.1 := by
  have hI :
      HasDerivAt (fun b : ℝ => ∫ u in (0 : ℝ)..b, f u)
        (f (coordinateSum p)) (coordinateSum p) :=
    intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable _ _)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuousAt
  have hs :
      HasDerivAt (fun x : ℝ => x + p.2.1 + p.2.2) 1 p.1 := by
    simpa using
      ((hasDerivAt_id p.1).add_const p.2.1).add_const p.2.2
  simpa [potential, coordinateSum] using hI.comp p.1 hs

theorem gap2 (f : ℝ → ℝ) (hf : Continuous f) (p : Point3) :
    HasDerivAt (fun y => potential f (p.1, y, p.2.2))
      (f (coordinateSum p)) p.2.1 := by
  have hI :
      HasDerivAt (fun b : ℝ => ∫ u in (0 : ℝ)..b, f u)
        (f (coordinateSum p)) (coordinateSum p) :=
    intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable _ _)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuousAt
  have hs :
      HasDerivAt (fun y : ℝ => p.1 + y + p.2.2) 1 p.2.1 := by
    simpa using
      ((hasDerivAt_const p.2.1 p.1).add (hasDerivAt_id p.2.1)).add_const p.2.2
  simpa [potential, coordinateSum] using hI.comp p.2.1 hs

theorem gap3 (f : ℝ → ℝ) (hf : Continuous f) (p : Point3) :
    HasDerivAt (fun z => potential f (p.1, p.2.1, z))
      (f (coordinateSum p)) p.2.2 := by
  have hI :
      HasDerivAt (fun b : ℝ => ∫ u in (0 : ℝ)..b, f u)
        (f (coordinateSum p)) (coordinateSum p) :=
    intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable _ _)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuousAt
  have hs :
      HasDerivAt (fun z : ℝ => p.1 + p.2.1 + z) 1 p.2.2 := by
    simpa using
      (hasDerivAt_const p.2.2 (p.1 + p.2.1)).add (hasDerivAt_id p.2.2)
  simpa [potential, coordinateSum] using hI.comp p.2.2 hs

theorem gap4 (f : ℝ → ℝ) (hf : Continuous f) (p v : Point3) :
    differential (potential f) p v =
      f (coordinateSum p) * (v.1 + v.2.1 + v.2.2) := by
  have hx := (gap1 f hf p).deriv
  have hy := (gap2 f hf p).deriv
  have hz := (gap3 f hf p).deriv
  simp only [differential]
  rw [hx, hy, hz]
  ring

theorem gap5 (f : ℝ → ℝ) (hf : Continuous f)
    (start finish : Point3) (γ : ℝ → Point3)
    (hγ : AdmissiblePath γ start finish) :
    lineIntegral f γ = potential f finish - potential f start := by
  rcases hγ with ⟨hγdiff, hγ0, hγ1⟩
  have hcx : ContDiff ℝ 1 (fun t : ℝ => (γ t).1) := by
    simpa only using (contDiff_fst.comp hγdiff)
  have hcsnd : ContDiff ℝ 1 (fun t : ℝ => (γ t).2) := by
    simpa only using (contDiff_snd.comp hγdiff)
  have hcy : ContDiff ℝ 1 (fun t : ℝ => (γ t).2.1) := by
    simpa only using (contDiff_fst.comp hcsnd)
  have hcz : ContDiff ℝ 1 (fun t : ℝ => (γ t).2.2) := by
    simpa only using (contDiff_snd.comp hcsnd)
  have hsumcd : ContDiff ℝ 1 (fun t : ℝ => coordinateSum (γ t)) := by
    simpa [coordinateSum] using (hcx.add hcy).add hcz
  have hc : Continuous (fun t : ℝ => f (coordinateSum (γ t))) :=
    hf.comp hsumcd.continuous
  have hfd :
      Continuous (fderiv ℝ (fun s : ℝ => coordinateSum (γ s))) :=
    hsumcd.continuous_fderiv (by norm_num)
  have hds :
      Continuous (deriv (fun s : ℝ => coordinateSum (γ s))) := by
    unfold deriv
    fun_prop
  have hs (t : ℝ) :
      HasDerivAt (fun s : ℝ => coordinateSum (γ s))
        (deriv (fun s : ℝ => (γ s).1) t +
          deriv (fun s : ℝ => (γ s).2.1) t +
          deriv (fun s : ℝ => (γ s).2.2) t) t := by
    simpa [coordinateSum] using
      (((hcx.differentiable (by norm_num) t).hasDerivAt.add
          (hcy.differentiable (by norm_num) t).hasDerivAt).add
        (hcz.differentiable (by norm_num) t).hasDerivAt)
  have hcurve (t : ℝ) :
      HasDerivAt (fun s : ℝ => potential f (γ s))
        (coordinateDifferential (field f (γ t))
          (deriv (fun s : ℝ => (γ s).1) t,
            deriv (fun s : ℝ => (γ s).2.1) t,
            deriv (fun s : ℝ => (γ s).2.2) t)) t := by
    have hout :
        HasDerivAt (fun b : ℝ => ∫ u in (0 : ℝ)..b, f u)
          (f (coordinateSum (γ t))) (coordinateSum (γ t)) :=
      intervalIntegral.integral_hasDerivAt_right
        (hf.intervalIntegrable _ _)
        hf.stronglyMeasurable.stronglyMeasurableAtFilter
        hf.continuousAt
    have hp := hout.comp t (hs t)
    have hp' :
        HasDerivAt (fun s : ℝ => potential f (γ s))
          (f (coordinateSum (γ t)) *
            (deriv (fun s : ℝ => (γ s).1) t +
              deriv (fun s : ℝ => (γ s).2.1) t +
              deriv (fun s : ℝ => (γ s).2.2) t)) t := by
      simpa [potential] using hp
    convert hp' using 1 <;> simp [coordinateDifferential, field] <;> ring
  have heq :
      (fun t : ℝ =>
        coordinateDifferential (field f (γ t))
          (deriv (fun s : ℝ => (γ s).1) t,
            deriv (fun s : ℝ => (γ s).2.1) t,
            deriv (fun s : ℝ => (γ s).2.2) t)) =
      (fun t : ℝ =>
        f (coordinateSum (γ t)) *
          deriv (fun s : ℝ => coordinateSum (γ s)) t) := by
    funext t
    rw [(hs t).deriv]
    simp [coordinateDifferential, field]
    ring
  have hint :
      IntervalIntegrable
        (fun t : ℝ =>
          coordinateDifferential (field f (γ t))
            (deriv (fun s : ℝ => (γ s).1) t,
              deriv (fun s : ℝ => (γ s).2.1) t,
              deriv (fun s : ℝ => (γ s).2.2) t))
        MeasureTheory.volume 0 1 := by
    rw [heq]
    simpa only [Pi.mul_apply] using
      (hc.mul hds).intervalIntegrable
        (μ := MeasureTheory.volume) (0 : ℝ) (1 : ℝ)
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := (1 : ℝ)) (fun t _ => hcurve t) hint
  simpa [lineIntegral, hγ0, hγ1] using hFTC

theorem gap6 (f : ℝ → ℝ) (start finish : Point3) :
    potential f finish - potential f start =
      (∫ u in (0 : ℝ)..coordinateSum finish, f u) -
        ∫ u in (0 : ℝ)..coordinateSum start, f u := by
  rfl

theorem gap7 (f : ℝ → ℝ) (hf : Continuous f)
    (start finish : Point3) (γ : ℝ → Point3)
    (hγ : AdmissiblePath γ start finish) :
    lineIntegral f γ = potential f finish - potential f start := by
  exact gap5 f hf start finish γ hγ

theorem gap8 (f : ℝ → ℝ) (hf : Continuous f)
    (start finish : Point3) (γ : ℝ → Point3)
    (hγ : AdmissiblePath γ start finish) :
    lineIntegral f γ =
      (∫ u in (0 : ℝ)..coordinateSum finish, f u) -
        ∫ u in (0 : ℝ)..coordinateSum start, f u := by
  rw [gap7 f hf start finish γ hγ]
  exact gap6 f start finish

theorem gap9 (f : ℝ → ℝ) (hf : Continuous f) (start finish : Point3) :
    (∫ u in (0 : ℝ)..coordinateSum finish, f u) -
        (∫ u in (0 : ℝ)..coordinateSum start, f u) =
      ∫ u in coordinateSum start..coordinateSum finish, f u := by
  have hsymm :
      (∫ u in coordinateSum start..(0 : ℝ), f u) =
        -(∫ u in (0 : ℝ)..coordinateSum start, f u) :=
    intervalIntegral.integral_symm _ _
  calc
    (∫ u in (0 : ℝ)..coordinateSum finish, f u) -
          (∫ u in (0 : ℝ)..coordinateSum start, f u) =
        (∫ u in coordinateSum start..(0 : ℝ), f u) +
          ∫ u in (0 : ℝ)..coordinateSum finish, f u := by
            rw [hsymm]
            ring
    _ = ∫ u in coordinateSum start..coordinateSum finish, f u :=
      intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

theorem gap10 (f : ℝ → ℝ) (hf : Continuous f)
    (start finish : Point3) (γ : ℝ → Point3)
    (hγ : AdmissiblePath γ start finish) :
    lineIntegral f γ =
      ∫ u in coordinateSum start..coordinateSum finish, f u := by
  calc
    lineIntegral f γ =
        (∫ u in (0 : ℝ)..coordinateSum finish, f u) -
          ∫ u in (0 : ℝ)..coordinateSum start, f u :=
      gap8 f hf start finish γ hγ
    _ = ∫ u in coordinateSum start..coordinateSum finish, f u :=
      gap9 f hf start finish

end

end ProofGap.Exercise4288
