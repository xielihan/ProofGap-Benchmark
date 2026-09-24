import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4364

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def topDisk (h : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ h ^ 2}

def topFlux (h : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ r in (0 : ℝ)..h, r ^ 2 * (Real.cos φ - Real.sin φ)

def lateralPoint (p : Vec3) : Prop :=
  p.1 ^ 2 + p.2.1 ^ 2 = p.2.2 ^ 2 ∧ 0 < p.2.2

def normalCosines (p : Vec3) : Vec3 :=
  (p.1 / (Real.sqrt 2 * p.2.2),
    p.2.1 / (Real.sqrt 2 * p.2.2),
    -1 / Real.sqrt 2)

def surfaceJacobian : ℝ :=
  Real.sqrt 2

def diskMoment (h : ℝ) : ℝ :=
  ∫ p in topDisk h, p.1 - p.2

def lateralFlux (h : ℝ) : ℝ :=
  -2 * diskMoment h

def totalFlux (h : ℝ) : ℝ :=
  topFlux h + lateralFlux h

theorem gap1 (h : ℝ) (hh : 0 < h) :
    topFlux h =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..h, r ^ 2 * (Real.cos φ - Real.sin φ) := by
  rfl

theorem gap2 (h : ℝ) (hh : 0 < h) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
      ∫ r in (0 : ℝ)..h, r ^ 2 * (Real.cos φ - Real.sin φ)) = 0 := by
  have hinner (φ : ℝ) :
      (∫ r in (0 : ℝ)..h, r ^ 2 * (Real.cos φ - Real.sin φ)) =
        (∫ r in (0 : ℝ)..h, r ^ 2) * (Real.cos φ - Real.sin φ) := by
    rw [intervalIntegral.integral_mul_const]
  have hderiv (x : ℝ) :
      HasDerivAt (fun t : ℝ => Real.sin t + Real.cos t)
        (Real.cos x - Real.sin x) x := by
    simpa only [sub_eq_add_neg] using
      (Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)
  have hangInt :
      IntervalIntegrable (fun x : ℝ => Real.cos x - Real.sin x)
        volume (0 : ℝ) (2 * Real.pi) :=
    (Real.continuous_cos.sub Real.continuous_sin).intervalIntegrable _ _
  have hang :
      (∫ φ in (0 : ℝ)..2 * Real.pi,
        Real.cos φ - Real.sin φ) = 0 := by
    calc
      (∫ φ in (0 : ℝ)..2 * Real.pi,
          Real.cos φ - Real.sin φ) =
          (Real.sin (2 * Real.pi) + Real.cos (2 * Real.pi)) -
            (Real.sin 0 + Real.cos 0) := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun x : ℝ => Real.sin x + Real.cos x)
        all_goals
          first
          | exact hangInt
          | exact (Real.continuous_cos.sub Real.continuous_sin).continuousOn
          | exact (Real.continuous_sin.add Real.continuous_cos).continuousOn
          | intro x hx
            exact hderiv x
          | intro x hx
            exact (hderiv x).hasDerivWithinAt
      _ = 0 := by simp
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul, hang]
  simp

theorem gap3 (h : ℝ) (hh : 0 < h) :
    topFlux h = 0 := by
  calc
    topFlux h =
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..h, r ^ 2 * (Real.cos φ - Real.sin φ) := gap1 h hh
    _ = 0 := gap2 h hh

theorem gap4 (p : Vec3) (hp : lateralPoint p)
    (hx : p.1 ≠ 0) (hy : p.2.1 ≠ 0) :
    (normalCosines p).1 / p.1 =
      (normalCosines p).2.1 / p.2.1 := by
  have hz : p.2.2 ≠ 0 := ne_of_gt hp.2
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  dsimp [normalCosines]
  field_simp [hx, hy, hz, hs] <;> ring

theorem gap5 (p : Vec3) (hp : lateralPoint p)
    (hy : p.2.1 ≠ 0) :
    (normalCosines p).2.1 / p.2.1 =
      (normalCosines p).2.2 / (-p.2.2) := by
  have hz : p.2.2 ≠ 0 := ne_of_gt hp.2
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  dsimp [normalCosines]
  field_simp [hy, hz, hs] <;> ring

theorem gap6 (p : Vec3) (hp : lateralPoint p)
    (hx : p.1 ≠ 0) :
    (normalCosines p).1 / p.1 =
      (normalCosines p).2.2 / (-p.2.2) := by
  have hz : p.2.2 ≠ 0 := ne_of_gt hp.2
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  dsimp [normalCosines]
  field_simp [hx, hz, hs] <;> ring

theorem gap7 (p : Vec3) (hp : lateralPoint p) :
    (normalCosines p).2.2 * surfaceJacobian = -1 := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  dsimp [normalCosines, surfaceJacobian]
  field_simp [hs] <;> ring

theorem gap8 (p : Vec3) (hp : lateralPoint p) :
    (normalCosines p).1 * surfaceJacobian =
      p.1 / p.2.2 := by
  have hz : p.2.2 ≠ 0 := ne_of_gt hp.2
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  dsimp [normalCosines, surfaceJacobian]
  field_simp [hz, hs] <;> ring

theorem gap9 (p : Vec3) (hp : lateralPoint p) :
    (normalCosines p).2.1 * surfaceJacobian =
      p.2.1 / p.2.2 := by
  have hz : p.2.2 ≠ 0 := ne_of_gt hp.2
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  dsimp [normalCosines, surfaceJacobian]
  field_simp [hz, hs] <;> ring

theorem gap10 (h : ℝ) (hh : 0 < h) :
    lateralFlux h = -2 * ∫ p in topDisk h, p.1 - p.2 := by
  rfl

theorem gap11 (h : ℝ) (hh : 0 < h) :
    (∫ p in topDisk h, p.1 - p.2) = 0 := by
  have hS : MeasurableSet (topDisk h) := by
    have hc : Continuous (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) :=
      (continuous_fst.pow 2).add (continuous_snd.pow 2)
    have hk : Continuous (fun _ : ℝ × ℝ => h ^ 2) := continuous_const
    exact measurableSet_le hc.measurable hk.measurable
  let F : ℝ × ℝ → ℝ :=
    (topDisk h).indicator (fun p => p.1 - p.2)
  have hmem (p : ℝ × ℝ) :
      Prod.swap p ∈ topDisk h ↔ p ∈ topDisk h := by
    rcases p with ⟨x, y⟩
    simp [topDisk, add_comm]
  have hFswap (p : ℝ × ℝ) : F (Prod.swap p) = -F p := by
    by_cases hp : p ∈ topDisk h
    · have hsp : Prod.swap p ∈ topDisk h := (hmem p).2 hp
      simp [F, hp, hsp]
    · have hsp : Prod.swap p ∉ topDisk h := by
        intro hs
        exact hp ((hmem p).1 hs)
      simp [F, hp, hsp]
  have hpres : MeasurePreserving Prod.swap
      (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × ℝ)) := by
    simpa using
      (Measure.measurePreserving_swap
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
  have htransform :
      (∫ p, F (Prod.swap p)) = ∫ p, F p := by
    simpa using
      hpres.integral_comp
        ((MeasurableEquiv.prodComm : MeasurableEquiv (ℝ × ℝ) (ℝ × ℝ)).measurableEmbedding) F
  have hodd : (∫ p, F p) = -(∫ p, F p) := by
    calc
      (∫ p, F p) = ∫ p, F (Prod.swap p) := htransform.symm
      _ = ∫ p, -F p :=
        integral_congr_ae (Filter.Eventually.of_forall hFswap)
      _ = -(∫ p, F p) := by
        rw [integral_neg]
  have hzero : (∫ p, F p) = 0 := by
    linarith
  rw [← integral_indicator hS]
  exact hzero

theorem gap12 (h : ℝ) (hh : 0 < h) :
    lateralFlux h = 0 := by
  simp [lateralFlux, diskMoment, gap11 h hh]

theorem gap13 (h : ℝ) (hh : 0 < h) :
    totalFlux h = 0 := by
  simp [totalFlux, gap3 h hh, gap12 h hh]

end

end ProofGap.Exercise4364
