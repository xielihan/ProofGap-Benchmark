import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4387

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (u v : Vec3) : ℝ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

def divergence (F : Vec3 → Vec3) (p : Vec3) : ℝ :=
  deriv (fun x => (F (x, p.2.1, p.2.2)).1) p.1 +
    deriv (fun y => (F (p.1, y, p.2.2)).2.1) p.2.1 +
      deriv (fun z => (F (p.1, p.2.1, z)).2.2) p.2.2

def squareField (p : Vec3) : Vec3 :=
  (p.1 ^ 2, p.2.1 ^ 2, p.2.2 ^ 2)

def cubeBoundaryFlux (a : ℝ) (F : Vec3 → Vec3) : ℝ :=
  (∫ y in (0 : ℝ)..a,
      ∫ z in (0 : ℝ)..a, dot (F (a, y, z)) (1, 0, 0)) +
    (∫ y in (0 : ℝ)..a,
      ∫ z in (0 : ℝ)..a, dot (F (0, y, z)) (-1, 0, 0)) +
    (∫ x in (0 : ℝ)..a,
      ∫ z in (0 : ℝ)..a, dot (F (x, a, z)) (0, 1, 0)) +
    (∫ x in (0 : ℝ)..a,
      ∫ z in (0 : ℝ)..a, dot (F (x, 0, z)) (0, -1, 0)) +
    (∫ x in (0 : ℝ)..a,
      ∫ y in (0 : ℝ)..a, dot (F (x, y, a)) (0, 0, 1)) +
    (∫ x in (0 : ℝ)..a,
      ∫ y in (0 : ℝ)..a, dot (F (x, y, 0)) (0, 0, -1))

def cubeDivergenceIntegral (a : ℝ) (F : Vec3 → Vec3) : ℝ :=
  ∫ x in (0 : ℝ)..a,
    ∫ y in (0 : ℝ)..a,
      ∫ z in (0 : ℝ)..a, divergence F (x, y, z)

def SatisfiesCubeDivergenceTheorem (a : ℝ) : Prop :=
  ∀ F : Vec3 → Vec3, ContDiff ℝ 1 F →
    cubeBoundaryFlux a F = cubeDivergenceIntegral a F

def boundaryFlux (a : ℝ) : ℝ :=
  cubeBoundaryFlux a squareField

def divergenceVolumeIntegral (a : ℝ) : ℝ :=
  cubeDivergenceIntegral a squareField

def symmetricReduction (a : ℝ) : ℝ :=
  6 * (∫ _x in (0 : ℝ)..a, (1 : ℝ)) *
    (∫ _y in (0 : ℝ)..a, (1 : ℝ)) *
      ∫ z in (0 : ℝ)..a, z

private theorem cube_integral_affine_from_zero (a c d : ℝ) :
    (∫ t in (0 : ℝ)..a, c + d * t) =
      c * a + d * (a ^ 2 / 2) := by
  have hanti (t : ℝ) :
      HasDerivAt
        (fun s : ℝ => c * s + (d / 2) * (s * s))
        (c + d * t) t := by
    convert
      (((hasDerivAt_const (x := t) c).mul (hasDerivAt_id t)).add
        ((hasDerivAt_const (x := t) (d / 2)).mul
          ((hasDerivAt_id t).mul (hasDerivAt_id t)))) using 1 <;>
      simp [id] <;> ring
  have hcont : Continuous (fun t : ℝ => c + d * t) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hint :
      IntervalIntegrable (fun t : ℝ => c + d * t)
        MeasureTheory.volume 0 a :=
    hcont.intervalIntegrable 0 a
  calc
    (∫ t in (0 : ℝ)..a, c + d * t) =
        (c * a + (d / 2) * (a * a)) -
          (c * 0 + (d / 2) * (0 * 0)) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ht => hanti t) hint
    _ = c * a + d * (a ^ 2 / 2) := by ring

theorem gap1 (a : ℝ) (ha : 0 < a)
    (hGauss : SatisfiesCubeDivergenceTheorem a) :
    boundaryFlux a = divergenceVolumeIntegral a := by
  refine hGauss squareField ?_
  have hx : ContDiff ℝ 1 (fun p : Vec3 => p.1) := contDiff_fst
  have hp : ContDiff ℝ 1 (fun p : Vec3 => p.2) := contDiff_snd
  have hy0 : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1) := contDiff_fst
  have hz0 : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.2) := contDiff_snd
  have hy : ContDiff ℝ 1 (fun p : Vec3 => p.2.1) := hy0.comp hp
  have hz : ContDiff ℝ 1 (fun p : Vec3 => p.2.2) := hz0.comp hp
  change ContDiff ℝ 1
    (fun p : Vec3 => (p.1 ^ 2, p.2.1 ^ 2, p.2.2 ^ 2))
  exact (hx.pow 2).prodMk ((hy.pow 2).prodMk (hz.pow 2))

theorem gap2 (a : ℝ) (ha : 0 < a) :
    divergenceVolumeIntegral a =
      2 *
        ∫ x in (0 : ℝ)..a,
          ∫ y in (0 : ℝ)..a,
            ∫ z in (0 : ℝ)..a, x + y + z := by
  have hsq (t : ℝ) : deriv (fun s : ℝ => s ^ 2) t = 2 * t := by
    simpa [pow_two, two_mul] using
      ((hasDerivAt_id t).mul (hasDerivAt_id t)).deriv
  simp only [divergenceVolumeIntegral, cubeDivergenceIntegral, divergence,
    squareField]
  simp_rw [hsq]
  rw [← intervalIntegral.integral_const_mul]
  apply congrArg (fun f : ℝ → ℝ => ∫ x in (0 : ℝ)..a, f x)
  funext x
  rw [← intervalIntegral.integral_const_mul]
  apply congrArg (fun f : ℝ → ℝ => ∫ y in (0 : ℝ)..a, f y)
  funext y
  rw [← intervalIntegral.integral_const_mul]
  apply congrArg (fun f : ℝ → ℝ => ∫ z in (0 : ℝ)..a, f z)
  funext z
  ring

theorem gap3 (a : ℝ) (ha : 0 < a) :
    divergenceVolumeIntegral a = symmetricReduction a := by
  have hz (x y : ℝ) :
      (∫ z in (0 : ℝ)..a, x + y + z) =
        (x + y) * a + a ^ 2 / 2 := by
    simpa using cube_integral_affine_from_zero a (x + y) 1
  have hy (x : ℝ) :
      (∫ y in (0 : ℝ)..a, (x + y) * a + a ^ 2 / 2) =
        (x * a + a ^ 2 / 2) * a + a * (a ^ 2 / 2) := by
    calc
      (∫ y in (0 : ℝ)..a, (x + y) * a + a ^ 2 / 2) =
          (∫ y in (0 : ℝ)..a,
            (x * a + a ^ 2 / 2) + a * y) := by
            apply congrArg
              (fun f : ℝ → ℝ => ∫ y in (0 : ℝ)..a, f y)
            funext y
            ring
      _ = (x * a + a ^ 2 / 2) * a + a * (a ^ 2 / 2) :=
        cube_integral_affine_from_zero a (x * a + a ^ 2 / 2) a
  have hx :
      (∫ x in (0 : ℝ)..a,
        (x * a + a ^ 2 / 2) * a + a * (a ^ 2 / 2)) =
        ((a ^ 2 / 2) * a + a * (a ^ 2 / 2)) * a +
          (a * a) * (a ^ 2 / 2) := by
    calc
      (∫ x in (0 : ℝ)..a,
        (x * a + a ^ 2 / 2) * a + a * (a ^ 2 / 2)) =
          (∫ x in (0 : ℝ)..a,
            ((a ^ 2 / 2) * a + a * (a ^ 2 / 2)) +
              (a * a) * x) := by
            apply congrArg
              (fun f : ℝ → ℝ => ∫ x in (0 : ℝ)..a, f x)
            funext x
            ring
      _ = ((a ^ 2 / 2) * a + a * (a ^ 2 / 2)) * a +
          (a * a) * (a ^ 2 / 2) :=
        cube_integral_affine_from_zero a
          ((a ^ 2 / 2) * a + a * (a ^ 2 / 2)) (a * a)
  have hone : (∫ _t in (0 : ℝ)..a, (1 : ℝ)) = a := by
    simpa using cube_integral_affine_from_zero a 1 0
  have hid : (∫ t in (0 : ℝ)..a, t) = a ^ 2 / 2 := by
    simpa using cube_integral_affine_from_zero a 0 1
  rw [gap2 a ha]
  simp_rw [hz]
  simp_rw [hy]
  rw [hx]
  simp only [symmetricReduction, hone, hid]
  ring

theorem gap4 (a : ℝ) (ha : 0 < a) :
    symmetricReduction a = 3 * a ^ 4 := by
  have hone : (∫ _t in (0 : ℝ)..a, (1 : ℝ)) = a := by
    simpa using cube_integral_affine_from_zero a 1 0
  have hid : (∫ t in (0 : ℝ)..a, t) = a ^ 2 / 2 := by
    simpa using cube_integral_affine_from_zero a 0 1
  simp only [symmetricReduction, hone, hid]
  ring

end

end ProofGap.Exercise4387
