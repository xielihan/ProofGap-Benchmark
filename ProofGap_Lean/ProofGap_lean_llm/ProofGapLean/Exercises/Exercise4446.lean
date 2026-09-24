import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise4446

noncomputable section

open MeasureTheory

abbrev Vec2 := ℝ × ℝ
abbrev Vec3 := ℝ × ℝ × ℝ

def coordinateMap (x y z : Vec2 → ℝ) (p : Vec2) : Vec3 :=
  (x p, y p, z p)

def partialU (f : Vec2 → ℝ) (p : Vec2) : ℝ :=
  deriv (fun u => f (u, p.2)) p.1

def partialV (f : Vec2 → ℝ) (p : Vec2) : ℝ :=
  deriv (fun v => f (p.1, v)) p.2

def surfacePartialU (r : Vec2 → Vec3) (p : Vec2) : Vec3 :=
  (partialU (fun q => (r q).1) p,
    partialU (fun q => (r q).2.1) p,
    partialU (fun q => (r q).2.2) p)

def surfacePartialV (r : Vec2 → Vec3) (p : Vec2) : Vec3 :=
  (partialV (fun q => (r q).1) p,
    partialV (fun q => (r q).2.1) p,
    partialV (fun q => (r q).2.2) p)

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def cross (a b : Vec3) : Vec3 :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1,
    a.2.2 * b.1 - a.1 * b.2.2,
    a.1 * b.2.1 - a.2.1 * b.1)

def scale (c : ℝ) (a : Vec3) : Vec3 :=
  (c * a.1, c * a.2.1, c * a.2.2)

def norm (a : Vec3) : ℝ :=
  Real.sqrt (dot a a)

def firstFundamentalE (r : Vec2 → Vec3) (p : Vec2) : ℝ :=
  dot (surfacePartialU r p) (surfacePartialU r p)

def firstFundamentalF (r : Vec2 → Vec3) (p : Vec2) : ℝ :=
  dot (surfacePartialU r p) (surfacePartialV r p)

def firstFundamentalG (r : Vec2 → Vec3) (p : Vec2) : ℝ :=
  dot (surfacePartialV r p) (surfacePartialV r p)

def areaDensity (r : Vec2 → Vec3) (p : Vec2) : ℝ :=
  Real.sqrt
    (firstFundamentalE r p * firstFundamentalG r p -
      firstFundamentalF r p ^ 2)

def unitNormal (r : Vec2 → Vec3) (p : Vec2) : Vec3 :=
  scale (1 / norm (cross (surfacePartialU r p) (surfacePartialV r p)))
    (cross (surfacePartialU r p) (surfacePartialV r p))

def parameterFlux (Ω : Set Vec2) (r : Vec2 → Vec3)
    (a : Vec3 → Vec3) : ℝ :=
  ∫ p in Ω,
    dot (a (r p)) (cross (surfacePartialU r p) (surfacePartialV r p))

def normalFormFlux (Ω : Set Vec2) (r : Vec2 → Vec3)
    (a : Vec3 → Vec3) : ℝ :=
  ∫ p in Ω,
    dot (a (r p)) (scale (areaDensity r p) (unitNormal r p))

theorem gap1 (x y z : Vec2 → ℝ) (p : Vec2) :
    coordinateMap x y z p = (x p, y p, z p) := by
  rfl

theorem gap2 (x y z : Vec2 → ℝ) (p : Vec2) :
    surfacePartialU (coordinateMap x y z) p =
      (partialU x p, partialU y p, partialU z p) := by
  rfl

theorem gap3 (x y z : Vec2 → ℝ) (p : Vec2) :
    surfacePartialV (coordinateMap x y z) p =
      (partialV x p, partialV y p, partialV z p) := by
  rfl

theorem gap4 (r : Vec2 → Vec3) (p : Vec2) :
    cross (surfacePartialU r p) (surfacePartialV r p) =
      ((surfacePartialU r p).2.1 * (surfacePartialV r p).2.2 -
          (surfacePartialU r p).2.2 * (surfacePartialV r p).2.1,
        (surfacePartialU r p).2.2 * (surfacePartialV r p).1 -
          (surfacePartialU r p).1 * (surfacePartialV r p).2.2,
        (surfacePartialU r p).1 * (surfacePartialV r p).2.1 -
          (surfacePartialU r p).2.1 * (surfacePartialV r p).1) := by
  rfl

theorem gap5 (r : Vec2 → Vec3) (p : Vec2) :
    norm (cross (surfacePartialU r p) (surfacePartialV r p)) =
      areaDensity r p := by
  unfold norm areaDensity firstFundamentalE firstFundamentalF
    firstFundamentalG dot cross
  apply congrArg Real.sqrt
  ring

theorem gap6 (r : Vec2 → Vec3) (p : Vec2)
    (hRegular :
      norm (cross (surfacePartialU r p) (surfacePartialV r p)) ≠ 0) :
    cross (surfacePartialU r p) (surfacePartialV r p) =
      scale (areaDensity r p) (unitNormal r p) := by
  rw [← gap5 r p]
  unfold unitNormal scale
  apply Prod.ext
  · field_simp [hRegular]
  · apply Prod.ext
    · field_simp [hRegular]
    · field_simp [hRegular]

theorem gap7 (Ω : Set Vec2) (r : Vec2 → Vec3) (a : Vec3 → Vec3)
    (hRegular :
      ∀ p ∈ Ω,
        norm (cross (surfacePartialU r p) (surfacePartialV r p)) ≠ 0) :
    parameterFlux Ω r a = normalFormFlux Ω r a := by
  unfold parameterFlux normalFormFlux
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  let c : Vec3 :=
    cross (surfacePartialU r p) (surfacePartialV r p)
  change
    dot (a (r p)) c =
      dot (a (r p)) (scale (areaDensity r p) (unitNormal r p))
  by_cases hc0 : norm c ≠ 0
  · have hvec :
        c = scale (areaDensity r p) (unitNormal r p) := by
      simpa [c] using
        (gap6 r p (by simpa [c] using hc0))
    rw [hvec]
  · have hn : norm c = 0 := by
      simpa using hc0
    have hnonneg : 0 ≤ dot c c := by
      unfold dot
      nlinarith [sq_nonneg c.1, sq_nonneg c.2.1,
        sq_nonneg c.2.2]
    have hdot : dot c c = 0 := by
      have hs := Real.sq_sqrt hnonneg
      unfold norm at hn
      nlinarith
    unfold dot at hdot
    have hc1 : c.1 = 0 := by
      nlinarith [sq_nonneg c.1, sq_nonneg c.2.1,
        sq_nonneg c.2.2]
    have hc2 : c.2.1 = 0 := by
      nlinarith [sq_nonneg c.1, sq_nonneg c.2.1,
        sq_nonneg c.2.2]
    have hc3 : c.2.2 = 0 := by
      nlinarith [sq_nonneg c.1, sq_nonneg c.2.1,
        sq_nonneg c.2.2]
    have hcvec : c = (0, 0, 0) := by
      apply Prod.ext
      · exact hc1
      · apply Prod.ext
        · exact hc2
        · exact hc3
    have ha : areaDensity r p = 0 := by
      rw [← gap5 r p]
      simpa [c] using hn
    rw [hcvec, ha]
    simp [dot, scale]

theorem gap8 (Ω : Set Vec2) (r : Vec2 → Vec3) (a : Vec3 → Vec3)
    (hRegular :
      ∀ p ∈ Ω,
        norm (cross (surfacePartialU r p) (surfacePartialV r p)) ≠ 0) :
    normalFormFlux Ω r a =
      ∫ p in Ω,
        dot (a (r p)) (cross (surfacePartialU r p) (surfacePartialV r p)) := by
  simpa [parameterFlux] using (gap7 Ω r a hRegular).symm

theorem gap9 (Ω : Set Vec2) (r : Vec2 → Vec3) (a : Vec3 → Vec3) :
    parameterFlux Ω r a =
      ∫ p in Ω,
        dot (a (r p)) (cross (surfacePartialU r p) (surfacePartialV r p)) := by
  rfl

theorem gap10 (Ω : Set Vec2) (r : Vec2 → Vec3) (a : Vec3 → Vec3) :
    parameterFlux Ω r a =
      ∫ p in Ω,
        dot (a (r p)) (cross (surfacePartialU r p) (surfacePartialV r p)) := by
  exact gap9 Ω r a

end

end ProofGap.Exercise4446
