import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise4453

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (p q : Vec3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def radialPath (t₀ : Vec3) (s : ℝ) : Vec3 :=
  (s * t₀.1, s * t₀.2.1, s * t₀.2.2)

def radialWorkIntegrand (f : ℝ → ℝ) (t₀ : Vec3) (s : ℝ) : ℝ :=
  f s * s * dot t₀ t₀

def radialWork (f : ℝ → ℝ) (t₀ : Vec3) (rA rB : ℝ) : ℝ :=
  ∫ s in rA..rB, radialWorkIntegrand f t₀ s

def scalarRadialIntegral (f : ℝ → ℝ) (rA rB : ℝ) : ℝ :=
  ∫ s in rA..rB, f s * s

def lineIntegral (f : ℝ → ℝ) (t₀ : Vec3) (rA rB : ℝ) : ℝ :=
  radialWork f t₀ rA rB

theorem gap1 (f : ℝ → ℝ) (t₀ : Vec3) (rA rB : ℝ)
    (hf : Continuous f) (hA : 0 ≤ rA) (hAB : rA ≤ rB)
    (ht : dot t₀ t₀ = 1) :
    radialWork f t₀ rA rB =
      ∫ s in rA..rB, radialWorkIntegrand f t₀ s := by
  rfl

theorem gap2 (f : ℝ → ℝ) (t₀ : Vec3) (rA rB : ℝ)
    (hf : Continuous f) (hA : 0 ≤ rA) (hAB : rA ≤ rB)
    (ht : dot t₀ t₀ = 1) :
    radialWork f t₀ rA rB =
      ∫ s in rA..rB, f s * s * dot t₀ t₀ := by
  rfl

theorem gap3 (f : ℝ → ℝ) (t₀ : Vec3) (rA rB : ℝ)
    (hf : Continuous f) (hA : 0 ≤ rA) (hAB : rA ≤ rB)
    (ht : dot t₀ t₀ = 1) :
    (∫ s in rA..rB, f s * s * dot t₀ t₀) =
      scalarRadialIntegral f rA rB := by
  simp [scalarRadialIntegral, ht]

theorem gap4 (f : ℝ → ℝ) (t₀ : Vec3) (rA rB : ℝ)
    (hf : Continuous f) (hA : 0 ≤ rA) (hAB : rA ≤ rB)
    (ht : dot t₀ t₀ = 1) :
    radialWork f t₀ rA rB = scalarRadialIntegral f rA rB := by
  simp [radialWork, radialWorkIntegrand, scalarRadialIntegral, ht]

theorem gap5 (f : ℝ → ℝ) (t₀ : Vec3) (rA rB : ℝ)
    (hf : Continuous f) (hA : 0 ≤ rA) (hAB : rA ≤ rB)
    (ht : dot t₀ t₀ = 1) :
    lineIntegral f t₀ rA rB = scalarRadialIntegral f rA rB := by
  simp [lineIntegral, radialWork, radialWorkIntegrand, scalarRadialIntegral, ht]

end

end ProofGap.Exercise4453
