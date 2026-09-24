import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise4368

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def scalarPotential (p : Vec3) : ℝ :=
  (p.1 ^ 3 + p.2.1 ^ 3 + p.2.2 ^ 3) / 3 -
    p.1 * p.2.1 * p.2.2

def pointA (a : ℝ) : Vec3 :=
  (a, 0, 0)

def pointB (a h : ℝ) : Vec3 :=
  (a, 0, h)

def vectorField (p : Vec3) : Vec3 :=
  (p.1 ^ 2 - p.2.1 * p.2.2,
    p.2.1 ^ 2 - p.1 * p.2.2,
    p.2.2 ^ 2 - p.1 * p.2.1)

def helixPath (a h t : ℝ) : Vec3 :=
  (a * Real.cos t, a * Real.sin t, h / (2 * Real.pi) * t)

def closingPath (a h t : ℝ) : Vec3 :=
  (a, 0, h * (1 - t))

def pathIntegral (F : Vec3 → Vec3) (γ : ℝ → Vec3)
    (c d : ℝ) : ℝ :=
  ∫ t in c..d,
    (F (γ t)).1 * deriv (fun s => (γ s).1) t +
      (F (γ t)).2.1 * deriv (fun s => (γ s).2.1) t +
      (F (γ t)).2.2 * deriv (fun s => (γ s).2.2) t

def derivative (γ : ℝ → Vec3) (t : ℝ) : Vec3 :=
  (deriv (fun s => (γ s).1) t,
    deriv (fun s => (γ s).2.1) t,
    deriv (fun s => (γ s).2.2) t)

def dot (p q : Vec3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def cross (p q : Vec3) : Vec3 :=
  (p.2.1 * q.2.2 - p.2.2 * q.2.1,
    p.2.2 * q.1 - p.1 * q.2.2,
    p.1 * q.2.1 - p.2.1 * q.1)

def curl (F : Vec3 → Vec3) (p : Vec3) : Vec3 :=
  (deriv (fun y => (F (p.1, y, p.2.2)).2.2) p.2.1 -
      deriv (fun z => (F (p.1, p.2.1, z)).2.1) p.2.2,
    deriv (fun z => (F (p.1, p.2.1, z)).1) p.2.2 -
      deriv (fun x => (F (x, p.2.1, p.2.2)).2.2) p.1,
    deriv (fun x => (F (x, p.2.1, p.2.2)).2.1) p.1 -
      deriv (fun y => (F (p.1, y, p.2.2)).1) p.2.1)

def coneSurface (a h r t : ℝ) : Vec3 :=
  let A := pointA a
  let H := helixPath a h t
  (A.1 + r * (H.1 - A.1),
    A.2.1 + r * (H.2.1 - A.2.1),
    A.2.2 + r * (H.2.2 - A.2.2))

def coneAreaVector (a h r t : ℝ) : Vec3 :=
  cross (derivative (fun s => coneSurface a h s t) r)
    (derivative (coneSurface a h r) t)

def curlSurfaceFlux (a h : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..1,
    ∫ t in (0 : ℝ)..2 * Real.pi,
      dot (curl vectorField (coneSurface a h r t))
        (coneAreaVector a h r t)

def helixIntegral (a h : ℝ) : ℝ :=
  pathIntegral vectorField (helixPath a h) 0 (2 * Real.pi)

def axialIntegral (h : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..h, z ^ 2

def closingSegmentIntegral (a h : ℝ) : ℝ :=
  pathIntegral vectorField (closingPath a h) 0 1

def closedLoopIntegral (a h : ℝ) : ℝ :=
  helixIntegral a h + closingSegmentIntegral a h

private theorem potentialAlongPath_hasDerivAt
    (x y z dx dy dz : ℝ → ℝ) (t : ℝ)
    (hx : HasDerivAt x (dx t) t)
    (hy : HasDerivAt y (dy t) t)
    (hz : HasDerivAt z (dz t) t) :
    HasDerivAt
      (fun s => scalarPotential (x s, y s, z s))
      ((vectorField (x t, y t, z t)).1 * dx t +
        (vectorField (x t, y t, z t)).2.1 * dy t +
        (vectorField (x t, y t, z t)).2.2 * dz t) t := by
  convert
    (((((hx.pow 3).add (hy.pow 3)).add (hz.pow 3)).div_const 3).sub
      ((hx.mul hy).mul hz)) using 1 <;>
    simp [vectorField] <;> ring

private theorem pathIntegral_vectorField_eq_potential_sub
    (x y z dx dy dz : ℝ → ℝ) (c d : ℝ)
    (hx : ∀ t, HasDerivAt x (dx t) t)
    (hy : ∀ t, HasDerivAt y (dy t) t)
    (hz : ∀ t, HasDerivAt z (dz t) t)
    (hcx : Continuous x) (hcy : Continuous y) (hcz : Continuous z)
    (hcdx : Continuous dx) (hcdy : Continuous dy)
    (hcdz : Continuous dz) :
    pathIntegral vectorField (fun t => (x t, y t, z t)) c d =
      scalarPotential (x d, y d, z d) -
        scalarPotential (x c, y c, z c) := by
  have hdx : ∀ t, deriv x t = dx t := fun t => (hx t).deriv
  have hdy : ∀ t, deriv y t = dy t := fun t => (hy t).deriv
  have hdz : ∀ t, deriv z t = dz t := fun t => (hz t).deriv
  unfold pathIntegral
  change
    (∫ t in c..d,
      (vectorField (x t, y t, z t)).1 * deriv x t +
        (vectorField (x t, y t, z t)).2.1 * deriv y t +
        (vectorField (x t, y t, z t)).2.2 * deriv z t) = _
  simp_rw [hdx, hdy, hdz]
  have hderiv :
      ∀ t ∈ Set.uIcc c d,
        HasDerivAt
          (fun s => scalarPotential (x s, y s, z s))
          ((vectorField (x t, y t, z t)).1 * dx t +
            (vectorField (x t, y t, z t)).2.1 * dy t +
            (vectorField (x t, y t, z t)).2.2 * dz t) t := by
    intro t _
    exact potentialAlongPath_hasDerivAt x y z dx dy dz t
      (hx t) (hy t) (hz t)
  have hc1 : Continuous (fun t =>
      ((x t) ^ 2 - y t * z t) * dx t) :=
    ((hcx.pow 2).sub (hcy.mul hcz)).mul hcdx
  have hc2 : Continuous (fun t =>
      ((y t) ^ 2 - x t * z t) * dy t) :=
    ((hcy.pow 2).sub (hcx.mul hcz)).mul hcdy
  have hc3 : Continuous (fun t =>
      ((z t) ^ 2 - x t * y t) * dz t) :=
    ((hcz.pow 2).sub (hcx.mul hcy)).mul hcdz
  have hc : Continuous (fun t =>
      (vectorField (x t, y t, z t)).1 * dx t +
        (vectorField (x t, y t, z t)).2.1 * dy t +
        (vectorField (x t, y t, z t)).2.2 * dz t) := by
    simpa [vectorField] using (hc1.add hc2).add hc3
  have hint : IntervalIntegrable
      (fun t : ℝ =>
        (vectorField (x t, y t, z t)).1 * dx t +
          (vectorField (x t, y t, z t)).2.1 * dy t +
          (vectorField (x t, y t, z t)).2.2 * dz t)
      MeasureTheory.volume c d := hc.intervalIntegrable c d
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

private theorem deriv_const_sub_const_mul (a b x : ℝ) :
    deriv (fun t : ℝ => a - b * t) x = -b := by
  convert
    ((hasDerivAt_const x a).sub
      ((hasDerivAt_const x b).mul (hasDerivAt_id x))).deriv using 1 <;>
    ring

private theorem curl_vectorField_zero (p : Vec3) :
    curl vectorField p = (0, 0, 0) := by
  simp [curl, vectorField, deriv_const_sub_const_mul]

private theorem curlSurfaceFlux_zero (a h : ℝ) :
    curlSurfaceFlux a h = 0 := by
  simp [curlSurfaceFlux, curl_vectorField_zero, dot]

private theorem helixIntegral_value (a h : ℝ) :
    helixIntegral a h = h ^ 3 / 3 := by
  let k : ℝ := h / (2 * Real.pi)
  have hx : ∀ t : ℝ,
      HasDerivAt (fun s => a * Real.cos s) (-a * Real.sin t) t := by
    intro t
    convert (hasDerivAt_const t a).mul (Real.hasDerivAt_cos t) using 1 <;>
      ring
  have hy : ∀ t : ℝ,
      HasDerivAt (fun s => a * Real.sin s) (a * Real.cos t) t := by
    intro t
    convert (hasDerivAt_const t a).mul (Real.hasDerivAt_sin t) using 1 <;>
      ring
  have hz : ∀ t : ℝ,
      HasDerivAt (fun s => k * s) k t := by
    intro t
    convert (hasDerivAt_const t k).mul (hasDerivAt_id t) using 1 <;>
      ring
  have hline := pathIntegral_vectorField_eq_potential_sub
    (fun t => a * Real.cos t) (fun t => a * Real.sin t)
    (fun t => k * t) (fun t => -a * Real.sin t)
    (fun t => a * Real.cos t) (fun _ : ℝ => k)
    0 (2 * Real.pi) hx hy hz
    (continuous_const.mul Real.continuous_cos)
    (continuous_const.mul Real.continuous_sin)
    (continuous_const.mul continuous_id)
    (continuous_const.mul Real.continuous_sin)
    (continuous_const.mul Real.continuous_cos) continuous_const
  calc
    helixIntegral a h =
        scalarPotential (helixPath a h (2 * Real.pi)) -
          scalarPotential (helixPath a h 0) := by
      simpa [helixIntegral, helixPath, k] using hline
    _ = h ^ 3 / 3 := by
      simp [helixPath, scalarPotential, Real.pi_ne_zero]
      <;> ring

private theorem closingSegmentIntegral_value (a h : ℝ) :
    closingSegmentIntegral a h = -(h ^ 3 / 3) := by
  have hx : ∀ t : ℝ,
      HasDerivAt (fun _ : ℝ => (a : ℝ)) 0 t := by
    intro t
    exact hasDerivAt_const t a
  have hy : ∀ t : ℝ,
      HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := by
    intro t
    exact hasDerivAt_const t (0 : ℝ)
  have hz : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => h * (1 - s)) (-h) t := by
    intro t
    convert (hasDerivAt_const t h).mul
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)) using 1 <;>
      ring
  have hline := pathIntegral_vectorField_eq_potential_sub
    (fun _ : ℝ => (a : ℝ)) (fun _ : ℝ => (0 : ℝ))
    (fun t : ℝ => h * (1 - t))
    (fun _ : ℝ => (0 : ℝ)) (fun _ : ℝ => (0 : ℝ))
    (fun _ : ℝ => -h)
    0 1 hx hy hz
    (continuous_const : Continuous (fun _ : ℝ => (a : ℝ)))
    (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
    (continuous_const.mul (continuous_const.sub continuous_id))
    (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
    (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
    (continuous_const : Continuous (fun _ : ℝ => (-h : ℝ)))
  calc
    closingSegmentIntegral a h =
        scalarPotential (closingPath a h 1) -
          scalarPotential (closingPath a h 0) := by
      simpa [closingSegmentIntegral, closingPath] using hline
    _ = -(h ^ 3 / 3) := by
      simp [closingPath, scalarPotential]
      <;> ring

private theorem axialIntegral_value (h : ℝ) :
    axialIntegral h = h ^ 3 / 3 := by
  have hderiv :
      ∀ z ∈ Set.uIcc (0 : ℝ) h,
        HasDerivAt (fun x : ℝ => x ^ 3 / 3) (z ^ 2) z := by
    intro z _
    convert (((hasDerivAt_id z).pow 3).div_const 3) using 1 <;>
      simp [id] <;> ring
  have hc : Continuous (fun z : ℝ => z ^ 2) := continuous_id.pow 2
  have hint : IntervalIntegrable (fun z : ℝ => z ^ 2)
      MeasureTheory.volume 0 h := hc.intervalIntegrable 0 h
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa [axialIntegral] using heq

theorem gap1 (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    closedLoopIntegral a h = curlSurfaceFlux a h := by
  rw [curlSurfaceFlux_zero]
  simp [closedLoopIntegral, helixIntegral_value,
    closingSegmentIntegral_value]

theorem gap2 (a h : ℝ) :
    curlSurfaceFlux a h = 0 := by
  exact curlSurfaceFlux_zero a h

theorem gap3 (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    closedLoopIntegral a h = 0 := by
  simp [closedLoopIntegral, helixIntegral_value,
    closingSegmentIntegral_value]

theorem gap4 (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    helixIntegral a h = axialIntegral h := by
  rw [helixIntegral_value, axialIntegral_value]

theorem gap5 (h : ℝ) (hh : 0 < h) :
    axialIntegral h = ∫ z in (0 : ℝ)..h, z ^ 2 := by
  rfl

theorem gap6 (h : ℝ) (hh : 0 < h) :
    (∫ z in (0 : ℝ)..h, z ^ 2) = h ^ 3 / 3 := by
  simpa [axialIntegral] using axialIntegral_value h

theorem gap7 (h : ℝ) (hh : 0 < h) :
    axialIntegral h = h ^ 3 / 3 := by
  exact axialIntegral_value h

theorem gap8 (a h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    helixIntegral a h = h ^ 3 / 3 := by
  exact helixIntegral_value a h

end

end ProofGap.Exercise4368
