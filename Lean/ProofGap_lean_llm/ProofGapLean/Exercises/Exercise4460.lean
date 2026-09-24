import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4460

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (p q : Vec3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def scale (a : ℝ) (p : Vec3) : Vec3 :=
  (a * p.1, a * p.2.1, a * p.2.2)

def radius (p : Vec3) : ℝ :=
  Real.sqrt (dot p p)

def radialField (f : ℝ → ℝ) (p : Vec3) : Vec3 :=
  scale (f (radius p)) p

def partialX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => u (x, p.2.1, p.2.2)) p.1

def partialY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => u (p.1, y, p.2.2)) p.2.1

def partialZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => u (p.1, p.2.1, z)) p.2.2

def gradient (u : Vec3 → ℝ) (p : Vec3) : Vec3 :=
  (partialX u p, partialY u p, partialZ u p)

def CoordinateConservative (F : Vec3 → Vec3) : Prop :=
  ∃ Φ : Vec3 → ℝ, ∀ p : Vec3, gradient Φ p = F p

def fieldOneForm (f : ℝ → ℝ) (p v : Vec3) : ℝ :=
  dot (radialField f p) v

def coordinateOneForm (f : ℝ → ℝ) (p v : Vec3) : ℝ :=
  f (radius p) *
    (p.1 * v.1 + p.2.1 * v.2.1 + p.2.2 * v.2.2)

def squaredRadiusDifferential (p v : Vec3) : ℝ :=
  2 * dot p v

def radialRate (p v : Vec3) : ℝ :=
  dot p v / radius p

def radialOneForm (f : ℝ → ℝ) (p v : Vec3) : ℝ :=
  radius p * f (radius p) * radialRate p v

def radialPrimitive (f : ℝ → ℝ) (r₀ r : ℝ) : ℝ :=
  ∫ t in r₀..r, t * f t

def radialPotential (f : ℝ → ℝ) (r₀ : ℝ) (p : Vec3) : ℝ :=
  radialPrimitive f r₀ (radius p)

def radialPotentialGradient (f : ℝ → ℝ) (r₀ : ℝ) (p : Vec3) : Vec3 :=
  gradient (radialPotential f r₀) p

def potentialDifferential (f : ℝ → ℝ) (r₀ : ℝ) (p v : Vec3) : ℝ :=
  dot (radialPotentialGradient f r₀ p) v

private theorem radialPrimitive_hasDerivAt
    (f : ℝ → ℝ) (hf : Continuous f) (r₀ r : ℝ) :
    HasDerivAt (radialPrimitive f r₀) (r * f r) r := by
  have hcont : Continuous (fun t : ℝ => t * f t) := continuous_id.mul hf
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable r₀ r)
    hcont.stronglyMeasurable.stronglyMeasurableAtFilter
    hcont.continuousAt

private theorem hasDerivAt_comp_abs_zero
    {g : ℝ → ℝ} (hg : HasDerivAt g 0 0) :
    HasDerivAt (fun x : ℝ => g |x|) 0 0 := by
  have hright :
      HasDerivWithinAt (fun x : ℝ => g |x|) 0 (Set.Ici 0) 0 := by
    refine hg.hasDerivWithinAt.congr ?_ ?_
    · intro x hx
      have hx' : 0 ≤ x := hx
      simp only [abs_of_nonneg hx']
    · simp
  have hinner : HasDerivAt (fun x : ℝ => -x) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).neg
  have hg' : HasDerivAt g 0 ((fun x : ℝ => -x) 0) := by
    simpa using hg
  have hneg : HasDerivAt (fun x : ℝ => g (-x)) 0 0 := by
    simpa only [Function.comp_apply, zero_mul] using hg'.comp 0 hinner
  have hleft :
      HasDerivWithinAt (fun x : ℝ => g |x|) 0 (Set.Iic 0) 0 := by
    refine hneg.hasDerivWithinAt.congr ?_ ?_
    · intro x hx
      have hx' : x ≤ 0 := hx
      simp only [abs_of_nonpos hx']
    · simp
  have hu := hleft.union hright
  have hsets : Set.Iic (0 : ℝ) ∪ Set.Ici 0 = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_univ, iff_true]
    exact le_total x 0
  rw [hsets] at hu
  simpa only [hasDerivWithinAt_univ] using hu

private theorem radius_pos_of_ne_zero (p : Vec3)
    (hp : p ≠ (0, 0, 0)) : 0 < radius p := by
  unfold radius
  apply Real.sqrt_pos.2
  rcases p with ⟨x, y, z⟩
  change 0 < x * x + y * y + z * z
  by_contra h
  have hle : x * x + y * y + z * z ≤ 0 := le_of_not_gt h
  have hx : x = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy : y = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hz : z = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  apply hp
  simp [hx, hy, hz]

private theorem hasDerivAt_sqrt_sq_add
    (x c : ℝ) (hc : 0 ≤ c)
    (hroot : Real.sqrt (x * x + c) ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.sqrt (y * y + c))
      (x / Real.sqrt (x * x + c)) x := by
  have harg : x * x + c ≠ 0 := by
    intro hzero
    apply hroot
    rw [hzero]
    simp
  have hinner : HasDerivAt (fun y : ℝ => y * y + c) (2 * x) x := by
    simpa [pow_two, add_comm] using
      ((hasDerivAt_id x).pow 2).add_const c
  convert (Real.hasDerivAt_sqrt harg).comp x hinner using 1
  field_simp [hroot]

private theorem hasDerivAt_radiusX (p : Vec3)
    (hr : radius p ≠ 0) :
    HasDerivAt (fun x : ℝ => radius (x, p.2.1, p.2.2))
      (p.1 / radius p) p.1 := by
  have hroot :
      Real.sqrt (p.1 * p.1 + (p.2.1 * p.2.1 + p.2.2 * p.2.2)) ≠ 0 := by
    simpa [radius, dot, add_assoc] using hr
  have hc : 0 ≤ p.2.1 * p.2.1 + p.2.2 * p.2.2 := by
    nlinarith [sq_nonneg p.2.1, sq_nonneg p.2.2]
  simpa [radius, dot, add_assoc] using
    hasDerivAt_sqrt_sq_add p.1
      (p.2.1 * p.2.1 + p.2.2 * p.2.2) hc hroot

private theorem hasDerivAt_radiusY (p : Vec3)
    (hr : radius p ≠ 0) :
    HasDerivAt (fun y : ℝ => radius (p.1, y, p.2.2))
      (p.2.1 / radius p) p.2.1 := by
  have hroot :
      Real.sqrt (p.2.1 * p.2.1 + (p.1 * p.1 + p.2.2 * p.2.2)) ≠ 0 := by
    simpa [radius, dot, add_comm, add_left_comm, add_assoc] using hr
  have hc : 0 ≤ p.1 * p.1 + p.2.2 * p.2.2 := by
    nlinarith [sq_nonneg p.1, sq_nonneg p.2.2]
  simpa [radius, dot, add_comm, add_left_comm, add_assoc] using
    hasDerivAt_sqrt_sq_add p.2.1
      (p.1 * p.1 + p.2.2 * p.2.2) hc hroot

private theorem hasDerivAt_radiusZ (p : Vec3)
    (hr : radius p ≠ 0) :
    HasDerivAt (fun z : ℝ => radius (p.1, p.2.1, z))
      (p.2.2 / radius p) p.2.2 := by
  have hroot :
      Real.sqrt (p.2.2 * p.2.2 + (p.1 * p.1 + p.2.1 * p.2.1)) ≠ 0 := by
    simpa [radius, dot, add_comm, add_left_comm, add_assoc] using hr
  have hc : 0 ≤ p.1 * p.1 + p.2.1 * p.2.1 := by
    nlinarith [sq_nonneg p.1, sq_nonneg p.2.1]
  simpa [radius, dot, add_comm, add_left_comm, add_assoc] using
    hasDerivAt_sqrt_sq_add p.2.2
      (p.1 * p.1 + p.2.1 * p.2.1) hc hroot

private theorem hasDerivAt_potentialX
    (f : ℝ → ℝ) (hf : Continuous f) (r₀ : ℝ) (p : Vec3)
    (hr : radius p ≠ 0) :
    HasDerivAt (fun x : ℝ => radialPotential f r₀ (x, p.2.1, p.2.2))
      (f (radius p) * p.1) p.1 := by
  unfold radialPotential
  have hcomp :=
    (radialPrimitive_hasDerivAt f hf r₀ (radius p)).comp p.1
      (hasDerivAt_radiusX p hr)
  convert hcomp using 1
  field_simp [hr]

private theorem hasDerivAt_potentialY
    (f : ℝ → ℝ) (hf : Continuous f) (r₀ : ℝ) (p : Vec3)
    (hr : radius p ≠ 0) :
    HasDerivAt (fun y : ℝ => radialPotential f r₀ (p.1, y, p.2.2))
      (f (radius p) * p.2.1) p.2.1 := by
  unfold radialPotential
  have hcomp :=
    (radialPrimitive_hasDerivAt f hf r₀ (radius p)).comp p.2.1
      (hasDerivAt_radiusY p hr)
  convert hcomp using 1
  field_simp [hr]

private theorem hasDerivAt_potentialZ
    (f : ℝ → ℝ) (hf : Continuous f) (r₀ : ℝ) (p : Vec3)
    (hr : radius p ≠ 0) :
    HasDerivAt (fun z : ℝ => radialPotential f r₀ (p.1, p.2.1, z))
      (f (radius p) * p.2.2) p.2.2 := by
  unfold radialPotential
  have hcomp :=
    (radialPrimitive_hasDerivAt f hf r₀ (radius p)).comp p.2.2
      (hasDerivAt_radiusZ p hr)
  convert hcomp using 1
  field_simp [hr]

private theorem radialPotentialGradient_eq
    (f : ℝ → ℝ) (hf : Continuous f) (r₀ : ℝ) (p : Vec3) :
    radialPotentialGradient f r₀ p = radialField f p := by
  by_cases hp : p = (0, 0, 0)
  · subst p
    have hzero : HasDerivAt (radialPrimitive f r₀) 0 0 := by
      simpa using radialPrimitive_hasDerivAt f hf r₀ 0
    have habs : HasDerivAt (fun x : ℝ => radialPrimitive f r₀ |x|) 0 0 :=
      hasDerivAt_comp_abs_zero hzero
    have hsqrt (x : ℝ) : Real.sqrt (x * x) = |x| := by
      rw [← pow_two, Real.sqrt_sq_eq_abs]
    have hx :
        HasDerivAt (fun x : ℝ => radialPotential f r₀ (x, 0, 0)) 0 0 := by
      simpa [radialPotential, radius, dot, hsqrt] using habs
    have hy :
        HasDerivAt (fun y : ℝ => radialPotential f r₀ (0, y, 0)) 0 0 := by
      simpa [radialPotential, radius, dot, hsqrt] using habs
    have hz :
        HasDerivAt (fun z : ℝ => radialPotential f r₀ (0, 0, z)) 0 0 := by
      simpa [radialPotential, radius, dot, hsqrt] using habs
    unfold radialPotentialGradient gradient partialX partialY partialZ
      radialField scale
    rw [hx.deriv, hy.deriv, hz.deriv]
    simp
  · have hr : radius p ≠ 0 := ne_of_gt (radius_pos_of_ne_zero p hp)
    have hx := hasDerivAt_potentialX f hf r₀ p hr
    have hy := hasDerivAt_potentialY f hf r₀ p hr
    have hz := hasDerivAt_potentialZ f hf r₀ p hr
    unfold radialPotentialGradient gradient partialX partialY partialZ
      radialField scale
    rw [hx.deriv, hy.deriv, hz.deriv]

theorem gap1 (f : ℝ → ℝ) (hf : Continuous f) :
    CoordinateConservative (radialField f) := by
  refine ⟨radialPotential f 0, ?_⟩
  intro p
  simpa [radialPotentialGradient] using
    radialPotentialGradient_eq f hf 0 p

theorem gap2 (f : ℝ → ℝ) (hf : Continuous f)
    (r₀ : ℝ) (p v : Vec3) :
    potentialDifferential f r₀ p v = fieldOneForm f p v := by
  unfold potentialDifferential fieldOneForm
  rw [radialPotentialGradient_eq f hf r₀ p]

theorem gap3 (f : ℝ → ℝ) (p v : Vec3) :
    fieldOneForm f p v = coordinateOneForm f p v := by
  unfold fieldOneForm radialField scale dot coordinateOneForm
  ring

theorem gap4 (f : ℝ → ℝ) (hf : Continuous f)
    (r₀ : ℝ) (p v : Vec3) :
    potentialDifferential f r₀ p v = coordinateOneForm f p v := by
  calc
    potentialDifferential f r₀ p v = fieldOneForm f p v := gap2 f hf r₀ p v
    _ = coordinateOneForm f p v := gap3 f p v

theorem gap5 (f : ℝ → ℝ) (p v : Vec3) :
    coordinateOneForm f p v =
      (1 / 2 : ℝ) * f (radius p) * squaredRadiusDifferential p v := by
  unfold coordinateOneForm squaredRadiusDifferential dot
  ring

theorem gap6 (f : ℝ → ℝ) (p v : Vec3)
    (hp : p ≠ (0, 0, 0)) :
    (1 / 2 : ℝ) * f (radius p) * squaredRadiusDifferential p v =
      radialOneForm f p v := by
  have hr : radius p ≠ 0 := ne_of_gt (radius_pos_of_ne_zero p hp)
  unfold squaredRadiusDifferential radialOneForm radialRate dot
  field_simp [hr]

theorem gap7 (f : ℝ → ℝ) (hf : Continuous f)
    (r₀ : ℝ) (p v : Vec3)
    (hp : p ≠ (0, 0, 0)) :
    potentialDifferential f r₀ p v = radialOneForm f p v := by
  calc
    potentialDifferential f r₀ p v = coordinateOneForm f p v :=
      gap4 f hf r₀ p v
    _ = (1 / 2 : ℝ) * f (radius p) * squaredRadiusDifferential p v :=
      gap5 f p v
    _ = radialOneForm f p v := gap6 f p v hp

theorem gap8 (f : ℝ → ℝ) (hf : Continuous f) (r₀ r : ℝ) :
    HasDerivAt (radialPrimitive f r₀) (r * f r) r := by
  exact radialPrimitive_hasDerivAt f hf r₀ r

theorem gap9 (f : ℝ → ℝ) (hf : Continuous f) (r₀ : ℝ) (p : Vec3) :
    radialPotentialGradient f r₀ p = radialField f p := by
  exact radialPotentialGradient_eq f hf r₀ p

end

end ProofGap.Exercise4460
