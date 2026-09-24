import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3578

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def squaredDistance (p center : Point3) : ℝ :=
  (p.x - center.x) ^ 2 + (p.y - center.y) ^ 2 +
    (p.z - center.z) ^ 2

def sphereCondition (rho : ℝ) (p center : Point3) : Prop :=
  squaredDistance p center = rho ^ 2

def centerOnCone (center : Point3) : Prop :=
  center.x ^ 2 + center.y ^ 2 = center.z ^ 2

def lagrangian (p : Point3) (lam : ℝ) (center : Point3) : ℝ :=
  squaredDistance p center +
    lam * (center.x ^ 2 + center.y ^ 2 - center.z ^ 2)

def partialA (p : Point3) (lam : ℝ) (center : Point3) : ℝ :=
  deriv (fun a => lagrangian p lam ⟨a, center.y, center.z⟩) center.x

def partialB (p : Point3) (lam : ℝ) (center : Point3) : ℝ :=
  deriv (fun b => lagrangian p lam ⟨center.x, b, center.z⟩) center.y

def partialC (p : Point3) (lam : ℝ) (center : Point3) : ℝ :=
  deriv (fun c => lagrangian p lam ⟨center.x, center.y, c⟩) center.z

def stationaryCenter (p : Point3) (lam : ℝ) (center : Point3) : Prop :=
  partialA p lam center = 0 ∧ partialB p lam center = 0 ∧
    partialC p lam center = 0

def centerParametrization (p center : Point3) (mu : ℝ) : Prop :=
  center.x = mu * p.x ∧ center.y = mu * p.y ∧
    center.z = mu * p.z / (2 * mu - 1)

def envelope (rho : ℝ) : Set Point3 :=
  {p | ∃ center : Point3, sphereCondition rho p center ∧
    centerOnCone center ∧ ∃ lam : ℝ, stationaryCenter p lam center}

def offsetCone (rho : ℝ) : Set Point3 :=
  {p |
    Real.sqrt 2 * rho =
        abs (Real.sqrt (p.x ^ 2 + p.y ^ 2) - p.z) ∨
      Real.sqrt 2 * rho =
        abs (Real.sqrt (p.x ^ 2 + p.y ^ 2) + p.z)}

theorem gap1 (rho : ℝ) (p center : Point3)
    (hSphere : sphereCondition rho p center) :
    (p.x - center.x) ^ 2 + (p.y - center.y) ^ 2 +
      (p.z - center.z) ^ 2 = rho ^ 2 :=
  hSphere

theorem gap2 (center : Point3)
    (hCone : centerOnCone center) :
    center.x ^ 2 + center.y ^ 2 = center.z ^ 2 :=
  hCone

theorem gap3 (p center : Point3) (lam : ℝ) :
    partialA p lam center =
      -2 * (p.x - center.x) + 2 * lam * center.x := by
  have hbase : HasDerivAt (fun a : ℝ => p.x - a) (-1) center.x := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using
      HasDerivAt.sub (hasDerivAt_const center.x p.x) (hasDerivAt_id center.x)
  have hdist : HasDerivAt
      (fun a : ℝ => (p.x - a) ^ 2 +
        ((p.y - center.y) ^ 2 + (p.z - center.z) ^ 2))
      (2 * (p.x - center.x) * (-1)) center.x := by
    convert (hasDerivAt_add_const_iff
      ((p.y - center.y) ^ 2 + (p.z - center.z) ^ 2)).2
      (HasDerivAt.fun_pow hbase 2) using 1 <;>
      norm_num <;> ring
  have hcon : HasDerivAt
      (fun a : ℝ => a ^ 2 + (center.y ^ 2 - center.z ^ 2))
      (2 * center.x) center.x := by
    convert (hasDerivAt_add_const_iff
      (center.y ^ 2 - center.z ^ 2)).2
      (hasDerivAt_pow 2 center.x) using 1 <;>
      norm_num <;> ring
  have hall := HasDerivAt.add hdist (HasDerivAt.const_mul lam hcon)
  have heq :
      (fun a : ℝ => lagrangian p lam ⟨a, center.y, center.z⟩) =
        (fun a : ℝ =>
          (p.x - a) ^ 2 +
              ((p.y - center.y) ^ 2 + (p.z - center.z) ^ 2) +
            lam * (a ^ 2 + (center.y ^ 2 - center.z ^ 2))) := by
    funext a
    simp [lagrangian, squaredDistance]
    ring
  unfold partialA
  rw [heq]
  convert hall.deriv using 1 <;> ring

theorem gap4 (p center : Point3) (lam : ℝ)
    (hStationary : stationaryCenter p lam center) :
    -2 * (p.x - center.x) + 2 * lam * center.x = 0 := by
  rw [← gap3]
  exact hStationary.1

theorem gap5 (p center : Point3) (lam : ℝ) :
    partialB p lam center =
      -2 * (p.y - center.y) + 2 * lam * center.y := by
  have hbase : HasDerivAt (fun b : ℝ => p.y - b) (-1) center.y := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using
      HasDerivAt.sub (hasDerivAt_const center.y p.y) (hasDerivAt_id center.y)
  have hdist : HasDerivAt
      (fun b : ℝ => (p.y - b) ^ 2 +
        ((p.x - center.x) ^ 2 + (p.z - center.z) ^ 2))
      (2 * (p.y - center.y) * (-1)) center.y := by
    convert (hasDerivAt_add_const_iff
      ((p.x - center.x) ^ 2 + (p.z - center.z) ^ 2)).2
      (HasDerivAt.fun_pow hbase 2) using 1 <;>
      norm_num <;> ring
  have hcon : HasDerivAt
      (fun b : ℝ => b ^ 2 + (center.x ^ 2 - center.z ^ 2))
      (2 * center.y) center.y := by
    convert (hasDerivAt_add_const_iff
      (center.x ^ 2 - center.z ^ 2)).2
      (hasDerivAt_pow 2 center.y) using 1 <;>
      norm_num <;> ring
  have hall := HasDerivAt.add hdist (HasDerivAt.const_mul lam hcon)
  have heq :
      (fun b : ℝ => lagrangian p lam ⟨center.x, b, center.z⟩) =
        (fun b : ℝ =>
          (p.y - b) ^ 2 +
              ((p.x - center.x) ^ 2 + (p.z - center.z) ^ 2) +
            lam * (b ^ 2 + (center.x ^ 2 - center.z ^ 2))) := by
    funext b
    simp [lagrangian, squaredDistance]
    ring
  unfold partialB
  rw [heq]
  convert hall.deriv using 1 <;> ring

theorem gap6 (p center : Point3) (lam : ℝ)
    (hStationary : stationaryCenter p lam center) :
    -2 * (p.y - center.y) + 2 * lam * center.y = 0 := by
  rw [← gap5]
  exact hStationary.2.1

theorem gap7 (p center : Point3) (lam : ℝ) :
    partialC p lam center =
      -2 * (p.z - center.z) - 2 * lam * center.z := by
  have hbase : HasDerivAt (fun c : ℝ => p.z - c) (-1) center.z := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using
      HasDerivAt.sub (hasDerivAt_const center.z p.z) (hasDerivAt_id center.z)
  have hdist : HasDerivAt
      (fun c : ℝ => (p.z - c) ^ 2 +
        ((p.x - center.x) ^ 2 + (p.y - center.y) ^ 2))
      (2 * (p.z - center.z) * (-1)) center.z := by
    convert (hasDerivAt_add_const_iff
      ((p.x - center.x) ^ 2 + (p.y - center.y) ^ 2)).2
      (HasDerivAt.fun_pow hbase 2) using 1 <;>
      norm_num <;> ring
  have hcon : HasDerivAt
      (fun c : ℝ => center.x ^ 2 + center.y ^ 2 - c ^ 2)
      (-2 * center.z) center.z := by
    convert HasDerivAt.sub
      (hasDerivAt_const center.z (center.x ^ 2 + center.y ^ 2))
      (hasDerivAt_pow 2 center.z) using 1 <;>
      norm_num <;> ring
  have hall := HasDerivAt.add hdist (HasDerivAt.const_mul lam hcon)
  have heq :
      (fun c : ℝ => lagrangian p lam ⟨center.x, center.y, c⟩) =
        (fun c : ℝ =>
          (p.z - c) ^ 2 +
              ((p.x - center.x) ^ 2 + (p.y - center.y) ^ 2) +
            lam * (center.x ^ 2 + center.y ^ 2 - c ^ 2)) := by
    funext c
    simp [lagrangian, squaredDistance]
    ring
  unfold partialC
  rw [heq]
  convert hall.deriv using 1 <;> ring

theorem gap8 (p center : Point3) (lam : ℝ)
    (hStationary : stationaryCenter p lam center) :
    -2 * (p.z - center.z) - 2 * lam * center.z = 0 := by
  rw [← gap7]
  exact hStationary.2.2

theorem gap9 (p center : Point3) (lam : ℝ)
    (ha : center.x ≠ 0) (hb : center.y ≠ 0)
    (hStationary : stationaryCenter p lam center) :
    p.x / center.x - 1 = p.y / center.y - 1 := by
  have hx := gap4 p center lam hStationary
  have hy := gap6 p center lam hStationary
  have hpx : p.x = (1 + lam) * center.x := by linarith
  have hpy : p.y = (1 + lam) * center.y := by linarith
  field_simp [ha, hb]
  rw [hpx, hpy]
  ring

theorem gap10 (p center : Point3) (lam : ℝ)
    (hb : center.y ≠ 0) (hc : center.z ≠ 0)
    (hStationary : stationaryCenter p lam center) :
    p.y / center.y - 1 = -p.z / center.z + 1 := by
  have hy := gap6 p center lam hStationary
  have hz := gap8 p center lam hStationary
  have hpy : p.y = (1 + lam) * center.y := by linarith
  have hpz : p.z = (1 - lam) * center.z := by linarith
  field_simp [hb, hc]
  rw [hpy, hpz]
  ring

theorem gap11 (p center : Point3) (lam : ℝ)
    (hc : center.z ≠ 0)
    (hStationary : stationaryCenter p lam center) :
    -p.z / center.z + 1 = lam := by
  have hz := gap8 p center lam hStationary
  field_simp [hc]
  nlinarith

theorem gap12 (p center : Point3) (lam : ℝ)
    (ha : center.x ≠ 0)
    (hStationary : stationaryCenter p lam center) :
    p.x / center.x - 1 = lam := by
  have hx := gap4 p center lam hStationary
  field_simp [ha]
  nlinarith

theorem gap13 (p center : Point3) (lam : ℝ)
    (ha : center.x ≠ 0)
    (hStationary : stationaryCenter p lam center)
    (hRegular : 1 + lam ≠ 0) :
    ∃ mu : ℝ, mu ≠ 0 ∧ 1 / mu = p.x / center.x := by
  refine ⟨(1 + lam)⁻¹, inv_ne_zero hRegular, ?_⟩
  rw [one_div, inv_inv]
  linarith [gap12 p center lam ha hStationary]

theorem gap14 (p center : Point3)
    (hRatio :
      p.x / center.x - 1 = p.y / center.y - 1) :
    p.x / center.x = p.y / center.y := by
  linarith

theorem gap15 (p center : Point3)
    (hRatio :
      p.y / center.y - 1 = -p.z / center.z + 1) :
    p.y / center.y = 2 - p.z / center.z := by
  rw [neg_div] at hRatio
  linarith

theorem gap16 (p center : Point3)
    (hXY : p.x / center.x = p.y / center.y)
    (hYZ : p.y / center.y = 2 - p.z / center.z)
    (hNonzero : p.x / center.x ≠ 0) :
    ∃ mu : ℝ, mu ≠ 0 ∧
      1 / mu = p.x / center.x ∧
      1 / mu = p.y / center.y ∧
      1 / mu = 2 - p.z / center.z := by
  refine ⟨(p.x / center.x)⁻¹, inv_ne_zero hNonzero, ?_⟩
  rw [one_div, inv_inv]
  exact ⟨rfl, hXY, hXY.trans hYZ⟩

theorem gap17 (p center : Point3) (mu : ℝ)
    (ha : center.x ≠ 0) (hmu : mu ≠ 0)
    (hReciprocal : 1 / mu = p.x / center.x) :
    center.x = mu * p.x := by
  field_simp [ha, hmu] at hReciprocal ⊢
  nlinarith

theorem gap18 (p center : Point3) (mu : ℝ)
    (hb : center.y ≠ 0) (hmu : mu ≠ 0)
    (hReciprocal : 1 / mu = p.y / center.y) :
    center.y = mu * p.y := by
  field_simp [hb, hmu] at hReciprocal ⊢
  nlinarith

theorem gap19 (p center : Point3) (mu : ℝ)
    (hc : center.z ≠ 0) (hmu : mu ≠ 0)
    (hDenom : 2 * mu - 1 ≠ 0)
    (hReciprocal : 1 / mu = 2 - p.z / center.z) :
    center.z = mu * p.z / (2 * mu - 1) := by
  field_simp [hc, hmu] at hReciprocal
  apply (eq_div_iff hDenom).2
  nlinarith

theorem gap20 (rho : ℝ) (p center : Point3) (mu : ℝ)
    (hSphere : sphereCondition rho p center)
    (hCenter : centerParametrization p center mu)
    (hMuOne : mu - 1 ≠ 0)
    (hDenom : 2 * mu - 1 ≠ 0) :
    p.x ^ 2 + p.y ^ 2 + p.z ^ 2 / (2 * mu - 1) ^ 2 =
      rho ^ 2 / (mu - 1) ^ 2 := by
  rcases hCenter with ⟨hx, hy, hz⟩
  unfold sphereCondition squaredDistance at hSphere
  rw [hx, hy, hz] at hSphere
  rw [eq_div_iff (pow_ne_zero 2 hMuOne)]
  rw [← hSphere]
  field_simp [hDenom]
  ring

theorem gap21 (p center : Point3) (mu : ℝ)
    (hCone : centerOnCone center)
    (hCenter : centerParametrization p center mu)
    (hmu : mu ≠ 0)
    (hDenom : 2 * mu - 1 ≠ 0) :
    p.x ^ 2 + p.y ^ 2 -
      p.z ^ 2 / (2 * mu - 1) ^ 2 = 0 := by
  rcases hCenter with ⟨hx, hy, hz⟩
  unfold centerOnCone at hCone
  rw [hx, hy, hz] at hCone
  field_simp [hmu, hDenom] at hCone ⊢
  nlinarith

theorem gap22 (rho : ℝ) (p : Point3) (mu : ℝ)
    (hRho : 0 ≤ rho)
    (hMuOne : mu - 1 ≠ 0)
    (hSphereReduced :
      p.x ^ 2 + p.y ^ 2 + p.z ^ 2 / (2 * mu - 1) ^ 2 =
        rho ^ 2 / (mu - 1) ^ 2)
    (hConeReduced :
      p.x ^ 2 + p.y ^ 2 -
        p.z ^ 2 / (2 * mu - 1) ^ 2 = 0) :
    2 * (p.x ^ 2 + p.y ^ 2) = rho ^ 2 / (mu - 1) ^ 2 ∧
      Real.sqrt 2 * rho =
        Real.sqrt (p.x ^ 2 + p.y ^ 2) * abs (2 * mu - 2) := by
  have hsum :
      2 * (p.x ^ 2 + p.y ^ 2) = rho ^ 2 / (mu - 1) ^ 2 := by
    linarith
  refine ⟨hsum, ?_⟩
  have hrad : 0 ≤ p.x ^ 2 + p.y ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtRad :
      (Real.sqrt (p.x ^ 2 + p.y ^ 2)) ^ 2 =
        p.x ^ 2 + p.y ^ 2 := Real.sq_sqrt hrad
  have hscaled :
      2 * rho ^ 2 =
        (p.x ^ 2 + p.y ^ 2) * (2 * mu - 2) ^ 2 := by
    field_simp [hMuOne] at hsum
    nlinarith
  have hsq :
      (Real.sqrt 2 * rho) ^ 2 =
        (Real.sqrt (p.x ^ 2 + p.y ^ 2) * abs (2 * mu - 2)) ^ 2 := by
    rw [mul_pow, mul_pow, hsqrt2, hsqrtRad, sq_abs]
    exact hscaled
  have hleft : 0 ≤ Real.sqrt 2 * rho :=
    mul_nonneg (Real.sqrt_nonneg _) hRho
  have hright :
      0 ≤ Real.sqrt (p.x ^ 2 + p.y ^ 2) * abs (2 * mu - 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  nlinarith

theorem gap23 (p : Point3) (mu : ℝ)
    (hRadial : 0 < p.x ^ 2 + p.y ^ 2)
    (hConeReduced :
      p.x ^ 2 + p.y ^ 2 -
        p.z ^ 2 / (2 * mu - 1) ^ 2 = 0) :
    2 * mu - 1 =
        p.z / Real.sqrt (p.x ^ 2 + p.y ^ 2) ∨
      2 * mu - 1 =
        -(p.z / Real.sqrt (p.x ^ 2 + p.y ^ 2)) := by
  have hdenom : 2 * mu - 1 ≠ 0 := by
    intro hzero
    rw [hzero] at hConeReduced
    norm_num at hConeReduced
    linarith
  have hsqrt :
      (Real.sqrt (p.x ^ 2 + p.y ^ 2)) ^ 2 =
        p.x ^ 2 + p.y ^ 2 :=
    Real.sq_sqrt (le_of_lt hRadial)
  have hsqrtNe : Real.sqrt (p.x ^ 2 + p.y ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hRadial)
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [div_pow]
  apply (eq_div_iff (pow_ne_zero 2 hsqrtNe)).2
  rw [hsqrt]
  field_simp [hdenom] at hConeReduced
  nlinarith

theorem gap24 (rho : ℝ) (p : Point3) (mu : ℝ)
    (hScale :
      Real.sqrt 2 * rho =
        Real.sqrt (p.x ^ 2 + p.y ^ 2) * abs (2 * mu - 2))
    (hBranch :
      2 * mu - 1 =
          p.z / Real.sqrt (p.x ^ 2 + p.y ^ 2) ∨
        2 * mu - 1 =
          -(p.z / Real.sqrt (p.x ^ 2 + p.y ^ 2)))
    (hRadial : 0 < p.x ^ 2 + p.y ^ 2) :
    Real.sqrt 2 * rho =
        abs (Real.sqrt (p.x ^ 2 + p.y ^ 2) - p.z) ∨
      Real.sqrt 2 * rho =
        abs (Real.sqrt (p.x ^ 2 + p.y ^ 2) + p.z) := by
  have hspos : 0 < Real.sqrt (p.x ^ 2 + p.y ^ 2) :=
    Real.sqrt_pos.2 hRadial
  have hsne : Real.sqrt (p.x ^ 2 + p.y ^ 2) ≠ 0 := ne_of_gt hspos
  rcases hBranch with hBranch | hBranch
  · left
    have harg :
        2 * mu - 2 =
          (p.z - Real.sqrt (p.x ^ 2 + p.y ^ 2)) /
            Real.sqrt (p.x ^ 2 + p.y ^ 2) := by
      apply (eq_div_iff hsne).2
      apply (eq_div_iff hsne).mp at hBranch
      nlinarith
    calc
      Real.sqrt 2 * rho =
          Real.sqrt (p.x ^ 2 + p.y ^ 2) * abs (2 * mu - 2) := hScale
      _ = Real.sqrt (p.x ^ 2 + p.y ^ 2) *
          abs ((p.z - Real.sqrt (p.x ^ 2 + p.y ^ 2)) /
            Real.sqrt (p.x ^ 2 + p.y ^ 2)) := by rw [harg]
      _ = abs (Real.sqrt (p.x ^ 2 + p.y ^ 2) - p.z) := by
        rw [abs_div, abs_of_pos hspos, abs_sub_comm]
        field_simp
  · right
    have harg :
        2 * mu - 2 =
          -(p.z + Real.sqrt (p.x ^ 2 + p.y ^ 2)) /
            Real.sqrt (p.x ^ 2 + p.y ^ 2) := by
      field_simp [hsne] at hBranch ⊢
      nlinarith
    calc
      Real.sqrt 2 * rho =
          Real.sqrt (p.x ^ 2 + p.y ^ 2) * abs (2 * mu - 2) := hScale
      _ = Real.sqrt (p.x ^ 2 + p.y ^ 2) *
          abs (-(p.z + Real.sqrt (p.x ^ 2 + p.y ^ 2)) /
            Real.sqrt (p.x ^ 2 + p.y ^ 2)) := by rw [harg]
      _ = abs (Real.sqrt (p.x ^ 2 + p.y ^ 2) + p.z) := by
        rw [abs_div, abs_neg, abs_of_pos hspos]
        field_simp
        congr 1
        ring

-- Statement correction: the algebraic offset set also contains a cone-apex
-- branch that is not produced by a regular Lagrange stationary center, so
-- the preceding derivation establishes the forward inclusion, not equality.
theorem gap25 (rho : ℝ) (hRho : 0 < rho) :
    envelope rho ⊆ offsetCone rho := by
  intro p hp
  rcases hp with ⟨center, hSphere, hCone, lam, hStationary⟩
  have hx := gap4 p center lam hStationary
  have hy := gap6 p center lam hStationary
  have hz := gap8 p center lam hStationary
  have hpx : p.x = (1 + lam) * center.x := by
    linarith
  have hpy : p.y = (1 + lam) * center.y := by
    linarith
  have hpz : p.z = (1 - lam) * center.z := by
    linarith
  have hCone' : center.x ^ 2 + center.y ^ 2 = center.z ^ 2 :=
    hCone
  have hSphere' :
      lam ^ 2 *
          (center.x ^ 2 + center.y ^ 2 + center.z ^ 2) =
        rho ^ 2 := by
    calc
      lam ^ 2 *
          (center.x ^ 2 + center.y ^ 2 + center.z ^ 2) =
          (p.x - center.x) ^ 2 + (p.y - center.y) ^ 2 +
            (p.z - center.z) ^ 2 := by
              rw [hpx, hpy, hpz]
              ring
      _ = rho ^ 2 := hSphere
  have hSphere'' :
      2 * (lam * center.z) ^ 2 = rho ^ 2 := by
    calc
      2 * (lam * center.z) ^ 2 =
          lam ^ 2 *
            (center.x ^ 2 + center.y ^ 2 + center.z ^ 2) := by
              rw [hCone']
              ring
      _ = rho ^ 2 := hSphere'
  have hscale :
      Real.sqrt 2 * rho = 2 * |lam * center.z| := by
    have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 :=
      Real.sq_sqrt (by norm_num)
    have hsq :
        (Real.sqrt 2 * rho) ^ 2 =
          (2 * |lam * center.z|) ^ 2 := by
      calc
        (Real.sqrt 2 * rho) ^ 2 = 2 * rho ^ 2 := by
          rw [mul_pow, hsqrt2]
        _ = 4 * (lam * center.z) ^ 2 := by
          nlinarith
        _ = (2 * |lam * center.z|) ^ 2 := by
          rw [show (2 * |lam * center.z|) ^ 2 =
            4 * |lam * center.z| ^ 2 by ring, sq_abs]
    have hleft : 0 ≤ Real.sqrt 2 * rho :=
      mul_nonneg (Real.sqrt_nonneg _) hRho.le
    have hright : 0 ≤ 2 * |lam * center.z| :=
      mul_nonneg (by norm_num) (abs_nonneg _)
    nlinarith
  have hradial :
      Real.sqrt (p.x ^ 2 + p.y ^ 2) =
        |(1 + lam) * center.z| := by
    rw [hpx, hpy]
    have heq :
        ((1 + lam) * center.x) ^ 2 +
            ((1 + lam) * center.y) ^ 2 =
          ((1 + lam) * center.z) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow]
      nlinarith
    rw [heq, Real.sqrt_sq_eq_abs]
  unfold offsetCone
  change
    Real.sqrt 2 * rho =
        abs (Real.sqrt (p.x ^ 2 + p.y ^ 2) - p.z) ∨
      Real.sqrt 2 * rho =
        abs (Real.sqrt (p.x ^ 2 + p.y ^ 2) + p.z)
  rw [hradial, hpz]
  by_cases hsign : 0 ≤ (1 + lam) * center.z
  · left
    rw [abs_of_nonneg hsign]
    calc
      Real.sqrt 2 * rho = 2 * |lam * center.z| := hscale
      _ = |2 * (lam * center.z)| := by
        rw [abs_mul]
        norm_num
      _ = |(1 + lam) * center.z - (1 - lam) * center.z| := by
        congr 1
        ring
  · right
    rw [abs_of_nonpos (le_of_not_ge hsign)]
    calc
      Real.sqrt 2 * rho = 2 * |lam * center.z| := hscale
      _ = |-2 * (lam * center.z)| := by
        simp [abs_mul]
      _ = |-((1 + lam) * center.z) + (1 - lam) * center.z| := by
        congr 1
        ring

end

end ProofGap.Exercise3578
