import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3577

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def ellipsoidValue (p : Point3) (a b c : ℝ) : ℝ :=
  p.x ^ 2 / a ^ 2 + p.y ^ 2 / b ^ 2 + p.z ^ 2 / c ^ 2

def onEllipsoid (p : Point3) (a b c : ℝ) : Prop :=
  ellipsoidValue p a b c = 1

def volumeConstraint (V a b c : ℝ) : Prop :=
  a * b * c = 3 * V / (4 * Real.pi)

def lagrangian (p : Point3) (V lam a b c : ℝ) : ℝ :=
  ellipsoidValue p a b c +
    lam * (a * b * c - 3 * V / (4 * Real.pi))

def partialA (p : Point3) (V lam a b c : ℝ) : ℝ :=
  deriv (fun t => lagrangian p V lam t b c) a

def partialB (p : Point3) (V lam a b c : ℝ) : ℝ :=
  deriv (fun t => lagrangian p V lam a t c) b

def partialC (p : Point3) (V lam a b c : ℝ) : ℝ :=
  deriv (fun t => lagrangian p V lam a b t) c

def stationaryAxes (p : Point3) (V lam a b c : ℝ) : Prop :=
  partialA p V lam a b c = 0 ∧
    partialB p V lam a b c = 0 ∧
    partialC p V lam a b c = 0

def normalizedCommon (p : Point3) (a b c mu : ℝ) : Prop :=
  p.x ^ 2 / a ^ 2 = mu ∧
    p.y ^ 2 / b ^ 2 = mu ∧
    p.z ^ 2 / c ^ 2 = mu

def envelope (V : ℝ) : Set Point3 :=
  {p | ∃ a b c : ℝ,
    0 < a ∧ 0 < b ∧ 0 < c ∧
      volumeConstraint V a b c ∧ onEllipsoid p a b c ∧
      ∃ lam : ℝ, stationaryAxes p V lam a b c}

def productSurface (V : ℝ) : Set Point3 :=
  {p | abs (p.x * p.y * p.z) =
    V / (4 * Real.pi * Real.sqrt 3)}

theorem gap1 (p : Point3) (a b c : ℝ)
    (hBoundary : onEllipsoid p a b c) :
    p.x ^ 2 / a ^ 2 + p.y ^ 2 / b ^ 2 +
      p.z ^ 2 / c ^ 2 = 1 := by
  exact hBoundary

theorem gap2 (V a b c : ℝ)
    (hVolume : volumeConstraint V a b c) :
    a * b * c = 3 * V / (4 * Real.pi) := by
  exact hVolume

theorem gap3 (p : Point3) (V lam a b c : ℝ)
    (ha : a ≠ 0) :
    partialA p V lam a b c =
      -(2 * p.x ^ 2 / a ^ 3) + lam * b * c := by
  unfold partialA
  apply HasDerivAt.deriv
  unfold lagrangian ellipsoidValue
  have hsq : HasDerivAt (fun t : ℝ => t * t) (a + a) a := by
    simpa using (hasDerivAt_id a).mul (hasDerivAt_id a)
  have hraw : HasDerivAt (fun t : ℝ => p.x ^ 2 / (t * t))
      ((0 * (a * a) - p.x ^ 2 * (a + a)) / (a * a) ^ 2) a := by
    simpa using
      ((hasDerivAt_const a (p.x ^ 2)).div hsq (mul_ne_zero ha ha))
  have hder :
      (0 * (a * a) - p.x ^ 2 * (a + a)) / (a * a) ^ 2 =
        -(2 * p.x ^ 2 / a ^ 3) := by
    field_simp [ha]
    ring
  rw [hder] at hraw
  have hq : HasDerivAt (fun t : ℝ => p.x ^ 2 / t ^ 2)
      (-(2 * p.x ^ 2 / a ^ 3)) a := by
    simpa only [pow_two] using hraw
  have hcon : HasDerivAt
      (fun t : ℝ => lam * (t * b * c - 3 * V / (4 * Real.pi)))
      (lam * b * c) a := by
    convert
      (((((hasDerivAt_id a).mul_const b).mul_const c).sub_const
        (3 * V / (4 * Real.pi))).const_mul lam) using 1 <;> ring
  convert
    (((hq.add (hasDerivAt_const a (p.y ^ 2 / b ^ 2))).add
      (hasDerivAt_const a (p.z ^ 2 / c ^ 2))).add hcon) using 1 <;> ring

theorem gap4 (p : Point3) (V lam a b c : ℝ)
    (ha : a ≠ 0)
    (hStationary : stationaryAxes p V lam a b c) :
    -(2 * p.x ^ 2 / a ^ 3) + lam * b * c = 0 := by
  have h := hStationary.1
  rw [gap3 p V lam a b c ha] at h
  exact h

theorem gap5 (p : Point3) (V lam a b c : ℝ)
    (hb : b ≠ 0) :
    partialB p V lam a b c =
      -(2 * p.y ^ 2 / b ^ 3) + lam * a * c := by
  unfold partialB
  apply HasDerivAt.deriv
  unfold lagrangian ellipsoidValue
  have hsq : HasDerivAt (fun t : ℝ => t * t) (b + b) b := by
    simpa using (hasDerivAt_id b).mul (hasDerivAt_id b)
  have hraw : HasDerivAt (fun t : ℝ => p.y ^ 2 / (t * t))
      ((0 * (b * b) - p.y ^ 2 * (b + b)) / (b * b) ^ 2) b := by
    simpa using
      ((hasDerivAt_const b (p.y ^ 2)).div hsq (mul_ne_zero hb hb))
  have hder :
      (0 * (b * b) - p.y ^ 2 * (b + b)) / (b * b) ^ 2 =
        -(2 * p.y ^ 2 / b ^ 3) := by
    field_simp [hb]
    ring
  rw [hder] at hraw
  have hq : HasDerivAt (fun t : ℝ => p.y ^ 2 / t ^ 2)
      (-(2 * p.y ^ 2 / b ^ 3)) b := by
    simpa only [pow_two] using hraw
  have hcon : HasDerivAt
      (fun t : ℝ => lam * (a * t * c - 3 * V / (4 * Real.pi)))
      (lam * a * c) b := by
    convert
      (((((hasDerivAt_id b).const_mul a).mul_const c).sub_const
        (3 * V / (4 * Real.pi))).const_mul lam) using 1 <;> ring
  convert
    ((((hasDerivAt_const b (p.x ^ 2 / a ^ 2)).add hq).add
      (hasDerivAt_const b (p.z ^ 2 / c ^ 2))).add hcon) using 1 <;> ring

theorem gap6 (p : Point3) (V lam a b c : ℝ)
    (hb : b ≠ 0)
    (hStationary : stationaryAxes p V lam a b c) :
    -(2 * p.y ^ 2 / b ^ 3) + lam * a * c = 0 := by
  have h := hStationary.2.1
  rw [gap5 p V lam a b c hb] at h
  exact h

theorem gap7 (p : Point3) (V lam a b c : ℝ)
    (hc : c ≠ 0) :
    partialC p V lam a b c =
      -(2 * p.z ^ 2 / c ^ 3) + lam * a * b := by
  unfold partialC
  apply HasDerivAt.deriv
  unfold lagrangian ellipsoidValue
  have hsq : HasDerivAt (fun t : ℝ => t * t) (c + c) c := by
    simpa using (hasDerivAt_id c).mul (hasDerivAt_id c)
  have hraw : HasDerivAt (fun t : ℝ => p.z ^ 2 / (t * t))
      ((0 * (c * c) - p.z ^ 2 * (c + c)) / (c * c) ^ 2) c := by
    simpa using
      ((hasDerivAt_const c (p.z ^ 2)).div hsq (mul_ne_zero hc hc))
  have hder :
      (0 * (c * c) - p.z ^ 2 * (c + c)) / (c * c) ^ 2 =
        -(2 * p.z ^ 2 / c ^ 3) := by
    field_simp [hc]
    ring
  rw [hder] at hraw
  have hq : HasDerivAt (fun t : ℝ => p.z ^ 2 / t ^ 2)
      (-(2 * p.z ^ 2 / c ^ 3)) c := by
    simpa only [pow_two] using hraw
  have hcon : HasDerivAt
      (fun t : ℝ => lam * (a * b * t - 3 * V / (4 * Real.pi)))
      (lam * a * b) c := by
    convert
      ((((hasDerivAt_id c).const_mul (a * b)).sub_const
        (3 * V / (4 * Real.pi))).const_mul lam) using 1 <;> ring
  convert
    ((((hasDerivAt_const c (p.x ^ 2 / a ^ 2)).add
      (hasDerivAt_const c (p.y ^ 2 / b ^ 2))).add hq).add hcon) using 1 <;> ring

theorem gap8 (p : Point3) (V lam a b c : ℝ)
    (hc : c ≠ 0)
    (hStationary : stationaryAxes p V lam a b c) :
    -(2 * p.z ^ 2 / c ^ 3) + lam * a * b = 0 := by
  have h := hStationary.2.2
  rw [gap7 p V lam a b c hc] at h
  exact h

theorem gap9 (p : Point3) (V lam a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hStationary : stationaryAxes p V lam a b c) :
    p.x ^ 2 / a ^ 2 = p.y ^ 2 / b ^ 2 := by
  have hx := gap4 p V lam a b c (ne_of_gt ha) hStationary
  have hy := gap6 p V lam a b c (ne_of_gt hb) hStationary
  have hx' : p.x ^ 2 / a ^ 2 = lam * a * b * c / 2 := by
    field_simp [ne_of_gt ha] at hx ⊢
    ring_nf at hx ⊢
    linarith
  have hy' : p.y ^ 2 / b ^ 2 = lam * a * b * c / 2 := by
    field_simp [ne_of_gt hb] at hy ⊢
    ring_nf at hy ⊢
    linarith
  exact hx'.trans hy'.symm

theorem gap10 (p : Point3) (V lam a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hStationary : stationaryAxes p V lam a b c) :
    p.y ^ 2 / b ^ 2 = p.z ^ 2 / c ^ 2 := by
  have hy := gap6 p V lam a b c (ne_of_gt hb) hStationary
  have hz := gap8 p V lam a b c (ne_of_gt hc) hStationary
  have hy' : p.y ^ 2 / b ^ 2 = lam * a * b * c / 2 := by
    field_simp [ne_of_gt hb] at hy ⊢
    ring_nf at hy ⊢
    linarith
  have hz' : p.z ^ 2 / c ^ 2 = lam * a * b * c / 2 := by
    field_simp [ne_of_gt hc] at hz ⊢
    ring_nf at hz ⊢
    linarith
  exact hy'.trans hz'.symm

theorem gap11 (p : Point3) (V lam a b c : ℝ)
    (hc : 0 < c)
    (hStationary : stationaryAxes p V lam a b c) :
    p.z ^ 2 / c ^ 2 = lam * a * b * c / 2 := by
  have hz := gap8 p V lam a b c (ne_of_gt hc) hStationary
  field_simp [ne_of_gt hc] at hz ⊢
  ring_nf at hz ⊢
  linarith

theorem gap12 (p : Point3) (lam a b c : ℝ)
    (hValue : p.z ^ 2 / c ^ 2 = lam * a * b * c / 2) :
    ∃ mu : ℝ, mu = lam * a * b * c / 2 ∧
      p.z ^ 2 / c ^ 2 = mu := by
  exact ⟨lam * a * b * c / 2, rfl, hValue⟩

theorem gap13 (p : Point3) (lam a b c : ℝ)
    (hXY : p.x ^ 2 / a ^ 2 = p.y ^ 2 / b ^ 2)
    (hYZ : p.y ^ 2 / b ^ 2 = p.z ^ 2 / c ^ 2)
    (hZ : p.z ^ 2 / c ^ 2 = lam * a * b * c / 2) :
    ∃ mu : ℝ, normalizedCommon p a b c mu := by
  refine ⟨lam * a * b * c / 2, ?_⟩
  unfold normalizedCommon
  exact ⟨hXY.trans (hYZ.trans hZ), hYZ.trans hZ, hZ⟩

theorem gap14 (p : Point3) (a b c : ℝ)
    (hCommon : ∃ mu : ℝ, normalizedCommon p a b c mu) :
    p.x ^ 2 / a ^ 2 = p.y ^ 2 / b ^ 2 := by
  rcases hCommon with ⟨mu, hmu⟩
  unfold normalizedCommon at hmu
  exact hmu.1.trans hmu.2.1.symm

theorem gap15 (p : Point3) (a b c : ℝ)
    (hCommon : ∃ mu : ℝ, normalizedCommon p a b c mu) :
    p.y ^ 2 / b ^ 2 = p.z ^ 2 / c ^ 2 := by
  rcases hCommon with ⟨mu, hmu⟩
  unfold normalizedCommon at hmu
  exact hmu.2.1.trans hmu.2.2.symm

theorem gap16 (p : Point3) (a b c : ℝ)
    (hXY : p.x ^ 2 / a ^ 2 = p.y ^ 2 / b ^ 2)
    (hYZ : p.y ^ 2 / b ^ 2 = p.z ^ 2 / c ^ 2) :
    ∃ mu : ℝ, normalizedCommon p a b c mu := by
  refine ⟨p.x ^ 2 / a ^ 2, ?_⟩
  unfold normalizedCommon
  exact ⟨rfl, hXY.symm, (hXY.trans hYZ).symm⟩

theorem gap17 (p : Point3) (a b c : ℝ)
    (hBoundary : onEllipsoid p a b c)
    (hCommon : ∃ mu : ℝ, normalizedCommon p a b c mu) :
    ∃ mu : ℝ, normalizedCommon p a b c mu ∧ mu = 1 / 3 := by
  rcases hCommon with ⟨mu, hmu⟩
  unfold normalizedCommon at hmu
  rcases hmu with ⟨hx, hy, hz⟩
  refine ⟨mu, ?_, ?_⟩
  · unfold normalizedCommon
    exact ⟨hx, hy, hz⟩
  · have hsum := gap1 p a b c hBoundary
    rw [hx, hy, hz] at hsum
    linarith

theorem gap18 (p : Point3) (a b c : ℝ)
    (hCommonOne :
      ∃ mu : ℝ, normalizedCommon p a b c mu ∧ mu = 1 / 3) :
    p.x ^ 2 / a ^ 2 = 1 / 3 := by
  rcases hCommonOne with ⟨mu, hmu, hvalue⟩
  unfold normalizedCommon at hmu
  exact hmu.1.trans hvalue

theorem gap19 (p : Point3) (a : ℝ)
    (ha : 0 < a)
    (hRatio : p.x ^ 2 / a ^ 2 = 1 / 3) :
    a = Real.sqrt 3 * abs p.x := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  field_simp [ha0] at hRatio
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have habs : abs p.x ^ 2 = p.x ^ 2 := sq_abs p.x
  have hrhs : 0 ≤ Real.sqrt 3 * abs p.x :=
    mul_nonneg (Real.sqrt_nonneg 3) (abs_nonneg p.x)
  nlinarith

theorem gap20 (p : Point3) (b : ℝ)
    (hb : 0 < b)
    (hRatio : p.y ^ 2 / b ^ 2 = 1 / 3) :
    b = Real.sqrt 3 * abs p.y := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  field_simp [hb0] at hRatio
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have habs : abs p.y ^ 2 = p.y ^ 2 := sq_abs p.y
  have hrhs : 0 ≤ Real.sqrt 3 * abs p.y :=
    mul_nonneg (Real.sqrt_nonneg 3) (abs_nonneg p.y)
  nlinarith

theorem gap21 (p : Point3) (c : ℝ)
    (hc : 0 < c)
    (hRatio : p.z ^ 2 / c ^ 2 = 1 / 3) :
    c = Real.sqrt 3 * abs p.z := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  field_simp [hc0] at hRatio
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have habs : abs p.z ^ 2 = p.z ^ 2 := sq_abs p.z
  have hrhs : 0 ≤ Real.sqrt 3 * abs p.z :=
    mul_nonneg (Real.sqrt_nonneg 3) (abs_nonneg p.z)
  nlinarith

theorem gap22 (p : Point3) (V a b c : ℝ)
    (hVolume : volumeConstraint V a b c)
    (ha : a = Real.sqrt 3 * abs p.x)
    (hb : b = Real.sqrt 3 * abs p.y)
    (hc : c = Real.sqrt 3 * abs p.z) :
    abs (p.x * p.y * p.z) =
      V / (4 * Real.pi * Real.sqrt 3) := by
  rw [ha, hb, hc] at hVolume
  unfold volumeConstraint at hVolume
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt0 : Real.sqrt (3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have habs : abs (p.x * p.y * p.z) =
      abs p.x * abs p.y * abs p.z := by
    rw [abs_mul, abs_mul]
  have hvol' :
      3 * Real.sqrt 3 * (abs p.x * abs p.y * abs p.z) =
        3 * V / (4 * Real.pi) := by
    calc
      3 * Real.sqrt 3 * (abs p.x * abs p.y * abs p.z) =
          (Real.sqrt 3) ^ 2 * Real.sqrt 3 *
            (abs p.x * abs p.y * abs p.z) := by rw [hsqrt]
      _ = (Real.sqrt 3 * abs p.x) *
            (Real.sqrt 3 * abs p.y) *
            (Real.sqrt 3 * abs p.z) := by ring
      _ = 3 * V / (4 * Real.pi) := hVolume
  rw [habs]
  field_simp [hpi, hsqrt0] at hvol' ⊢
  ring_nf at hvol' ⊢
  linarith

theorem gap23 (V : ℝ) (hV : 0 < V) :
    envelope V = productSurface V := by
  apply Set.ext
  intro p
  constructor
  · intro hp
    change ∃ a b c : ℝ,
      0 < a ∧ 0 < b ∧ 0 < c ∧
        volumeConstraint V a b c ∧ onEllipsoid p a b c ∧
        ∃ lam : ℝ, stationaryAxes p V lam a b c at hp
    change abs (p.x * p.y * p.z) =
      V / (4 * Real.pi * Real.sqrt 3)
    rcases hp with
      ⟨a, b, c, ha, hb, hc, hVolume, hBoundary, lam, hStationary⟩
    have hXY := gap9 p V lam a b c ha hb hc hStationary
    have hYZ := gap10 p V lam a b c ha hb hc hStationary
    have hCommon := gap16 p a b c hXY hYZ
    have hCommonOne := gap17 p a b c hBoundary hCommon
    rcases hCommonOne with ⟨mu, hmu, hvalue⟩
    unfold normalizedCommon at hmu
    have hxRatio : p.x ^ 2 / a ^ 2 = 1 / 3 := hmu.1.trans hvalue
    have hyRatio : p.y ^ 2 / b ^ 2 = 1 / 3 := hmu.2.1.trans hvalue
    have hzRatio : p.z ^ 2 / c ^ 2 = 1 / 3 := hmu.2.2.trans hvalue
    exact gap22 p V a b c hVolume
      (gap19 p a ha hxRatio)
      (gap20 p b hb hyRatio)
      (gap21 p c hc hzRatio)
  · intro hp
    change abs (p.x * p.y * p.z) =
      V / (4 * Real.pi * Real.sqrt 3) at hp
    change ∃ a b c : ℝ,
      0 < a ∧ 0 < b ∧ 0 < c ∧
        volumeConstraint V a b c ∧ onEllipsoid p a b c ∧
        ∃ lam : ℝ, stationaryAxes p V lam a b c
    have hsqrtpos : 0 < Real.sqrt (3 : ℝ) :=
      Real.sqrt_pos.2 (by norm_num)
    have hsqrt0 : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt hsqrtpos
    have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num)
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hdenpos : 0 < 4 * Real.pi * Real.sqrt 3 :=
      mul_pos (mul_pos (by norm_num) Real.pi_pos) hsqrtpos
    have hprodpos : 0 < abs (p.x * p.y * p.z) := by
      rw [hp]
      exact div_pos hV hdenpos
    have hxyz0 : p.x * p.y * p.z ≠ 0 := abs_pos.mp hprodpos
    have hx0 : p.x ≠ 0 := by
      intro hx
      apply hxyz0
      simp [hx]
    have hy0 : p.y ≠ 0 := by
      intro hy
      apply hxyz0
      simp [hy]
    have hz0 : p.z ≠ 0 := by
      intro hz
      apply hxyz0
      simp [hz]
    let a : ℝ := Real.sqrt 3 * abs p.x
    let b : ℝ := Real.sqrt 3 * abs p.y
    let c : ℝ := Real.sqrt 3 * abs p.z
    have ha : 0 < a := by
      dsimp [a]
      exact mul_pos hsqrtpos (abs_pos.mpr hx0)
    have hb : 0 < b := by
      dsimp [b]
      exact mul_pos hsqrtpos (abs_pos.mpr hy0)
    have hc : 0 < c := by
      dsimp [c]
      exact mul_pos hsqrtpos (abs_pos.mpr hz0)
    have hxRatio : p.x ^ 2 / a ^ 2 = 1 / 3 := by
      dsimp [a]
      field_simp [hsqrt0, abs_ne_zero.mpr hx0]
      nlinarith [hsqrt, sq_abs p.x]
    have hyRatio : p.y ^ 2 / b ^ 2 = 1 / 3 := by
      dsimp [b]
      field_simp [hsqrt0, abs_ne_zero.mpr hy0]
      nlinarith [hsqrt, sq_abs p.y]
    have hzRatio : p.z ^ 2 / c ^ 2 = 1 / 3 := by
      dsimp [c]
      field_simp [hsqrt0, abs_ne_zero.mpr hz0]
      nlinarith [hsqrt, sq_abs p.z]
    have hq : abs p.x * abs p.y * abs p.z =
        V / (4 * Real.pi * Real.sqrt 3) := by
      simpa [abs_mul] using hp
    have hVolume : volumeConstraint V a b c := by
      unfold volumeConstraint
      dsimp [a, b, c]
      calc
        (Real.sqrt 3 * abs p.x) *
            (Real.sqrt 3 * abs p.y) *
            (Real.sqrt 3 * abs p.z) =
          (Real.sqrt 3) ^ 2 * Real.sqrt 3 *
            (abs p.x * abs p.y * abs p.z) := by ring
        _ = 3 * Real.sqrt 3 *
            (abs p.x * abs p.y * abs p.z) := by rw [hsqrt]
        _ = 3 * V / (4 * Real.pi) := by
          field_simp [hpi, hsqrt0] at hq ⊢
          ring_nf at hq ⊢
          linarith
    have hBoundary : onEllipsoid p a b c := by
      unfold onEllipsoid ellipsoidValue
      rw [hxRatio, hyRatio, hzRatio]
      norm_num
    let lam : ℝ := 2 / (3 * a * b * c)
    have hstatA : -(2 * p.x ^ 2 / a ^ 3) + lam * b * c = 0 := by
      dsimp [lam]
      calc
        -(2 * p.x ^ 2 / a ^ 3) +
            (2 / (3 * a * b * c)) * b * c =
          (2 / a) * (-(p.x ^ 2 / a ^ 2) + 1 / 3) := by
            field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]
            <;> ring
        _ = 0 := by rw [hxRatio]; ring
    have hstatB : -(2 * p.y ^ 2 / b ^ 3) + lam * a * c = 0 := by
      dsimp [lam]
      calc
        -(2 * p.y ^ 2 / b ^ 3) +
            (2 / (3 * a * b * c)) * a * c =
          (2 / b) * (-(p.y ^ 2 / b ^ 2) + 1 / 3) := by
            field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]
            <;> ring
        _ = 0 := by rw [hyRatio]; ring
    have hstatC : -(2 * p.z ^ 2 / c ^ 3) + lam * a * b = 0 := by
      dsimp [lam]
      calc
        -(2 * p.z ^ 2 / c ^ 3) +
            (2 / (3 * a * b * c)) * a * b =
          (2 / c) * (-(p.z ^ 2 / c ^ 2) + 1 / 3) := by
            field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]
            <;> ring
        _ = 0 := by rw [hzRatio]; ring
    have hStationary : stationaryAxes p V lam a b c := by
      unfold stationaryAxes
      constructor
      · rw [gap3 p V lam a b c (ne_of_gt ha)]
        exact hstatA
      constructor
      · rw [gap5 p V lam a b c (ne_of_gt hb)]
        exact hstatB
      · rw [gap7 p V lam a b c (ne_of_gt hc)]
        exact hstatC
    exact ⟨a, b, c, ha, hb, hc, hVolume, hBoundary, lam, hStationary⟩

end

end ProofGap.Exercise3577
