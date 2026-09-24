import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Homotopy.Lifting

namespace ProofGap.Exercise4321

noncomputable section

open MeasureTheory
open scoped Interval unitInterval

def determinant (a b c d : ℝ) : ℝ := a * d - b * c

def X (a b x y : ℝ) : ℝ := a * x + b * y

def Y (c d x y : ℝ) : ℝ := c * x + d * y

def denominator (a b c d x y : ℝ) : ℝ :=
  (X a b x y) ^ 2 + (Y c d x y) ^ 2

def P (a b c d x y : ℝ) : ℝ :=
  -determinant a b c d * y / denominator a b c d x y

def Q (a b c d x y : ℝ) : ℝ :=
  determinant a b c d * x / denominator a b c d x y

def curveIntegral
    (a b c d : ℝ) (γ : ℝ → ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi,
    P a b c d (γ t).1 (γ t).2 *
        deriv (fun s => (γ s).1) t +
      Q a b c d (γ t).1 (γ t).2 *
        deriv (fun s => (γ s).2) t

def HomotopicAwayFromOrigin
    (γ δ : ℝ → ℝ × ℝ) : Prop :=
  ContDiff ℝ 1 γ ∧
    ContDiff ℝ 1 δ ∧
    γ 0 = γ (2 * Real.pi) ∧
    δ 0 = δ (2 * Real.pi) ∧
    ∃ H : ℝ → ℝ → ℝ × ℝ,
      Continuous (Function.uncurry H) ∧
      (∀ u ∈ Set.Icc (0 : ℝ) 1, ContDiff ℝ 1 (H u)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) (2 * Real.pi), H 0 s = γ s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) (2 * Real.pi), H 1 s = δ s) ∧
      (∀ u ∈ Set.Icc (0 : ℝ) 1, H u 0 = H u (2 * Real.pi)) ∧
      (∀ u ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) (2 * Real.pi), H u s ≠ (0, 0))

def smallEllipse
    (a b c d r t : ℝ) : ℝ × ℝ :=
  let Δ := determinant a b c d
  let u := r * Real.cos t
  let v := SignType.sign Δ * r * Real.sin t
  ((d * u - b * v) / Δ, (-c * u + a * v) / Δ)

def preimageDisk
    (a b c d r : ℝ) : Set (ℝ × ℝ) :=
  {z | denominator a b c d z.1 z.2 ≤ r ^ 2}

def transformedDisk (r : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ^ 2 + z.2 ^ 2 ≤ r ^ 2}

def normalizedIntegral
    (a b c d : ℝ) (γ : ℝ → ℝ × ℝ) : ℝ :=
  (1 / (2 * Real.pi) : ℝ) * curveIntegral a b c d γ

theorem gap1
    (a b c d x y : ℝ)
    (hdet : determinant a b c d ≠ 0) :
    denominator a b c d x y = 0 ↔ (x, y) = (0, 0) := by
  constructor
  · intro h
    have hX : X a b x y = 0 := by
      have hx := sq_nonneg (X a b x y)
      have hy := sq_nonneg (Y c d x y)
      simp only [denominator] at h
      nlinarith
    have hY : Y c d x y = 0 := by
      have hx := sq_nonneg (X a b x y)
      have hy := sq_nonneg (Y c d x y)
      simp only [denominator] at h
      nlinarith
    have hxdet :
        determinant a b c d * x =
          d * X a b x y - b * Y c d x y := by
      simp only [determinant, X, Y]
      ring
    have hydet :
        determinant a b c d * y =
          a * Y c d x y - c * X a b x y := by
      simp only [determinant, X, Y]
      ring
    rw [hX, hY] at hxdet hydet
    simp only [mul_zero, sub_self] at hxdet hydet
    have hx0 : x = 0 := (mul_eq_zero.mp hxdet).resolve_left hdet
    have hy0 : y = 0 := (mul_eq_zero.mp hydet).resolve_left hdet
    simp [hx0, hy0]
  · intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp [denominator, X, Y]

private lemma denominator_ne
    (a b c d x y : ℝ) (hxy : (x, y) ≠ (0, 0))
    (hdet : determinant a b c d ≠ 0) :
    denominator a b c d x y ≠ 0 := by
  exact (gap1 a b c d x y hdet).not.mpr hxy

theorem gap2
    (a b c d : ℝ) (γ : ℝ → ℝ × ℝ) (t : ℝ)
    (hDiffX : DifferentiableAt ℝ (fun s => (γ s).1) t)
    (hDiffY : DifferentiableAt ℝ (fun s => (γ s).2) t) :
    X a b (γ t).1 (γ t).2 *
          deriv (fun s => Y c d (γ s).1 (γ s).2) t -
        Y c d (γ t).1 (γ t).2 *
          deriv (fun s => X a b (γ s).1 (γ s).2) t =
      determinant a b c d *
        ((γ t).1 * deriv (fun s => (γ s).2) t -
          (γ t).2 * deriv (fun s => (γ s).1) t) := by
  have hXd :
      deriv (fun s => X a b (γ s).1 (γ s).2) t =
        a * deriv (fun s => (γ s).1) t +
          b * deriv (fun s => (γ s).2) t := by
    simpa [X] using
      (HasDerivAt.add
        (HasDerivAt.const_mul a hDiffX.hasDerivAt)
        (HasDerivAt.const_mul b hDiffY.hasDerivAt)).deriv
  have hYd :
      deriv (fun s => Y c d (γ s).1 (γ s).2) t =
        c * deriv (fun s => (γ s).1) t +
          d * deriv (fun s => (γ s).2) t := by
    simpa [Y] using
      (HasDerivAt.add
        (HasDerivAt.const_mul c hDiffX.hasDerivAt)
        (HasDerivAt.const_mul d hDiffY.hasDerivAt)).deriv
  rw [hXd, hYd]
  simp only [X, Y, determinant]
  ring

private lemma deriv_P_formula
    (a b c d x y : ℝ) (hxy : (x, y) ≠ (0, 0))
    (hdet : determinant a b c d ≠ 0) :
    deriv (fun t => P a b c d x t) y =
      -(determinant a b c d *
          ((a ^ 2 + c ^ 2) * x ^ 2 -
            (b ^ 2 + d ^ 2) * y ^ 2)) /
        (denominator a b c d x y) ^ 2 := by
  have hden := denominator_ne a b c d x y hxy hdet
  have hnum :
      HasDerivAt (fun t : ℝ => -determinant a b c d * t)
        (-determinant a b c d) y := by
    simpa only [id_eq, mul_one] using
      HasDerivAt.const_mul (-determinant a b c d) (hasDerivAt_id y)
  have hD :
      HasDerivAt (fun t : ℝ => denominator a b c d x t)
        (2 * b * X a b x y + 2 * d * Y c d x y) y := by
    simp only [denominator, X, Y]
    convert HasDerivAt.add
      (HasDerivAt.pow (HasDerivAt.add
        (hasDerivAt_const y (a * x))
        (HasDerivAt.const_mul b (hasDerivAt_id y))) 2)
      (HasDerivAt.pow (HasDerivAt.add
        (hasDerivAt_const y (c * x))
        (HasDerivAt.const_mul d (hasDerivAt_id y))) 2) using 1 <;>
      simp only [Pi.add_apply, id_eq] <;> ring
  have H := HasDerivAt.div hnum hD hden
  have hderiv := H.deriv
  change deriv (fun t =>
      (-determinant a b c d * t) /
        denominator a b c d x t) y = _ at hderiv
  change deriv (fun t => P a b c d x t) y = _
  rw [show (fun t => P a b c d x t) =
      fun t => (-determinant a b c d * t) /
        denominator a b c d x t by rfl,
    hderiv]
  simp only [X, Y, denominator, determinant]
  field_simp [show
    (a * x + b * y) ^ 2 + (c * x + d * y) ^ 2 ≠ 0 by
      simpa [denominator, X, Y, determinant] using hden]
  ring

private lemma deriv_Q_formula
    (a b c d x y : ℝ) (hxy : (x, y) ≠ (0, 0))
    (hdet : determinant a b c d ≠ 0) :
    deriv (fun t => Q a b c d t y) x =
      -(determinant a b c d *
          ((a ^ 2 + c ^ 2) * x ^ 2 -
            (b ^ 2 + d ^ 2) * y ^ 2)) /
        (denominator a b c d x y) ^ 2 := by
  have hden := denominator_ne a b c d x y hxy hdet
  have hnum :
      HasDerivAt (fun t : ℝ => determinant a b c d * t)
        (determinant a b c d) x := by
    simpa only [id_eq, mul_one] using
      HasDerivAt.const_mul (determinant a b c d) (hasDerivAt_id x)
  have hD :
      HasDerivAt (fun t : ℝ => denominator a b c d t y)
        (2 * a * X a b x y + 2 * c * Y c d x y) x := by
    simp only [denominator, X, Y]
    convert HasDerivAt.add
      (HasDerivAt.pow (HasDerivAt.add
        (HasDerivAt.const_mul a (hasDerivAt_id x))
        (hasDerivAt_const x (b * y))) 2)
      (HasDerivAt.pow (HasDerivAt.add
        (HasDerivAt.const_mul c (hasDerivAt_id x))
        (hasDerivAt_const x (d * y))) 2) using 1 <;>
      simp only [Pi.add_apply, id_eq] <;> ring
  have H := HasDerivAt.div hnum hD hden
  have hderiv := H.deriv
  change deriv (fun t =>
      (determinant a b c d * t) /
        denominator a b c d t y) x = _ at hderiv
  change deriv (fun t => Q a b c d t y) x = _
  rw [show (fun t => Q a b c d t y) =
      fun t => (determinant a b c d * t) /
        denominator a b c d t y by rfl,
    hderiv]
  simp only [X, Y, denominator, determinant]
  field_simp [show
    (a * x + b * y) ^ 2 + (c * x + d * y) ^ 2 ≠ 0 by
      simpa [denominator, X, Y, determinant] using hden]
  ring

theorem gap3
    (a b c d x y : ℝ) (hxy : (x, y) ≠ (0, 0))
    (hdet : determinant a b c d ≠ 0) :
    deriv (fun t => Q a b c d t y) x =
      deriv (fun t => P a b c d x t) y := by
  rw [deriv_Q_formula a b c d x y hxy hdet,
    deriv_P_formula a b c d x y hxy hdet]

theorem gap4
    (a b c d x y : ℝ) (hxy : (x, y) ≠ (0, 0))
    (hdet : determinant a b c d ≠ 0) :
    deriv (fun t => P a b c d x t) y =
      -(determinant a b c d *
          ((a ^ 2 + c ^ 2) * x ^ 2 -
            (b ^ 2 + d ^ 2) * y ^ 2)) /
        (denominator a b c d x y) ^ 2 := by
  exact deriv_P_formula a b c d x y hxy hdet

theorem gap5
    (a b c d x y : ℝ) (hxy : (x, y) ≠ (0, 0))
    (hdet : determinant a b c d ≠ 0) :
    deriv (fun t => Q a b c d t y) x =
      -(determinant a b c d *
          ((a ^ 2 + c ^ 2) * x ^ 2 -
            (b ^ 2 + d ^ 2) * y ^ 2)) /
        (denominator a b c d x y) ^ 2 := by
  exact deriv_Q_formula a b c d x y hxy hdet

private lemma matrix_det_formula (a b c d : ℝ) :
    (Matrix.of (fun i : Fin 2 => fun j : Fin 2 =>
      if i = 0 ∧ j = 0 then a
      else if i = 0 ∧ j = 1 then b
      else if i = 1 ∧ j = 0 then c
      else d)).det =
      determinant a b c d := by
  rw [Matrix.det_fin_two]
  simp [determinant]

private lemma smallEllipse_X
    (a b c d r t : ℝ) (hdet : determinant a b c d ≠ 0) :
    X a b (smallEllipse a b c d r t).1
        (smallEllipse a b c d r t).2 =
      r * Real.cos t := by
  simp only [smallEllipse, X]
  field_simp [hdet]
  simp only [determinant] at hdet ⊢
  ring

private lemma smallEllipse_Y
    (a b c d r t : ℝ) (hdet : determinant a b c d ≠ 0) :
    Y c d (smallEllipse a b c d r t).1
        (smallEllipse a b c d r t).2 =
      (SignType.sign (determinant a b c d) : ℝ) * r * Real.sin t := by
  simp only [smallEllipse, Y]
  field_simp [hdet]
  simp only [determinant] at hdet ⊢
  ring

private lemma sign_sq_of_ne_zero (x : ℝ) (hx : x ≠ 0) :
    (SignType.sign x : ℝ) ^ 2 = 1 := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rw [sign_neg hxneg]
    norm_num
  · rw [sign_pos hxpos]
    norm_num

private lemma smallEllipse_denominator
    (a b c d r t : ℝ) (hdet : determinant a b c d ≠ 0) :
    denominator a b c d
        (smallEllipse a b c d r t).1
        (smallEllipse a b c d r t).2 =
      r ^ 2 := by
  rw [denominator, smallEllipse_X a b c d r t hdet,
    smallEllipse_Y a b c d r t hdet]
  have hs := sign_sq_of_ne_zero (determinant a b c d) hdet
  simp only [mul_pow, hs, one_mul]
  rw [← mul_add, Real.cos_sq_add_sin_sq]
  ring

private lemma smallEllipse_integrand
    (a b c d r t : ℝ) (hdet : determinant a b c d ≠ 0)
    (hr : 0 < r) :
    P a b c d
          (smallEllipse a b c d r t).1
          (smallEllipse a b c d r t).2 *
        deriv (fun s => (smallEllipse a b c d r s).1) t +
      Q a b c d
          (smallEllipse a b c d r t).1
          (smallEllipse a b c d r t).2 *
        deriv (fun s => (smallEllipse a b c d r s).2) t =
      determinant a b c d / r ^ 2 *
        ((smallEllipse a b c d r t).1 *
            deriv (fun s => (smallEllipse a b c d r s).2) t -
          (smallEllipse a b c d r t).2 *
            deriv (fun s => (smallEllipse a b c d r s).1) t) := by
  rw [P, Q, smallEllipse_denominator a b c d r t hdet]
  field_simp [ne_of_gt hr]
  ring

private lemma normalized_smallEllipse_formula
    (a b c d r : ℝ)
    (hdet : determinant a b c d ≠ 0) (hr : 0 < r) :
    normalizedIntegral a b c d (smallEllipse a b c d r) =
      determinant a b c d / (2 * Real.pi * r ^ 2) *
        (∫ t in (0 : ℝ)..2 * Real.pi,
          (smallEllipse a b c d r t).1 *
              deriv (fun s => (smallEllipse a b c d r s).2) t -
            (smallEllipse a b c d r t).2 *
              deriv (fun s => (smallEllipse a b c d r s).1) t) := by
  rw [normalizedIntegral, curveIntegral]
  simp_rw [smallEllipse_integrand a b c d r _ hdet hr,
    intervalIntegral.integral_const_mul]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hr0 : r ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hr)
  field_simp

private theorem transformedDisk_volume (r : ℝ) (hr : 0 < r) :
    volume (transformedDisk r) =
      ENNReal.ofReal (Real.pi * r ^ 2) := by
  let e : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) :=
    MeasurableEquiv.finTwoArrow
  let T : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2
  have hpre :
      e ⁻¹' transformedDisk r =
        T ⁻¹' Metric.closedBall 0 r := by
    ext x
    simp only [Set.mem_preimage, transformedDisk, Set.mem_setOf_eq,
      Metric.mem_closedBall, dist_zero_right]
    change x 0 ^ 2 + x 1 ^ 2 ≤ r ^ 2 ↔ ‖WithLp.toLp 2 x‖ ≤ r
    rw [← sq_le_sq₀ (norm_nonneg _) hr.le]
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two]
  have hball : MeasurableSet (Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin 2)) r) := measurableSet_closedBall
  have hdisk : MeasurableSet (transformedDisk r) := by
    exact measurableSet_le
      ((continuous_fst.pow 2).add (continuous_snd.pow 2)).measurable
      measurable_const
  have he := MeasureTheory.volume_preserving_piFinTwo
    (fun _ : Fin 2 => ℝ)
  have hT := PiLp.volume_preserving_toLp (Fin 2)
  calc
    volume (transformedDisk r) =
        volume (e ⁻¹' transformedDisk r) := by
      symm
      exact he.measure_preimage hdisk.nullMeasurableSet
    _ = volume (T ⁻¹' Metric.closedBall 0 r) := by rw [hpre]
    _ = volume (Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin 2)) r) := by
      exact hT.measure_preimage hball.nullMeasurableSet
    _ = ENNReal.ofReal (Real.pi * r ^ 2) := by
      simp
      rw [← ENNReal.ofReal_pow hr.le 2,
        mul_comm,
        ← ENNReal.ofReal_mul Real.pi_nonneg]

private noncomputable def linearXY (a b c d : ℝ) :
    (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![a, b; c, d]

private lemma linearXY_apply (a b c d : ℝ) (z : ℝ × ℝ) :
    linearXY a b c d z =
      (X a b z.1 z.2, Y c d z.1 z.2) := by
  simp [linearXY, Matrix.toLin_finTwoProd_apply, X, Y]

private lemma linearXY_det (a b c d : ℝ) :
    LinearMap.det (linearXY a b c d) = determinant a b c d := by
  simp [linearXY, LinearMap.det_toLin, Matrix.det_fin_two, determinant]

private lemma linearXY_preimage (a b c d r : ℝ) :
    linearXY a b c d ⁻¹' transformedDisk r =
      preimageDisk a b c d r := by
  ext z
  simp [linearXY_apply, transformedDisk, preimageDisk, denominator]

private theorem preimageDisk_volume
    (a b c d r : ℝ)
    (hdet : determinant a b c d ≠ 0) (hr : 0 < r) :
    volume (preimageDisk a b c d r) =
      ENNReal.ofReal
        (Real.pi * r ^ 2 / |determinant a b c d|) := by
  have hlin :
      LinearMap.det (linearXY a b c d) ≠ 0 := by
    simpa [linearXY_det] using hdet
  rw [← linearXY_preimage a b c d r,
    MeasureTheory.Measure.addHaar_preimage_linearMap volume hlin,
    transformedDisk_volume r hr, linearXY_det]
  rw [← ENNReal.ofReal_mul
    (abs_nonneg ((determinant a b c d)⁻¹))]
  congr 1
  rw [abs_inv]
  field_simp [abs_ne_zero.mpr hdet]

private lemma smallEllipse_oriented_integrand
    (a b c d r t : ℝ)
    (hdet : determinant a b c d ≠ 0) :
    (smallEllipse a b c d r t).1 *
          deriv (fun s => (smallEllipse a b c d r s).2) t -
        (smallEllipse a b c d r t).2 *
          deriv (fun s => (smallEllipse a b c d r s).1) t =
      r ^ 2 / |determinant a b c d| := by
  have hx : DifferentiableAt ℝ
      (fun s => (smallEllipse a b c d r s).1) t := by
    simp only [smallEllipse]
    fun_prop
  have hy : DifferentiableAt ℝ
      (fun s => (smallEllipse a b c d r s).2) t := by
    simp only [smallEllipse]
    fun_prop
  have hmain := gap2 a b c d (smallEllipse a b c d r) t hx hy
  have hXd :
      deriv (fun s =>
        X a b (smallEllipse a b c d r s).1
          (smallEllipse a b c d r s).2) t =
        r * (-Real.sin t) := by
    have hfun :
        (fun s =>
          X a b (smallEllipse a b c d r s).1
            (smallEllipse a b c d r s).2) =
          fun s => r * Real.cos s := by
      funext s
      exact smallEllipse_X a b c d r s hdet
    rw [hfun]
    exact (HasDerivAt.const_mul r (Real.hasDerivAt_cos t)).deriv
  have hYd :
      deriv (fun s =>
        Y c d (smallEllipse a b c d r s).1
          (smallEllipse a b c d r s).2) t =
        (SignType.sign (determinant a b c d) : ℝ) *
          r * Real.cos t := by
    have hfun :
        (fun s =>
          Y c d (smallEllipse a b c d r s).1
            (smallEllipse a b c d r s).2) =
          fun s =>
            (SignType.sign (determinant a b c d) : ℝ) *
              r * Real.sin s := by
      funext s
      exact smallEllipse_Y a b c d r s hdet
    rw [hfun]
    convert HasDerivAt.const_mul
      ((SignType.sign (determinant a b c d) : ℝ) * r)
      (Real.hasDerivAt_sin t) |>.deriv using 1 <;> ring
  rw [smallEllipse_X a b c d r t hdet,
    smallEllipse_Y a b c d r t hdet, hXd, hYd] at hmain
  have htrig := Real.cos_sq_add_sin_sq t
  have hs := sign_sq_of_ne_zero (determinant a b c d) hdet
  have hleft :
      r * Real.cos t *
            ((SignType.sign (determinant a b c d) : ℝ) *
              r * Real.cos t) -
          (SignType.sign (determinant a b c d) : ℝ) *
            r * Real.sin t * (r * -Real.sin t) =
        (SignType.sign (determinant a b c d) : ℝ) * r ^ 2 := by
    calc
      _ = (SignType.sign (determinant a b c d) : ℝ) *
          r ^ 2 * (Real.cos t ^ 2 + Real.sin t ^ 2) := by ring
      _ = (SignType.sign (determinant a b c d) : ℝ) *
          r ^ 2 := by rw [htrig]; ring
  rw [hleft] at hmain
  rw [eq_div_iff (abs_ne_zero.mpr hdet)]
  rw [← sign_mul_self (determinant a b c d)]
  calc
    _ = (SignType.sign (determinant a b c d) : ℝ) *
        (determinant a b c d *
          ((smallEllipse a b c d r t).1 *
              deriv (fun s => (smallEllipse a b c d r s).2) t -
            (smallEllipse a b c d r t).2 *
              deriv (fun s => (smallEllipse a b c d r s).1) t)) := by ring
    _ = (SignType.sign (determinant a b c d) : ℝ) *
        ((SignType.sign (determinant a b c d) : ℝ) * r ^ 2) := by
      rw [← hmain]
    _ = (SignType.sign (determinant a b c d) : ℝ) ^ 2 *
        r ^ 2 := by ring
    _ = r ^ 2 := by rw [hs, one_mul]

private theorem smallEllipse_oriented_integral
    (a b c d r : ℝ)
    (hdet : determinant a b c d ≠ 0) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
        (smallEllipse a b c d r t).1 *
            deriv (fun s => (smallEllipse a b c d r s).2) t -
          (smallEllipse a b c d r t).2 *
            deriv (fun s => (smallEllipse a b c d r s).1) t) =
      2 * Real.pi * (r ^ 2 / |determinant a b c d|) := by
  rw [intervalIntegral.integral_congr
    (fun t _ => smallEllipse_oriented_integrand
      a b c d r t hdet)]
  simp
  ring

private theorem preimageDisk_integral_two
    (a b c d r : ℝ)
    (hdet : determinant a b c d ≠ 0) (hr : 0 < r) :
    (∫ _z in preimageDisk a b c d r, (2 : ℝ)) =
      2 * (Real.pi * r ^ 2 / |determinant a b c d|) := by
  have hnonneg :
      0 ≤ Real.pi * r ^ 2 / |determinant a b c d| :=
    div_nonneg (mul_nonneg Real.pi_nonneg (sq_nonneg r))
      (abs_nonneg _)
  rw [MeasureTheory.setIntegral_const, Measure.real,
    preimageDisk_volume a b c d r hdet hr,
    ENNReal.toReal_ofReal hnonneg]
  simp [smul_eq_mul]
  ring

private theorem transformedDisk_integral_invdet
    (a b c d r : ℝ)
    (hdet : determinant a b c d ≠ 0) (hr : 0 < r) :
    (∫ _w in transformedDisk r,
        (1 / |determinant a b c d| : ℝ)) =
      Real.pi * r ^ 2 *
        (1 / |determinant a b c d| : ℝ) := by
  have hnonneg : 0 ≤ Real.pi * r ^ 2 :=
    mul_nonneg Real.pi_nonneg (sq_nonneg r)
  rw [MeasureTheory.setIntegral_const, Measure.real,
    transformedDisk_volume r hr,
    ENNReal.toReal_ofReal hnonneg]
  simp [smul_eq_mul]

private theorem boundary_eq_area
    (a b c d r : ℝ)
    (hdet : determinant a b c d ≠ 0) (hr : 0 < r) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
        (smallEllipse a b c d r t).1 *
            deriv (fun s => (smallEllipse a b c d r s).2) t -
          (smallEllipse a b c d r t).2 *
            deriv (fun s => (smallEllipse a b c d r s).1) t) =
      ∫ _z in preimageDisk a b c d r, (2 : ℝ) := by
  rw [smallEllipse_oriented_integral a b c d r hdet,
    preimageDisk_integral_two a b c d r hdet hr]
  ring

private theorem transformed_change_formula
    (a b c d r : ℝ)
    (hdet : determinant a b c d ≠ 0) (hr : 0 < r) :
    determinant a b c d / (2 * Real.pi * r ^ 2) *
        (∫ _z in preimageDisk a b c d r, (2 : ℝ)) =
      determinant a b c d / (Real.pi * r ^ 2) *
        (∫ _w in transformedDisk r,
          (1 / |determinant a b c d| : ℝ)) := by
  rw [preimageDisk_integral_two a b c d r hdet hr,
    transformedDisk_integral_invdet a b c d r hdet hr]
  ring

private theorem transformed_normalized_eq_sign
    (a b c d r : ℝ)
    (hdet : determinant a b c d ≠ 0) (hr : 0 < r) :
    determinant a b c d / (Real.pi * r ^ 2) *
        (∫ _w in transformedDisk r,
          (1 / |determinant a b c d| : ℝ)) =
      SignType.sign (determinant a b c d) := by
  rw [transformedDisk_integral_invdet
    a b c d r hdet hr]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hr0 : r ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hr)
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · rw [sign_neg hneg, SignType.coe_neg, SignType.coe_one,
      abs_of_neg hneg]
    field_simp
  · rw [sign_pos hpos, SignType.coe_one, abs_of_pos hpos]
    field_simp

private theorem exists_log_lift_with_integral
    (T : ℝ) (hT : 0 < T) (w : ℝ → ℂ)
    (hw : ContDiff ℝ 1 w)
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) T, w t ≠ 0) :
    ∃ L : C(unitInterval, ℂ),
      (∀ u, Complex.exp (L u) = w (T * (u : ℝ))) ∧
      (L 1 - L 0).im =
        ∫ t in (0 : ℝ)..T, (deriv w t / w t).im := by
  let f : ℝ → ℂ := fun t => deriv w t / w t
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) T) := by
    exact hw.continuous_deriv_one.continuousOn.div
      hw.continuous.continuousOn hne
  let fI : C(Set.Icc (0 : ℝ) T, ℂ) :=
    ⟨fun t => f t, hfcont.restrict⟩
  let fe : ℝ → ℂ :=
    Set.IccExtend hT.le fI
  have hfecont : Continuous fe := by
    exact continuous_IccExtend_iff.mpr fI.continuous
  have hfe_eq (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      fe t = f t := by
    simp [fe, fI, Set.IccExtend_of_mem hT.le _ ht]
  let Lr : ℝ → ℂ := fun t =>
    Complex.log (w 0) + ∫ u in (0 : ℝ)..t, fe u
  have hLderiv (t : ℝ) : HasDerivAt Lr (fe t) t := by
    apply HasDerivAt.const_add
    exact intervalIntegral.integral_hasDerivAt_right
      (hfecont.intervalIntegrable 0 t)
      hfecont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hfecont.continuousAt
  have hLdiff : Differentiable ℝ Lr :=
    fun t => (hLderiv t).differentiableAt
  let R : ℝ → ℂ := fun t => Complex.exp (-Lr t) * w t
  have hwdiff : Differentiable ℝ w :=
    hw.differentiable (by norm_num)
  have hRdiff : Differentiable ℝ R := by
    intro t
    exact (HasDerivAt.mul ((hLderiv t).neg.cexp)
      (hwdiff t).hasDerivAt).differentiableAt
  have hRderiv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      HasDerivAt R 0 t := by
    have H := HasDerivAt.mul ((hLderiv t).neg.cexp)
      (hwdiff t).hasDerivAt
    convert H using 1
    rw [hfe_eq t ht]
    dsimp only [f]
    field_simp [hne t ht]
    ring
  have hRzero : R 0 = 1 := by
    have hw0 : w 0 ≠ 0 := hne 0 ⟨le_rfl, hT.le⟩
    simp [R, Lr, Complex.exp_neg, Complex.exp_log hw0,
      hw0]
  have hRone (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      R t = 1 := by
    have hconst :
        R t = R 0 := by
      apply Convex.is_const_of_fderivWithin_eq_zero (convex_Icc 0 T)
        hRdiff.differentiableOn
      · intro s hs
        rw [(hRdiff s).fderivWithin
          ((uniqueDiffOn_Icc hT) s hs)]
        rw [(hRderiv s hs).hasFDerivAt.fderiv]
        simp
      · exact ht
      · exact ⟨le_rfl, hT.le⟩
    exact hconst.trans hRzero
  have hexp (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      Complex.exp (Lr t) = w t := by
    have h := hRone t ht
    simp only [R, Complex.exp_neg] at h
    exact (inv_mul_eq_one₀ (Complex.exp_ne_zero (Lr t))).mp h
  let L : C(unitInterval, ℂ) :=
    ⟨fun u => Lr (T * (u : ℝ)),
      hLdiff.continuous.comp
        (continuous_const.mul continuous_subtype_val)⟩
  refine ⟨L, ?_, ?_⟩
  · intro u
    apply hexp
    exact ⟨mul_nonneg hT.le u.2.1,
      by simpa using mul_le_mul_of_nonneg_left u.2.2 hT.le⟩
  · dsimp only [L, ContinuousMap.coe_mk]
    norm_num
    have hfint : IntervalIntegrable f volume 0 T := by
      apply ContinuousOn.intervalIntegrable
      simpa [Set.uIcc_of_le hT.le] using hfcont
    have hLint :
        Lr T - Lr 0 = ∫ t in (0 : ℝ)..T, f t := by
      have hLdiff :
          Lr T - Lr 0 = ∫ t in (0 : ℝ)..T, fe t := by
        simp [Lr]
      rw [hLdiff]
      apply intervalIntegral.integral_congr
      intro t ht
      exact hfe_eq t (by
        simpa [Set.uIcc_of_le hT.le] using ht)
    rw [← Complex.sub_im, hLint]
    change (Complex.imCLM (∫ t in (0 : ℝ)..T, f t)) =
      ∫ t in (0 : ℝ)..T, Complex.imCLM (f t)
    exact (Complex.imCLM.intervalIntegral_comp_comm hfint).symm

private lemma exp_lifts_endpoint_sub_eq
    (γ : C(unitInterval, {z : ℂ // z ≠ 0}))
    (L M : C(unitInterval, ℂ))
    (hL : ∀ s, Complex.exp (L s) = (γ s : ℂ))
    (hM : ∀ s, Complex.exp (M s) = (γ s : ℂ)) :
    L 1 - L 0 = M 1 - M 0 := by
  let p : ℂ → {z : ℂ // z ≠ 0} :=
    fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩
  let k : ℂ := M 0 - L 0
  have hk : Complex.exp k = 1 := by
    rw [show k = M 0 - L 0 by rfl, Complex.exp_sub,
      hM 0, hL 0, div_self (γ 0).2]
  let C : unitInterval → ℂ := fun s => L s + k
  have hCcont : Continuous C := by
    exact L.continuous.add continuous_const
  have hcomp : p ∘ C = p ∘ M := by
    funext s
    apply Subtype.ext
    simp only [Function.comp_apply, p, C]
    rw [Complex.exp_add, hk, mul_one, hL s, hM s]
  have hCM : C = M := by
    apply Complex.isCoveringMap_exp.eq_of_comp_eq
      hCcont M.continuous hcomp 0
    simp [C, k]
  have hzero := congrFun hCM 0
  have hone := congrFun hCM 1
  dsimp only [C] at hzero hone
  calc
    L 1 - L 0 = (L 1 + k) - (L 0 + k) := by abel
    _ = M 1 - M 0 := by rw [hone, hzero]

private lemma exp_lift_endpoint_sub_eq_of_free_homotopy
    (F : C(unitInterval × unitInterval,
      {z : ℂ // z ≠ 0}))
    (hloop : ∀ u, F (u, 0) = F (u, 1))
    (L₀ L₁ : C(unitInterval, ℂ))
    (hL₀ : ∀ s, Complex.exp (L₀ s) = (F (0, s) : ℂ))
    (hL₁ : ∀ s, Complex.exp (L₁ s) = (F (1, s) : ℂ)) :
    L₀ 1 - L₀ 0 = L₁ 1 - L₁ 0 := by
  let p : ℂ → {z : ℂ // z ≠ 0} :=
    fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩
  have hzero (s : unitInterval) : F (0, s) = p (L₀ s) := by
    apply Subtype.ext
    exact (hL₀ s).symm
  let Φ : C(unitInterval × unitInterval, ℂ) :=
    Complex.isCoveringMap_exp.liftHomotopy F L₀ hzero
  have hΦlift :
      p ∘ Φ = F :=
    Complex.isCoveringMap_exp.liftHomotopy_lifts F L₀ hzero
  have hΦzero (s : unitInterval) :
      Φ (0, s) = L₀ s :=
    Complex.isCoveringMap_exp.liftHomotopy_zero F L₀ hzero s
  let A : C(unitInterval, ℂ) :=
    ⟨fun u => Φ (u, 0), by fun_prop⟩
  let B : C(unitInterval, ℂ) :=
    ⟨fun u => Φ (u, 1), by fun_prop⟩
  let β : C(unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun u => F (u, 0), by fun_prop⟩
  have hA (u : unitInterval) :
      Complex.exp (A u) = (β u : ℂ) := by
    have h := congrFun hΦlift (u, 0)
    exact congrArg Subtype.val h
  have hB (u : unitInterval) :
      Complex.exp (B u) = (β u : ℂ) := by
    have h := congrFun hΦlift (u, 1)
    have hv := congrArg Subtype.val h
    exact hv.trans (congrArg Subtype.val (hloop u).symm)
  have hAB :
      A 1 - A 0 = B 1 - B 0 :=
    exp_lifts_endpoint_sub_eq β A B hA hB
  let M : C(unitInterval, ℂ) :=
    ⟨fun s => Φ (1, s), by fun_prop⟩
  let δ : C(unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun s => F (1, s), by fun_prop⟩
  have hM (s : unitInterval) :
      Complex.exp (M s) = (δ s : ℂ) := by
    have h := congrFun hΦlift (1, s)
    exact congrArg Subtype.val h
  have hML :
      M 1 - M 0 = L₁ 1 - L₁ 0 :=
    exp_lifts_endpoint_sub_eq δ M L₁ hM hL₁
  have hrow :
      M 1 - M 0 = L₀ 1 - L₀ 0 := by
    have hA0 : A 0 = L₀ 0 := hΦzero 0
    have hB0 : B 0 = L₀ 1 := hΦzero 1
    rw [hA0, hB0] at hAB
    change M 0 - L₀ 0 = M 1 - L₀ 1 at hAB
    linear_combination -hAB
  exact hrow.symm.trans hML

private def complexTransform
    (a b c d : ℝ) (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℂ :=
  (X a b (γ t).1 (γ t).2 : ℂ) +
    Complex.I * (Y c d (γ t).1 (γ t).2 : ℂ)

private lemma complexTransform_contDiff
    (a b c d : ℝ) (γ : ℝ → ℝ × ℝ)
    (hγ : ContDiff ℝ 1 γ) :
    ContDiff ℝ 1 (complexTransform a b c d γ) := by
  have hU : ContDiff ℝ 1
      (fun t => X a b (γ t).1 (γ t).2) := by
    unfold X
    fun_prop
  have hV : ContDiff ℝ 1
      (fun t => Y c d (γ t).1 (γ t).2) := by
    unfold Y
    fun_prop
  have hUc : ContDiff ℝ 1
      (fun t => (X a b (γ t).1 (γ t).2 : ℂ)) := by
    simpa [Function.comp_def] using
      (Complex.ofRealCLM.contDiff.comp hU)
  have hVc : ContDiff ℝ 1
      (fun t => (Y c d (γ t).1 (γ t).2 : ℂ)) := by
    simpa [Function.comp_def] using
      (Complex.ofRealCLM.contDiff.comp hV)
  exact hUc.add (contDiff_const.mul hVc)

private lemma complexTransform_ne
    (a b c d : ℝ) (γ : ℝ → ℝ × ℝ) (t : ℝ)
    (hdet : determinant a b c d ≠ 0)
    (hγt : γ t ≠ (0, 0)) :
    complexTransform a b c d γ t ≠ 0 := by
  intro hz
  have hX : X a b (γ t).1 (γ t).2 = 0 := by
    have h := congrArg Complex.re hz
    simpa [complexTransform] using h
  have hY : Y c d (γ t).1 (γ t).2 = 0 := by
    have h := congrArg Complex.im hz
    simpa [complexTransform] using h
  apply hγt
  apply (gap1 a b c d (γ t).1 (γ t).2 hdet).mp
  simp [denominator, hX, hY]

private lemma complexTransform_deriv
    (a b c d : ℝ) (γ : ℝ → ℝ × ℝ)
    (hγ : ContDiff ℝ 1 γ) (t : ℝ) :
    deriv (complexTransform a b c d γ) t =
      ((deriv (fun s =>
        X a b (γ s).1 (γ s).2) t : ℝ) : ℂ) +
      Complex.I * ((deriv (fun s =>
        Y c d (γ s).1 (γ s).2) t : ℝ) : ℂ) := by
  have hγdiff : Differentiable ℝ γ :=
    hγ.differentiable (by norm_num)
  have hU : Differentiable ℝ
      (fun s => X a b (γ s).1 (γ s).2) := by
    unfold X
    fun_prop
  have hV : Differentiable ℝ
      (fun s => Y c d (γ s).1 (γ s).2) := by
    unfold Y
    fun_prop
  have HU := (hU t).hasDerivAt.ofReal_comp
  have HV := (hV t).hasDerivAt.ofReal_comp
  have H := HasDerivAt.add HU
    (HasDerivAt.const_mul Complex.I HV)
  simpa [complexTransform] using H.deriv

private lemma curve_integrand_eq_logDeriv
    (a b c d : ℝ) (γ : ℝ → ℝ × ℝ) (t : ℝ)
    (hdet : determinant a b c d ≠ 0)
    (hγ : ContDiff ℝ 1 γ)
    (hγt : γ t ≠ (0, 0)) :
    P a b c d (γ t).1 (γ t).2 *
          deriv (fun s => (γ s).1) t +
        Q a b c d (γ t).1 (γ t).2 *
          deriv (fun s => (γ s).2) t =
      (deriv (complexTransform a b c d γ) t /
        complexTransform a b c d γ t).im := by
  have hγdiff : Differentiable ℝ γ :=
    hγ.differentiable (by norm_num)
  have hx : DifferentiableAt ℝ
      (fun s => (γ s).1) t := by fun_prop
  have hy : DifferentiableAt ℝ
      (fun s => (γ s).2) t := by fun_prop
  have hmain := gap2 a b c d γ t hx hy
  have hlog :
      (deriv (complexTransform a b c d γ) t /
          complexTransform a b c d γ t).im =
        (X a b (γ t).1 (γ t).2 *
              deriv (fun s =>
                Y c d (γ s).1 (γ s).2) t -
            Y c d (γ t).1 (γ t).2 *
              deriv (fun s =>
                X a b (γ s).1 (γ s).2) t) /
          denominator a b c d (γ t).1 (γ t).2 := by
    rw [complexTransform_deriv a b c d γ hγ t]
    simp only [complexTransform, Complex.div_im,
      Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      one_mul, mul_zero, zero_add, add_zero,
      Complex.normSq_apply, denominator]
    ring
  rw [hlog, hmain]
  have hden := denominator_ne a b c d
    (γ t).1 (γ t).2 hγt hdet
  unfold P Q
  field_simp [hden]
  ring

private theorem curveIntegral_eq_lift_increment
    (a b c d : ℝ) (γ : ℝ → ℝ × ℝ)
    (hdet : determinant a b c d ≠ 0)
    (hγ : ContDiff ℝ 1 γ)
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      γ t ≠ (0, 0)) :
    ∃ L : C(unitInterval, ℂ),
      (∀ u, Complex.exp (L u) =
        complexTransform a b c d γ
          ((2 * Real.pi) * (u : ℝ))) ∧
      curveIntegral a b c d γ = (L 1 - L 0).im := by
  have hT : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hw := complexTransform_contDiff a b c d γ hγ
  have hwne :
      ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        complexTransform a b c d γ t ≠ 0 := by
    intro t ht
    exact complexTransform_ne a b c d γ t hdet (hne t ht)
  obtain ⟨L, hL, hLint⟩ :=
    exists_log_lift_with_integral
      (2 * Real.pi) hT
      (complexTransform a b c d γ) hw hwne
  refine ⟨L, hL, ?_⟩
  calc
    curveIntegral a b c d γ =
        ∫ t in (0 : ℝ)..2 * Real.pi,
          (deriv (complexTransform a b c d γ) t /
            complexTransform a b c d γ t).im := by
      unfold curveIntegral
      apply intervalIntegral.integral_congr
      intro t ht
      exact curve_integrand_eq_logDeriv
        a b c d γ t hdet hγ (hne t (by
          simpa [Set.uIcc_of_le hT.le] using ht))
    _ = (L 1 - L 0).im := hLint.symm

private theorem curveIntegral_homotopy_invariant
    (a b c d : ℝ) (γ δ : ℝ → ℝ × ℝ)
    (hdet : determinant a b c d ≠ 0)
    (hHom : HomotopicAwayFromOrigin γ δ) :
    curveIntegral a b c d γ = curveIntegral a b c d δ := by
  rcases hHom with
    ⟨hγ, hδ, hγloop, hδloop, H, hHcont, hHslice,
      hHzero, hHone, hHloop, hHne⟩
  have hT : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hγne :
      ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        γ t ≠ (0, 0) := by
    intro t ht
    simpa [hHzero t ht] using hHne 0 ⟨le_rfl, by norm_num⟩ t ht
  have hδne :
      ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        δ t ≠ (0, 0) := by
    intro t ht
    simpa [hHone t ht] using hHne 1 ⟨by norm_num, le_rfl⟩ t ht
  obtain ⟨Lγ, hLγ, hIγ⟩ :=
    curveIntegral_eq_lift_increment
      a b c d γ hdet hγ hγne
  obtain ⟨Lδ, hLδ, hIδ⟩ :=
    curveIntegral_eq_lift_increment
      a b c d δ hdet hδ hδne
  have hscaled (s : unitInterval) :
      (2 * Real.pi) * (s : ℝ) ∈
        Set.Icc (0 : ℝ) (2 * Real.pi) :=
    ⟨mul_nonneg hT.le s.2.1,
      by simpa using mul_le_mul_of_nonneg_left s.2.2 hT.le⟩
  have hbase :
      Continuous (fun us : unitInterval × unitInterval =>
        H (us.1 : ℝ) ((2 * Real.pi) * (us.2 : ℝ))) := by
    have hu : Continuous
        (fun us : unitInterval × unitInterval => (us.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hs : Continuous
        (fun us : unitInterval × unitInterval =>
          (2 * Real.pi) * (us.2 : ℝ)) :=
      continuous_const.mul
        (continuous_subtype_val.comp continuous_snd)
    exact hHcont.comp (hu.prodMk hs)
  have hUcont :
      Continuous (fun us : unitInterval × unitInterval =>
        X a b
          (H (us.1 : ℝ)
            ((2 * Real.pi) * (us.2 : ℝ))).1
          (H (us.1 : ℝ)
            ((2 * Real.pi) * (us.2 : ℝ))).2) := by
    unfold X
    fun_prop
  have hVcont :
      Continuous (fun us : unitInterval × unitInterval =>
        Y c d
          (H (us.1 : ℝ)
            ((2 * Real.pi) * (us.2 : ℝ))).1
          (H (us.1 : ℝ)
            ((2 * Real.pi) * (us.2 : ℝ))).2) := by
    unfold Y
    fun_prop
  have hCcont :
      Continuous (fun us : unitInterval × unitInterval =>
        complexTransform a b c d (H (us.1 : ℝ))
          ((2 * Real.pi) * (us.2 : ℝ))) := by
    have hUc :
        Continuous (fun us : unitInterval × unitInterval =>
          (X a b
            (H (us.1 : ℝ)
              ((2 * Real.pi) * (us.2 : ℝ))).1
            (H (us.1 : ℝ)
              ((2 * Real.pi) * (us.2 : ℝ))).2 : ℂ)) :=
      Complex.ofRealCLM.continuous.comp hUcont
    have hVc :
        Continuous (fun us : unitInterval × unitInterval =>
          (Y c d
            (H (us.1 : ℝ)
              ((2 * Real.pi) * (us.2 : ℝ))).1
            (H (us.1 : ℝ)
              ((2 * Real.pi) * (us.2 : ℝ))).2 : ℂ)) :=
      Complex.ofRealCLM.continuous.comp hVcont
    exact hUc.add (continuous_const.mul hVc)
  let F : C(unitInterval × unitInterval,
      {z : ℂ // z ≠ 0}) :=
    ⟨fun us =>
      ⟨complexTransform a b c d (H (us.1 : ℝ))
          ((2 * Real.pi) * (us.2 : ℝ)),
        complexTransform_ne a b c d (H (us.1 : ℝ))
          ((2 * Real.pi) * (us.2 : ℝ)) hdet
          (hHne (us.1 : ℝ) us.1.2
            ((2 * Real.pi) * (us.2 : ℝ))
            (hscaled us.2))⟩,
      hCcont.subtype_mk _⟩
  have hFloop (u : unitInterval) :
      F (u, 0) = F (u, 1) := by
    apply Subtype.ext
    dsimp only [F, ContinuousMap.coe_mk]
    norm_num
    unfold complexTransform
    rw [hHloop (u : ℝ) u.2]
  have hLγF (s : unitInterval) :
      Complex.exp (Lγ s) = (F (0, s) : ℂ) := by
    rw [hLγ s]
    dsimp only [F, ContinuousMap.coe_mk]
    norm_num
    unfold complexTransform
    rw [hHzero _ (hscaled s)]
  have hLδF (s : unitInterval) :
      Complex.exp (Lδ s) = (F (1, s) : ℂ) := by
    rw [hLδ s]
    dsimp only [F, ContinuousMap.coe_mk]
    norm_num
    unfold complexTransform
    rw [hHone _ (hscaled s)]
  have hends :=
    exp_lift_endpoint_sub_eq_of_free_homotopy
      F hFloop Lγ Lδ hLγF hLδF
  rw [hIγ, hIδ, hends]

theorem gap6
    (a b c d : ℝ) (γ δ : ℝ → ℝ × ℝ)
    (hdet : determinant a b c d ≠ 0)
    (hHom : HomotopicAwayFromOrigin γ δ) :
    curveIntegral a b c d γ = curveIntegral a b c d δ := by
  exact curveIntegral_homotopy_invariant
    a b c d γ δ hdet hHom

theorem gap7
    (a b c d r : ℝ) (γ : ℝ → ℝ × ℝ)
    (hdet : determinant a b c d ≠ 0) (hr : 0 < r)
    (hHom : HomotopicAwayFromOrigin γ (smallEllipse a b c d r)) :
    normalizedIntegral a b c d γ =
      normalizedIntegral a b c d (smallEllipse a b c d r) := by
  unfold normalizedIntegral
  rw [gap6 a b c d γ (smallEllipse a b c d r) hdet hHom]

theorem gap8
    (a b c d r : ℝ)
    (hdet : determinant a b c d ≠ 0) (hr : 0 < r) :
    normalizedIntegral a b c d (smallEllipse a b c d r) =
      determinant a b c d / (2 * Real.pi * r ^ 2) *
        (∫ t in (0 : ℝ)..2 * Real.pi,
          (smallEllipse a b c d r t).1 *
              deriv (fun s => (smallEllipse a b c d r s).2) t -
            (smallEllipse a b c d r t).2 *
              deriv (fun s => (smallEllipse a b c d r s).1) t) := by
  exact normalized_smallEllipse_formula
    a b c d r hdet hr

theorem gap9
    (a b c d r : ℝ) (γ : ℝ → ℝ × ℝ)
    (hdet : determinant a b c d ≠ 0) (hr : 0 < r)
    (hHom : HomotopicAwayFromOrigin γ (smallEllipse a b c d r)) :
    normalizedIntegral a b c d γ =
      determinant a b c d / (2 * Real.pi * r ^ 2) *
        (∫ t in (0 : ℝ)..2 * Real.pi,
          (smallEllipse a b c d r t).1 *
              deriv (fun s => (smallEllipse a b c d r s).2) t -
            (smallEllipse a b c d r t).2 *
              deriv (fun s => (smallEllipse a b c d r s).1) t) := by
  rw [gap7 a b c d r γ hdet hr hHom,
    gap8 a b c d r hdet hr]

theorem gap10
    (a b c d r : ℝ)
    (hdet : determinant a b c d ≠ 0) (hr : 0 < r) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
        (smallEllipse a b c d r t).1 *
            deriv (fun s => (smallEllipse a b c d r s).2) t -
          (smallEllipse a b c d r t).2 *
            deriv (fun s => (smallEllipse a b c d r s).1) t) =
      ∫ _z in preimageDisk a b c d r, (2 : ℝ) := by
  exact boundary_eq_area a b c d r hdet hr

theorem gap11 (a b c d : ℝ) :
    (Matrix.of (fun i : Fin 2 => fun j : Fin 2 =>
      if i = 0 ∧ j = 0 then a
      else if i = 0 ∧ j = 1 then b
      else if i = 1 ∧ j = 0 then c
      else d)).det =
      determinant a b c d := by
  exact matrix_det_formula a b c d

theorem gap12
    (a b c d r : ℝ)
    (hdet : determinant a b c d ≠ 0) (hr : 0 < r) :
    determinant a b c d / (2 * Real.pi * r ^ 2) *
        (∫ _z in preimageDisk a b c d r, (2 : ℝ)) =
      determinant a b c d / (Real.pi * r ^ 2) *
        (∫ _w in transformedDisk r,
          (1 / |determinant a b c d| : ℝ)) := by
  exact transformed_change_formula a b c d r hdet hr

theorem gap13
    (a b c d r : ℝ)
    (hdet : determinant a b c d ≠ 0) (hr : 0 < r) :
    determinant a b c d / (Real.pi * r ^ 2) *
        (∫ _w in transformedDisk r,
          (1 / |determinant a b c d| : ℝ)) =
      SignType.sign (determinant a b c d) := by
  exact transformed_normalized_eq_sign
    a b c d r hdet hr

theorem gap14
    (a b c d r : ℝ) (γ : ℝ → ℝ × ℝ)
    (hdet : determinant a b c d ≠ 0) (hr : 0 < r)
    (hHom : HomotopicAwayFromOrigin γ (smallEllipse a b c d r)) :
    normalizedIntegral a b c d γ =
      SignType.sign (determinant a b c d) := by
  rw [gap9 a b c d r γ hdet hr hHom,
    gap10 a b c d r hdet hr,
    gap12 a b c d r hdet hr,
    gap13 a b c d r hdet hr]

end

end ProofGap.Exercise4321
