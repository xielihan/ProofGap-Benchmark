import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3216

noncomputable section

def radiusSq (x y : ℝ) : ℝ :=
  x ^ 2 + y ^ 2

def powThreeHalves (x y : ℝ) : ℝ :=
  Real.rpow (radiusSq x y) (3 / 2 : ℝ)

def powFiveHalves (x y : ℝ) : ℝ :=
  Real.rpow (radiusSq x y) (5 / 2 : ℝ)

def u (x y : ℝ) : ℝ :=
  x / Real.sqrt (radiusSq x y)

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def secondXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def secondYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def mixedXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

private theorem hasDerivAt_radiusSq_left (x y : ℝ) :
    HasDerivAt (fun t : ℝ => radiusSq t y) (2 * x) x := by
  simpa [radiusSq] using ((hasDerivAt_id x).pow 2).add_const (y ^ 2)

private theorem hasDerivAt_radiusSq_right (x y : ℝ) :
    HasDerivAt (fun t : ℝ => radiusSq x t) (2 * y) y := by
  simpa [radiusSq, add_comm] using
    ((hasDerivAt_id y).pow 2).const_add (x ^ 2)

private theorem explicitRpow_eq_exp_of_pos {z p : ℝ} (hz : 0 < z) :
    Real.rpow z p = Real.exp (Real.log z * p) := by
  exact Real.rpow_def_of_pos hz p

private theorem rpowHalf_eq_sqrt {x y : ℝ}
    (h : 0 < radiusSq x y) :
    Real.rpow (radiusSq x y) (1 / 2 : ℝ) =
      Real.sqrt (radiusSq x y) := by
  change (radiusSq x y) ^ (1 / 2 : ℝ) = Real.sqrt (radiusSq x y)
  simp only [Real.sqrt_eq_rpow]

private theorem powThreeHalves_eq_radius_mul_sqrt {x y : ℝ}
    (h : 0 < radiusSq x y) :
    powThreeHalves x y = radiusSq x y * Real.sqrt (radiusSq x y) := by
  unfold powThreeHalves
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num]
  calc
    Real.rpow (radiusSq x y) (1 + 1 / 2) =
        Real.exp (Real.log (radiusSq x y) * (1 + 1 / 2)) :=
      explicitRpow_eq_exp_of_pos h
    _ = Real.exp (Real.log (radiusSq x y)) *
          Real.exp (Real.log (radiusSq x y) * (1 / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = radiusSq x y *
          Real.exp (Real.log (radiusSq x y) * (1 / 2)) := by
      rw [Real.exp_log h]
    _ = radiusSq x y * Real.rpow (radiusSq x y) (1 / 2) := by
      rw [explicitRpow_eq_exp_of_pos h]
    _ = radiusSq x y * Real.sqrt (radiusSq x y) := by
      rw [rpowHalf_eq_sqrt h]

private theorem powFiveHalves_eq_radius_mul_three {x y : ℝ}
    (h : 0 < radiusSq x y) :
    powFiveHalves x y = radiusSq x y * powThreeHalves x y := by
  unfold powFiveHalves powThreeHalves
  rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num]
  calc
    Real.rpow (radiusSq x y) (1 + 3 / 2) =
        Real.exp (Real.log (radiusSq x y) * (1 + 3 / 2)) :=
      explicitRpow_eq_exp_of_pos h
    _ = Real.exp (Real.log (radiusSq x y)) *
          Real.exp (Real.log (radiusSq x y) * (3 / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = radiusSq x y *
          Real.exp (Real.log (radiusSq x y) * (3 / 2)) := by
      rw [Real.exp_log h]
    _ = radiusSq x y * Real.rpow (radiusSq x y) (3 / 2) := by
      rw [explicitRpow_eq_exp_of_pos h]

private theorem powThreeHalves_ne_zero {x y : ℝ}
    (h : 0 < radiusSq x y) : powThreeHalves x y ≠ 0 := by
  unfold powThreeHalves
  exact ne_of_gt (Real.rpow_pos_of_pos h _)

private theorem powFiveHalves_ne_zero {x y : ℝ}
    (h : 0 < radiusSq x y) : powFiveHalves x y ≠ 0 := by
  unfold powFiveHalves
  exact ne_of_gt (Real.rpow_pos_of_pos h _)

private theorem powThreeHalves_sq_eq_sqrt_mul_powFive {x y : ℝ}
    (h : 0 < radiusSq x y) :
    powThreeHalves x y ^ 2 =
      Real.sqrt (radiusSq x y) * powFiveHalves x y := by
  rw [powThreeHalves_eq_radius_mul_sqrt h,
    powFiveHalves_eq_radius_mul_three h,
    powThreeHalves_eq_radius_mul_sqrt h]
  ring

private theorem eventually_radiusSq_pos_left {x y : ℝ}
    (h : 0 < radiusSq x y) :
    ∀ᶠ t in nhds x, 0 < radiusSq t y := by
  have hc : ContinuousAt (fun t : ℝ => radiusSq t y) x := by
    simpa [radiusSq] using
      (continuousAt_id.pow 2).add
        (continuousAt_const : ContinuousAt (fun _ : ℝ => y ^ 2) x)
  exact hc.eventually (Ioi_mem_nhds h)

private theorem eventually_radiusSq_pos_right {x y : ℝ}
    (h : 0 < radiusSq x y) :
    ∀ᶠ t in nhds y, 0 < radiusSq x t := by
  have hc : ContinuousAt (fun t : ℝ => radiusSq x t) y := by
    simpa [radiusSq] using
      (continuousAt_const : ContinuousAt (fun _ : ℝ => x ^ 2) y).add
        (continuousAt_id.pow 2)
  exact hc.eventually (Ioi_mem_nhds h)

theorem gap1 :
    ∀ x y : ℝ, 0 < radiusSq x y →
      partialX u x y =
        1 / Real.sqrt (radiusSq x y) -
          (2 * x * x) / (2 * powThreeHalves x y) := by
  intro x y h
  have hs :
      HasDerivAt (fun t : ℝ => Real.sqrt (radiusSq t y))
        ((1 / (2 * Real.sqrt (radiusSq x y))) * (2 * x)) x := by
    exact (Real.hasDerivAt_sqrt (ne_of_gt h)).comp x
      (hasDerivAt_radiusSq_left x y)
  have hu := (hasDerivAt_id x).div hs (Real.sqrt_ne_zero'.mpr h)
  unfold partialX u
  calc
    deriv (fun t : ℝ => t / Real.sqrt (radiusSq t y)) x =
        (Real.sqrt (radiusSq x y) -
          x * ((1 / (2 * Real.sqrt (radiusSq x y))) * (2 * x))) /
            Real.sqrt (radiusSq x y) ^ 2 := by
      simpa using hu.deriv
    _ = 1 / Real.sqrt (radiusSq x y) -
          (2 * x * x) / (2 * powThreeHalves x y) := by
      rw [powThreeHalves_eq_radius_mul_sqrt h]
      field_simp [ne_of_gt h, Real.sqrt_ne_zero'.mpr h]
      rw [Real.sq_sqrt h.le]
      unfold radiusSq
      ring

theorem gap2 :
    ∀ x y : ℝ, 0 < radiusSq x y →
      1 / Real.sqrt (radiusSq x y) -
          (2 * x * x) / (2 * powThreeHalves x y) =
        y ^ 2 / powThreeHalves x y := by
  intro x y h
  rw [powThreeHalves_eq_radius_mul_sqrt h]
  field_simp [ne_of_gt h, Real.sqrt_ne_zero'.mpr h]
  unfold radiusSq
  ring

theorem gap3 :
    ∀ x y : ℝ, 0 < radiusSq x y →
      partialX u x y = y ^ 2 / powThreeHalves x y := by
  intro x y h
  exact (gap1 x y h).trans (gap2 x y h)

theorem gap4 :
    ∀ x y : ℝ, 0 < radiusSq x y →
      partialY u x y = -(x * y / powThreeHalves x y) := by
  intro x y h
  have hs :
      HasDerivAt (fun t : ℝ => Real.sqrt (radiusSq x t))
        ((1 / (2 * Real.sqrt (radiusSq x y))) * (2 * y)) y := by
    exact (Real.hasDerivAt_sqrt (ne_of_gt h)).comp y
      (hasDerivAt_radiusSq_right x y)
  have hc : HasDerivAt (fun _ : ℝ => x) 0 y :=
    hasDerivAt_const (x := y) (c := x)
  have hu := hc.div hs (Real.sqrt_ne_zero'.mpr h)
  unfold partialY u
  calc
    deriv (fun t : ℝ => x / Real.sqrt (radiusSq x t)) y =
        -(x * ((1 / (2 * Real.sqrt (radiusSq x y))) * (2 * y))) /
          Real.sqrt (radiusSq x y) ^ 2 := by
      simpa using hu.deriv
    _ = -(x * y / powThreeHalves x y) := by
      rw [powThreeHalves_eq_radius_mul_sqrt h,
        Real.sq_sqrt h.le]
      field_simp [ne_of_gt h, Real.sqrt_ne_zero'.mpr h]

theorem gap5 :
    ∀ x y : ℝ, 0 < radiusSq x y →
      secondXX u x y =
        -(3 / 2 : ℝ) * y ^ 2 *
          ((2 * x) / powFiveHalves x y) := by
  intro x y h
  have heq :
      (fun t : ℝ => partialX u t y) =ᶠ[nhds x]
        (fun t : ℝ => y ^ 2 / powThreeHalves t y) :=
    (eventually_radiusSq_pos_left h).mono (fun t ht => gap3 t y ht)
  have hp :
      HasDerivAt (fun t : ℝ => powThreeHalves t y)
        ((3 / 2 : ℝ) *
          Real.rpow (radiusSq x y) ((3 / 2 : ℝ) - 1) * (2 * x)) x := by
    unfold powThreeHalves
    exact
      (Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ))
        (Or.inl (ne_of_gt h))).comp x (hasDerivAt_radiusSq_left x y)
  have hc : HasDerivAt (fun _ : ℝ => y ^ 2) 0 x :=
    hasDerivAt_const (x := x) (c := y ^ 2)
  have hq := hc.div hp (powThreeHalves_ne_zero h)
  unfold secondXX
  calc
    deriv (fun t : ℝ => partialX u t y) x =
        deriv (fun t : ℝ => y ^ 2 / powThreeHalves t y) x :=
      heq.deriv_eq
    _ = -(y ^ 2 *
          ((3 / 2 : ℝ) *
            Real.rpow (radiusSq x y) ((3 / 2 : ℝ) - 1) * (2 * x))) /
          powThreeHalves x y ^ 2 := by
      simpa using hq.deriv
    _ = -(3 / 2 : ℝ) * y ^ 2 *
          ((2 * x) / powFiveHalves x y) := by
      rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num,
        rpowHalf_eq_sqrt h,
        powThreeHalves_sq_eq_sqrt_mul_powFive h]
      field_simp [Real.sqrt_ne_zero'.mpr h, powFiveHalves_ne_zero h] <;>
        ring

theorem gap6 :
    ∀ y x : ℝ, 0 < radiusSq x y →
      -(3 / 2 : ℝ) * y ^ 2 *
          ((2 * x) / powFiveHalves x y) =
        -(3 * x * y ^ 2 / powFiveHalves x y) := by
  intro y x h
  ring

theorem gap7 :
    ∀ x y : ℝ, 0 < radiusSq x y →
      secondXX u x y =
        -(3 * x * y ^ 2 / powFiveHalves x y) := by
  intro x y h
  exact (gap5 x y h).trans (gap6 y x h)

theorem gap8 :
    ∀ x y : ℝ, 0 < radiusSq x y →
      secondYY u x y =
        -(x / powThreeHalves x y) +
          (3 / 2 : ℝ) * x * y *
            ((2 * y) / powFiveHalves x y) := by
  intro x y h
  have heq :
      (fun t : ℝ => partialY u x t) =ᶠ[nhds y]
        (fun t : ℝ => -(x * t / powThreeHalves x t)) :=
    (eventually_radiusSq_pos_right h).mono (fun t ht => gap4 x t ht)
  have hp :
      HasDerivAt (fun t : ℝ => powThreeHalves x t)
        ((3 / 2 : ℝ) *
          Real.rpow (radiusSq x y) ((3 / 2 : ℝ) - 1) * (2 * y)) y := by
    unfold powThreeHalves
    exact
      (Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ))
        (Or.inl (ne_of_gt h))).comp y (hasDerivAt_radiusSq_right x y)
  have hn : HasDerivAt (fun t : ℝ => x * t) x y := by
    simpa using
      (hasDerivAt_const (x := y) (c := x)).mul (hasDerivAt_id y)
  have hq := (hn.div hp (powThreeHalves_ne_zero h)).neg
  unfold secondYY
  calc
    deriv (fun t : ℝ => partialY u x t) y =
        deriv (fun t : ℝ => -(x * t / powThreeHalves x t)) y :=
      heq.deriv_eq
    _ = -((x * powThreeHalves x y -
          x * y * ((3 / 2 : ℝ) *
            Real.rpow (radiusSq x y) ((3 / 2 : ℝ) - 1) * (2 * y))) /
          powThreeHalves x y ^ 2) := by
      simpa using hq.deriv
    _ = -(x / powThreeHalves x y) +
          (3 / 2 : ℝ) * x * y *
            ((2 * y) / powFiveHalves x y) := by
      rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num,
        rpowHalf_eq_sqrt h,
        powThreeHalves_sq_eq_sqrt_mul_powFive h]
      field_simp [Real.sqrt_ne_zero'.mpr h, powThreeHalves_ne_zero h,
        powFiveHalves_ne_zero h]
      calc
        -(x * powThreeHalves x y *
            (powThreeHalves x y -
              y ^ 2 * 3 * Real.sqrt (radiusSq x y))) =
            -x * powThreeHalves x y ^ 2 +
              3 * x * powThreeHalves x y * y ^ 2 *
                Real.sqrt (radiusSq x y) := by
          ring
        _ = -x *
              (Real.sqrt (radiusSq x y) * powFiveHalves x y) +
              3 * x * powThreeHalves x y * y ^ 2 *
                Real.sqrt (radiusSq x y) := by
          rw [powThreeHalves_sq_eq_sqrt_mul_powFive h]
        _ = x * Real.sqrt (radiusSq x y) *
              (-powFiveHalves x y +
                powThreeHalves x y * y ^ 2 * 3) := by
          ring

theorem gap9 :
    ∀ x y : ℝ, 0 < radiusSq x y →
      -(x / powThreeHalves x y) +
          (3 / 2 : ℝ) * x * y *
            ((2 * y) / powFiveHalves x y) =
        x * (2 * y ^ 2 - x ^ 2) / powFiveHalves x y := by
  intro x y h
  rw [powFiveHalves_eq_radius_mul_three h]
  field_simp [ne_of_gt h, powThreeHalves_ne_zero h]
  unfold radiusSq
  ring

theorem gap10 :
    ∀ x y : ℝ, 0 < radiusSq x y →
      secondYY u x y =
        x * (2 * y ^ 2 - x ^ 2) / powFiveHalves x y := by
  intro x y h
  exact (gap8 x y h).trans (gap9 x y h)

theorem gap11 :
    ∀ x y : ℝ, 0 < radiusSq x y →
      mixedXY u x y =
        2 * y / powThreeHalves x y -
          3 * y ^ 3 / powFiveHalves x y := by
  intro x y h
  have heq :
      (fun t : ℝ => partialX u x t) =ᶠ[nhds y]
        (fun t : ℝ => t ^ 2 / powThreeHalves x t) :=
    (eventually_radiusSq_pos_right h).mono (fun t ht => gap3 x t ht)
  have hp :
      HasDerivAt (fun t : ℝ => powThreeHalves x t)
        ((3 / 2 : ℝ) *
          Real.rpow (radiusSq x y) ((3 / 2 : ℝ) - 1) * (2 * y)) y := by
    unfold powThreeHalves
    exact
      (Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ))
        (Or.inl (ne_of_gt h))).comp y (hasDerivAt_radiusSq_right x y)
  have hn : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_id y).pow 2
  have hq := hn.div hp (powThreeHalves_ne_zero h)
  unfold mixedXY
  calc
    deriv (fun t : ℝ => partialX u x t) y =
        deriv (fun t : ℝ => t ^ 2 / powThreeHalves x t) y :=
      heq.deriv_eq
    _ = ((2 * y) * powThreeHalves x y -
          y ^ 2 * ((3 / 2 : ℝ) *
            Real.rpow (radiusSq x y) ((3 / 2 : ℝ) - 1) * (2 * y))) /
          powThreeHalves x y ^ 2 := by
      simpa using hq.deriv
    _ = 2 * y / powThreeHalves x y -
          3 * y ^ 3 / powFiveHalves x y := by
      rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num,
        rpowHalf_eq_sqrt h,
        powThreeHalves_sq_eq_sqrt_mul_powFive h]
      field_simp [Real.sqrt_ne_zero'.mpr h, powThreeHalves_ne_zero h,
        powFiveHalves_ne_zero h]
      calc
        y * powThreeHalves x y *
            (2 * powThreeHalves x y -
              y ^ 2 * 3 * Real.sqrt (radiusSq x y)) =
            2 * y * powThreeHalves x y ^ 2 -
              3 * y * powThreeHalves x y * y ^ 2 *
                Real.sqrt (radiusSq x y) := by
          ring
        _ = 2 * y *
              (Real.sqrt (radiusSq x y) * powFiveHalves x y) -
              3 * y * powThreeHalves x y * y ^ 2 *
                Real.sqrt (radiusSq x y) := by
          rw [powThreeHalves_sq_eq_sqrt_mul_powFive h]
        _ = y * Real.sqrt (radiusSq x y) *
              (2 * powFiveHalves x y -
                y ^ 2 * powThreeHalves x y * 3) := by
          ring

theorem gap12 :
    ∀ y x : ℝ, 0 < radiusSq x y →
      2 * y / powThreeHalves x y -
          3 * y ^ 3 / powFiveHalves x y =
        y * (2 * x ^ 2 - y ^ 2) / powFiveHalves x y := by
  intro y x h
  rw [powFiveHalves_eq_radius_mul_three h]
  field_simp [ne_of_gt h, powThreeHalves_ne_zero h]
  unfold radiusSq
  ring

theorem gap13 :
    ∀ x y : ℝ, 0 < radiusSq x y →
      mixedXY u x y =
        y * (2 * x ^ 2 - y ^ 2) / powFiveHalves x y := by
  intro x y h
  exact (gap11 x y h).trans (gap12 y x h)

end

end ProofGap.Exercise3216
