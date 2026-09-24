import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

namespace ProofGap.Exercise2355
noncomputable section

open MeasureTheory

def radicandRoot (a b t : ℝ) : ℝ := Real.sqrt (t ^ 2 + 4 * a * b)
def change (a b x : ℝ) : ℝ := a * x - b / x
def inverseChange (a b t : ℝ) : ℝ :=
  (t + radicandRoot a b t) / (2 * a)
def jacobian (a b t : ℝ) : ℝ :=
  (1 / (2 * a)) * (t + radicandRoot a b t) / radicandRoot a b t

def lhs (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), f (a * x + b / x)
def wholeRhs (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  (1 / (2 * a)) *
    ∫ t : ℝ, f (radicandRoot a b t) *
      ((t + radicandRoot a b t) / radicandRoot a b t)
def negativeRhs (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  (1 / (2 * a)) *
    ∫ t in Set.Iio (0 : ℝ), f (radicandRoot a b t) *
      ((t + radicandRoot a b t) / radicandRoot a b t)
def positiveRhs (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  (1 / (2 * a)) *
    ∫ t in Set.Ioi (0 : ℝ), f (radicandRoot a b t) *
      ((t + radicandRoot a b t) / radicandRoot a b t)
def reflectedNegativeRhs (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  (1 / (2 * a)) *
    ∫ t in Set.Ioi (0 : ℝ), f (radicandRoot a b t) *
      ((radicandRoot a b t - t) / radicandRoot a b t)
def combinedRhs (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  (1 / (2 * a)) *
    ∫ t in Set.Ioi (0 : ℝ), f (radicandRoot a b t) *
      ((radicandRoot a b t - t + radicandRoot a b t + t) /
        radicandRoot a b t)
def finalRhs (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  (1 / a) * ∫ t in Set.Ioi (0 : ℝ), f (radicandRoot a b t)

def Admissible (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  IntegrableOn (fun x => f (a * x + b / x)) (Set.Ioi 0) ∧
  Integrable (fun t => f (radicandRoot a b t) *
    ((t + radicandRoot a b t) / radicandRoot a b t)) ∧
  IntegrableOn (fun t => f (radicandRoot a b t)) (Set.Ioi 0)

private theorem radicand_pos (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < t ^ 2 + 4 * a * b := by
  nlinarith [mul_pos ha hb]

theorem gap1 (a b x t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (ht : change a b x = t) :
    a * x + b / x = radicandRoot a b t := by
  have hrad : (change a b x) ^ 2 + 4 * a * b = (a * x + b / x) ^ 2 := by
    unfold change
    field_simp [hx.ne']
    ring
  have hsum : 0 < a * x + b / x := by positivity
  unfold radicandRoot
  rw [← ht, hrad, Real.sqrt_sq_eq_abs, abs_of_pos hsum]

theorem gap2 (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) :
    inverseChange a b t =
      (t + Real.sqrt (t ^ 2 + 4 * a * b)) / (2 * a) := by
  rfl

theorem gap3 (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (inverseChange a b) (jacobian a b t) t := by
  have hrad : 0 < t ^ 2 + 4 * a * b := radicand_pos a b t ha hb
  have hinner : HasDerivAt (fun u : ℝ => u ^ 2 + 4 * a * b) (2 * t) t := by
    convert ((hasDerivAt_id t).pow 2).add_const (4 * a * b) using 1 <;>
      simp [id] <;> ring
  have hsqrt := hinner.sqrt hrad.ne'
  have hraw := ((hasDerivAt_id t).add hsqrt).div_const (2 * a)
  have hr0 : Real.sqrt (t ^ 2 + 4 * a * b) ≠ 0 := (Real.sqrt_pos.2 hrad).ne'
  unfold inverseChange jacobian radicandRoot
  convert hraw using 1
  field_simp [ha.ne', hr0]
  ring

private theorem inverseChange_pos (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < inverseChange a b t := by
  have hsq : t ^ 2 < t ^ 2 + 4 * a * b := by nlinarith [mul_pos ha hb]
  have hneg : -Real.sqrt (t ^ 2 + 4 * a * b) < t :=
    Real.neg_sqrt_lt_of_sq_lt hsq
  unfold inverseChange radicandRoot
  exact div_pos (by linarith) (by positivity)

private theorem change_inverseChange (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) :
    change a b (inverseChange a b t) = t := by
  let r := Real.sqrt (t ^ 2 + 4 * a * b)
  have hrad : 0 < t ^ 2 + 4 * a * b := radicand_pos a b t ha hb
  have hr2 : r ^ 2 = t ^ 2 + 4 * a * b := by
    simpa [r] using Real.sq_sqrt hrad.le
  have hsq : t ^ 2 < t ^ 2 + 4 * a * b := by nlinarith [mul_pos ha hb]
  have hneg : -r < t := by
    simpa [r] using Real.neg_sqrt_lt_of_sq_lt hsq
  have hnum : t + r ≠ 0 := by linarith
  have hfrac : b / ((t + r) / (2 * a)) = (r - t) / 2 := by
    field_simp [ha.ne', hnum]
    nlinarith [hr2]
  unfold change inverseChange radicandRoot
  change a * ((t + r) / (2 * a)) - b / ((t + r) / (2 * a)) = t
  rw [hfrac]
  field_simp [ha.ne']
  ring

private theorem inverseChange_change (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) : inverseChange a b (change a b x) = x := by
  have hroot := gap1 a b x (change a b x) ha hb hx rfl
  unfold inverseChange
  rw [← hroot]
  unfold change
  field_simp [ha.ne', hx.ne']
  ring

private theorem jacobian_pos (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < jacobian a b t := by
  have hrad : 0 < t ^ 2 + 4 * a * b := radicand_pos a b t ha hb
  have hrpos : 0 < Real.sqrt (t ^ 2 + 4 * a * b) := Real.sqrt_pos.2 hrad
  have hsq : t ^ 2 < t ^ 2 + 4 * a * b := by nlinarith [mul_pos ha hb]
  have hneg : -Real.sqrt (t ^ 2 + 4 * a * b) < t :=
    Real.neg_sqrt_lt_of_sq_lt hsq
  unfold jacobian radicandRoot
  exact div_pos (mul_pos (one_div_pos.mpr (by positivity)) (by linarith)) hrpos

private theorem inverseChange_image_univ (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    inverseChange a b '' Set.univ = Set.Ioi 0 := by
  ext x
  constructor
  · rintro ⟨t, -, rfl⟩
    exact inverseChange_pos a b t ha hb
  · intro hx
    exact ⟨change a b x, Set.mem_univ _, inverseChange_change a b x ha hb hx⟩

private theorem sum_inverseChange (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a * inverseChange a b t + b / inverseChange a b t = radicandRoot a b t :=
  gap1 a b (inverseChange a b t) t ha hb (inverseChange_pos a b t ha hb)
    (change_inverseChange a b t ha hb)

private theorem wholeIntegrand_reflect (a b t : ℝ) (f : ℝ → ℝ) :
    f (radicandRoot a b (-t)) *
        ((-t + radicandRoot a b (-t)) / radicandRoot a b (-t)) =
      f (radicandRoot a b t) *
        ((radicandRoot a b t - t) / radicandRoot a b t) := by
  have hr : radicandRoot a b (-t) = radicandRoot a b t := by
    unfold radicandRoot
    congr 2
    ring
  rw [hr]
  ring

theorem gap4 (a b : ℝ) (f : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hf : Admissible a b f) :
    lhs a b f = wholeRhs a b f := by
  have hmono : Monotone (inverseChange a b) :=
    (strictMono_of_hasDerivAt_pos (gap3 a b · ha hb)
      (jacobian_pos a b · ha hb)).monotone
  have hcv := integral_image_eq_integral_deriv_smul_of_monotoneOn
    (s := Set.univ) (f := inverseChange a b) (f' := jacobian a b)
    MeasurableSet.univ (fun t _ => (gap3 a b t ha hb).hasDerivWithinAt)
    (hmono.monotoneOn Set.univ) (fun x => f (a * x + b / x))
  rw [inverseChange_image_univ a b ha hb] at hcv
  simp only [setIntegral_univ, smul_eq_mul, sum_inverseChange a b _ ha hb] at hcv
  have hfirst : lhs a b f =
      ∫ t : ℝ, jacobian a b t * f (radicandRoot a b t) := by
    unfold lhs
    exact hcv
  calc
    lhs a b f = ∫ t : ℝ, jacobian a b t * f (radicandRoot a b t) := hfirst
    _ = (1 / (2 * a)) * ∫ t : ℝ,
        f (radicandRoot a b t) *
          ((t + radicandRoot a b t) / radicandRoot a b t) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      unfold jacobian
      ring
    _ = wholeRhs a b f := rfl

theorem gap5 (a b : ℝ) (f : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hf : Admissible a b f) :
    lhs a b f = negativeRhs a b f + positiveRhs a b f := by
  let G : ℝ → ℝ := fun t => f (radicandRoot a b t) *
    ((t + radicandRoot a b t) / radicandRoot a b t)
  have hsplit : (∫ t : ℝ, G t) =
      (∫ t in Set.Iio (0 : ℝ), G t) + ∫ t in Set.Ioi (0 : ℝ), G t := by
    rw [← setIntegral_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)),
      setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        hf.2.1.integrableOn hf.2.1.integrableOn,
      integral_Iic_eq_integral_Iio]
  rw [gap4 a b f ha hb hf]
  unfold wholeRhs negativeRhs positiveRhs
  change (1 / (2 * a)) * ∫ t : ℝ, G t =
    (1 / (2 * a)) * (∫ t in Set.Iio (0 : ℝ), G t) +
      (1 / (2 * a)) * ∫ t in Set.Ioi (0 : ℝ), G t
  rw [hsplit]
  ring

theorem gap6 (a b : ℝ) (f : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hf : Admissible a b f) :
    lhs a b f = reflectedNegativeRhs a b f + positiveRhs a b f := by
  let G : ℝ → ℝ := fun t => f (radicandRoot a b t) *
    ((t + radicandRoot a b t) / radicandRoot a b t)
  let R : ℝ → ℝ := fun t => f (radicandRoot a b t) *
    ((radicandRoot a b t - t) / radicandRoot a b t)
  have hreflect : (∫ t in Set.Iio (0 : ℝ), G t) =
      ∫ t in Set.Ioi (0 : ℝ), R t := by
    calc
      (∫ t in Set.Iio (0 : ℝ), G t) = ∫ t in Set.Iic (0 : ℝ), G t :=
        integral_Iic_eq_integral_Iio.symm
      _ = ∫ t in Set.Ioi (0 : ℝ), G (-t) := by
        simpa using (integral_comp_neg_Ioi 0 G).symm
      _ = ∫ t in Set.Ioi (0 : ℝ), R t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        exact wholeIntegrand_reflect a b t f
  calc
    lhs a b f = negativeRhs a b f + positiveRhs a b f := gap5 a b f ha hb hf
    _ = reflectedNegativeRhs a b f + positiveRhs a b f := by
      unfold negativeRhs reflectedNegativeRhs positiveRhs
      change (1 / (2 * a)) * (∫ t in Set.Iio (0 : ℝ), G t) + _ =
        (1 / (2 * a)) * (∫ t in Set.Ioi (0 : ℝ), R t) + _
      rw [hreflect]

theorem gap7 (a b : ℝ) (f : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hf : Admissible a b f) :
    lhs a b f = combinedRhs a b f := by
  let G : ℝ → ℝ := fun t => f (radicandRoot a b t) *
    ((t + radicandRoot a b t) / radicandRoot a b t)
  let R : ℝ → ℝ := fun t => f (radicandRoot a b t) *
    ((radicandRoot a b t - t) / radicandRoot a b t)
  let P : ℝ → ℝ := fun t => f (radicandRoot a b t) *
    ((t + radicandRoot a b t) / radicandRoot a b t)
  have hRint : IntegrableOn R (Set.Ioi (0 : ℝ)) := by
    apply hf.2.1.comp_neg.integrableOn.congr_fun _ measurableSet_Ioi
    intro t _
    exact wholeIntegrand_reflect a b t f
  have hPint : IntegrableOn P (Set.Ioi (0 : ℝ)) := hf.2.1.integrableOn
  calc
    lhs a b f = reflectedNegativeRhs a b f + positiveRhs a b f :=
      gap6 a b f ha hb hf
    _ = combinedRhs a b f := by
      unfold reflectedNegativeRhs positiveRhs combinedRhs
      change (1 / (2 * a)) * (∫ t in Set.Ioi (0 : ℝ), R t) +
          (1 / (2 * a)) * (∫ t in Set.Ioi (0 : ℝ), P t) =
        (1 / (2 * a)) * ∫ t in Set.Ioi (0 : ℝ),
          f (radicandRoot a b t) *
            ((radicandRoot a b t - t + radicandRoot a b t + t) /
              radicandRoot a b t)
      rw [← mul_add, ← integral_add hRint hPint]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp [R, P]
      ring

theorem gap8 (a b : ℝ) (f : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hf : Admissible a b f) :
    lhs a b f = finalRhs a b f := by
  have hInt :
      (∫ t in Set.Ioi (0 : ℝ), f (radicandRoot a b t) *
        ((radicandRoot a b t - t + radicandRoot a b t + t) /
          radicandRoot a b t)) =
        2 * ∫ t in Set.Ioi (0 : ℝ), f (radicandRoot a b t) := by
    calc
      _ = ∫ t in Set.Ioi (0 : ℝ), 2 * f (radicandRoot a b t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        have hr0 : radicandRoot a b t ≠ 0 := by
          unfold radicandRoot
          exact (Real.sqrt_pos.2 (radicand_pos a b t ha hb)).ne'
        field_simp [hr0]
        ring
      _ = 2 * ∫ t in Set.Ioi (0 : ℝ), f (radicandRoot a b t) :=
        integral_const_mul 2 _
  calc
    lhs a b f = combinedRhs a b f := gap7 a b f ha hb hf
    _ = finalRhs a b f := by
      unfold combinedRhs finalRhs
      rw [hInt]
      field_simp [ha.ne']

theorem gap9 (a b : ℝ) (f : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hf : Admissible a b f) :
    lhs a b f =
      (1 / a) * ∫ x in Set.Ioi (0 : ℝ), f (Real.sqrt (x ^ 2 + 4 * a * b) ) := by
  simpa [finalRhs, radicandRoot] using gap8 a b f ha hb hf

theorem gap10 (a b : ℝ) (f : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hf : Admissible a b f) :
    lhs a b f = finalRhs a b f := gap8 a b f ha hb hf

end
end ProofGap.Exercise2355
