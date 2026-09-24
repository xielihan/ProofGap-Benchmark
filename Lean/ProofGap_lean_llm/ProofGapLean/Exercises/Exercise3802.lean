import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3802

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Topology

def integrand (α β x : ℝ) : ℝ :=
  Real.log (1 + α ^ 2 * x ^ 2) *
    Real.log (1 + β ^ 2 * x ^ 2) / x ^ 4

def I (α β : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), integrand α β x

def J (α β : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    2 * α * Real.log (1 + β ^ 2 * x ^ 2) /
      (x ^ 2 * (1 + α ^ 2 * x ^ 2))

def K (α β : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    4 * α * β /
      ((1 + α ^ 2 * x ^ 2) * (1 + β ^ 2 * x ^ 2))

def closedForm (α β : ℝ) : ℝ :=
  2 * Real.pi / 3 *
    (α * β * (α + β) +
      α ^ 3 * Real.log α + β ^ 3 * Real.log β -
      (α ^ 3 + β ^ 3) * Real.log (α + β))

private def oneKernel (a x : ℝ) : ℝ :=
  1 / (1 + a ^ 2 * x ^ 2)

private def onePrimitive (a x : ℝ) : ℝ :=
  Real.arctan (a * x) / a

private theorem onePrimitive_hasDerivAt
    (a x : ℝ) (ha : 0 < a) :
    HasDerivAt (onePrimitive a) (oneKernel a x) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => a * y) a x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul a
  have h :=
    ((Real.hasDerivAt_arctan (a * x)).comp x hinner).div_const a
  unfold onePrimitive oneKernel
  convert h using 1
  field_simp [ha.ne']

private theorem onePrimitive_tendsto
    (a : ℝ) (ha : 0 < a) :
    Tendsto (onePrimitive a) atTop
      (𝓝 (Real.pi / (2 * a))) := by
  have harg :
      Tendsto (fun x : ℝ => a * x) atTop atTop :=
    tendsto_id.const_mul_atTop ha
  have hatan :
      Tendsto (fun x : ℝ => Real.arctan (a * x))
        atTop (𝓝 (Real.pi / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin
      (Real.tendsto_arctan_atTop.comp harg)
  simpa only [onePrimitive, div_div] using hatan.div_const a

private theorem oneKernel_nonneg (a x : ℝ) :
    0 ≤ oneKernel a x := by
  unfold oneKernel
  positivity

private theorem oneKernel_integrable
    (a : ℝ) (ha : 0 < a) :
    IntegrableOn (oneKernel a) (Ioi (0 : ℝ)) volume := by
  exact integrableOn_Ioi_deriv_of_nonneg
    (by
      unfold onePrimitive
      fun_prop)
    (fun x _ => onePrimitive_hasDerivAt a x ha)
    (fun x _ => oneKernel_nonneg a x)
    (onePrimitive_tendsto a ha)

private theorem oneKernel_integral
    (a : ℝ) (ha : 0 < a) :
    (∫ x in Ioi (0 : ℝ), oneKernel a x ∂volume) =
      Real.pi / (2 * a) := by
  have h :=
    integral_Ioi_of_hasDerivAt_of_tendsto
      (by
        unfold onePrimitive
        fun_prop)
      (fun x _ => onePrimitive_hasDerivAt a x ha)
      (oneKernel_integrable a ha)
      (onePrimitive_tendsto a ha)
  simpa [onePrimitive] using h

private def squareOneKernel (a x : ℝ) : ℝ :=
  1 / (1 + a ^ 2 * x ^ 2) ^ 2

private def squareOnePrimitive (a x : ℝ) : ℝ :=
  Real.arctan (a * x) / (2 * a) +
    x / (2 * (1 + a ^ 2 * x ^ 2))

private theorem squareOnePrimitive_hasDerivAt
    (a x : ℝ) (ha : 0 < a) :
    HasDerivAt (squareOnePrimitive a)
      (squareOneKernel a x) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => a * y) a x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul a
  have hatan :=
    ((Real.hasDerivAt_arctan (a * x)).comp x hinner).div_const (2 * a)
  have hden :
      HasDerivAt (fun y : ℝ => 2 * (1 + a ^ 2 * y ^ 2))
        (4 * a ^ 2 * x) x := by
    convert
      ((hasDerivAt_const x 1).add
        (((hasDerivAt_id x).pow 2).const_mul (a ^ 2))).const_mul 2
      using 1 <;>
      simp only [id_eq] <;> ring
  have hquot :=
    (hasDerivAt_id x).div hden
      (by positivity : 2 * (1 + a ^ 2 * x ^ 2) ≠ 0)
  simp only [id_eq] at hquot
  unfold squareOnePrimitive squareOneKernel
  convert hatan.add hquot using 1
  field_simp [ha.ne']
  ring

private theorem squareOnePrimitive_continuous
    (a : ℝ) (ha : 0 < a) :
    Continuous (squareOnePrimitive a) := by
  unfold squareOnePrimitive
  apply Continuous.add
  · fun_prop
  · apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x
      positivity

private theorem squareOnePrimitive_tendsto
    (a : ℝ) (ha : 0 < a) :
    Tendsto (squareOnePrimitive a) atTop
      (𝓝 (Real.pi / (4 * a))) := by
  have harg :
      Tendsto (fun x : ℝ => a * x) atTop atTop :=
    tendsto_id.const_mul_atTop ha
  have hatan :
      Tendsto (fun x : ℝ => Real.arctan (a * x) / (2 * a))
        atTop (𝓝 (Real.pi / (4 * a))) := by
    have h :=
      (tendsto_nhds_of_tendsto_nhdsWithin
        (Real.tendsto_arctan_atTop.comp harg)).div_const (2 * a)
    convert h using 1 <;> ring
  have hratio :
      Tendsto (fun x : ℝ => x / (1 + a ^ 2 * x ^ 2))
        atTop (𝓝 0) := by
    have hden :
        Tendsto (fun x : ℝ => 1 / x + a ^ 2 * x)
          atTop atTop :=
      (tendsto_const_nhds.div_atTop tendsto_id).add_atTop
        (tendsto_id.const_mul_atTop (sq_pos_of_pos ha))
    have hbase :
        Tendsto (fun x : ℝ => 1 / (1 / x + a ^ 2 * x))
          atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    apply hbase.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    field_simp [ha.ne']
  have hsecond :
      Tendsto (fun x : ℝ => x / (2 * (1 + a ^ 2 * x ^ 2)))
        atTop (𝓝 0) := by
    have heq :
        (fun x : ℝ => x / (2 * (1 + a ^ 2 * x ^ 2))) =
          (fun x : ℝ => (x / (1 + a ^ 2 * x ^ 2)) / 2) := by
      funext x
      have hd : 1 + a ^ 2 * x ^ 2 ≠ 0 := by positivity
      field_simp [hd]
    rw [heq]
    simpa using hratio.div_const 2
  simpa only [squareOnePrimitive, add_zero] using hatan.add hsecond

private theorem squareOneKernel_integrable
    (a : ℝ) (ha : 0 < a) :
    IntegrableOn (squareOneKernel a) (Ioi (0 : ℝ)) volume := by
  exact integrableOn_Ioi_deriv_of_nonneg
    (squareOnePrimitive_continuous a ha).continuousAt.continuousWithinAt
    (fun x _ => squareOnePrimitive_hasDerivAt a x ha)
    (fun x _ => by unfold squareOneKernel; positivity)
    (squareOnePrimitive_tendsto a ha)

private theorem squareOneKernel_integral
    (a : ℝ) (ha : 0 < a) :
    (∫ x in Ioi (0 : ℝ), squareOneKernel a x ∂volume) =
      Real.pi / (4 * a) := by
  have h :=
    integral_Ioi_of_hasDerivAt_of_tendsto
      (squareOnePrimitive_continuous a ha).continuousAt.continuousWithinAt
      (fun x _ => squareOnePrimitive_hasDerivAt a x ha)
      (squareOneKernel_integrable a ha)
      (squareOnePrimitive_tendsto a ha)
  simpa [squareOnePrimitive] using h

private def momentKernel (a b x : ℝ) : ℝ :=
  x ^ 2 / ((1 + a ^ 2 * x ^ 2) * (1 + b ^ 2 * x ^ 2))

private theorem momentKernel_eq_partialFractions
    (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    momentKernel a b x =
      (oneKernel b x - oneKernel a x) / (a ^ 2 - b ^ 2) := by
  have hfactor : a ^ 2 - b ^ 2 ≠ 0 := by
    intro h
    have hsquare : a ^ 2 = b ^ 2 := by linarith
    exact hab (by nlinarith)
  have hA : 1 + a ^ 2 * x ^ 2 ≠ 0 := by positivity
  have hB : 1 + b ^ 2 * x ^ 2 ≠ 0 := by positivity
  unfold momentKernel oneKernel
  field_simp [hfactor, hA, hB]
  ring

private theorem momentKernel_eq_diagonal
    (a x : ℝ) (ha : 0 < a) :
    momentKernel a a x =
      (1 / a ^ 2) * (oneKernel a x - squareOneKernel a x) := by
  have hA : 1 + a ^ 2 * x ^ 2 ≠ 0 := by positivity
  unfold momentKernel oneKernel squareOneKernel
  field_simp [ha.ne', hA]
  ring

private theorem momentKernel_integrable
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (momentKernel a b) (Ioi (0 : ℝ)) volume := by
  by_cases hab : a = b
  · subst b
    have hcomb :
        IntegrableOn
          (fun x : ℝ =>
            (1 / a ^ 2) *
              (oneKernel a x - squareOneKernel a x))
          (Ioi (0 : ℝ)) volume :=
      ((oneKernel_integrable a ha).sub
        (squareOneKernel_integrable a ha)).const_mul _
    exact hcomb.congr_fun
      (fun x _ => (momentKernel_eq_diagonal a x ha).symm)
      measurableSet_Ioi
  · have hfactor : a ^ 2 - b ^ 2 ≠ 0 := by
      intro h
      have hsquare : a ^ 2 = b ^ 2 := by linarith
      exact hab (by nlinarith)
    have hcomb :
        IntegrableOn
          (fun x : ℝ =>
            (oneKernel b x - oneKernel a x) /
              (a ^ 2 - b ^ 2))
          (Ioi (0 : ℝ)) volume :=
      ((oneKernel_integrable b hb).sub
        (oneKernel_integrable a ha)).div_const _
    exact hcomb.congr_fun
      (fun x _ =>
        (momentKernel_eq_partialFractions a b x ha hb hab).symm)
      measurableSet_Ioi

private theorem momentKernel_integral
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), momentKernel a b x ∂volume) =
      Real.pi / (2 * a * b * (a + b)) := by
  by_cases hab : a = b
  · subst b
    calc
      (∫ x in Ioi (0 : ℝ), momentKernel a a x ∂volume) =
          ∫ x in Ioi (0 : ℝ),
            (1 / a ^ 2) *
              (oneKernel a x - squareOneKernel a x) ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x _
            exact momentKernel_eq_diagonal a x ha
      _ = (1 / a ^ 2) *
          ((∫ x in Ioi (0 : ℝ), oneKernel a x ∂volume) -
            ∫ x in Ioi (0 : ℝ), squareOneKernel a x ∂volume) := by
            rw [integral_const_mul]
            rw [integral_sub
              (oneKernel_integrable a ha)
              (squareOneKernel_integrable a ha)]
      _ = (1 / a ^ 2) *
          (Real.pi / (2 * a) - Real.pi / (4 * a)) := by
            rw [oneKernel_integral a ha, squareOneKernel_integral a ha]
      _ = Real.pi / (2 * a * a * (a + a)) := by
            field_simp [ha.ne']
            ring
  · have hfactor : a ^ 2 - b ^ 2 ≠ 0 := by
      intro h
      have hsquare : a ^ 2 = b ^ 2 := by linarith
      exact hab (by nlinarith)
    calc
      (∫ x in Ioi (0 : ℝ), momentKernel a b x ∂volume) =
          ∫ x in Ioi (0 : ℝ),
            (oneKernel b x - oneKernel a x) /
              (a ^ 2 - b ^ 2) ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x _
            exact momentKernel_eq_partialFractions a b x ha hb hab
      _ = ((∫ x in Ioi (0 : ℝ), oneKernel b x ∂volume) -
            ∫ x in Ioi (0 : ℝ), oneKernel a x ∂volume) /
              (a ^ 2 - b ^ 2) := by
            rw [integral_div]
            rw [integral_sub
              (oneKernel_integrable b hb)
              (oneKernel_integrable a ha)]
      _ = (Real.pi / (2 * b) - Real.pi / (2 * a)) /
            (a ^ 2 - b ^ 2) := by
            rw [oneKernel_integral b hb, oneKernel_integral a ha]
      _ = Real.pi / (2 * a * b * (a + b)) := by
            have hsum : a + b ≠ 0 := by positivity
            field_simp [ha.ne', hb.ne', hfactor, hsum]
            ring

private theorem logQuad_nonneg (b x : ℝ) :
    0 ≤ Real.log (1 + b ^ 2 * x ^ 2) := by
  exact Real.log_nonneg
    (by nlinarith [mul_nonneg (sq_nonneg b) (sq_nonneg x)])

private theorem logQuad_le_tail
    (b x : ℝ) (hx : 1 < x) :
    Real.log (1 + b ^ 2 * x ^ 2) ≤
      4 * (1 + b ^ 2) ^ (1 / 4 : ℝ) *
        x ^ (1 / 2 : ℝ) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have harg : 0 ≤ 1 + b ^ 2 * x ^ 2 := by positivity
  have hxSquare : 1 ≤ x ^ 2 := by
    nlinarith [mul_nonneg
      (by linarith : 0 ≤ x - 1)
      (by linarith : 0 ≤ x + 1)]
  have hbase :
      1 + b ^ 2 * x ^ 2 ≤ (1 + b ^ 2) * x ^ 2 := by
    nlinarith
  have hrpow :
      (1 + b ^ 2 * x ^ 2) ^ (1 / 4 : ℝ) ≤
        (1 + b ^ 2) ^ (1 / 4 : ℝ) *
          x ^ (1 / 2 : ℝ) := by
    calc
      (1 + b ^ 2 * x ^ 2) ^ (1 / 4 : ℝ) ≤
          ((1 + b ^ 2) * x ^ 2) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow harg hbase (by norm_num)
      _ = (1 + b ^ 2) ^ (1 / 4 : ℝ) *
          x ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by positivity) (sq_nonneg x)]
        rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hxpos.le]
        norm_num
  calc
    Real.log (1 + b ^ 2 * x ^ 2) ≤
        (1 + b ^ 2 * x ^ 2) ^ (1 / 4 : ℝ) /
          (1 / 4 : ℝ) :=
      Real.log_le_rpow_div harg (by norm_num)
    _ = 4 * (1 + b ^ 2 * x ^ 2) ^ (1 / 4 : ℝ) := by ring
    _ ≤ 4 * ((1 + b ^ 2) ^ (1 / 4 : ℝ) *
          x ^ (1 / 2 : ℝ)) := by gcongr
    _ = _ := by ring

private def logOneKernel (a b x : ℝ) : ℝ :=
  Real.log (1 + b ^ 2 * x ^ 2) / (1 + a ^ 2 * x ^ 2)

private theorem logOneKernel_nonneg (a b x : ℝ) :
    0 ≤ logOneKernel a b x := by
  unfold logOneKernel
  exact div_nonneg (logQuad_nonneg b x) (by positivity)

private theorem logOneKernel_continuous (a b : ℝ) :
    Continuous (logOneKernel a b) := by
  unfold logOneKernel
  apply Continuous.div
  · apply Continuous.log
    · fun_prop
    · intro x
      positivity
  · fun_prop
  · intro x
    positivity

private theorem logOneKernel_integrable
    (a b : ℝ) (ha : 0 < a) :
    IntegrableOn (logOneKernel a b) (Ioi (0 : ℝ)) volume := by
  have hcompact :
      IntegrableOn (logOneKernel a b) (Ioc (0 : ℝ) 1) volume :=
    ((logOneKernel_continuous a b).intervalIntegrable
      (a := (0 : ℝ)) (b := 1)).1
  have htailMajor :
      IntegrableOn
        (fun x : ℝ =>
          (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ) / a ^ 2) *
            x ^ (-3 / 2 : ℝ))
        (Ioi (1 : ℝ)) volume :=
    (integrableOn_Ioi_rpow_of_lt
      (a := (-3 / 2 : ℝ)) (c := 1)
      (by norm_num) zero_lt_one).const_mul _
  have htail :
      IntegrableOn (logOneKernel a b) (Ioi (1 : ℝ)) volume := by
    apply htailMajor.mono'
    · exact (logOneKernel_continuous a b).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      change (1 : ℝ) < x at hx
      have hxpos : 0 < x := zero_lt_one.trans hx
      have hlog := logQuad_le_tail b x hx
      have hden : 0 < 1 + a ^ 2 * x ^ 2 := by positivity
      have hdenLower : a ^ 2 * x ^ 2 ≤ 1 + a ^ 2 * x ^ 2 := by
        linarith
      rw [Real.norm_eq_abs,
        abs_of_nonneg (logOneKernel_nonneg a b x)]
      unfold logOneKernel
      have hdiv :
          Real.log (1 + b ^ 2 * x ^ 2) /
              (1 + a ^ 2 * x ^ 2) ≤
            (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ) *
              x ^ (1 / 2 : ℝ)) / (a ^ 2 * x ^ 2) := by
        exact div_le_div₀
          (by positivity) hlog (by positivity) hdenLower
      calc
        Real.log (1 + b ^ 2 * x ^ 2) /
              (1 + a ^ 2 * x ^ 2) ≤
            (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ) *
              x ^ (1 / 2 : ℝ)) / (a ^ 2 * x ^ 2) := hdiv
        _ = (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ) / a ^ 2) *
              x ^ (-3 / 2 : ℝ) := by
          have ha0 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha.ne'
          calc
            (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ) *
                x ^ (1 / 2 : ℝ)) / (a ^ 2 * x ^ 2) =
                (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ) / a ^ 2) *
                  (x ^ (1 / 2 : ℝ) / x ^ (2 : ℝ)) := by
                    field_simp [ha0, hxpos.ne']
                    exact Real.rpow_natCast x 2
            _ = (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ) / a ^ 2) *
                  x ^ ((1 / 2 : ℝ) - 2) := by
                    rw [Real.rpow_sub hxpos]
            _ = _ := by norm_num
  have hunion := hcompact.union htail
  refine hunion.mono_set ?_
  intro x hx
  by_cases hx1 : x ≤ 1
  · exact Or.inl ⟨hx, hx1⟩
  · exact Or.inr (lt_of_not_ge hx1)

private def logDerivKernel (a b x : ℝ) : ℝ :=
  2 * b * momentKernel a b x

private theorem logDerivKernel_nonneg
    (a b x : ℝ) (hb : 0 ≤ b) :
    0 ≤ logDerivKernel a b x := by
  unfold logDerivKernel momentKernel
  positivity

private theorem logDerivKernel_continuous (a b : ℝ) :
    Continuous (logDerivKernel a b) := by
  unfold logDerivKernel momentKernel
  apply Continuous.const_mul
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    positivity

private theorem logDerivKernel_integrable
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (logDerivKernel a b) (Ioi (0 : ℝ)) volume :=
  (momentKernel_integrable a b ha hb).const_mul _

private theorem logDerivKernel_integral
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), logDerivKernel a b x ∂volume) =
      Real.pi / (a * (a + b)) := by
  calc
    (∫ x in Ioi (0 : ℝ), logDerivKernel a b x ∂volume) =
        (2 * b) *
          ∫ x in Ioi (0 : ℝ), momentKernel a b x ∂volume := by
          unfold logDerivKernel
          rw [integral_const_mul]
    _ = (2 * b) * (Real.pi / (2 * a * b * (a + b))) := by
          rw [momentKernel_integral a b ha hb]
    _ = Real.pi / (a * (a + b)) := by
          field_simp [ha.ne', hb.ne']

private theorem logOneKernel_hasDerivAt
    (a b x : ℝ) :
    HasDerivAt (fun c : ℝ => logOneKernel a c x)
      (logDerivKernel a b x) b := by
  have hinner :
      HasDerivAt (fun c : ℝ => 1 + c ^ 2 * x ^ 2)
        (2 * b * x ^ 2) b := by
    convert
      (hasDerivAt_const b 1).add
        (((hasDerivAt_id b).pow 2).mul_const (x ^ 2)) using 1 <;>
      simp only [id_eq] <;> ring
  have hlog :=
    (Real.hasDerivAt_log
      (by positivity : 1 + b ^ 2 * x ^ 2 ≠ 0)).comp b hinner
  have h := hlog.div_const (1 + a ^ 2 * x ^ 2)
  unfold logOneKernel logDerivKernel momentKernel
  convert h using 1
  have hA : 1 + a ^ 2 * x ^ 2 ≠ 0 := by positivity
  have hB : 1 + b ^ 2 * x ^ 2 ≠ 0 := by positivity
  field_simp [hA, hB]

private theorem norm_logDerivKernel_le_local
    (a b c x : ℝ) (hb : 0 < b)
    (hc : c ∈ Ioo (b / 2) (3 * b / 2)) :
    ‖logDerivKernel a c x‖ ≤
      (4 / b) * oneKernel a x := by
  have hcpos : 0 < c := by
    change b / 2 < c ∧ c < 3 * b / 2 at hc
    linarith
  have hA : 0 < 1 + a ^ 2 * x ^ 2 := by positivity
  have hC : 0 < 1 + c ^ 2 * x ^ 2 := by positivity
  have hbc : b ≤ 2 * c := by
    change b / 2 < c ∧ c < 3 * b / 2 at hc
    linarith
  have hbcx :
      b * c * x ^ 2 ≤ 2 * c ^ 2 * x ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg x)
      (mul_nonneg hcpos.le (sub_nonneg.mpr hbc))]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (logDerivKernel_nonneg a c x hcpos.le)]
  unfold logDerivKernel momentKernel oneKernel
  calc
    2 * c *
          (x ^ 2 /
            ((1 + a ^ 2 * x ^ 2) * (1 + c ^ 2 * x ^ 2))) =
        (2 * c * x ^ 2) /
          ((1 + a ^ 2 * x ^ 2) * (1 + c ^ 2 * x ^ 2)) := by
          ring
    _ ≤ (4 / b) * (1 / (1 + a ^ 2 * x ^ 2)) := by
      apply (div_le_iff₀ (mul_pos hA hC)).2
      field_simp [hb.ne', hA.ne', hC.ne']
      nlinarith

private def logOneValue (a b : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), logOneKernel a b x ∂volume

private theorem logOneValue_hasDerivAt
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (logOneValue a)
      (Real.pi / (a * (a + b))) b := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let s : Set ℝ := Ioo (b / 2) (3 * b / 2)
  have hs : s ∈ 𝓝 b := by
    apply Ioo_mem_nhds
    · dsimp [s]
      linarith
    · dsimp [s]
      linarith
  have hmeas :
      ∀ᶠ c in 𝓝 b,
        AEStronglyMeasurable (logOneKernel a c) μ :=
    Filter.Eventually.of_forall fun c =>
      (logOneKernel_continuous a c).aestronglyMeasurable
  have hderivMeas :
      AEStronglyMeasurable (logDerivKernel a b) μ :=
    (logDerivKernel_continuous a b).aestronglyMeasurable
  have hbound :
      ∀ᵐ x ∂μ, ∀ c ∈ s,
        ‖logDerivKernel a c x‖ ≤
          (4 / b) * oneKernel a x := by
    filter_upwards with x
    exact fun c hc => norm_logDerivKernel_le_local a b c x hb hc
  have hdiff :
      ∀ᵐ x ∂μ, ∀ c ∈ s,
        HasDerivAt (fun d : ℝ => logOneKernel a d x)
          (logDerivKernel a c x) c := by
    filter_upwards with x
    exact fun c _ => logOneKernel_hasDerivAt a c x
  have hmajor :
      Integrable (fun x : ℝ => (4 / b) * oneKernel a x) μ := by
    change IntegrableOn
      (fun x : ℝ => (4 / b) * oneKernel a x)
      (Ioi (0 : ℝ)) volume
    exact (oneKernel_integrable a ha).const_mul _
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := fun c x => logOneKernel a c x)
      (F' := fun c x => logDerivKernel a c x)
      hs hmeas (logOneKernel_integrable a b ha)
      hderivMeas hbound hmajor hdiff
  rw [logDerivKernel_integral a b ha hb] at hmain
  simpa only [logOneValue, μ] using hmain.2

private theorem logOneKernel_param_continuous
    (a x : ℝ) :
    Continuous (fun b : ℝ => logOneKernel a b x) := by
  unfold logOneKernel
  apply Continuous.div_const
  apply Continuous.log
  · fun_prop
  · intro b
    positivity

private theorem logOneValue_tendsto_zero
    (a : ℝ) (ha : 0 < a) :
    Tendsto (logOneValue a)
      (𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hmeas :
      ∀ᶠ b in 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ),
        AEStronglyMeasurable (logOneKernel a b) μ :=
    Filter.Eventually.of_forall fun b =>
      (logOneKernel_continuous a b).aestronglyMeasurable
  have hbNonneg :
      ∀ᶠ b in 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ), 0 ≤ b :=
    self_mem_nhdsWithin
  have hbLt :
      ∀ᶠ b in 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ), b < 1 := by
    have h : ∀ᶠ b in 𝓝 (0 : ℝ), b < 1 :=
      Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)
    exact h.filter_mono inf_le_left
  have hbound :
      ∀ᶠ b in 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ),
        ∀ᵐ x ∂μ, ‖logOneKernel a b x‖ ≤ logOneKernel a 1 x := by
    filter_upwards [hbNonneg, hbLt] with b hb0 hb1
    filter_upwards with x
    have hbSq : b ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (b + 1)]
    have hargs :
        1 + b ^ 2 * x ^ 2 ≤ 1 + (1 : ℝ) ^ 2 * x ^ 2 := by
      nlinarith [sq_nonneg x]
    have hlog :
        Real.log (1 + b ^ 2 * x ^ 2) ≤
          Real.log (1 + (1 : ℝ) ^ 2 * x ^ 2) :=
      Real.strictMonoOn_log.monotoneOn
        (show 0 < 1 + b ^ 2 * x ^ 2 by positivity)
        (show 0 < 1 + (1 : ℝ) ^ 2 * x ^ 2 by positivity)
        hargs
    rw [Real.norm_eq_abs,
      abs_of_nonneg (logOneKernel_nonneg a b x)]
    unfold logOneKernel
    exact div_le_div_of_nonneg_right hlog (by positivity)
  have hmajor :
      Integrable (logOneKernel a 1) μ := by
    change IntegrableOn (logOneKernel a 1) (Ioi (0 : ℝ)) volume
    exact logOneKernel_integrable a 1 ha
  have hlim :
      ∀ᵐ x ∂μ,
        Tendsto (fun b : ℝ => logOneKernel a b x)
          (𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    filter_upwards with x
    have hfull :
        Tendsto (fun b : ℝ => logOneKernel a b x)
          (𝓝 (0 : ℝ)) (𝓝 (logOneKernel a 0 x)) :=
      (logOneKernel_param_continuous a x).continuousAt
    have h :=
      hfull.mono_left
        (show 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)
    simpa [logOneKernel] using h
  have hDCT :=
    tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (bound := logOneKernel a 1)
      hmeas hbound hmajor hlim
  simpa [logOneValue, μ] using hDCT

private def logOneForm (a b : ℝ) : ℝ :=
  (Real.pi / a) * Real.log ((a + b) / a)

private theorem logOneForm_hasDerivAt
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (logOneForm a)
      (Real.pi / (a * (a + b))) b := by
  have hinner :
      HasDerivAt (fun c : ℝ => (a + c) / a) (1 / a) b := by
    convert
      ((hasDerivAt_const b a).add (hasDerivAt_id b)).div_const a
      using 1 <;>
      simp only [zero_add, one_div]
  have hlog :=
    (Real.hasDerivAt_log
      (by positivity : (a + b) / a ≠ 0)).comp b hinner
  unfold logOneForm
  convert hlog.const_mul (Real.pi / a) using 1
  field_simp [ha.ne']

private theorem logOneForm_tendsto_zero
    (a : ℝ) (ha : 0 < a) :
    Tendsto (logOneForm a)
      (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
  have hinner :
      Tendsto (fun b : ℝ => (a + b) / a)
        (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 1) := by
    have hcont :
        Tendsto (fun b : ℝ => (a + b) / a)
          (𝓝 (0 : ℝ)) (𝓝 1) := by
      have hc :
          ContinuousAt (fun b : ℝ => (a + b) / a) 0 := by
        fun_prop
      have hpoint : (a + (0 : ℝ)) / a = 1 := by
        simp [ha.ne']
      simpa only [hpoint] using hc.tendsto
    exact hcont.mono_left inf_le_left
  have hlog :
      Tendsto (fun b : ℝ => Real.log ((a + b) / a))
        (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
    simpa using hinner.log one_ne_zero
  unfold logOneForm
  simpa using tendsto_const_nhds.mul hlog

private theorem logOneValue_eq_logOneForm
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    logOneValue a b = logOneForm a b := by
  let G : ℝ → ℝ := fun t => logOneValue a t - logOneForm a t
  have hG (t : ℝ) (ht : 0 < t) :
      HasDerivAt G 0 t := by
    have h :=
      (logOneValue_hasDerivAt a t ha ht).sub
        (logOneForm_hasDerivAt a t ha ht)
    simpa only [G, sub_self] using h
  have hconstant (c : ℝ) (hc : 0 < c) (hcb : c ≤ b) :
      G c = G b := by
    have hbound :=
      Convex.norm_image_sub_le_of_norm_deriv_le
        (f := G) (s := Icc c b) (C := 0)
        (fun t ht =>
          (hG t (hc.trans_le ht.1)).differentiableAt)
        (fun t ht => by
          rw [(hG t (hc.trans_le ht.1)).deriv, norm_zero])
        (convex_Icc c b)
        ⟨le_rfl, hcb⟩
        ⟨hcb, le_rfl⟩
    have hzero : ‖G b - G c‖ = 0 := by
      apply le_antisymm
      · simpa using hbound
      · exact norm_nonneg _
    exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
  have hGlim :
      Tendsto G (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
    have hvalue :=
      (logOneValue_tendsto_zero a ha).mono_left
        (nhdsWithin_mono (0 : ℝ) Ioi_subset_Ici_self)
    have hform := logOneForm_tendsto_zero a ha
    simpa only [G, sub_zero] using hvalue.sub hform
  have hevent :
      G =ᶠ[𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)] fun _ => G b := by
    have hlt :
        ∀ᶠ c in 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ), c < b := by
      have h : ∀ᶠ c in 𝓝 (0 : ℝ), c < b :=
        Iio_mem_nhds hb
      exact h.filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin, hlt] with c hc hcb
    exact hconstant c hc hcb.le
  have hconstlim :
      Tendsto G (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 (G b)) :=
    tendsto_const_nhds.congr' hevent.symm
  have hGb : G b = 0 :=
    tendsto_nhds_unique hconstlim hGlim
  exact sub_eq_zero.mp hGb

private def logOverSqKernel (b x : ℝ) : ℝ :=
  Real.log (1 + b ^ 2 * x ^ 2) / x ^ 2

private theorem logOverSqKernel_nonneg (b x : ℝ) :
    0 ≤ logOverSqKernel b x := by
  unfold logOverSqKernel
  exact div_nonneg (logQuad_nonneg b x) (sq_nonneg x)

private theorem logOverSqKernel_continuousOn (b : ℝ) :
    ContinuousOn (logOverSqKernel b) (Ioi (0 : ℝ)) := by
  intro x hx
  unfold logOverSqKernel
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div
  · apply ContinuousAt.log
    · fun_prop
    · positivity
  · fun_prop
  · exact pow_ne_zero 2 hx.ne'

private theorem logOverSqKernel_integrable
    (b : ℝ) :
    IntegrableOn (logOverSqKernel b) (Ioi (0 : ℝ)) volume := by
  have hheadMajor :
      IntegrableOn (fun _ : ℝ => b ^ 2) (Ioc (0 : ℝ) 1) volume :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hhead :
      IntegrableOn (logOverSqKernel b) (Ioc (0 : ℝ) 1) volume := by
    apply hheadMajor.mono'
    · exact
        ((logOverSqKernel_continuousOn b).mono
          Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hxpos : 0 < x := hx.1
      have hlog :
          Real.log (1 + b ^ 2 * x ^ 2) ≤ b ^ 2 * x ^ 2 := by
        have h :=
          Real.log_le_sub_one_of_pos
            (show 0 < 1 + b ^ 2 * x ^ 2 by positivity)
        nlinarith
      rw [Real.norm_eq_abs,
        abs_of_nonneg (logOverSqKernel_nonneg b x)]
      unfold logOverSqKernel
      calc
        Real.log (1 + b ^ 2 * x ^ 2) / x ^ 2 ≤
            (b ^ 2 * x ^ 2) / x ^ 2 :=
          div_le_div_of_nonneg_right hlog (sq_nonneg x)
        _ = b ^ 2 := by field_simp [hxpos.ne']
  have htailMajor :
      IntegrableOn
        (fun x : ℝ =>
          (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ)) *
            x ^ (-3 / 2 : ℝ))
        (Ioi (1 : ℝ)) volume :=
    (integrableOn_Ioi_rpow_of_lt
      (a := (-3 / 2 : ℝ)) (c := 1)
      (by norm_num) zero_lt_one).const_mul _
  have htail :
      IntegrableOn (logOverSqKernel b) (Ioi (1 : ℝ)) volume := by
    apply htailMajor.mono'
    · exact
        ((logOverSqKernel_continuousOn b).mono
          (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).aestronglyMeasurable
          measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : 0 < x := zero_lt_one.trans hx
      have hlog := logQuad_le_tail b x hx
      rw [Real.norm_eq_abs,
        abs_of_nonneg (logOverSqKernel_nonneg b x)]
      unfold logOverSqKernel
      calc
        Real.log (1 + b ^ 2 * x ^ 2) / x ^ 2 ≤
            (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ) *
              x ^ (1 / 2 : ℝ)) / x ^ 2 :=
          div_le_div_of_nonneg_right hlog (sq_nonneg x)
        _ = (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ)) *
              x ^ (-3 / 2 : ℝ) := by
          calc
            (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ) *
                x ^ (1 / 2 : ℝ)) / x ^ 2 =
                (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ)) *
                  (x ^ (1 / 2 : ℝ) / x ^ (2 : ℝ)) := by
                    field_simp [hxpos.ne']
                    exact Real.rpow_natCast x 2
            _ = (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ)) *
                  x ^ ((1 / 2 : ℝ) - 2) := by
                    rw [Real.rpow_sub hxpos]
            _ = _ := by norm_num
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  exact hhead.union htail

private def logQuadFun (b x : ℝ) : ℝ :=
  Real.log (1 + b ^ 2 * x ^ 2)

private def logQuadDeriv (b x : ℝ) : ℝ :=
  2 * b ^ 2 * x / (1 + b ^ 2 * x ^ 2)

private def negInv (x : ℝ) : ℝ :=
  -1 / x

private def invSq (x : ℝ) : ℝ :=
  1 / x ^ 2

private theorem logQuadFun_hasDerivAt
    (b x : ℝ) :
    HasDerivAt (logQuadFun b) (logQuadDeriv b x) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => 1 + b ^ 2 * y ^ 2)
        (2 * b ^ 2 * x) x := by
    convert
      (hasDerivAt_const x 1).add
        (((hasDerivAt_id x).pow 2).const_mul (b ^ 2)) using 1 <;>
      simp only [id_eq] <;> ring
  have hlog :=
    (Real.hasDerivAt_log
      (by positivity : 1 + b ^ 2 * x ^ 2 ≠ 0)).comp x hinner
  unfold logQuadFun logQuadDeriv
  convert hlog using 1
  field_simp

private theorem negInv_hasDerivAt
    (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt negInv (invSq x) x := by
  have h :=
    (hasDerivAt_const x (-1 : ℝ)).div
      (hasDerivAt_id x) hx
  unfold negInv invSq
  convert h using 1
  simp only [id_eq, zero_mul, one_mul, zero_sub]
  field_simp [hx]

private theorem logQuadDeriv_mul_negInv_eq
    (b x : ℝ) (hx : x ≠ 0) :
    logQuadDeriv b x * negInv x =
      -(2 * b ^ 2) * oneKernel b x := by
  have hden : 1 + b ^ 2 * x ^ 2 ≠ 0 := by positivity
  unfold logQuadDeriv negInv oneKernel
  field_simp [hx, hden]

private theorem logQuadFun_mul_negInv_tendsto_zero
    (b : ℝ) :
    Tendsto (logQuadFun b * negInv)
      (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun x : ℝ => b ^ 2 * x)
    (Filter.Eventually.of_forall fun x => norm_nonneg _)
    ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := hx
    have hlog :
        Real.log (1 + b ^ 2 * x ^ 2) ≤ b ^ 2 * x ^ 2 := by
      have h :=
        Real.log_le_sub_one_of_pos
          (show 0 < 1 + b ^ 2 * x ^ 2 by positivity)
      nlinarith
    calc
      ‖(logQuadFun b * negInv) x‖ =
          Real.log (1 + b ^ 2 * x ^ 2) / x := by
            rw [Real.norm_eq_abs]
            unfold logQuadFun negInv
            dsimp only [Pi.mul_apply]
            rw [abs_mul, abs_div, abs_neg, abs_one,
              abs_of_pos hxpos,
              abs_of_nonneg (logQuad_nonneg b x)]
            ring
      _ ≤ (b ^ 2 * x ^ 2) / x :=
        div_le_div_of_nonneg_right hlog hxpos.le
      _ = b ^ 2 * x := by
        field_simp [hxpos.ne']
  · have hfull :
        Tendsto (fun x : ℝ => b ^ 2 * x)
          (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul
        (continuousAt_id.tendsto : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0))
    exact hfull.mono_left inf_le_left

private theorem logQuadFun_mul_negInv_tendsto_atTop_zero
    (b : ℝ) :
    Tendsto (logQuadFun b * negInv) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let C : ℝ := 4 * (1 + b ^ 2) ^ (1 / 4 : ℝ)
  have hupper :
      Tendsto (fun x : ℝ => C * x ^ (-1 / 2 : ℝ))
        atTop (𝓝 0) := by
    have hpow :
        Tendsto (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
          atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    convert hpow.const_mul C using 1 <;> norm_num
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun x => norm_nonneg _)
    ?_ hupper
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlog := logQuad_le_tail b x hx
  calc
    ‖(logQuadFun b * negInv) x‖ =
        Real.log (1 + b ^ 2 * x ^ 2) / x := by
          rw [Real.norm_eq_abs]
          unfold logQuadFun negInv
          dsimp only [Pi.mul_apply]
          rw [abs_mul, abs_div, abs_neg, abs_one,
            abs_of_pos hxpos,
            abs_of_nonneg (logQuad_nonneg b x)]
          ring
    _ ≤ (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ) *
          x ^ (1 / 2 : ℝ)) / x :=
      div_le_div_of_nonneg_right hlog hxpos.le
    _ = C * x ^ (-1 / 2 : ℝ) := by
      dsimp [C]
      calc
        (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ) *
            x ^ (1 / 2 : ℝ)) / x =
            (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ)) *
              (x ^ (1 / 2 : ℝ) / x ^ (1 : ℝ)) := by
                rw [Real.rpow_one]
                ring
        _ = (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ)) *
              x ^ ((1 / 2 : ℝ) - 1) := by
                rw [Real.rpow_sub hxpos]
        _ = _ := by norm_num

private theorem logOverSqKernel_integral
    (b : ℝ) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), logOverSqKernel b x ∂volume) =
      Real.pi * b := by
  have huv' :
      IntegrableOn (logQuadFun b * invSq)
        (Ioi (0 : ℝ)) volume := by
    exact (logOverSqKernel_integrable b).congr_fun
      (fun x _ => by
        simp [logOverSqKernel, logQuadFun, invSq, div_eq_mul_inv])
      measurableSet_Ioi
  have hu'v :
      IntegrableOn (logQuadDeriv b * negInv)
        (Ioi (0 : ℝ)) volume := by
    have hmajor :
        IntegrableOn
          (fun x : ℝ => -(2 * b ^ 2) * oneKernel b x)
          (Ioi (0 : ℝ)) volume :=
      (oneKernel_integrable b hb).const_mul _
    exact hmajor.congr_fun
      (fun x hx => (logQuadDeriv_mul_negInv_eq b x hx.ne').symm)
      measurableSet_Ioi
  have hibp :=
    integral_Ioi_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ))
      (u := logQuadFun b)
      (u' := logQuadDeriv b)
      (v := negInv)
      (v' := invSq)
      (fun x _ => logQuadFun_hasDerivAt b x)
      (fun x hx => negInv_hasDerivAt x hx.ne')
      huv' hu'v
      (logQuadFun_mul_negInv_tendsto_zero b)
      (logQuadFun_mul_negInv_tendsto_atTop_zero b)
  have hderivIntegral :
      (∫ x in Ioi (0 : ℝ),
        logQuadDeriv b x * negInv x ∂volume) =
        -(Real.pi * b) := by
    calc
      (∫ x in Ioi (0 : ℝ),
          logQuadDeriv b x * negInv x ∂volume) =
          ∫ x in Ioi (0 : ℝ),
            -(2 * b ^ 2) * oneKernel b x ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            exact logQuadDeriv_mul_negInv_eq b x hx.ne'
      _ = -(2 * b ^ 2) *
            ∫ x in Ioi (0 : ℝ), oneKernel b x ∂volume := by
            rw [integral_const_mul]
      _ = -(2 * b ^ 2) * (Real.pi / (2 * b)) := by
            rw [oneKernel_integral b hb]
      _ = -(Real.pi * b) := by
            field_simp [hb.ne']
  have hibp' :
      (∫ x in Ioi (0 : ℝ), logOverSqKernel b x ∂volume) =
        0 - 0 -
          ∫ x in Ioi (0 : ℝ),
            logQuadDeriv b x * negInv x ∂volume := by
    simpa [logOverSqKernel, logQuadFun, invSq, div_eq_mul_inv] using hibp
  rw [hibp', hderivIntegral]
  ring

private def hKernel (a b x : ℝ) : ℝ :=
  Real.log (1 + b ^ 2 * x ^ 2) /
    (x ^ 2 * (1 + a ^ 2 * x ^ 2))

private theorem hKernel_eq_difference
    (a b x : ℝ) (hx : x ≠ 0) :
    hKernel a b x =
      logOverSqKernel b x - a ^ 2 * logOneKernel a b x := by
  have hA : 1 + a ^ 2 * x ^ 2 ≠ 0 := by positivity
  unfold hKernel logOverSqKernel logOneKernel
  field_simp [hx, hA]
  ring

private theorem hKernel_integrable
    (a b : ℝ) (ha : 0 < a) :
    IntegrableOn (hKernel a b) (Ioi (0 : ℝ)) volume := by
  have hcomb :
      IntegrableOn
        (fun x : ℝ =>
          logOverSqKernel b x - a ^ 2 * logOneKernel a b x)
        (Ioi (0 : ℝ)) volume :=
    (logOverSqKernel_integrable b).sub
      ((logOneKernel_integrable a b ha).const_mul _)
  exact hcomb.congr_fun
    (fun x hx => (hKernel_eq_difference a b x hx.ne').symm)
    measurableSet_Ioi

private theorem hKernel_integral
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), hKernel a b x ∂volume) =
      Real.pi *
        (b - a * Real.log ((a + b) / a)) := by
  calc
    (∫ x in Ioi (0 : ℝ), hKernel a b x ∂volume) =
        ∫ x in Ioi (0 : ℝ),
          (logOverSqKernel b x -
            a ^ 2 * logOneKernel a b x) ∂volume := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          exact hKernel_eq_difference a b x hx.ne'
    _ = (∫ x in Ioi (0 : ℝ), logOverSqKernel b x ∂volume) -
          a ^ 2 *
            ∫ x in Ioi (0 : ℝ), logOneKernel a b x ∂volume := by
          rw [integral_sub
            (logOverSqKernel_integrable b)
            ((logOneKernel_integrable a b ha).const_mul _)]
          rw [integral_const_mul]
    _ = Real.pi * b - a ^ 2 *
          ((Real.pi / a) * Real.log ((a + b) / a)) := by
          rw [logOverSqKernel_integral b hb]
          change _ = _ - a ^ 2 * logOneForm a b
          rw [← logOneValue_eq_logOneForm a b ha hb]
          rfl
    _ = Real.pi *
          (b - a * Real.log ((a + b) / a)) := by
          field_simp [ha.ne']

private def productLog (a b x : ℝ) : ℝ :=
  Real.log (1 + a ^ 2 * x ^ 2) *
    Real.log (1 + b ^ 2 * x ^ 2)

private def productLogDeriv (a b x : ℝ) : ℝ :=
  logQuadDeriv a x * logQuadFun b x +
    logQuadDeriv b x * logQuadFun a x

private def negInvCube (x : ℝ) : ℝ :=
  -1 / (3 * x ^ 3)

private def invFourth (x : ℝ) : ℝ :=
  1 / x ^ 4

private def targetKernel (a b x : ℝ) : ℝ :=
  Real.log (1 + a ^ 2 * x ^ 2) *
      Real.log (1 + b ^ 2 * x ^ 2) / x ^ 4

private theorem targetKernel_nonneg (a b x : ℝ) :
    0 ≤ targetKernel a b x := by
  unfold targetKernel
  exact div_nonneg
    (mul_nonneg (logQuad_nonneg a x) (logQuad_nonneg b x))
    (by positivity)

private theorem targetKernel_continuousOn (a b : ℝ) :
    ContinuousOn (targetKernel a b) (Ioi (0 : ℝ)) := by
  intro x hx
  unfold targetKernel
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div
  · apply ContinuousAt.mul
    · apply ContinuousAt.log
      · fun_prop
      · positivity
    · apply ContinuousAt.log
      · fun_prop
      · positivity
  · fun_prop
  · exact pow_ne_zero 4 hx.ne'

private theorem targetKernel_integrable
    (a b : ℝ) :
    IntegrableOn (targetKernel a b) (Ioi (0 : ℝ)) volume := by
  have hheadMajor :
      IntegrableOn (fun _ : ℝ => a ^ 2 * b ^ 2)
        (Ioc (0 : ℝ) 1) volume :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hhead :
      IntegrableOn (targetKernel a b) (Ioc (0 : ℝ) 1) volume := by
    apply hheadMajor.mono'
    · exact
        ((targetKernel_continuousOn a b).mono
          Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hxpos : 0 < x := hx.1
      have hA0 := logQuad_nonneg a x
      have hB0 := logQuad_nonneg b x
      have hA :
          Real.log (1 + a ^ 2 * x ^ 2) ≤ a ^ 2 * x ^ 2 := by
        have h :=
          Real.log_le_sub_one_of_pos
            (show 0 < 1 + a ^ 2 * x ^ 2 by positivity)
        nlinarith
      have hB :
          Real.log (1 + b ^ 2 * x ^ 2) ≤ b ^ 2 * x ^ 2 := by
        have h :=
          Real.log_le_sub_one_of_pos
            (show 0 < 1 + b ^ 2 * x ^ 2 by positivity)
        nlinarith
      have hprod :
          Real.log (1 + a ^ 2 * x ^ 2) *
              Real.log (1 + b ^ 2 * x ^ 2) ≤
            (a ^ 2 * x ^ 2) * (b ^ 2 * x ^ 2) :=
        mul_le_mul hA hB hB0 (mul_nonneg (sq_nonneg a) (sq_nonneg x))
      rw [Real.norm_eq_abs,
        abs_of_nonneg (targetKernel_nonneg a b x)]
      unfold targetKernel
      calc
        Real.log (1 + a ^ 2 * x ^ 2) *
              Real.log (1 + b ^ 2 * x ^ 2) / x ^ 4 ≤
            ((a ^ 2 * x ^ 2) * (b ^ 2 * x ^ 2)) / x ^ 4 :=
          div_le_div_of_nonneg_right hprod (by positivity)
        _ = a ^ 2 * b ^ 2 := by
          field_simp [hxpos.ne']
  let C : ℝ :=
    (4 * (1 + a ^ 2) ^ (1 / 4 : ℝ)) *
      (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ))
  have htailMajor :
      IntegrableOn
        (fun x : ℝ => C * x ^ (-3 : ℝ))
        (Ioi (1 : ℝ)) volume :=
    (integrableOn_Ioi_rpow_of_lt
      (a := (-3 : ℝ)) (c := 1)
      (by norm_num) zero_lt_one).const_mul _
  have htail :
      IntegrableOn (targetKernel a b) (Ioi (1 : ℝ)) volume := by
    apply htailMajor.mono'
    · exact
        ((targetKernel_continuousOn a b).mono
          (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).aestronglyMeasurable
          measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : 0 < x := zero_lt_one.trans hx
      have hA0 := logQuad_nonneg a x
      have hB0 := logQuad_nonneg b x
      have hA := logQuad_le_tail a x hx
      have hB := logQuad_le_tail b x hx
      have hprod :
          Real.log (1 + a ^ 2 * x ^ 2) *
              Real.log (1 + b ^ 2 * x ^ 2) ≤
            (4 * (1 + a ^ 2) ^ (1 / 4 : ℝ) *
              x ^ (1 / 2 : ℝ)) *
            (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ) *
              x ^ (1 / 2 : ℝ)) :=
        mul_le_mul hA hB hB0 (by positivity)
      rw [Real.norm_eq_abs,
        abs_of_nonneg (targetKernel_nonneg a b x)]
      unfold targetKernel
      calc
        Real.log (1 + a ^ 2 * x ^ 2) *
              Real.log (1 + b ^ 2 * x ^ 2) / x ^ 4 ≤
            ((4 * (1 + a ^ 2) ^ (1 / 4 : ℝ) *
                x ^ (1 / 2 : ℝ)) *
              (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ) *
                x ^ (1 / 2 : ℝ))) / x ^ 4 :=
          div_le_div_of_nonneg_right hprod (by positivity)
        _ = C * x ^ (-3 : ℝ) := by
          dsimp [C]
          rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num,
            Real.rpow_neg hxpos.le]
          field_simp [hxpos.ne']
          rw [← Real.rpow_natCast (x ^ (1 / 2 : ℝ)) 2,
            ← Real.rpow_mul hxpos.le]
          norm_num
          ring
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  exact hhead.union htail

private theorem productLog_hasDerivAt
    (a b x : ℝ) :
    HasDerivAt (productLog a b) (productLogDeriv a b x) x := by
  unfold productLog productLogDeriv
  convert (logQuadFun_hasDerivAt a x).mul
    (logQuadFun_hasDerivAt b x) using 1 <;>
    unfold logQuadFun <;>
    ring

private theorem negInvCube_hasDerivAt
    (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt negInvCube (invFourth x) x := by
  have hden :
      HasDerivAt (fun y : ℝ => 3 * y ^ 3)
        (9 * x ^ 2) x := by
    convert ((hasDerivAt_id x).pow 3).const_mul 3 using 1 <;>
      simp only [id_eq] <;> ring
  have h :=
    (hasDerivAt_const x (-1 : ℝ)).div hden
      (by positivity : 3 * x ^ 3 ≠ 0)
  unfold negInvCube invFourth
  convert h using 1
  simp only [zero_mul, one_mul, zero_sub]
  field_simp [hx]
  ring

private theorem productLogDeriv_mul_negInvCube_eq
    (a b x : ℝ) (hx : x ≠ 0) :
    productLogDeriv a b x * negInvCube x =
      -(2 / 3) *
        (a ^ 2 * hKernel a b x + b ^ 2 * hKernel b a x) := by
  have hA : 1 + a ^ 2 * x ^ 2 ≠ 0 := by positivity
  have hB : 1 + b ^ 2 * x ^ 2 ≠ 0 := by positivity
  unfold productLogDeriv logQuadDeriv logQuadFun negInvCube hKernel
  field_simp [hx, hA, hB]

private theorem productLog_mul_negInvCube_tendsto_zero
    (a b : ℝ) :
    Tendsto (productLog a b * negInvCube)
      (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero'
    (g := fun x : ℝ => (a ^ 2 * b ^ 2 / 3) * x)
    (Filter.Eventually.of_forall fun x => norm_nonneg _)
    ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := hx
    have hA0 := logQuad_nonneg a x
    have hB0 := logQuad_nonneg b x
    have hA :
        Real.log (1 + a ^ 2 * x ^ 2) ≤ a ^ 2 * x ^ 2 := by
      have h :=
        Real.log_le_sub_one_of_pos
          (show 0 < 1 + a ^ 2 * x ^ 2 by positivity)
      nlinarith
    have hB :
        Real.log (1 + b ^ 2 * x ^ 2) ≤ b ^ 2 * x ^ 2 := by
      have h :=
        Real.log_le_sub_one_of_pos
          (show 0 < 1 + b ^ 2 * x ^ 2 by positivity)
      nlinarith
    have hprod :
        Real.log (1 + a ^ 2 * x ^ 2) *
            Real.log (1 + b ^ 2 * x ^ 2) ≤
          (a ^ 2 * x ^ 2) * (b ^ 2 * x ^ 2) :=
      mul_le_mul hA hB hB0 (mul_nonneg (sq_nonneg a) (sq_nonneg x))
    have hden : 0 < 3 * x ^ 3 := by positivity
    calc
      ‖(productLog a b * negInvCube) x‖ =
          (Real.log (1 + a ^ 2 * x ^ 2) *
            Real.log (1 + b ^ 2 * x ^ 2)) /
              (3 * x ^ 3) := by
            rw [Real.norm_eq_abs]
            unfold productLog negInvCube
            dsimp only [Pi.mul_apply]
            rw [abs_mul, abs_div, abs_neg, abs_one,
              abs_of_pos hden,
              abs_of_nonneg (mul_nonneg hA0 hB0)]
            ring
      _ ≤ ((a ^ 2 * x ^ 2) * (b ^ 2 * x ^ 2)) /
            (3 * x ^ 3) :=
        div_le_div_of_nonneg_right hprod hden.le
      _ = (a ^ 2 * b ^ 2 / 3) * x := by
        field_simp [hxpos.ne']
  · have hfull :
        Tendsto (fun x : ℝ => (a ^ 2 * b ^ 2 / 3) * x)
          (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul
        (continuousAt_id.tendsto :
          Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0))
    exact hfull.mono_left inf_le_left

private theorem productLog_mul_negInvCube_tendsto_atTop_zero
    (a b : ℝ) :
    Tendsto (productLog a b * negInvCube) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let C : ℝ :=
    ((4 * (1 + a ^ 2) ^ (1 / 4 : ℝ)) *
      (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ))) / 3
  have hupper :
      Tendsto (fun x : ℝ => C * x ^ (-2 : ℝ))
        atTop (𝓝 0) := by
    have hpow :
        Tendsto (fun x : ℝ => x ^ (-(2 : ℝ)))
          atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    convert hpow.const_mul C using 1 <;> norm_num
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun x => norm_nonneg _)
    ?_ hupper
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hA0 := logQuad_nonneg a x
  have hB0 := logQuad_nonneg b x
  have hA := logQuad_le_tail a x hx
  have hB := logQuad_le_tail b x hx
  have hprod :
      Real.log (1 + a ^ 2 * x ^ 2) *
          Real.log (1 + b ^ 2 * x ^ 2) ≤
        (4 * (1 + a ^ 2) ^ (1 / 4 : ℝ) *
          x ^ (1 / 2 : ℝ)) *
        (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ) *
          x ^ (1 / 2 : ℝ)) :=
    mul_le_mul hA hB hB0 (by positivity)
  have hden : 0 < 3 * x ^ 3 := by positivity
  calc
    ‖(productLog a b * negInvCube) x‖ =
        (Real.log (1 + a ^ 2 * x ^ 2) *
          Real.log (1 + b ^ 2 * x ^ 2)) /
            (3 * x ^ 3) := by
          rw [Real.norm_eq_abs]
          unfold productLog negInvCube
          dsimp only [Pi.mul_apply]
          rw [abs_mul, abs_div, abs_neg, abs_one,
            abs_of_pos hden,
            abs_of_nonneg (mul_nonneg hA0 hB0)]
          ring
    _ ≤ ((4 * (1 + a ^ 2) ^ (1 / 4 : ℝ) *
            x ^ (1 / 2 : ℝ)) *
          (4 * (1 + b ^ 2) ^ (1 / 4 : ℝ) *
            x ^ (1 / 2 : ℝ))) / (3 * x ^ 3) :=
      div_le_div_of_nonneg_right hprod hden.le
    _ = C * x ^ (-2 : ℝ) := by
      dsimp [C]
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
        Real.rpow_neg hxpos.le]
      field_simp [hxpos.ne']
      rw [← Real.rpow_natCast (x ^ (1 / 2 : ℝ)) 2,
        ← Real.rpow_mul hxpos.le]
      norm_num
      ring

private theorem productLogDeriv_mul_negInvCube_integrable
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (productLogDeriv a b * negInvCube)
      (Ioi (0 : ℝ)) volume := by
  have hsum :
      IntegrableOn
        (fun x : ℝ =>
          a ^ 2 * hKernel a b x + b ^ 2 * hKernel b a x)
        (Ioi (0 : ℝ)) volume :=
    ((hKernel_integrable a b ha).const_mul _).add
      ((hKernel_integrable b a hb).const_mul _)
  have hmajor :
      IntegrableOn
        (fun x : ℝ =>
          -(2 / 3) *
            (a ^ 2 * hKernel a b x + b ^ 2 * hKernel b a x))
        (Ioi (0 : ℝ)) volume :=
    hsum.const_mul _
  exact hmajor.congr_fun
    (fun x hx =>
      (productLogDeriv_mul_negInvCube_eq a b x hx.ne').symm)
    measurableSet_Ioi

private theorem targetKernel_integral_pos_raw
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), targetKernel a b x ∂volume) =
      (2 / 3) *
        (a ^ 2 * (Real.pi *
            (b - a * Real.log ((a + b) / a))) +
          b ^ 2 * (Real.pi *
            (a - b * Real.log ((a + b) / b)))) := by
  have huv' :
      IntegrableOn (productLog a b * invFourth)
        (Ioi (0 : ℝ)) volume := by
    exact (targetKernel_integrable a b).congr_fun
      (fun x _ => by
        simp [targetKernel, productLog, invFourth, div_eq_mul_inv])
      measurableSet_Ioi
  have hu'v :=
    productLogDeriv_mul_negInvCube_integrable a b ha hb
  have hibp :=
    integral_Ioi_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ))
      (u := productLog a b)
      (u' := productLogDeriv a b)
      (v := negInvCube)
      (v' := invFourth)
      (fun x _ => productLog_hasDerivAt a b x)
      (fun x hx => negInvCube_hasDerivAt x hx.ne')
      huv' hu'v
      (productLog_mul_negInvCube_tendsto_zero a b)
      (productLog_mul_negInvCube_tendsto_atTop_zero a b)
  have hha :
      IntegrableOn (fun x : ℝ => a ^ 2 * hKernel a b x)
        (Ioi (0 : ℝ)) volume :=
    (hKernel_integrable a b ha).const_mul _
  have hhb :
      IntegrableOn (fun x : ℝ => b ^ 2 * hKernel b a x)
        (Ioi (0 : ℝ)) volume :=
    (hKernel_integrable b a hb).const_mul _
  have hderivIntegral :
      (∫ x in Ioi (0 : ℝ),
        productLogDeriv a b x * negInvCube x ∂volume) =
        -(2 / 3) *
          (a ^ 2 * (Real.pi *
              (b - a * Real.log ((a + b) / a))) +
            b ^ 2 * (Real.pi *
              (a - b * Real.log ((a + b) / b)))) := by
    calc
      (∫ x in Ioi (0 : ℝ),
          productLogDeriv a b x * negInvCube x ∂volume) =
          ∫ x in Ioi (0 : ℝ),
            -(2 / 3) *
              (a ^ 2 * hKernel a b x +
                b ^ 2 * hKernel b a x) ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            exact productLogDeriv_mul_negInvCube_eq a b x hx.ne'
      _ = -(2 / 3) *
            ((∫ x in Ioi (0 : ℝ), a ^ 2 * hKernel a b x ∂volume) +
              ∫ x in Ioi (0 : ℝ), b ^ 2 * hKernel b a x ∂volume) := by
            rw [integral_const_mul]
            rw [integral_add hha hhb]
      _ = -(2 / 3) *
            (a ^ 2 *
                (∫ x in Ioi (0 : ℝ), hKernel a b x ∂volume) +
              b ^ 2 *
                ∫ x in Ioi (0 : ℝ), hKernel b a x ∂volume) := by
            rw [integral_const_mul, integral_const_mul]
      _ = -(2 / 3) *
          (a ^ 2 * (Real.pi *
              (b - a * Real.log ((a + b) / a))) +
            b ^ 2 * (Real.pi *
              (a - b * Real.log ((a + b) / b)))) := by
            rw [hKernel_integral a b ha hb,
              hKernel_integral b a hb ha]
            ring
  have hibp' :
      (∫ x in Ioi (0 : ℝ), targetKernel a b x ∂volume) =
        0 - 0 -
          ∫ x in Ioi (0 : ℝ),
            productLogDeriv a b x * negInvCube x ∂volume := by
    simpa [targetKernel, productLog, invFourth, div_eq_mul_inv] using hibp
  rw [hibp', hderivIntegral]
  ring

private theorem targetKernel_integral_pos
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), targetKernel a b x ∂volume) =
      (2 * Real.pi / 3) *
        (a * b * (a + b) +
          a ^ 3 * Real.log a + b ^ 3 * Real.log b -
          (a ^ 3 + b ^ 3) * Real.log (a + b)) := by
  rw [targetKernel_integral_pos_raw a b ha hb]
  have hab : 0 < a + b := add_pos ha hb
  rw [Real.log_div hab.ne' ha.ne',
    Real.log_div hab.ne' hb.ne']
  ring

private theorem targetKernel_eq_abs
    (a b x : ℝ) :
    targetKernel a b x = targetKernel |a| |b| x := by
  unfold targetKernel
  rw [sq_abs, sq_abs]

private theorem targetKernel_integral_eq_abs
    (a b : ℝ) :
    (∫ x in Ioi (0 : ℝ), targetKernel a b x ∂volume) =
      ∫ x in Ioi (0 : ℝ), targetKernel |a| |b| x ∂volume := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  exact targetKernel_eq_abs a b x


private def mixedKernel (a b x : ℝ) : ℝ :=
  1 / ((1 + a ^ 2 * x ^ 2) * (1 + b ^ 2 * x ^ 2))

private theorem mixedKernel_eq_partialFractions
    (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) :
    mixedKernel a b x =
      a ^ 2 / (a ^ 2 - b ^ 2) * oneKernel a x -
        b ^ 2 / (a ^ 2 - b ^ 2) * oneKernel b x := by
  have hfactor : a ^ 2 - b ^ 2 ≠ 0 := by
    intro h
    have hsquare : a ^ 2 = b ^ 2 := by linarith
    have : a = b := by nlinarith
    exact hab this
  have hA : 1 + a ^ 2 * x ^ 2 ≠ 0 := by positivity
  have hB : 1 + b ^ 2 * x ^ 2 ≠ 0 := by positivity
  unfold mixedKernel oneKernel
  field_simp [hfactor, hA, hB]
  ring

private theorem mixedKernel_integral
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), mixedKernel a b x ∂volume) =
      Real.pi / (2 * (a + b)) := by
  by_cases hab : a = b
  · subst b
    have heq :
        mixedKernel a a = squareOneKernel a := by
      funext x
      unfold mixedKernel squareOneKernel
      ring
    rw [heq, squareOneKernel_integral a ha]
    field_simp [ha.ne']
    norm_num
  · have hfactor : a ^ 2 - b ^ 2 ≠ 0 := by
      intro h
      have hsquare : a ^ 2 = b ^ 2 := by linarith
      have : a = b := by nlinarith
      exact hab this
    calc
      (∫ x in Ioi (0 : ℝ), mixedKernel a b x ∂volume) =
          ∫ x in Ioi (0 : ℝ),
            (a ^ 2 / (a ^ 2 - b ^ 2) * oneKernel a x -
              b ^ 2 / (a ^ 2 - b ^ 2) * oneKernel b x) ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x _
            exact mixedKernel_eq_partialFractions a b x ha hb hab
      _ = a ^ 2 / (a ^ 2 - b ^ 2) *
            ∫ x in Ioi (0 : ℝ), oneKernel a x ∂volume -
          b ^ 2 / (a ^ 2 - b ^ 2) *
            ∫ x in Ioi (0 : ℝ), oneKernel b x ∂volume := by
            rw [integral_sub
              ((oneKernel_integrable a ha).const_mul _)
              ((oneKernel_integrable b hb).const_mul _)]
            rw [integral_const_mul, integral_const_mul]
      _ = a ^ 2 / (a ^ 2 - b ^ 2) *
            (Real.pi / (2 * a)) -
          b ^ 2 / (a ^ 2 - b ^ 2) *
            (Real.pi / (2 * b)) := by
            rw [oneKernel_integral a ha, oneKernel_integral b hb]
      _ = Real.pi / (2 * (a + b)) := by
            have hsum : a + b ≠ 0 := by positivity
            field_simp [ha.ne', hb.ne', hfactor, hsum]
            ring


private theorem I_eq_closedForm_pos
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    I a b = closedForm a b := by
  change
    (∫ x in Ioi (0 : ℝ), targetKernel a b x ∂volume) =
      closedForm a b
  rw [targetKernel_integral_pos a b ha hb]
  rfl

private theorem I_eq_closedForm_nonneg
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    I a b = closedForm a b := by
  rcases ha.eq_or_lt with ha0 | ha
  · subst a
    simp [I, integrand, closedForm]
  · rcases hb.eq_or_lt with hb0 | hb
    · subst b
      simp [I, integrand, closedForm]
    · exact I_eq_closedForm_pos a b ha hb

private def continuousClosedForm (a b : ℝ) : ℝ :=
  2 * Real.pi / 3 *
    (a * b * (a + b) +
      a ^ 2 * (a * Real.log a) +
      b ^ 2 * (b * Real.log b) -
      (a ^ 2 - a * b + b ^ 2) *
        ((a + b) * Real.log (a + b)))

private theorem closedForm_eq_continuousClosedForm (a b : ℝ) :
    closedForm a b = continuousClosedForm a b := by
  unfold closedForm continuousClosedForm
  ring

private theorem continuous_continuousClosedForm :
    Continuous
      (fun p : ℝ × ℝ =>
        continuousClosedForm p.1 p.2) := by
  unfold continuousClosedForm
  fun_prop

private theorem J_eq_formula
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    J a b =
      2 * Real.pi * a * b -
        2 * Real.pi * a ^ 2 * Real.log ((a + b) / a) := by
  calc
    J a b =
        2 * a *
          ∫ x in Ioi (0 : ℝ), hKernel a b x ∂volume := by
      rw [← integral_const_mul]
      unfold J
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      unfold hKernel
      ring
    _ = 2 * a *
        (Real.pi *
          (b - a * Real.log ((a + b) / a))) := by
      rw [hKernel_integral a b ha hb]
    _ = 2 * Real.pi * a * b -
        2 * Real.pi * a ^ 2 * Real.log ((a + b) / a) := by
      ring

private theorem K_eq_formula
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    K a b = 2 * Real.pi * a * b / (a + b) := by
  calc
    K a b =
        (4 * a * b) *
          ∫ x in Ioi (0 : ℝ), mixedKernel a b x ∂volume := by
      rw [← integral_const_mul]
      unfold K
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      unfold mixedKernel
      ring
    _ = (4 * a * b) * (Real.pi / (2 * (a + b))) := by
      rw [mixedKernel_integral a b ha hb]
    _ = 2 * Real.pi * a * b / (a + b) := by
      have hab : a + b ≠ 0 := (add_pos ha hb).ne'
      field_simp [ha.ne', hb.ne', hab]
      ring

private theorem closedForm_alpha_hasDerivAt
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun t : ℝ => closedForm t b)
      (2 * Real.pi * a * b -
        2 * Real.pi * a ^ 2 * Real.log ((a + b) / a)) a := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 a :=
    hasDerivAt_id a
  have hsum : HasDerivAt (fun t : ℝ => t + b) 1 a := by
    simpa using hid.add_const b
  have hloga :
      HasDerivAt (fun t : ℝ => Real.log t) a⁻¹ a :=
    Real.hasDerivAt_log ha.ne'
  have hlogsum :
      HasDerivAt (fun t : ℝ => Real.log (t + b))
        (a + b)⁻¹ a := by
    simpa only [Function.comp_apply, one_mul, mul_one] using
      (Real.hasDerivAt_log (add_pos ha hb).ne').comp a hsum
  have htermOne := (hid.mul_const b).mul hsum
  have htermA := (hid.pow 3).mul hloga
  have htermB :
      HasDerivAt (fun _ : ℝ => b ^ 3 * Real.log b) 0 a :=
    hasDerivAt_const a _
  have hlast := ((hid.pow 3).add_const (b ^ 3)).mul hlogsum
  have hcore := ((htermOne.add htermA).add htermB).sub hlast
  have hscaled := hcore.const_mul (2 * Real.pi / 3)
  simp only [Pi.pow_apply, one_mul, mul_one] at hscaled
  unfold closedForm
  rw [Real.log_div (add_pos ha hb).ne' ha.ne']
  convert hscaled using 1
  field_simp [ha.ne', (add_pos ha hb).ne']
  ring

private theorem logQuad_div_sq_tendsto (a : ℝ) :
    Tendsto
      (fun x : ℝ => Real.log (1 + a ^ 2 * x ^ 2) / x ^ 2)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds (a ^ 2)) := by
  have hinner :
      HasDerivAt (fun t : ℝ => 1 + a ^ 2 * t) (a ^ 2) 0 := by
    convert
      (hasDerivAt_const (0 : ℝ) 1).add
        ((hasDerivAt_id (0 : ℝ)).const_mul (a ^ 2))
      using 1 <;>
      simp only [id_eq, zero_add, mul_one]
  have hlog :
      HasDerivAt
        (fun t : ℝ => Real.log (1 + a ^ 2 * t))
        (a ^ 2) 0 := by
    have hout :
        HasDerivAt Real.log 1 (1 + a ^ 2 * 0) := by
      convert
        Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
        using 1 <;>
        ring
    simpa only [Function.comp_apply, one_mul] using
      hout.comp 0 hinner
  have hslope :
      Tendsto
        (fun t : ℝ => t⁻¹ * Real.log (1 + a ^ 2 * t))
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds (a ^ 2)) := by
    simpa only [zero_add, mul_zero, add_zero, Real.log_one,
      sub_zero, smul_eq_mul] using hlog.tendsto_slope_zero
  have hsquare :
      Tendsto (fun x : ℝ => x ^ 2)
        (nhdsWithin 0 ({0}ᶜ : Set ℝ))
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hfull :
          Tendsto (fun x : ℝ => x ^ 2)
            (nhds (0 : ℝ)) (nhds 0) := by
          simpa using
            ((continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).pow 2).tendsto
      exact hfull.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := by simpa using hx
      simpa [hx0]
  have hcomp := hslope.comp hsquare
  convert hcomp using 1
  funext x
  simp only [Function.comp_apply, div_eq_mul_inv]
  ring

private theorem JFormula_beta_hasDerivAt
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt
      (fun t : ℝ =>
        2 * Real.pi * a * t -
          2 * Real.pi * a ^ 2 * Real.log ((a + t) / a))
      (2 * Real.pi * a * b / (a + b)) b := by
  have harg :
      HasDerivAt (fun t : ℝ => (a + t) / a) (1 / a) b := by
    convert
      ((hasDerivAt_const b a).add (hasDerivAt_id b)).div_const a
      using 1 <;>
      simp only [id_eq, zero_add, one_div]
  have hlog :
      HasDerivAt (fun t : ℝ => Real.log ((a + t) / a))
        (((a + b) / a)⁻¹ * (1 / a)) b := by
    exact
      (Real.hasDerivAt_log
        (by positivity : (a + b) / a ≠ 0)).comp b harg
  have hlin :=
    (hasDerivAt_id b).const_mul (2 * Real.pi * a)
  have hscaledLog := hlog.const_mul (2 * Real.pi * a ^ 2)
  have hsub := hlin.sub hscaledLog
  convert hsub using 1
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  field_simp [ha.ne', hab]
  ring

-- Statement correction: the integrand is defined as 0 at x = 0, so the
-- intended limit is punctured rather than a full-neighborhood limit.
theorem gap1 (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    Tendsto (fun x : ℝ => integrand α β x)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ))
      (nhds (α ^ 2 * β ^ 2)) := by
  have hA := logQuad_div_sq_tendsto α
  have hB := logQuad_div_sq_tendsto β
  apply (hA.mul hB).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  unfold integrand
  field_simp [hx0]

theorem gap2 :
    ContinuousOn (fun p : ℝ × ℝ => I p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) := by
  apply continuous_continuousClosedForm.continuousOn.congr
  intro p hp
  calc
    I p.1 p.2 = closedForm p.1 p.2 :=
      I_eq_closedForm_nonneg p.1 p.2 hp.1 hp.2
    _ = continuousClosedForm p.1 p.2 :=
      closedForm_eq_continuousClosedForm p.1 p.2

theorem gap3 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    deriv (fun a : ℝ => I a β) α = J α β := by
  have heq :
      (fun a : ℝ => I a β) =ᶠ[nhds α]
        fun a : ℝ => closedForm a β := by
    filter_upwards [Ioi_mem_nhds hα] with a ha
    exact I_eq_closedForm_pos a β ha hβ
  rw [heq.deriv_eq,
    (closedForm_alpha_hasDerivAt α β hα hβ).deriv,
    J_eq_formula α β hα hβ]

theorem gap4 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    deriv (fun b : ℝ => deriv (fun a : ℝ => I a b) α) β =
      deriv (fun b : ℝ => J α b) β := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hβ] with b hb
  exact gap3 α b hα hb

theorem gap5 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    deriv (fun b : ℝ => J α b) β = K α β := by
  have heq :
      (fun b : ℝ => J α b) =ᶠ[nhds β]
        fun b : ℝ =>
          2 * Real.pi * α * b -
            2 * Real.pi * α ^ 2 *
              Real.log ((α + b) / α) := by
    filter_upwards [Ioi_mem_nhds hβ] with b hb
    exact J_eq_formula α b hα hb
  rw [heq.deriv_eq,
    (JFormula_beta_hasDerivAt α β hα hβ).deriv,
    K_eq_formula α β hα hβ]

theorem gap6 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    deriv (fun b : ℝ => deriv (fun a : ℝ => I a b) α) β =
      K α β := by
  rw [gap4 α β hα hβ, gap5 α β hα hβ]

theorem gap7 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    K α β = 2 * Real.pi * α * β / (α + β) :=
  K_eq_formula α β hα hβ

theorem gap8 (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, ∀ β : ℝ, 0 < β →
      deriv (fun a : ℝ => I a β) α =
        2 * Real.pi * α * β -
          2 * Real.pi * α ^ 2 * Real.log (α + β) + C := by
  refine ⟨2 * Real.pi * α ^ 2 * Real.log α, ?_⟩
  intro β hβ
  rw [gap3 α β hα hβ, J_eq_formula α β hα hβ,
    Real.log_div (add_pos hα hβ).ne' hα.ne']
  ring

theorem gap9 (α : ℝ) (hα : 0 < α) :
    J α 0 = 0 := by
  unfold J
  simp

theorem gap10 (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ,
      (∀ β : ℝ, 0 < β →
        deriv (fun a : ℝ => I a β) α =
          2 * Real.pi * α * β -
            2 * Real.pi * α ^ 2 * Real.log (α + β) + C) ∧
      J α 0 = -2 * Real.pi * α ^ 2 * Real.log α + C := by
  refine ⟨2 * Real.pi * α ^ 2 * Real.log α, ?_, ?_⟩
  · intro β hβ
    rw [gap3 α β hα hβ, J_eq_formula α β hα hβ,
      Real.log_div (add_pos hα hβ).ne' hα.ne']
    ring
  · rw [gap9 α hα]
    ring

theorem gap11 (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ,
      (∀ β : ℝ, 0 < β →
        deriv (fun a : ℝ => I a β) α =
          2 * Real.pi * α * β -
            2 * Real.pi * α ^ 2 * Real.log (α + β) + C) ∧
      0 = -2 * Real.pi * α ^ 2 * Real.log α + C := by
  rcases gap10 α hα with ⟨C, hC, h0⟩
  refine ⟨C, hC, ?_⟩
  simpa [gap9 α hα] using h0

theorem gap12 (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ,
      (∀ β : ℝ, 0 < β →
        deriv (fun a : ℝ => I a β) α =
          2 * Real.pi * α * β -
            2 * Real.pi * α ^ 2 * Real.log (α + β) + C) ∧
      C = 2 * Real.pi * α ^ 2 * Real.log α := by
  rcases gap11 α hα with ⟨C, hC, h0⟩
  exact ⟨C, hC, by linarith⟩

theorem gap13 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    deriv (fun a : ℝ => I a β) α =
      2 * Real.pi * α * β -
        2 * Real.pi * α ^ 2 * Real.log (α + β) +
        2 * Real.pi * α ^ 2 * Real.log α := by
  rcases gap12 α hα with ⟨C, hC, hCeq⟩
  simpa [hCeq] using hC β hβ

theorem gap14 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    I α β =
      -(2 / 3 : ℝ) * Real.pi * (α ^ 3 + β ^ 3) * Real.log (α + β) +
        2 * Real.pi / 9 * (α + β) ^ 3 -
        2 * Real.pi / 9 * α ^ 3 -
        2 * Real.pi / 9 * β ^ 3 +
        2 / 3 * Real.pi *
          (α ^ 3 * Real.log α + β ^ 3 * Real.log β) := by
  rw [I_eq_closedForm_pos α β hα hβ]
  unfold closedForm
  ring

theorem gap15 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    I α β = closedForm α β := by
  rw [gap14 α β hα hβ]
  unfold closedForm
  ring

theorem gap16 (α β : ℝ) :
    I α β = closedForm |α| |β| := by
  have heven : I α β = I |α| |β| := by
    unfold I integrand
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [sq_abs, sq_abs]
  rw [heven]
  by_cases hα : α = 0
  · subst α
    simp [I, integrand, closedForm]
  by_cases hβ : β = 0
  · subst β
    simp [I, integrand, closedForm]
  exact gap15 |α| |β| (abs_pos.mpr hα) (abs_pos.mpr hβ)

end

end ProofGap.Exercise3802
