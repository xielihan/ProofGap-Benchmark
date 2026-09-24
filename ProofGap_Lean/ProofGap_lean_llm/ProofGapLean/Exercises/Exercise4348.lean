import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise4348

noncomputable section

open scoped Interval

abbrev Point3 := ℝ × (ℝ × ℝ)

def helicoidParam (u v : ℝ) : Point3 :=
  (u * Real.cos v, (u * Real.sin v, v))

def partialU (u v : ℝ) : Point3 :=
  (deriv (fun s => (helicoidParam s v).1) u,
    (deriv (fun s => (helicoidParam s v).2.1) u,
      deriv (fun s => (helicoidParam s v).2.2) u))

def partialV (u v : ℝ) : Point3 :=
  (deriv (fun s => (helicoidParam u s).1) v,
    (deriv (fun s => (helicoidParam u s).2.1) v,
      deriv (fun s => (helicoidParam u s).2.2) v))

def dot3 (p q : Point3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def E (u v : ℝ) : ℝ := dot3 (partialU u v) (partialU u v)

def G (u v : ℝ) : ℝ := dot3 (partialV u v) (partialV u v)

def F (u v : ℝ) : ℝ := dot3 (partialU u v) (partialV u v)

def areaFactor (u v : ℝ) : ℝ :=
  Real.sqrt (E u v * G u v - F u v ^ 2)

def helicoidSurface (a : ℝ) : Set Point3 :=
  (fun p : ℝ × ℝ => helicoidParam p.1 p.2) ''
    (Set.Ioo (0 : ℝ) a ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))

def helicoidMoment (a : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..a,
    ∫ v in (0 : ℝ)..2 * Real.pi,
      v * areaFactor u v

def antiderivative (u : ℝ) : ℝ :=
  2 * Real.pi ^ 2 *
    (u / 2 * Real.sqrt (1 + u ^ 2) +
      1 / 2 * Real.log (u + Real.sqrt (1 + u ^ 2)))

private theorem antiderivative_hasDerivAt (x : ℝ) :
    HasDerivAt antiderivative
      (2 * Real.pi ^ 2 * Real.sqrt (1 + x ^ 2)) x := by
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have hspos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hpos
  have hsne : Real.sqrt (1 + x ^ 2) ≠ 0 := ne_of_gt hspos
  have hsq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (le_of_lt hpos)
  have hinner : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).const_add 1 using 1 <;>
      simp only [id_eq] <;> ring
  have hsqrt : HasDerivAt
      (fun y : ℝ => Real.sqrt (1 + y ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp x hinner using 1
    field_simp [hsne] <;> ring
  have hargpos : 0 < x + Real.sqrt (1 + x ^ 2) := by
    by_contra hn
    have hle : x + Real.sqrt (1 + x ^ 2) ≤ 0 := le_of_not_gt hn
    have hdiff : 0 ≤ Real.sqrt (1 + x ^ 2) - x := by linarith
    have hmul :
        (Real.sqrt (1 + x ^ 2) - x) *
            (x + Real.sqrt (1 + x ^ 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hdiff hle
    have heq :
        (Real.sqrt (1 + x ^ 2) - x) *
            (x + Real.sqrt (1 + x ^ 2)) = 1 := by
      nlinarith [hsq]
    linarith
  have harg : HasDerivAt
      (fun y : ℝ => y + Real.sqrt (1 + y ^ 2))
      (1 + x / Real.sqrt (1 + x ^ 2)) x := by
    simpa using (hasDerivAt_id x).add hsqrt
  have hlog : HasDerivAt
      (fun y : ℝ => Real.log (y + Real.sqrt (1 + y ^ 2)))
      (1 / Real.sqrt (1 + x ^ 2)) x := by
    have h := (Real.hasDerivAt_log (ne_of_gt hargpos)).comp x harg
    convert h using 1
    field_simp [hsne, ne_of_gt hargpos] <;> ring
  have hprimitive : HasDerivAt
      (fun y : ℝ =>
        y / 2 * Real.sqrt (1 + y ^ 2) +
          1 / 2 * Real.log (y + Real.sqrt (1 + y ^ 2)))
      (Real.sqrt (1 + x ^ 2)) x := by
    convert
      ((((hasDerivAt_id x).div_const 2).mul hsqrt).add
        (hlog.const_mul (1 / 2))) using 1
    simp only [id_eq]
    field_simp [hsne]
    nlinarith [hsq]
  change HasDerivAt
    (fun y : ℝ =>
      2 * Real.pi ^ 2 *
        (y / 2 * Real.sqrt (1 + y ^ 2) +
          1 / 2 * Real.log (y + Real.sqrt (1 + y ^ 2))))
    (2 * Real.pi ^ 2 * Real.sqrt (1 + x ^ 2)) x
  exact hprimitive.const_mul (2 * Real.pi ^ 2)

theorem gap1 (u v : ℝ) :
    E u v =
      (partialU u v).1 ^ 2 +
        (partialU u v).2.1 ^ 2 +
        (partialU u v).2.2 ^ 2 := by
  simp [E, dot3, pow_two]

theorem gap2 (u v : ℝ) :
    (partialU u v).1 ^ 2 +
        (partialU u v).2.1 ^ 2 +
        (partialU u v).2.2 ^ 2 =
      Real.cos v ^ 2 + Real.sin v ^ 2 := by
  have hcos : deriv (fun s : ℝ => s * Real.cos v) u = Real.cos v := by
    simpa using ((hasDerivAt_id u).mul_const (Real.cos v)).deriv
  have hsin : deriv (fun s : ℝ => s * Real.sin v) u = Real.sin v := by
    simpa using ((hasDerivAt_id u).mul_const (Real.sin v)).deriv
  simp [partialU, helicoidParam, hcos, hsin]

theorem gap3 (v : ℝ) :
    Real.cos v ^ 2 + Real.sin v ^ 2 = 1 := by
  simpa [add_comm] using Real.sin_sq_add_cos_sq v

theorem gap4 (u v : ℝ) :
    E u v = 1 := by
  rw [gap1, gap2, gap3]

theorem gap5 (u v : ℝ) :
    G u v =
      (partialV u v).1 ^ 2 +
        (partialV u v).2.1 ^ 2 +
        (partialV u v).2.2 ^ 2 := by
  simp [G, dot3, pow_two]

theorem gap6 (u v : ℝ) :
    (partialV u v).1 ^ 2 +
        (partialV u v).2.1 ^ 2 +
        (partialV u v).2.2 ^ 2 =
      u ^ 2 * Real.sin v ^ 2 +
        u ^ 2 * Real.cos v ^ 2 + 1 := by
  have hcos : deriv (fun s : ℝ => u * Real.cos s) v = -u * Real.sin v := by
    simpa [mul_neg, neg_mul] using ((Real.hasDerivAt_cos v).const_mul u).deriv
  have hsin : deriv (fun s : ℝ => u * Real.sin s) v = u * Real.cos v := by
    simpa using ((Real.hasDerivAt_sin v).const_mul u).deriv
  simp [partialV, helicoidParam, hcos, hsin] <;> ring

theorem gap7 (u v : ℝ) :
    u ^ 2 * Real.sin v ^ 2 +
        u ^ 2 * Real.cos v ^ 2 + 1 =
      1 + u ^ 2 := by
  calc
    u ^ 2 * Real.sin v ^ 2 + u ^ 2 * Real.cos v ^ 2 + 1 =
        u ^ 2 * (Real.sin v ^ 2 + Real.cos v ^ 2) + 1 := by ring
    _ = 1 + u ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring

theorem gap8 (u v : ℝ) :
    G u v = 1 + u ^ 2 := by
  rw [gap5, gap6, gap7]

theorem gap9 (u v : ℝ) :
    F u v =
      (partialU u v).1 * (partialV u v).1 +
        (partialU u v).2.1 * (partialV u v).2.1 +
        (partialU u v).2.2 * (partialV u v).2.2 := by
  simp [F, dot3]

theorem gap10 (u v : ℝ) :
    (partialU u v).1 * (partialV u v).1 +
        (partialU u v).2.1 * (partialV u v).2.1 +
        (partialU u v).2.2 * (partialV u v).2.2 =
      -u * Real.sin v * Real.cos v +
        u * Real.cos v * Real.sin v := by
  have hUcos : deriv (fun s : ℝ => s * Real.cos v) u = Real.cos v := by
    simpa using ((hasDerivAt_id u).mul_const (Real.cos v)).deriv
  have hUsin : deriv (fun s : ℝ => s * Real.sin v) u = Real.sin v := by
    simpa using ((hasDerivAt_id u).mul_const (Real.sin v)).deriv
  have hVcos : deriv (fun s : ℝ => u * Real.cos s) v = -u * Real.sin v := by
    simpa [mul_neg, neg_mul] using ((Real.hasDerivAt_cos v).const_mul u).deriv
  have hVsin : deriv (fun s : ℝ => u * Real.sin s) v = u * Real.cos v := by
    simpa using ((Real.hasDerivAt_sin v).const_mul u).deriv
  simp [partialU, partialV, helicoidParam, hUcos, hUsin, hVcos, hVsin] <;> ring

theorem gap11 (u v : ℝ) :
    -u * Real.sin v * Real.cos v +
        u * Real.cos v * Real.sin v = 0 := by
  ring

theorem gap12 (u v : ℝ) :
    F u v = 0 := by
  rw [gap9, gap10, gap11]

theorem gap13 (u v : ℝ) :
    areaFactor u v = Real.sqrt (1 + u ^ 2) := by
  simp [areaFactor, gap4, gap8, gap12]

theorem gap14 (a : ℝ) (ha : 0 < a) :
    helicoidMoment a =
      ∫ u in (0 : ℝ)..a,
        ∫ v in (0 : ℝ)..2 * Real.pi,
          v * Real.sqrt (1 + u ^ 2) := by
  unfold helicoidMoment
  simp_rw [gap13]

theorem gap15 (a : ℝ) (ha : 0 < a) :
    (∫ u in (0 : ℝ)..a,
        ∫ v in (0 : ℝ)..2 * Real.pi,
          v * Real.sqrt (1 + u ^ 2)) =
      2 * Real.pi ^ 2 *
        (∫ u in (0 : ℝ)..a,
          Real.sqrt (1 + u ^ 2)) := by
  have hint : IntervalIntegrable (fun x : ℝ => x)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    continuous_id.intervalIntegrable 0 (2 * Real.pi)
  have hderiv (x : ℝ) :
      HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    convert (((hasDerivAt_id x).pow 2).div_const 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hid :
      (∫ x : ℝ in (0 : ℝ)..2 * Real.pi, x) = 2 * Real.pi ^ 2 := by
    calc
      (∫ x : ℝ in (0 : ℝ)..2 * Real.pi, x) =
          (fun y : ℝ => y ^ 2 / 2) (2 * Real.pi) -
            (fun y : ℝ => y ^ 2 / 2) 0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x hx => hderiv x) hint
      _ = 2 * Real.pi ^ 2 := by ring
  calc
    (∫ u in (0 : ℝ)..a,
        ∫ v in (0 : ℝ)..2 * Real.pi,
          v * Real.sqrt (1 + u ^ 2)) =
        ∫ u in (0 : ℝ)..a,
          (2 * Real.pi ^ 2) * Real.sqrt (1 + u ^ 2) := by
      apply intervalIntegral.integral_congr
      intro u hu
      change (∫ v in (0 : ℝ)..2 * Real.pi,
          v * Real.sqrt (1 + u ^ 2)) =
        2 * Real.pi ^ 2 * Real.sqrt (1 + u ^ 2)
      rw [intervalIntegral.integral_mul_const, hid]
    _ = 2 * Real.pi ^ 2 *
        (∫ u in (0 : ℝ)..a, Real.sqrt (1 + u ^ 2)) := by
      rw [intervalIntegral.integral_const_mul]

theorem gap16 (a : ℝ) (ha : 0 < a) :
    helicoidMoment a =
      2 * Real.pi ^ 2 *
        (∫ u in (0 : ℝ)..a,
          Real.sqrt (1 + u ^ 2)) := by
  rw [gap14 a ha, gap15 a ha]

theorem gap17 (a : ℝ) (ha : 0 < a) :
    helicoidMoment a = antiderivative a - antiderivative 0 := by
  rw [gap16 a ha]
  rw [← intervalIntegral.integral_const_mul]
  have hinner : Continuous (fun x : ℝ => 1 + x ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hcont : Continuous
      (fun x : ℝ => 2 * Real.pi ^ 2 * Real.sqrt (1 + x ^ 2)) :=
    continuous_const.mul (Real.continuous_sqrt.comp hinner)
  have hint : IntervalIntegrable
      (fun x : ℝ => 2 * Real.pi ^ 2 * Real.sqrt (1 + x ^ 2))
      MeasureTheory.volume 0 a :=
    hcont.intervalIntegrable 0 a
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => antiderivative_hasDerivAt x) hint

theorem gap18 (a : ℝ) (ha : 0 < a) :
    antiderivative a - antiderivative 0 =
      Real.pi ^ 2 *
        (a * Real.sqrt (1 + a ^ 2) +
          Real.log (a + Real.sqrt (1 + a ^ 2))) := by
  simp [antiderivative] <;> ring

theorem gap19 (a : ℝ) (ha : 0 < a) :
    helicoidMoment a =
      Real.pi ^ 2 *
        (a * Real.sqrt (1 + a ^ 2) +
          Real.log (a + Real.sqrt (1 + a ^ 2))) := by
  rw [gap17 a ha, gap18 a ha]

end

end ProofGap.Exercise4348
