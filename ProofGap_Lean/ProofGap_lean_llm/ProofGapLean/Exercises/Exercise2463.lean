import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2463

noncomputable section

def EllipsoidPoint (a b c x y z : ℝ) : Prop :=
  x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 + z ^ 2 / c ^ 2 = 1

def sectionArea (a b c x : ℝ) : ℝ :=
  Real.pi * b * c * (1 - x ^ 2 / a ^ 2)

def volume (a b c : ℝ) : ℝ :=
  ∫ x in -a..a, sectionArea a b c x

theorem gap1 (a b c x y z : ℝ) (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hp : EllipsoidPoint a b c x y z)
    (hx : x ^ 2 ≠ a ^ 2) :
    y ^ 2 / (b ^ 2 * (1 - x ^ 2 / a ^ 2)) +
        z ^ 2 / (c ^ 2 * (1 - x ^ 2 / a ^ 2)) = 1 := by
  unfold EllipsoidPoint at hp
  have hden : 1 - x ^ 2 / a ^ 2 ≠ 0 := by
    intro hd
    apply hx
    have hq : x ^ 2 / a ^ 2 = 1 := by
      linarith
    exact (div_eq_one_iff_eq (pow_ne_zero 2 ha)).mp hq
  have hrest : y ^ 2 / b ^ 2 + z ^ 2 / c ^ 2 = 1 - x ^ 2 / a ^ 2 := by
    linarith [hp]
  calc
    y ^ 2 / (b ^ 2 * (1 - x ^ 2 / a ^ 2)) +
          z ^ 2 / (c ^ 2 * (1 - x ^ 2 / a ^ 2)) =
        (y ^ 2 / b ^ 2 + z ^ 2 / c ^ 2) /
          (1 - x ^ 2 / a ^ 2) := by
            field_simp [ha, hb, hc, hden] <;> ring
    _ = (1 - x ^ 2 / a ^ 2) / (1 - x ^ 2 / a ^ 2) := by rw [hrest]
    _ = 1 := div_self hden

theorem gap2 (a b x : ℝ) (hx : -a ≤ x ∧ x ≤ a) :
    ∃ u : ℝ, u = b * Real.sqrt (1 - x ^ 2 / a ^ 2) := by
  exact ⟨b * Real.sqrt (1 - x ^ 2 / a ^ 2), rfl⟩

theorem gap3 (a c x : ℝ) (hx : -a ≤ x ∧ x ≤ a) :
    ∃ v : ℝ, v = c * Real.sqrt (1 - x ^ 2 / a ^ 2) := by
  exact ⟨c * Real.sqrt (1 - x ^ 2 / a ^ 2), rfl⟩

theorem gap4 (a b c x : ℝ) :
    sectionArea a b c x =
      Real.pi * b * c * (1 - x ^ 2 / a ^ 2) := by
  rfl

theorem gap5 (a x : ℝ) (hx : x ∈ Set.Icc (-a) a) :
    -a ≤ x := by
  exact hx.1

theorem gap6 (a x : ℝ) (hx : x ∈ Set.Icc (-a) a) :
    x ≤ a := by
  exact hx.2

theorem gap7 (a b c V : ℝ) (hV : V = volume a b c) :
    V = ∫ x in -a..a, sectionArea a b c x := by
  simpa only [volume] using hV

theorem gap8 (a b c V : ℝ) (hV : V = volume a b c) :
    V = ∫ x in -a..a,
      (1 - x ^ 2 / a ^ 2) * Real.pi * b * c := by
  simpa only [volume, sectionArea, mul_comm, mul_left_comm, mul_assoc] using hV

theorem gap9 (a b c : ℝ) (ha : 0 < a) :
    (∫ x in -a..a,
      (1 - x ^ 2 / a ^ 2) * Real.pi * b * c) =
        4 / 3 * Real.pi * a * b * c := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hcube (x : ℝ) :
      HasDerivAt (fun t : ℝ => t * t * t) (3 * x ^ 2) x := by
    convert
      (((hasDerivAt_id x).mul (hasDerivAt_id x)).mul
        (hasDerivAt_id x)) using 1 <;>
      simp <;> ring
  have hderiv (x : ℝ) :
      HasDerivAt
        (fun t : ℝ => Real.pi * b * c *
          (t - (t * t * t) / (3 * a ^ 2)))
        ((1 - x ^ 2 / a ^ 2) * Real.pi * b * c) x := by
    convert
      (((hasDerivAt_id x).sub
        ((hcube x).div_const (3 * a ^ 2))).const_mul
          (Real.pi * b * c)) using 1 <;>
      field_simp [ha0] <;> ring
  have hsq : Continuous (fun x : ℝ => x * x) :=
    continuous_id.mul continuous_id
  have hone : Continuous (fun _ : ℝ => (1 : ℝ)) := continuous_const
  have hpi : Continuous (fun _ : ℝ => Real.pi) := continuous_const
  have hbcont : Continuous (fun _ : ℝ => b) := continuous_const
  have hccont : Continuous (fun _ : ℝ => c) := continuous_const
  have hbase : Continuous (fun x : ℝ => 1 - (x * x) / a ^ 2) :=
    hone.sub (hsq.div_const (a ^ 2))
  have hcont : Continuous (fun x : ℝ =>
      (1 - x ^ 2 / a ^ 2) * Real.pi * b * c) := by
    simpa only [pow_two] using
      (((hbase.mul hpi).mul hbcont).mul hccont)
  have hint : IntervalIntegrable
      (fun x : ℝ => (1 - x ^ 2 / a ^ 2) * Real.pi * b * c)
      MeasureTheory.volume (-a) a :=
    hcont.intervalIntegrable (-a) a
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x) hint]
  field_simp [ha0] <;> ring

theorem gap10 (a b c V : ℝ) (ha : 0 < a)
    (hV : V = volume a b c) :
    V = 4 / 3 * Real.pi * a * b * c := by
  calc
    V = ∫ x in -a..a,
        (1 - x ^ 2 / a ^ 2) * Real.pi * b * c := gap8 a b c V hV
    _ = 4 / 3 * Real.pi * a * b * c := gap9 a b c ha

end

end ProofGap.Exercise2463
