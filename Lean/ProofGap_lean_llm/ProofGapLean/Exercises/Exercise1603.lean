import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1603

noncomputable section

def curve (p q x : ℝ) := Real.sqrt (2 * p * x - q * x ^ 2)
def powThreeHalves (u : ℝ) := u * Real.sqrt u
def curvatureRadius (p q x : ℝ) :=
  powThreeHalves (1 + (deriv (curve p q) x) ^ 2) /
    |deriv (deriv (curve p q)) x|
def subnormal (p q x : ℝ) :=
  |curve p q x * Real.sqrt (1 + (deriv (curve p q) x) ^ 2)|

private theorem radicand_eventually_pos (p q x : ℝ)
    (hy : 0 < 2 * p * x - q * x ^ 2) :
    ∀ᶠ t in nhds x, 0 < 2 * p * t - q * t ^ 2 := by
  have hcont : ContinuousAt (fun t : ℝ => 2 * p * t - q * t ^ 2) x :=
    (continuousAt_const.mul continuousAt_id).sub
      (continuousAt_const.mul (continuousAt_id.pow 2))
  exact hcont.eventually (Ioi_mem_nhds hy)

private theorem curve_hasDerivAt (p q x : ℝ)
    (hy : 0 < 2 * p * x - q * x ^ 2) :
    HasDerivAt (curve p q)
      ((1 / (2 * curve p q x)) * (2 * p - 2 * q * x)) x := by
  have hinner :
      HasDerivAt (fun t : ℝ => 2 * p * t - q * t ^ 2)
        (2 * p - 2 * q * x) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).const_mul (2 * p)).sub
        (((hasDerivAt_id x).pow 2).const_mul q))
  simpa [curve] using
    (Real.hasDerivAt_sqrt (ne_of_gt hy)).comp x hinner

private theorem differentiableAt_deriv_curve (p q x : ℝ)
    (hy : 0 < 2 * p * x - q * x ^ 2) :
    DifferentiableAt ℝ (deriv (curve p q)) x := by
  have hcurve := curve_hasDerivAt p q x hy
  have hcurve_ne : curve p q x ≠ 0 := by
    exact ne_of_gt (by simpa [curve] using Real.sqrt_pos.2 hy)
  have hnum : HasDerivAt (fun t : ℝ => p - q * t) (-q) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_const x p).sub ((hasDerivAt_id x).const_mul q)
  have hquot := hnum.div hcurve hcurve_ne
  have hpos := radicand_eventually_pos p q x hy
  have heq :
      (fun t => (p - q * t) / curve p q t) =ᶠ[nhds x]
        deriv (curve p q) := by
    filter_upwards [hpos] with t ht
    have hct : curve p q t ≠ 0 := by
      exact ne_of_gt (by simpa [curve] using Real.sqrt_pos.2 ht)
    rw [(curve_hasDerivAt p q t ht).deriv]
    field_simp [hct]
    <;> ring
  have hderiv := hquot.congr_of_eventuallyEq heq.symm
  exact hderiv.differentiableAt

theorem gap1 (p q x : ℝ) (hp : 0 < p) (hy : 0 < 2 * p * x - q * x ^ 2) :
    curvatureRadius p q x =
      powThreeHalves (1 + (deriv (curve p q) x) ^ 2) /
        |deriv (deriv (curve p q)) x| := by
  rfl
theorem gap2 (p q x : ℝ) (hp : 0 < p) (hy : 0 < 2 * p * x - q * x ^ 2) :
    subnormal p q x =
      |curve p q x * Real.sqrt (1 + (deriv (curve p q) x) ^ 2)| := by
  rfl
theorem gap3 (p q x : ℝ) (hp : 0 < p) (hy : 0 < 2 * p * x - q * x ^ 2) :
    curvatureRadius p q x / (subnormal p q x) ^ 3 =
      1 / |(curve p q x) ^ 3 * deriv (deriv (curve p q)) x| := by
  have hcurve : 0 < curve p q x := by
    simpa [curve] using Real.sqrt_pos.2 hy
  have hsqrt : 0 < Real.sqrt (1 + (deriv (curve p q) x) ^ 2) := by
    apply Real.sqrt_pos.2
    positivity
  have hsquare :
      (Real.sqrt (1 + (deriv (curve p q) x) ^ 2)) ^ 2 =
        1 + (deriv (curve p q) x) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hpow :
      (1 + (deriv (curve p q) x) ^ 2) *
          Real.sqrt (1 + (deriv (curve p q) x) ^ 2) =
        (Real.sqrt (1 + (deriv (curve p q) x) ^ 2)) ^ 3 := by
    calc
      (1 + (deriv (curve p q) x) ^ 2) *
          Real.sqrt (1 + (deriv (curve p q) x) ^ 2) =
        (Real.sqrt (1 + (deriv (curve p q) x) ^ 2)) ^ 2 *
          Real.sqrt (1 + (deriv (curve p q) x) ^ 2) := by rw [hsquare]
      _ = (Real.sqrt (1 + (deriv (curve p q) x) ^ 2)) ^ 3 := by ring
  have habs_curve :
      |curve p q x * Real.sqrt (1 + (deriv (curve p q) x) ^ 2)| =
        curve p q x * Real.sqrt (1 + (deriv (curve p q) x) ^ 2) :=
    abs_of_pos (mul_pos hcurve hsqrt)
  have habs_product :
      |(curve p q x) ^ 3 * deriv (deriv (curve p q)) x| =
        (curve p q x) ^ 3 * |deriv (deriv (curve p q)) x| := by
    rw [abs_mul, abs_of_pos (pow_pos hcurve 3)]
  unfold curvatureRadius subnormal powThreeHalves
  rw [habs_curve, habs_product, hpow]
  by_cases hsecond : deriv (deriv (curve p q)) x = 0
  · simp [hsecond]
  · field_simp [abs_ne_zero.mpr hsecond, ne_of_gt hcurve, ne_of_gt hsqrt]
    <;> ring
theorem gap4 (p q x : ℝ) (hp : 0 < p) (hy : 0 < 2 * p * x - q * x ^ 2) :
    2 * curve p q x * deriv (curve p q) x = 2 * p - 2 * q * x := by
  have hcurve : 0 < curve p q x := by
    simpa [curve] using Real.sqrt_pos.2 hy
  rw [(curve_hasDerivAt p q x hy).deriv]
  field_simp [ne_of_gt hcurve]
  <;> ring
theorem gap5 (p q x : ℝ) (hp : 0 < p) (hy : 0 < 2 * p * x - q * x ^ 2) :
    curve p q x * deriv (curve p q) x = p - q * x := by
  have h := gap4 p q x hp hy
  linarith
theorem gap6 (p q x : ℝ) (hp : 0 < p) (hy : 0 < 2 * p * x - q * x ^ 2) :
    curve p q x * deriv (deriv (curve p q)) x +
        (deriv (curve p q) x) ^ 2 =
      -q := by
  have hpos := radicand_eventually_pos p q x hy
  have heq :
      (fun t => curve p q t * deriv (curve p q) t) =ᶠ[nhds x]
        (fun t => p - q * t) := by
    filter_upwards [hpos] with t ht
    exact gap5 p q t hp ht
  have hcurve :
      HasDerivAt (curve p q) (deriv (curve p q) x) x :=
    (curve_hasDerivAt p q x hy).differentiableAt.hasDerivAt
  have hderiv :
      HasDerivAt (deriv (curve p q))
        (deriv (deriv (curve p q)) x) x :=
    (differentiableAt_deriv_curve p q x hy).hasDerivAt
  have hproduct := hcurve.mul hderiv
  have hlinear : HasDerivAt (fun t : ℝ => p - q * t) (-q) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_const x p).sub ((hasDerivAt_id x).const_mul q)
  have hu := (hproduct.congr_of_eventuallyEq heq.symm).unique hlinear
  simpa [pow_two, add_comm, add_left_comm, add_assoc] using hu
theorem gap7 (p q x : ℝ) (hp : 0 < p) (hy : 0 < 2 * p * x - q * x ^ 2) :
    (curve p q x) ^ 3 * deriv (deriv (curve p q)) x + (p - q * x) ^ 2 =
      -q * (2 * p * x - q * x ^ 2) := by
  have h5 := gap5 p q x hp hy
  have h6 := gap6 p q x hp hy
  have hsquare :
      (curve p q x) ^ 2 = 2 * p * x - q * x ^ 2 := by
    simpa [curve] using Real.sq_sqrt (le_of_lt hy)
  calc
    (curve p q x) ^ 3 * deriv (deriv (curve p q)) x +
        (p - q * x) ^ 2 =
      (curve p q x) ^ 2 *
        (curve p q x * deriv (deriv (curve p q)) x +
          (deriv (curve p q) x) ^ 2) := by
            rw [← h5]
            ring
    _ = (curve p q x) ^ 2 * (-q) := by rw [h6]
    _ = -q * (2 * p * x - q * x ^ 2) := by
      rw [hsquare]
      ring
theorem gap8 (p q x : ℝ) (hp : 0 < p) (hy : 0 < 2 * p * x - q * x ^ 2) :
    (curve p q x) ^ 3 * deriv (deriv (curve p q)) x = -p ^ 2 := by
  have h7 := gap7 p q x hp hy
  calc
    (curve p q x) ^ 3 * deriv (deriv (curve p q)) x =
        -q * (2 * p * x - q * x ^ 2) - (p - q * x) ^ 2 := by
      linarith
    _ = -p ^ 2 := by ring
theorem gap9 (p q x : ℝ) (hp : 0 < p) (hy : 0 < 2 * p * x - q * x ^ 2) :
    curvatureRadius p q x / (subnormal p q x) ^ 3 = 1 / p ^ 2 := by
  rw [gap3 p q x hp hy, gap8 p q x hp hy]
  have hp2 : 0 < p ^ 2 := sq_pos_of_pos hp
  rw [abs_neg, abs_of_pos hp2]
theorem gap10 (p q x : ℝ) (hp : 0 < p) (hy : 0 < 2 * p * x - q * x ^ 2) :
    curvatureRadius p q x / (subnormal p q x) ^ 3 = 1 / p ^ 2 := by
  exact gap9 p q x hp hy

end
end ProofGap.Exercise1603
