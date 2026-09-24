import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1596

noncomputable section

def parabola (p x : ℝ) := Real.sqrt (2 * p * x)
def powThreeHalves (u : ℝ) := u * Real.sqrt u
def curvatureRadius (p x : ℝ) :=
  powThreeHalves (1 + (deriv (parabola p) x) ^ 2) /
    |deriv (deriv (parabola p)) x|

private theorem hasDerivAt_parabola (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    HasDerivAt (parabola p) (p / parabola p x) x := by
  have harg : 2 * p * x ≠ 0 := by
    positivity
  have hsqrt : Real.sqrt (2 * p * x) ≠ 0 := by
    positivity
  have hinner : HasDerivAt (fun y : ℝ => 2 * p * y) (2 * p) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * p)
  unfold parabola
  convert (Real.hasDerivAt_sqrt harg).comp x hinner using 1 <;>
    field_simp [hsqrt] <;> ring

theorem gap1 (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    deriv (parabola p) x = p / parabola p x := by
  exact (hasDerivAt_parabola p x hp hx).deriv
theorem gap2 (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    deriv (deriv (parabola p)) x =
      -(p / (parabola p x) ^ 2) * deriv (parabola p) x := by
  have heq : deriv (parabola p) =ᶠ[nhds x]
      (fun y : ℝ => p / parabola p y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact gap1 p y hp hy
  have hne : parabola p x ≠ 0 := by
    unfold parabola
    positivity
  have hquot :=
    (hasDerivAt_const x p).div (hasDerivAt_parabola p x hp hx) hne
  have hquot_deriv :
      deriv (fun y : ℝ => p / parabola p y) x =
        (0 * parabola p x - p * (p / parabola p x)) /
          (parabola p x) ^ 2 := by
    simpa using hquot.deriv
  calc
    deriv (deriv (parabola p)) x =
        deriv (fun y : ℝ => p / parabola p y) x := heq.deriv_eq
    _ = (0 * parabola p x - p * (p / parabola p x)) /
          (parabola p x) ^ 2 := hquot_deriv
    _ = -(p / (parabola p x) ^ 2) * deriv (parabola p) x := by
      rw [gap1 p x hp hx]
      field_simp [hne]
      <;> ring
theorem gap3 (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    -(p / (parabola p x) ^ 2) * deriv (parabola p) x =
      -(p ^ 2 / (parabola p x) ^ 3) := by
  have hne : parabola p x ≠ 0 := by
    unfold parabola
    positivity
  rw [gap1 p x hp hx]
  field_simp [hne]
  <;> ring
theorem gap4 (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    deriv (deriv (parabola p)) x = -(p ^ 2 / (parabola p x) ^ 3) := by
  calc
    deriv (deriv (parabola p)) x =
        -(p / (parabola p x) ^ 2) * deriv (parabola p) x :=
      gap2 p x hp hx
    _ = -(p ^ 2 / (parabola p x) ^ 3) := gap3 p x hp hx
theorem gap5 (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    curvatureRadius p x =
      powThreeHalves (1 + (deriv (parabola p) x) ^ 2) /
        |deriv (deriv (parabola p)) x| := by
  rfl
theorem gap6 (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    powThreeHalves (1 + (deriv (parabola p) x) ^ 2) /
        |deriv (deriv (parabola p)) x| =
      powThreeHalves (1 + p ^ 2 / (parabola p x) ^ 2) /
        |p ^ 2 / (parabola p x) ^ 3| := by
  rw [gap1 p x hp hx, gap4 p x hp hx]
  simp only [div_pow, abs_neg]
theorem gap7 (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    powThreeHalves (1 + p ^ 2 / (parabola p x) ^ 2) /
        |p ^ 2 / (parabola p x) ^ 3| =
      powThreeHalves ((parabola p x) ^ 2 + p ^ 2) / p ^ 2 := by
  have hy : 0 < parabola p x := by
    unfold parabola
    positivity
  have harg :
      1 + p ^ 2 / (parabola p x) ^ 2 =
        ((parabola p x) ^ 2 + p ^ 2) / (parabola p x) ^ 2 := by
    field_simp [ne_of_gt hy]
    <;> ring
  have habs :
      |p ^ 2 / (parabola p x) ^ 3| =
        p ^ 2 / (parabola p x) ^ 3 := by
    rw [abs_of_pos]
    positivity
  unfold powThreeHalves
  rw [harg, Real.sqrt_div (by positivity),
    Real.sqrt_sq (le_of_lt hy), habs]
  field_simp [ne_of_gt hp, ne_of_gt hy]
  <;> ring
theorem gap8 (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    powThreeHalves ((parabola p x) ^ 2 + p ^ 2) / p ^ 2 =
      p * powThreeHalves (1 + (parabola p x) ^ 2 / p ^ 2) := by
  have harg :
      1 + (parabola p x) ^ 2 / p ^ 2 =
        ((parabola p x) ^ 2 + p ^ 2) / p ^ 2 := by
    field_simp [ne_of_gt hp]
    <;> ring
  unfold powThreeHalves
  rw [harg, Real.sqrt_div (by positivity),
    Real.sqrt_sq (le_of_lt hp)]
  field_simp [ne_of_gt hp]
  <;> ring
theorem gap9 (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    p * powThreeHalves (1 + (parabola p x) ^ 2 / p ^ 2) =
      p * powThreeHalves (1 + 2 * x / p) := by
  have hsq : (parabola p x) ^ 2 = 2 * p * x := by
    unfold parabola
    exact Real.sq_sqrt (by positivity)
  have harg :
      1 + (parabola p x) ^ 2 / p ^ 2 = 1 + 2 * x / p := by
    rw [hsq]
    field_simp [ne_of_gt hp]
    <;> ring
  rw [harg]
theorem gap10 (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    curvatureRadius p x = p * powThreeHalves (1 + 2 * x / p) := by
  calc
    curvatureRadius p x =
        powThreeHalves (1 + (deriv (parabola p) x) ^ 2) /
          |deriv (deriv (parabola p)) x| := gap5 p x hp hx
    _ = powThreeHalves (1 + p ^ 2 / (parabola p x) ^ 2) /
          |p ^ 2 / (parabola p x) ^ 3| := gap6 p x hp hx
    _ = powThreeHalves ((parabola p x) ^ 2 + p ^ 2) / p ^ 2 :=
      gap7 p x hp hx
    _ = p * powThreeHalves (1 + (parabola p x) ^ 2 / p ^ 2) :=
      gap8 p x hp hx
    _ = p * powThreeHalves (1 + 2 * x / p) := gap9 p x hp hx

end
end ProofGap.Exercise1596
