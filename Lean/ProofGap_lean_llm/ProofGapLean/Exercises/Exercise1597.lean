import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise1597

noncomputable section

def ellipseY (a b x : ℝ) := b / a * Real.sqrt (a ^ 2 - x ^ 2)
def eccentricity (a b : ℝ) := Real.sqrt (a ^ 2 - b ^ 2) / a
def powThreeHalves (u : ℝ) := u * Real.sqrt u
def curvatureRadius (a b x : ℝ) :=
  powThreeHalves
      (1 + b ^ 4 * x ^ 2 / (a ^ 4 * (ellipseY a b x) ^ 2)) /
    |deriv (deriv (ellipseY a b)) x|

theorem gap1 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : |x| < a) :
    deriv (ellipseY a b) x =
      -(b ^ 2 * x / (a ^ 2 * ellipseY a b x)) := by
  have hrad : 0 < a ^ 2 - x ^ 2 := by
    have hx' := abs_lt.mp hx
    nlinarith
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hs0 : Real.sqrt (a ^ 2 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hrad)
  have hc : HasDerivAt (fun _ : ℝ => a ^ 2) 0 x :=
    hasDerivAt_const x (a ^ 2)
  have hp : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    simpa [mul_comm] using (hasDerivAt_id x).pow 2
  have hinner :
      HasDerivAt (fun z : ℝ => a ^ 2 - z ^ 2) (-2 * x) x := by
    simpa [mul_comm] using HasDerivAt.sub hc hp
  have hs :
      HasDerivAt (fun z : ℝ => Real.sqrt (a ^ 2 - z ^ 2))
        (-x / Real.sqrt (a ^ 2 - x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp x hinner using 1
    field_simp [hs0]
  have hk : HasDerivAt (fun _ : ℝ => b / a) 0 x :=
    hasDerivAt_const x (b / a)
  have hd :
      HasDerivAt (ellipseY a b)
        (0 * Real.sqrt (a ^ 2 - x ^ 2) +
          (b / a) * (-x / Real.sqrt (a ^ 2 - x ^ 2))) x := by
    simpa [ellipseY] using HasDerivAt.mul hk hs
  rw [hd.deriv]
  unfold ellipseY
  field_simp [ha0, hb0, hs0] <;> ring
theorem gap2 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : |x| < a) :
    deriv (deriv (ellipseY a b)) x =
      -(b ^ 4 / (a ^ 2 * (ellipseY a b x) ^ 3)) := by
  have hrad : 0 < a ^ 2 - x ^ 2 := by
    have hx' := abs_lt.mp hx
    nlinarith
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hs0 : Real.sqrt (a ^ 2 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hrad)
  have hc : HasDerivAt (fun _ : ℝ => a ^ 2) 0 x :=
    hasDerivAt_const x (a ^ 2)
  have hp : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    simpa [mul_comm] using (hasDerivAt_id x).pow 2
  have hinner :
      HasDerivAt (fun z : ℝ => a ^ 2 - z ^ 2) (-2 * x) x := by
    simpa [mul_comm] using HasDerivAt.sub hc hp
  have hs :
      HasDerivAt (fun z : ℝ => Real.sqrt (a ^ 2 - z ^ 2))
        (-x / Real.sqrt (a ^ 2 - x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp x hinner using 1
    field_simp [hs0]
  have hq :
      HasDerivAt
        (fun z : ℝ => z / Real.sqrt (a ^ 2 - z ^ 2))
        ((Real.sqrt (a ^ 2 - x ^ 2) -
            x * (-x / Real.sqrt (a ^ 2 - x ^ 2))) /
          Real.sqrt (a ^ 2 - x ^ 2) ^ 2) x := by
    simpa [id_eq] using
      HasDerivAt.div (hasDerivAt_id x) hs hs0
  have hk : HasDerivAt (fun _ : ℝ => b / a) 0 x :=
    hasDerivAt_const x (b / a)
  have hg :
      HasDerivAt
        (fun z : ℝ => -(b / a *
          (z / Real.sqrt (a ^ 2 - z ^ 2))))
        (-(b / a *
          ((Real.sqrt (a ^ 2 - x ^ 2) -
              x * (-x / Real.sqrt (a ^ 2 - x ^ 2))) /
            Real.sqrt (a ^ 2 - x ^ 2) ^ 2))) x := by
    simpa using HasDerivAt.neg (HasDerivAt.mul hk hq)
  have hx' := abs_lt.mp hx
  have hstay : ∀ᶠ z : ℝ in nhds x, |z| < a := by
    filter_upwards [Ioo_mem_nhds hx'.1 hx'.2] with z hz
    exact abs_lt.mpr hz
  have hlocal :
      deriv (ellipseY a b) =ᶠ[nhds x]
        (fun z : ℝ => -(b / a *
          (z / Real.sqrt (a ^ 2 - z ^ 2)))) := by
    refine hstay.mono ?_
    intro z hz
    have hzrad : 0 < a ^ 2 - z ^ 2 := by
      have hz' := abs_lt.mp hz
      nlinarith
    have hzs0 : Real.sqrt (a ^ 2 - z ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hzrad)
    rw [gap1 a b z ha hb hz]
    unfold ellipseY
    field_simp [ha0, hb0, hzs0] <;> ring
  rw [hlocal.deriv_eq, hg.deriv]
  unfold ellipseY
  field_simp [ha0, hb0, hs0] <;>
    nlinarith [Real.sq_sqrt (le_of_lt hrad)]
theorem gap3 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : |x| < a) :
    curvatureRadius a b x =
      powThreeHalves
          (1 + b ^ 4 * x ^ 2 / (a ^ 4 * (ellipseY a b x) ^ 2)) /
        |deriv (deriv (ellipseY a b)) x| := by
  rfl
theorem gap4 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : |x| < a) :
    powThreeHalves
          (1 + b ^ 4 * x ^ 2 / (a ^ 4 * (ellipseY a b x) ^ 2)) /
        |deriv (deriv (ellipseY a b)) x| =
      powThreeHalves
          (1 + b ^ 4 * x ^ 2 / (a ^ 4 * (ellipseY a b x) ^ 2)) /
        (b ^ 4 / (a ^ 2 * |ellipseY a b x| ^ 3)) := by
  rw [gap2 a b x ha hb hx]
  simp [abs_div, abs_mul, abs_pow, abs_of_pos ha, abs_of_pos hb]
theorem gap5 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : |x| < a) :
    powThreeHalves
          (1 + b ^ 4 * x ^ 2 / (a ^ 4 * (ellipseY a b x) ^ 2)) /
        (b ^ 4 / (a ^ 2 * |ellipseY a b x| ^ 3)) =
      powThreeHalves
          (a ^ 4 * (ellipseY a b x) ^ 2 + b ^ 4 * x ^ 2) /
        (a ^ 4 * b ^ 4) := by
  have hrad : 0 < a ^ 2 - x ^ 2 := by
    have hx' := abs_lt.mp hx
    nlinarith
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hy : 0 < ellipseY a b x := by
    unfold ellipseY
    exact mul_pos (div_pos hb ha) (Real.sqrt_pos.2 hrad)
  have hden : 0 < a ^ 2 * ellipseY a b x :=
    mul_pos (pow_pos ha 2) hy
  have hS :
      0 ≤ a ^ 4 * (ellipseY a b x) ^ 2 + b ^ 4 * x ^ 2 := by
    positivity
  have hU :
      0 ≤ 1 + b ^ 4 * x ^ 2 /
        (a ^ 4 * (ellipseY a b x) ^ 2) := by
    positivity
  have heqrad :
      1 + b ^ 4 * x ^ 2 / (a ^ 4 * (ellipseY a b x) ^ 2) =
        (a ^ 4 * (ellipseY a b x) ^ 2 + b ^ 4 * x ^ 2) /
          (a ^ 2 * ellipseY a b x) ^ 2 := by
    field_simp [ha0, ne_of_gt hy] <;> ring
  have hsq :
      (Real.sqrt
          (a ^ 4 * (ellipseY a b x) ^ 2 + b ^ 4 * x ^ 2) /
          (a ^ 2 * ellipseY a b x)) ^ 2 =
        1 + b ^ 4 * x ^ 2 / (a ^ 4 * (ellipseY a b x) ^ 2) := by
    rw [div_pow, Real.sq_sqrt hS, heqrad]
  have hsqrt :
      Real.sqrt
          (1 + b ^ 4 * x ^ 2 / (a ^ 4 * (ellipseY a b x) ^ 2)) =
        Real.sqrt
            (a ^ 4 * (ellipseY a b x) ^ 2 + b ^ 4 * x ^ 2) /
          (a ^ 2 * ellipseY a b x) := by
    have hl := Real.sqrt_nonneg
      (1 + b ^ 4 * x ^ 2 / (a ^ 4 * (ellipseY a b x) ^ 2))
    have hr :
        0 ≤ Real.sqrt
            (a ^ 4 * (ellipseY a b x) ^ 2 + b ^ 4 * x ^ 2) /
          (a ^ 2 * ellipseY a b x) :=
      div_nonneg (Real.sqrt_nonneg _) (le_of_lt hden)
    nlinarith [Real.sq_sqrt hU, hsq]
  unfold powThreeHalves
  rw [abs_of_pos hy, hsqrt, heqrad]
  field_simp [ha0, hb0, ne_of_gt hy] <;> ring
theorem gap6 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : |x| < a) :
    powThreeHalves
          (a ^ 4 * (ellipseY a b x) ^ 2 + b ^ 4 * x ^ 2) /
        (a ^ 4 * b ^ 4) =
      powThreeHalves
          (a ^ 4 * b ^ 2 - a ^ 2 * b ^ 2 * x ^ 2 + b ^ 4 * x ^ 2) /
        (a ^ 4 * b ^ 4) := by
  have hrad : 0 < a ^ 2 - x ^ 2 := by
    have hx' := abs_lt.mp hx
    nlinarith
  apply congrArg (fun u : ℝ => u / (a ^ 4 * b ^ 4))
  apply congrArg powThreeHalves
  unfold ellipseY
  rw [mul_pow, Real.sq_sqrt (le_of_lt hrad)]
  field_simp [ne_of_gt ha] <;> ring
theorem gap7 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : |x| < a) :
    powThreeHalves
          (a ^ 4 * b ^ 2 - a ^ 2 * b ^ 2 * x ^ 2 + b ^ 4 * x ^ 2) /
        (a ^ 4 * b ^ 4) =
      a ^ 3 * b ^ 3 *
          powThreeHalves (a ^ 2 - (a ^ 2 - b ^ 2) / a ^ 2 * x ^ 2) /
        (a ^ 4 * b ^ 4) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  let v : ℝ := a ^ 2 - (a ^ 2 - b ^ 2) / a ^ 2 * x ^ 2
  let s : ℝ := a ^ 4 * b ^ 2 - a ^ 2 * b ^ 2 * x ^ 2 + b ^ 4 * x ^ 2
  have hrad : 0 < a ^ 2 - x ^ 2 := by
    have hx' := abs_lt.mp hx
    nlinarith
  have hveq :
      v = (a ^ 2 - x ^ 2) + (b ^ 2 / a ^ 2) * x ^ 2 := by
    dsimp [v]
    field_simp [ha0] <;> ring
  have hcoef : 0 ≤ b ^ 2 / a ^ 2 :=
    div_nonneg (sq_nonneg b) (sq_nonneg a)
  have hv : 0 < v := by
    have hp := mul_nonneg hcoef (sq_nonneg x)
    rw [hveq]
    nlinarith
  have hscale : s = (a * b) ^ 2 * v := by
    dsimp [s, v]
    field_simp [ha0] <;> ring
  have hs : 0 < s := by
    rw [hscale]
    exact mul_pos (pow_pos (mul_pos ha hb) 2) hv
  have hsqrhs :
      (a * b * Real.sqrt v) ^ 2 = s := by
    calc
      (a * b * Real.sqrt v) ^ 2 =
          (a * b) ^ 2 * (Real.sqrt v) ^ 2 := by ring
      _ = (a * b) ^ 2 * v := by rw [Real.sq_sqrt (le_of_lt hv)]
      _ = s := hscale.symm
  have hsqrt : Real.sqrt s = a * b * Real.sqrt v := by
    have hl := Real.sqrt_nonneg s
    have hr : 0 ≤ a * b * Real.sqrt v := by positivity
    nlinarith [Real.sq_sqrt (le_of_lt hs), hsqrhs]
  change powThreeHalves s / (a ^ 4 * b ^ 4) =
    a ^ 3 * b ^ 3 * powThreeHalves v / (a ^ 4 * b ^ 4)
  apply congrArg (fun u : ℝ => u / (a ^ 4 * b ^ 4))
  unfold powThreeHalves
  rw [hsqrt, hscale]
  ring
theorem gap8 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hx : |x| < a) :
    a ^ 3 * b ^ 3 *
          powThreeHalves (a ^ 2 - (a ^ 2 - b ^ 2) / a ^ 2 * x ^ 2) /
        (a ^ 4 * b ^ 4) =
      powThreeHalves (a ^ 2 - (eccentricity a b) ^ 2 * x ^ 2) / (a * b) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hdif : 0 ≤ a ^ 2 - b ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hba)
      (add_nonneg (le_of_lt ha) (le_of_lt hb))
    nlinarith
  have hecc :
      (eccentricity a b) ^ 2 = (a ^ 2 - b ^ 2) / a ^ 2 := by
    unfold eccentricity
    rw [div_pow, Real.sq_sqrt hdif]
  rw [hecc]
  field_simp [ha0, hb0] <;> ring
theorem gap9 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hx : |x| < a) :
    curvatureRadius a b x =
      powThreeHalves (a ^ 2 - (eccentricity a b) ^ 2 * x ^ 2) / (a * b) := by
  calc
    curvatureRadius a b x =
        powThreeHalves
            (1 + b ^ 4 * x ^ 2 /
              (a ^ 4 * (ellipseY a b x) ^ 2)) /
          |deriv (deriv (ellipseY a b)) x| :=
      gap3 a b x ha hb hx
    _ = powThreeHalves
            (1 + b ^ 4 * x ^ 2 /
              (a ^ 4 * (ellipseY a b x) ^ 2)) /
          (b ^ 4 / (a ^ 2 * |ellipseY a b x| ^ 3)) :=
      gap4 a b x ha hb hx
    _ = powThreeHalves
            (a ^ 4 * (ellipseY a b x) ^ 2 + b ^ 4 * x ^ 2) /
          (a ^ 4 * b ^ 4) :=
      gap5 a b x ha hb hx
    _ = powThreeHalves
            (a ^ 4 * b ^ 2 - a ^ 2 * b ^ 2 * x ^ 2 + b ^ 4 * x ^ 2) /
          (a ^ 4 * b ^ 4) :=
      gap6 a b x ha hb hx
    _ = a ^ 3 * b ^ 3 *
            powThreeHalves
              (a ^ 2 - (a ^ 2 - b ^ 2) / a ^ 2 * x ^ 2) /
          (a ^ 4 * b ^ 4) :=
      gap7 a b x ha hb hx
    _ = powThreeHalves
            (a ^ 2 - (eccentricity a b) ^ 2 * x ^ 2) / (a * b) :=
      gap8 a b x ha hb hba hx
theorem gap10 (a b : ℝ) :
    eccentricity a b = Real.sqrt (a ^ 2 - b ^ 2) / a := by
  rfl

end
end ProofGap.Exercise1597
