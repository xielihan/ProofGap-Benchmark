import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise935

noncomputable section

def y (x : ℝ) : ℝ :=
  (1 / 6) * Real.log ((x + 1) ^ 2 / (x ^ 2 - x + 1)) +
    1 / Real.sqrt 3 * Real.arctan ((2 * x - 1) / Real.sqrt 3)

def expandedDerivative (x : ℝ) : ℝ :=
  (1 / 3) * (1 / (x + 1)) -
    (1 / 6) * ((2 * x - 1) / (x ^ 2 - x + 1)) +
    1 / Real.sqrt 3 *
      (1 / (1 + ((2 * x - 1) / Real.sqrt 3) ^ 2)) *
      (2 / Real.sqrt 3)

def finalDerivative (x : ℝ) : ℝ :=
  1 / (1 + x ^ 3)

/-- Source: `proof_gap/exercise_935/1.txt`; exclude `x = -1`, where the
logarithm argument vanishes and the target rational function has a pole. -/
private lemma quadratic_pos (x : ℝ) : 0 < x ^ 2 - x + 1 := by
  nlinarith [sq_nonneg (x - (1 / 2 : ℝ))]

theorem gap1 (x : ℝ) (hx : x ≠ -1) :
    HasDerivAt y (expandedDerivative x) x := by
  have hxp : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hq : x ^ 2 - x + 1 ≠ 0 := ne_of_gt (quadratic_pos x)
  have hq_alt : x * (x - 1) + 1 ≠ 0 := by
    intro h
    apply hq
    calc
      x ^ 2 - x + 1 = x * (x - 1) + 1 := by ring
      _ = 0 := h
  have harg : (x + 1) ^ 2 / (x ^ 2 - x + 1) ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 hxp) hq
  have hbase : HasDerivAt (fun z : ℝ => z + 1) 1 x := by
    convert
      (hasDerivAt_id x).add (hasDerivAt_const x (1 : ℝ)) using 1 <;>
      ring
  have hnum :
      HasDerivAt (fun z : ℝ => (z + 1) ^ 2) (2 * (x + 1)) x := by
    convert hbase.mul hbase using 1
    · funext z
      dsimp
      ring
    · ring
  have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).mul (hasDerivAt_id x) using 1
    · funext z
      dsimp
      ring
    · dsimp [id]
      ring
  have hden :
      HasDerivAt (fun z : ℝ => z ^ 2 - z + 1) (2 * x - 1) x := by
    convert
      (hsq.sub (hasDerivAt_id x)).add (hasDerivAt_const x (1 : ℝ)) using 1 <;>
      ring
  have hquot := hnum.div hden hq
  have hlog :
      HasDerivAt
        (fun z : ℝ => Real.log ((z + 1) ^ 2 / (z ^ 2 - z + 1)))
        (2 * (1 / (x + 1)) - (2 * x - 1) / (x ^ 2 - x + 1)) x := by
    convert hquot.log harg using 1 <;>
      dsimp <;>
      field_simp [hxp, hq, hq_alt, harg] <;>
      ring
  have hs : Real.sqrt 3 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hlin :
      HasDerivAt (fun z : ℝ => 2 * z - 1) 2 x := by
    convert
      ((hasDerivAt_id x).const_mul (2 : ℝ)).sub
        (hasDerivAt_const x (1 : ℝ)) using 1 <;>
      ring
  have hsderiv :
      HasDerivAt (fun _ : ℝ => Real.sqrt 3) 0 x :=
    hasDerivAt_const x _
  have hinner :
      HasDerivAt (fun z : ℝ => (2 * z - 1) / Real.sqrt 3)
        (2 / Real.sqrt 3) x := by
    convert hlin.div hsderiv hs using 1 <;> field_simp [hs] <;> ring
  have hatan :=
    (Real.hasDerivAt_arctan ((2 * x - 1) / Real.sqrt 3)).comp x hinner
  change
    HasDerivAt
      (fun z : ℝ => Real.arctan ((2 * z - 1) / Real.sqrt 3))
      ((1 / (1 + ((2 * x - 1) / Real.sqrt 3) ^ 2)) *
        (2 / Real.sqrt 3)) x at hatan
  unfold y expandedDerivative
  convert
    (hlog.const_mul (1 / 6)).add
      (hatan.const_mul (1 / Real.sqrt 3)) using 1 <;> ring

/-- Source: `proof_gap/exercise_935/2.txt`; the omitted condition `x ≠ -1`
is exactly the nonzero factor in `1+x³`. -/
theorem gap2 (x : ℝ) (hx : x ≠ -1) :
    expandedDerivative x = finalDerivative x := by
  have hxp : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hq : x ^ 2 - x + 1 ≠ 0 := ne_of_gt (quadratic_pos x)
  have hq_alt : x * (x - 1) + 1 ≠ 0 := by
    intro h
    apply hq
    calc
      x ^ 2 - x + 1 = x * (x - 1) + 1 := by ring
      _ = 0 := h
  have hsquare : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hs_inv_sq :
      (1 / Real.sqrt 3) * (1 / Real.sqrt 3) = (1 / 3 : ℝ) := by
    calc
      (1 / Real.sqrt 3) * (1 / Real.sqrt 3) =
          (1 / Real.sqrt 3) ^ 2 := by ring
      _ = (1 : ℝ) ^ 2 / (Real.sqrt 3) ^ 2 := by rw [div_pow]
      _ = 1 / 3 := by rw [hsquare]; norm_num
  have hdenom :
      1 + ((2 * x - 1) / Real.sqrt 3) ^ 2 =
        4 * (x ^ 2 - x + 1) / 3 := by
    rw [div_pow, hsquare]
    ring
  have hinv :
      1 / (4 * (x ^ 2 - x + 1) / 3) =
        3 / (4 * (x ^ 2 - x + 1)) := by
    field_simp [hq, hq_alt] <;> ring
  have hatan_alg :
      1 / Real.sqrt 3 *
          (1 / (1 + ((2 * x - 1) / Real.sqrt 3) ^ 2)) *
          (2 / Real.sqrt 3) =
        1 / (2 * (x ^ 2 - x + 1)) := by
    rw [hdenom, hinv]
    calc
      1 / Real.sqrt 3 * (3 / (4 * (x ^ 2 - x + 1))) *
          (2 / Real.sqrt 3) =
          ((1 / Real.sqrt 3) * (1 / Real.sqrt 3)) *
            (6 / (4 * (x ^ 2 - x + 1))) := by ring
      _ = (1 / 3 : ℝ) * (6 / (4 * (x ^ 2 - x + 1))) := by
        rw [hs_inv_sq]
      _ = 1 / (2 * (x ^ 2 - x + 1)) := by
        field_simp [hq, hq_alt] <;> ring
  have hmain :
      (1 / 3) * (1 / (x + 1)) -
          (1 / 6) * ((2 * x - 1) / (x ^ 2 - x + 1)) +
          1 / (2 * (x ^ 2 - x + 1)) =
        1 / ((x + 1) * (x ^ 2 - x + 1)) := by
    field_simp [hxp, hq, hq_alt] <;> ring
  unfold expandedDerivative finalDerivative
  rw [hatan_alg]
  rw [show 1 + x ^ 3 = (x + 1) * (x ^ 2 - x + 1) by ring]
  exact hmain

/-- Source: `proof_gap/exercise_935/3.txt`; retain the logarithm's punctured
domain in the final derivative statement. -/
theorem gap3 (x : ℝ) (hx : x ≠ -1) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise935
