import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ProofGap.Exercise1599

noncomputable section

def cubeRoot (u : ℝ) := Real.cbrt u
def twoThirds (u : ℝ) := (cubeRoot u) ^ 2
def fourThirds (u : ℝ) := u * cubeRoot u
def astroidY (a x : ℝ) :=
  (Real.sqrt (twoThirds a - twoThirds x)) ^ 3
def powThreeHalves (u : ℝ) := u * Real.sqrt u
def curvatureRadius (a x : ℝ) :=
  powThreeHalves (1 + (deriv (astroidY a) x) ^ 2) /
    |deriv (deriv (astroidY a)) x|

private lemma cubeRoot_pos {u : ℝ} (hu : 0 < u) : 0 < cubeRoot u := by
  unfold cubeRoot Real.cbrt
  exact Real.rpow_pos_of_pos hu _

private lemma cubeRoot_cube {u : ℝ} (hu : 0 < u) : (cubeRoot u) ^ 3 = u := by
  unfold cubeRoot Real.cbrt
  calc
    (u.rpow (1 / 3 : ℝ)) ^ 3 = (u.rpow (1 / 3 : ℝ)).rpow (3 : ℝ) :=
      (Real.rpow_natCast _ 3).symm
    _ = u.rpow ((1 / 3 : ℝ) * 3) := (Real.rpow_mul hu.le _ _).symm
    _ = u := by norm_num

private lemma hasDerivAt_cubeRoot {u : ℝ} (hu : 0 < u) :
    HasDerivAt cubeRoot (1 / (3 * (cubeRoot u) ^ 2)) u := by
  unfold cubeRoot Real.cbrt
  have h := Real.hasDerivAt_rpow_const (p := (1 / 3 : ℝ)) (Or.inl hu.ne')
  convert h using 1
  symm
  rw [Real.rpow_sub hu]
  field_simp [hu.ne', (Real.rpow_pos_of_pos hu (1 / 3 : ℝ)).ne']
  norm_num
  have hc := cubeRoot_cube hu
  calc
    u ^ (1 / 3 : ℝ) * (u ^ (1 / 3 : ℝ)) ^ 2 =
        (u ^ (1 / 3 : ℝ)) ^ 3 := by ring
    _ = u := by simpa [cubeRoot, Real.cbrt] using hc

private lemma hasDerivAt_twoThirds {u : ℝ} (hu : 0 < u) :
    HasDerivAt twoThirds (2 / (3 * cubeRoot u)) u := by
  unfold twoThirds
  have h := (hasDerivAt_cubeRoot hu).pow 2
  convert h using 1
  field_simp [(cubeRoot_pos hu).ne']
  ring

private lemma rad_pos (a x : ℝ) (ha : 0 < a) (hx : 0 < x) (hxa : x < a) :
    0 < twoThirds a - twoThirds x := by
  have hA := cubeRoot_pos ha
  have hX := cubeRoot_pos hx
  have hAc := cubeRoot_cube ha
  have hXc := cubeRoot_cube hx
  unfold twoThirds
  nlinarith [sq_nonneg (cubeRoot a + cubeRoot x)]

private lemma cubeRoot_astroid (a x : ℝ) (ha : 0 < a) (hx : 0 < x)
    (hxa : x < a) :
    cubeRoot (astroidY a x) =
      Real.sqrt (twoThirds a - twoThirds x) := by
  have hr := rad_pos a x ha hx hxa
  have hs : 0 < Real.sqrt (twoThirds a - twoThirds x) := Real.sqrt_pos.2 hr
  have hy : 0 < astroidY a x := by unfold astroidY; positivity
  apply (show Odd 3 by decide).pow_injective
  change (cubeRoot (astroidY a x)) ^ 3 =
    (Real.sqrt (twoThirds a - twoThirds x)) ^ 3
  rw [cubeRoot_cube hy]
  rfl

private lemma cubeRoot_ratio (a x : ℝ) (ha : 0 < a) (hx : 0 < x)
    (hxa : x < a) :
    cubeRoot (astroidY a x / x) =
      Real.sqrt (twoThirds a - twoThirds x) / cubeRoot x := by
  have hr := rad_pos a x ha hx hxa
  have hs : 0 < Real.sqrt (twoThirds a - twoThirds x) := Real.sqrt_pos.2 hr
  have hy : 0 < astroidY a x := by unfold astroidY; positivity
  have hX := cubeRoot_pos hx
  apply (show Odd 3 by decide).pow_injective
  change (cubeRoot (astroidY a x / x)) ^ 3 =
    (Real.sqrt (twoThirds a - twoThirds x) / cubeRoot x) ^ 3
  rw [cubeRoot_cube (div_pos hy hx), div_pow, cubeRoot_cube hx]
  rfl

private lemma deriv_astroid_raw (a x : ℝ) (ha : 0 < a) (hx : 0 < x)
    (hxa : x < a) :
    deriv (astroidY a) x =
      -Real.sqrt (twoThirds a - twoThirds x) / cubeRoot x := by
  have hr := rad_pos a x ha hx hxa
  have hs : 0 < Real.sqrt (twoThirds a - twoThirds x) := Real.sqrt_pos.2 hr
  have hinner : HasDerivAt (fun z : ℝ => twoThirds a - twoThirds z)
      (-(2 / (3 * cubeRoot x))) x := by
    convert (hasDerivAt_const x (twoThirds a)).sub
      (hasDerivAt_twoThirds hx) using 1 <;> simp [Pi.sub_apply]
  have hsqrt : HasDerivAt
      (fun z : ℝ => Real.sqrt (twoThirds a - twoThirds z))
      ((1 / (2 * Real.sqrt (twoThirds a - twoThirds x))) *
        (-(2 / (3 * cubeRoot x)))) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sqrt hr.ne').comp x hinner
  have hpow := hsqrt.pow 3
  unfold astroidY
  convert hpow.deriv using 1
  field_simp [hs.ne', (cubeRoot_pos hx).ne']
  ring

theorem gap1 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) (hxa : x < a) :
    deriv (astroidY a) x =
      -cubeRoot (astroidY a x / x) := by
  rw [deriv_astroid_raw a x ha hx hxa, cubeRoot_ratio a x ha hx hxa]
  ring
theorem gap2 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) (hxa : x < a) :
    deriv (deriv (astroidY a)) x =
      twoThirds a / (3 * fourThirds x * cubeRoot (astroidY a x)) := by
  have hlocal : deriv (astroidY a) =ᶠ[nhds x]
      fun z => -Real.sqrt (twoThirds a - twoThirds z) / cubeRoot z := by
    filter_upwards [Ioo_mem_nhds hx hxa] with z hz
    exact deriv_astroid_raw a z ha hz.1 hz.2
  rw [hlocal.deriv_eq]
  have hr := rad_pos a x ha hx hxa
  have hs : 0 < Real.sqrt (twoThirds a - twoThirds x) := Real.sqrt_pos.2 hr
  have hX := cubeRoot_pos hx
  have hinner : HasDerivAt (fun z : ℝ => twoThirds a - twoThirds z)
      (-(2 / (3 * cubeRoot x))) x := by
    convert (hasDerivAt_const x (twoThirds a)).sub
      (hasDerivAt_twoThirds hx) using 1 <;> simp [Pi.sub_apply]
  have hsqrt : HasDerivAt
      (fun z : ℝ => Real.sqrt (twoThirds a - twoThirds z))
      ((1 / (2 * Real.sqrt (twoThirds a - twoThirds x))) *
        (-(2 / (3 * cubeRoot x)))) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sqrt hr.ne').comp x hinner
  have hquot : HasDerivAt
      (fun z : ℝ => -Real.sqrt (twoThirds a - twoThirds z) / cubeRoot z)
      ((-(1 / (2 * Real.sqrt (twoThirds a - twoThirds x)) *
          -(2 / (3 * cubeRoot x))) * cubeRoot x -
        (-Real.sqrt (twoThirds a - twoThirds x)) *
          (1 / (3 * cubeRoot x ^ 2))) / cubeRoot x ^ 2) x := by
    simpa using hsqrt.neg.div (hasDerivAt_cubeRoot hx) hX.ne'
  have hsq := Real.sq_sqrt hr.le
  have hrel : twoThirds a =
      (cubeRoot x) ^ 2 + (Real.sqrt (twoThirds a - twoThirds x)) ^ 2 := by
    unfold twoThirds at hsq ⊢
    nlinarith
  have hX4 : fourThirds x = (cubeRoot x) ^ 4 := by
    unfold fourThirds
    calc
      x * cubeRoot x = (cubeRoot x) ^ 3 * cubeRoot x := by
        exact congrArg (fun z => z * cubeRoot x) (cubeRoot_cube hx).symm
      _ = (cubeRoot x) ^ 4 := by ring
  rw [cubeRoot_astroid a x ha hx hxa, hX4]
  convert hquot.deriv using 1
  field_simp [hs.ne', hX.ne']
  nlinarith
theorem gap3 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) (hxa : x < a) :
    curvatureRadius a x =
      powThreeHalves (1 + twoThirds (astroidY a x / x)) /
        |twoThirds a / (3 * fourThirds x * cubeRoot (astroidY a x))| := by
  unfold curvatureRadius
  rw [gap1 a x ha hx hxa, gap2 a x ha hx hxa]
  simp only [neg_sq]
  rfl
theorem gap4 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) (hxa : x < a) :
    curvatureRadius a x =
      |(a / x) /
        (twoThirds a / (3 * fourThirds x * cubeRoot (astroidY a x)))| := by
  rw [gap3 a x ha hx hxa]
  have hr := rad_pos a x ha hx hxa
  have hA := cubeRoot_pos ha
  have hX := cubeRoot_pos hx
  have hratio := cubeRoot_ratio a x ha hx hxa
  have hsquare := Real.sq_sqrt hr.le
  have hrel : twoThirds a =
      (cubeRoot x) ^ 2 + (Real.sqrt (twoThirds a - twoThirds x)) ^ 2 := by
    unfold twoThirds at hsquare ⊢
    nlinarith
  have hbase :
      1 + twoThirds (astroidY a x / x) =
        (cubeRoot a / cubeRoot x) ^ 2 := by
    unfold twoThirds
    rw [hratio]
    field_simp [hX.ne']
    have hrel' : (cubeRoot a) ^ 2 =
        (cubeRoot x) ^ 2 +
          (Real.sqrt (twoThirds a - twoThirds x)) ^ 2 := by
      simpa [twoThirds] using hrel
    nlinarith
  have hnum :
      powThreeHalves (1 + twoThirds (astroidY a x / x)) = a / x := by
    unfold powThreeHalves
    rw [hbase, Real.sqrt_sq_eq_abs, abs_of_pos (div_pos hA hX)]
    field_simp [hx.ne', hX.ne']
    nlinarith [cubeRoot_cube ha, cubeRoot_cube hx]
  have hden : 0 < twoThirds a /
      (3 * fourThirds x * cubeRoot (astroidY a x)) := by
    rw [cubeRoot_astroid a x ha hx hxa]
    unfold twoThirds fourThirds
    positivity
  rw [hnum, abs_of_pos hden,
    abs_of_pos (div_pos (div_pos ha hx) hden)]
theorem gap5 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) (hxa : x < a) :
    curvatureRadius a x =
      3 * cubeRoot |a * x * astroidY a x| := by
  rw [gap4 a x ha hx hxa]
  have hr := rad_pos a x ha hx hxa
  have hs : 0 < Real.sqrt (twoThirds a - twoThirds x) := Real.sqrt_pos.2 hr
  have hy : 0 < astroidY a x := by unfold astroidY; positivity
  have hA := cubeRoot_pos ha
  have hX := cubeRoot_pos hx
  have hY : cubeRoot (astroidY a x) =
      Real.sqrt (twoThirds a - twoThirds x) :=
    cubeRoot_astroid a x ha hx hxa
  have hfour : fourThirds x = (cubeRoot x) ^ 4 := by
    unfold fourThirds
    calc
      x * cubeRoot x = (cubeRoot x) ^ 3 * cubeRoot x := by
        exact congrArg (fun z => z * cubeRoot x) (cubeRoot_cube hx).symm
      _ = (cubeRoot x) ^ 4 := by ring
  have hcprod :
      cubeRoot |a * x * astroidY a x| =
        cubeRoot a * cubeRoot x * cubeRoot (astroidY a x) := by
    rw [abs_of_pos (mul_pos (mul_pos ha hx) hy)]
    apply (show Odd 3 by decide).pow_injective
    change (cubeRoot (a * x * astroidY a x)) ^ 3 =
      (cubeRoot a * cubeRoot x * cubeRoot (astroidY a x)) ^ 3
    rw [cubeRoot_cube (mul_pos (mul_pos ha hx) hy), mul_pow, mul_pow,
      cubeRoot_cube ha, cubeRoot_cube hx, cubeRoot_cube hy]
  have hden : 0 < twoThirds a /
      (3 * fourThirds x * cubeRoot (astroidY a x)) := by
    rw [cubeRoot_astroid a x ha hx hxa]
    unfold twoThirds fourThirds
    positivity
  rw [abs_of_pos (div_pos (div_pos ha hx) hden), hfour, hcprod]
  unfold twoThirds
  field_simp [hA.ne', hX.ne', (cubeRoot_pos hy).ne']
  nlinarith [cubeRoot_cube ha, cubeRoot_cube hx]

end
end ProofGap.Exercise1599
