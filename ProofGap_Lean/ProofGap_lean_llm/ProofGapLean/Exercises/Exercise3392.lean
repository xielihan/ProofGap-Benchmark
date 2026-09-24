import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3392

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

def secondDifferential (f : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  partialXX f x y * dx ^ 2 +
    2 * partialXY f x y * dx * dy +
    partialYY f x y * dy ^ 2

def solvedDifferential (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  z x y * (y * dx + z x y * dy) / (y * (x + z x y))

def expandedSecondRhs (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  -(dx + differential z x y dx dy) * differential z x y dx dy +
    differential z x y dx dy * dx +
    (2 * z x y / y) * differential z x y dx dy * dy -
    (z x y) ^ 2 / y ^ 2 * dy ^ 2

def quadraticSecondRhs (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  -(differential z x y dx dy) ^ 2 +
    (2 * z x y / y) * dy * differential z x y dx dy -
    (z x y) ^ 2 / y ^ 2 * dy ^ 2

def squareSecondRhs (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  -(differential z x y dx dy - z x y / y * dy) ^ 2

def substitutedSecondRhs (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  -((z x y) ^ 2 *
      (y * dx + z x y * dy - (x + z x y) * dy) ^ 2) /
    (y ^ 2 * (x + z x y) ^ 2)

def simplifiedSecondRhs (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  -((z x y) ^ 2 * (y * dx - x * dy) ^ 2) /
    (y ^ 2 * (x + z x y) ^ 2)

def finalSecondDifferential (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  -((z x y) ^ 2 * (y * dx - x * dy) ^ 2) /
    (y ^ 2 * (x + z x y) ^ 3)

theorem gap1 (x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (hy : y ≠ 0) (hz : z x y ≠ 0)
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hImplicit :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        p.1 / z p.1 p.2 = Real.log (z p.1 p.2 / p.2) + 1) :
    (z x y * dx - x * differential z x y dx dy) / (z x y) ^ 2 =
      differential z x y dx dy / z x y - dy / y := by
  have hpairX : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x := by
    fun_prop
  have hpairY : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y := by
    fun_prop
  have hzx : DifferentiableAt ℝ (fun t : ℝ => z t y) x := by
    simpa [Function.uncurry] using hzDiff.comp x hpairX
  have hzy : DifferentiableAt ℝ (fun t : ℝ => z x t) y := by
    simpa [Function.uncurry] using hzDiff.comp y hpairY
  have hzx' : HasDerivAt (fun t : ℝ => z t y) (partialX z x y) x := by
    simpa [partialX] using hzx.hasDerivAt
  have hzy' : HasDerivAt (fun t : ℝ => z x t) (partialY z x y) y := by
    simpa [partialY] using hzy.hasDerivAt
  have hImplicitX :
      (fun t : ℝ => t / z t y) =ᶠ[nhds x]
        (fun t : ℝ => Real.log (z t y / y) + 1) := by
    filter_upwards [hpairX.continuousAt.tendsto.eventually hImplicit] with t ht
    exact ht
  have hImplicitY :
      (fun t : ℝ => x / z x t) =ᶠ[nhds y]
        (fun t : ℝ => Real.log (z x t / t) + 1) := by
    filter_upwards [hpairY.continuousAt.tendsto.eventually hImplicit] with t ht
    exact ht
  have hLx :
      HasDerivAt (fun t : ℝ => t / z t y)
        ((z x y - x * partialX z x y) / z x y ^ 2) x := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id x).div hzx' hz
  have hRx :
      HasDerivAt (fun t : ℝ => Real.log (z t y / y) + 1)
        (partialX z x y / y / (z x y / y)) x :=
    ((hzx'.div_const y).log (div_ne_zero hz hy)).add_const 1
  have hLy :
      HasDerivAt (fun t : ℝ => x / z x t)
        ((-x * partialY z x y) / z x y ^ 2) y := by
    simpa only [Pi.div_apply, zero_mul, zero_sub, neg_mul] using
      (hasDerivAt_const (x := y) x).div hzy' hz
  have hRy :
      HasDerivAt (fun t : ℝ => Real.log (z x t / t) + 1)
        ((partialY z x y * y - z x y) / y ^ 2 / (z x y / y)) y := by
    simpa only [id_eq, mul_one] using
      ((hzy'.div (hasDerivAt_id y) hy).log (div_ne_zero hz hy)).add_const 1
  have hDerivX :
      (z x y - x * partialX z x y) / z x y ^ 2 =
        partialX z x y / y / (z x y / y) := by
    calc
      (z x y - x * partialX z x y) / z x y ^ 2 =
          deriv (fun t : ℝ => t / z t y) x := hLx.deriv.symm
      _ = deriv (fun t : ℝ => Real.log (z t y / y) + 1) x :=
        hImplicitX.deriv_eq
      _ = partialX z x y / y / (z x y / y) := hRx.deriv
  have hDerivY :
      (-x * partialY z x y) / z x y ^ 2 =
        (partialY z x y * y - z x y) / y ^ 2 / (z x y / y) := by
    calc
      (-x * partialY z x y) / z x y ^ 2 =
          deriv (fun t : ℝ => x / z x t) y := hLy.deriv.symm
      _ = deriv (fun t : ℝ => Real.log (z x t / t) + 1) y :=
        hImplicitY.deriv_eq
      _ = (partialY z x y * y - z x y) / y ^ 2 / (z x y / y) :=
        hRy.deriv
  have hX :
      (z x y - x * partialX z x y) / z x y ^ 2 =
        partialX z x y / z x y := by
    calc
      (z x y - x * partialX z x y) / z x y ^ 2 =
          partialX z x y / y / (z x y / y) := hDerivX
      _ = partialX z x y / z x y := by field_simp [hy, hz]
  have hY :
      (-x * partialY z x y) / z x y ^ 2 =
        partialY z x y / z x y - 1 / y := by
    calc
      (-x * partialY z x y) / z x y ^ 2 =
          (partialY z x y * y - z x y) / y ^ 2 / (z x y / y) := hDerivY
      _ = partialY z x y / z x y - 1 / y := by field_simp [hy, hz]
  unfold differential
  linear_combination dx * hX + dy * hY

theorem gap2 (x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (hy : y ≠ 0) (hz : z x y ≠ 0)
    (hxz : x + z x y ≠ 0)
    (hDifferentialIdentity :
      (z x y * dx - x * differential z x y dx dy) /
          (z x y) ^ 2 =
        differential z x y dx dy / z x y - dy / y) :
    differential z x y dx dy =
      solvedDifferential z x y dx dy := by
  unfold solvedDifferential
  apply (eq_div_iff (mul_ne_zero hy hxz)).2
  field_simp [hy, hz] at hDifferentialIdentity
  linear_combination -1 * hDifferentialIdentity

theorem gap3 (x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (hy : y ≠ 0) (hz : z x y ≠ 0)
    (hxz : x + z x y ≠ 0)
    (hzC2 : ContDiffAt ℝ 2 (Function.uncurry z) (x, y))
    (hImplicit :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        p.1 / z p.1 p.2 = Real.log (z p.1 p.2 / p.2) + 1) :
    (x + z x y) * secondDifferential z x y dx dy =
      expandedSecondRhs z x y dx dy := by
  have hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y) :=
    hzC2.differentiableAt (by decide)
  rcases mem_nhds_iff.mp hImplicit with ⟨s, hs, hsOpen, hxy⟩
  have hPX :
      (fun p : ℝ × ℝ => partialX z p.1 p.2) =ᶠ[nhds (x, y)]
        (fun p : ℝ × ℝ => z p.1 p.2 / (p.1 + z p.1 p.2)) := by
    filter_upwards [hsOpen.mem_nhds hxy, hzC2.eventually (by decide),
      continuous_snd.continuousAt.eventually_ne hy,
      hzDiff.continuousAt.eventually_ne hz,
      (continuous_fst.continuousAt.add hzDiff.continuousAt).eventually_ne hxz] with
        p hp hpC2 hpY hpZ hpXZ
    have hpImplicit :
        ∀ᶠ q : ℝ × ℝ in nhds p,
          q.1 / z q.1 q.2 = Real.log (z q.1 q.2 / q.2) + 1 := by
      filter_upwards [hsOpen.mem_nhds hp] with q hq
      exact hs hq
    have hpFirst := gap1 p.1 p.2 1 0 z hpY hpZ
      (hpC2.differentiableAt (by decide)) hpImplicit
    have hpSolved := gap2 p.1 p.2 1 0 z hpY hpZ hpXZ hpFirst
    calc
      partialX z p.1 p.2 = solvedDifferential z p.1 p.2 1 0 := by
        simpa [differential] using hpSolved
      _ = z p.1 p.2 / (p.1 + z p.1 p.2) := by
        unfold solvedDifferential
        field_simp [hpY]
        ring
  have hPY :
      (fun p : ℝ × ℝ => partialY z p.1 p.2) =ᶠ[nhds (x, y)]
        (fun p : ℝ × ℝ => z p.1 p.2 ^ 2 /
          (p.2 * (p.1 + z p.1 p.2))) := by
    filter_upwards [hsOpen.mem_nhds hxy, hzC2.eventually (by decide),
      continuous_snd.continuousAt.eventually_ne hy,
      hzDiff.continuousAt.eventually_ne hz,
      (continuous_fst.continuousAt.add hzDiff.continuousAt).eventually_ne hxz] with
        p hp hpC2 hpY hpZ hpXZ
    have hpImplicit :
        ∀ᶠ q : ℝ × ℝ in nhds p,
          q.1 / z q.1 q.2 = Real.log (z q.1 q.2 / q.2) + 1 := by
      filter_upwards [hsOpen.mem_nhds hp] with q hq
      exact hs hq
    have hpFirst := gap1 p.1 p.2 0 1 z hpY hpZ
      (hpC2.differentiableAt (by decide)) hpImplicit
    have hpSolved := gap2 p.1 p.2 0 1 z hpY hpZ hpXZ hpFirst
    calc
      partialY z p.1 p.2 = solvedDifferential z p.1 p.2 0 1 := by
        simpa [differential] using hpSolved
      _ = z p.1 p.2 ^ 2 / (p.2 * (p.1 + z p.1 p.2)) := by
        unfold solvedDifferential
        field_simp [hpY]
        ring
  have hpairX : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x := by
    fun_prop
  have hpairY : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y := by
    fun_prop
  have hPXx :
      (fun t : ℝ => partialX z t y) =ᶠ[nhds x]
        (fun t : ℝ => z t y / (t + z t y)) :=
    hpairX.continuousAt.tendsto.eventually hPX
  have hPXy :
      (fun t : ℝ => partialX z x t) =ᶠ[nhds y]
        (fun t : ℝ => z x t / (x + z x t)) :=
    hpairY.continuousAt.tendsto.eventually hPX
  have hPYy :
      (fun t : ℝ => partialY z x t) =ᶠ[nhds y]
        (fun t : ℝ => z x t ^ 2 / (t * (x + z x t))) :=
    hpairY.continuousAt.tendsto.eventually hPY
  have hzx : DifferentiableAt ℝ (fun t : ℝ => z t y) x := by
    simpa [Function.uncurry] using hzDiff.comp x hpairX
  have hzy : DifferentiableAt ℝ (fun t : ℝ => z x t) y := by
    simpa [Function.uncurry] using hzDiff.comp y hpairY
  have hzx' : HasDerivAt (fun t : ℝ => z t y) (partialX z x y) x := by
    simpa [partialX] using hzx.hasDerivAt
  have hzy' : HasDerivAt (fun t : ℝ => z x t) (partialY z x y) y := by
    simpa [partialY] using hzy.hasDerivAt
  have hAX :
      HasDerivAt (fun t : ℝ => z t y / (t + z t y))
        ((partialX z x y * (x + z x y) -
            z x y * (1 + partialX z x y)) /
          (x + z x y) ^ 2) x := by
    convert hzx'.div ((hasDerivAt_id x).add hzx') hxz using 1 <;>
      simp [id_eq] <;> ring
  have hAY :
      HasDerivAt (fun t : ℝ => z x t / (x + z x t))
        ((partialY z x y * (x + z x y) -
            z x y * partialY z x y) /
          (x + z x y) ^ 2) y := by
    convert hzy'.div ((hasDerivAt_const (x := y) x).add hzy') hxz using 1 <;>
      simp <;> ring
  have hBY :
      HasDerivAt (fun t : ℝ => z x t ^ 2 / (t * (x + z x t)))
        (((2 * z x y * partialY z x y) * (y * (x + z x y)) -
            z x y ^ 2 * ((x + z x y) + y * partialY z x y)) /
          (y * (x + z x y)) ^ 2) y := by
    convert (hzy'.pow 2).div
      ((hasDerivAt_id y).mul
        ((hasDerivAt_const (x := y) x).add hzy'))
      (mul_ne_zero hy hxz) using 1 <;> simp <;> ring
  have hXX :
      partialXX z x y =
        (partialX z x y * (x + z x y) -
            z x y * (1 + partialX z x y)) /
          (x + z x y) ^ 2 := by
    unfold partialXX
    calc
      deriv (fun t : ℝ => partialX z t y) x =
          deriv (fun t : ℝ => z t y / (t + z t y)) x := hPXx.deriv_eq
      _ = _ := hAX.deriv
  have hXY :
      partialXY z x y =
        (partialY z x y * (x + z x y) -
            z x y * partialY z x y) /
          (x + z x y) ^ 2 := by
    unfold partialXY
    calc
      deriv (fun t : ℝ => partialX z x t) y =
          deriv (fun t : ℝ => z x t / (x + z x t)) y := hPXy.deriv_eq
      _ = _ := hAY.deriv
  have hYY :
      partialYY z x y =
        ((2 * z x y * partialY z x y) * (y * (x + z x y)) -
            z x y ^ 2 * ((x + z x y) + y * partialY z x y)) /
          (y * (x + z x y)) ^ 2 := by
    unfold partialYY
    calc
      deriv (fun t : ℝ => partialY z x t) y =
          deriv (fun t : ℝ => z x t ^ 2 / (t * (x + z x t))) y := hPYy.deriv_eq
      _ = _ := hBY.deriv
  have hA : partialX z x y = z x y / (x + z x y) := hPX.eq_of_nhds
  have hB :
      partialY z x y = z x y ^ 2 / (y * (x + z x y)) := hPY.eq_of_nhds
  unfold secondDifferential expandedSecondRhs differential
  rw [hXX, hXY, hYY, hA, hB]
  field_simp [hy, hxz]
  <;> ring

theorem gap4 (x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (hExpanded :
      (x + z x y) * secondDifferential z x y dx dy =
        expandedSecondRhs z x y dx dy) :
    (x + z x y) * secondDifferential z x y dx dy =
      quadraticSecondRhs z x y dx dy := by
  rw [hExpanded]
  unfold expandedSecondRhs quadraticSecondRhs
  ring

theorem gap5 (x y dx dy : ℝ) (z : ℝ → ℝ → ℝ) :
    quadraticSecondRhs z x y dx dy =
      squareSecondRhs z x y dx dy := by
  unfold quadraticSecondRhs squareSecondRhs
  ring

theorem gap6 (x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (hQuadratic :
      (x + z x y) * secondDifferential z x y dx dy =
        quadraticSecondRhs z x y dx dy)
    (hSquare :
      quadraticSecondRhs z x y dx dy =
        squareSecondRhs z x y dx dy) :
    (x + z x y) * secondDifferential z x y dx dy =
      squareSecondRhs z x y dx dy := by
  exact hQuadratic.trans hSquare

theorem gap7 (x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (hy : y ≠ 0) (hxz : x + z x y ≠ 0)
    (hFirst :
      differential z x y dx dy =
        solvedDifferential z x y dx dy)
    (hSquare :
      (x + z x y) * secondDifferential z x y dx dy =
        squareSecondRhs z x y dx dy) :
    (x + z x y) * secondDifferential z x y dx dy =
      substitutedSecondRhs z x y dx dy := by
  rw [hSquare]
  unfold squareSecondRhs substitutedSecondRhs
  rw [hFirst]
  unfold solvedDifferential
  field_simp [hy, hxz]
  <;> ring

theorem gap8 (x y dx dy : ℝ) (z : ℝ → ℝ → ℝ) :
    substitutedSecondRhs z x y dx dy =
      simplifiedSecondRhs z x y dx dy := by
  unfold substitutedSecondRhs simplifiedSecondRhs
  ring

theorem gap9 (x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (hSubstituted :
      (x + z x y) * secondDifferential z x y dx dy =
        substitutedSecondRhs z x y dx dy)
    (hSimplified :
      substitutedSecondRhs z x y dx dy =
        simplifiedSecondRhs z x y dx dy) :
    (x + z x y) * secondDifferential z x y dx dy =
      simplifiedSecondRhs z x y dx dy := by
  exact hSubstituted.trans hSimplified

theorem gap10 (x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (hxz : x + z x y ≠ 0)
    (hFactored :
      (x + z x y) * secondDifferential z x y dx dy =
        simplifiedSecondRhs z x y dx dy) :
    secondDifferential z x y dx dy =
      finalSecondDifferential z x y dx dy := by
  apply mul_left_cancel₀ hxz
  rw [hFactored]
  unfold simplifiedSecondRhs finalSecondDifferential
  field_simp [hxz]
  <;> ring

end

end ProofGap.Exercise3392
