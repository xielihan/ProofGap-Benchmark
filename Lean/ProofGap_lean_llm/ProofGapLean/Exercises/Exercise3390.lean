import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3390

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

def solvedDifferential (a b c : ℝ) (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  -(c ^ 2 / z x y) * (x * dx / a ^ 2 + y * dy / b ^ 2)

def intermediateSecond (a b c : ℝ) (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  -(c ^ 2 / (z x y) ^ 2) *
    (z x y * (dx ^ 2 / a ^ 2 + dy ^ 2 / b ^ 2) -
      (x * dx / a ^ 2 + y * dy / b ^ 2) *
        differential z x y dx dy)

def closedSecond (a b c : ℝ) (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  -(c ^ 4 / (z x y) ^ 3) *
    ((x ^ 2 / a ^ 2 + (z x y) ^ 2 / c ^ 2) * (dx ^ 2 / a ^ 2) +
      (2 * x * y / (a ^ 2 * b ^ 2)) * dx * dy +
      (y ^ 2 / b ^ 2 + (z x y) ^ 2 / c ^ 2) * (dy ^ 2 / b ^ 2))

theorem gap1 (a b c x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hSurface :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 +
          (z p.1 p.2) ^ 2 / c ^ 2 = 1) :
    (2 * x / a ^ 2) * dx + (2 * y / b ^ 2) * dy +
      (2 * z x y / c ^ 2) * differential z x y dx dy = 0 := by
  have hzx : DifferentiableAt ℝ (fun t : ℝ => z t y) x := by
    fun_prop
  have hzy : DifferentiableAt ℝ (fun t : ℝ => z x t) y := by
    fun_prop
  have htx : ContinuousAt (fun t : ℝ => (t, y)) x := by
    fun_prop
  have hty : ContinuousAt (fun t : ℝ => (x, t)) y := by
    fun_prop
  have hsx :
      (fun t : ℝ => t ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 + (z t y) ^ 2 / c ^ 2) =ᶠ[nhds x]
        (fun _ : ℝ => 1) := by
    simpa using htx.eventually hSurface
  have hsy :
      (fun t : ℝ => x ^ 2 / a ^ 2 + t ^ 2 / b ^ 2 + (z x t) ^ 2 / c ^ 2) =ᶠ[nhds y]
        (fun _ : ℝ => 1) := by
    simpa using hty.eventually hSurface
  have hsqIdX : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).mul (hasDerivAt_id x)) using 1 <;>
      simp [pow_two] <;> try ring
    funext t
    rfl
  have hsqIdY : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
    convert ((hasDerivAt_id y).mul (hasDerivAt_id y)) using 1 <;>
      simp [pow_two] <;> try ring
    funext t
    rfl
  have hsqZX : HasDerivAt (fun t : ℝ => (z t y) ^ 2)
      (2 * z x y * partialX z x y) x := by
    convert (hzx.hasDerivAt.mul hzx.hasDerivAt) using 1 <;>
      simp [partialX, pow_two] <;> try ring
    funext t
    rfl
  have hsqZY : HasDerivAt (fun t : ℝ => (z x t) ^ 2)
      (2 * z x y * partialY z x y) y := by
    convert (hzy.hasDerivAt.mul hzy.hasDerivAt) using 1 <;>
      simp [partialY, pow_two] <;> try ring
    funext t
    rfl
  have hcalcX : HasDerivAt
      (fun t : ℝ => t ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 + (z t y) ^ 2 / c ^ 2)
      (2 * x / a ^ 2 + 2 * z x y / c ^ 2 * partialX z x y) x := by
    have h1 :=
      (hsqIdX.div_const (a ^ 2)).add
        (hasDerivAt_const x (y ^ 2 / b ^ 2))
    have h2 := h1.add (hsqZX.div_const (c ^ 2))
    convert h2 using 1 <;>
      simp [partialX] <;> ring
  have hcalcY : HasDerivAt
      (fun t : ℝ => x ^ 2 / a ^ 2 + t ^ 2 / b ^ 2 + (z x t) ^ 2 / c ^ 2)
      (2 * y / b ^ 2 + 2 * z x y / c ^ 2 * partialY z x y) y := by
    have h1 :=
      (hasDerivAt_const y (x ^ 2 / a ^ 2)).add
        (hsqIdY.div_const (b ^ 2))
    have h2 := h1.add (hsqZY.div_const (c ^ 2))
    convert h2 using 1 <;>
      simp [partialY] <;> ring
  have hxRel : 2 * x / a ^ 2 + 2 * z x y / c ^ 2 * partialX z x y = 0 := by
    have hzero : deriv
        (fun t : ℝ => t ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 + (z t y) ^ 2 / c ^ 2) x = 0 := by
      calc
        deriv (fun t : ℝ => t ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 + (z t y) ^ 2 / c ^ 2) x =
            deriv (fun _ : ℝ => 1) x := hsx.deriv_eq
        _ = 0 := by simp
    rw [hcalcX.deriv] at hzero
    exact hzero
  have hyRel : 2 * y / b ^ 2 + 2 * z x y / c ^ 2 * partialY z x y = 0 := by
    have hzero : deriv
        (fun t : ℝ => x ^ 2 / a ^ 2 + t ^ 2 / b ^ 2 + (z x t) ^ 2 / c ^ 2) y = 0 := by
      calc
        deriv (fun t : ℝ => x ^ 2 / a ^ 2 + t ^ 2 / b ^ 2 + (z x t) ^ 2 / c ^ 2) y =
            deriv (fun _ : ℝ => 1) y := hsy.deriv_eq
        _ = 0 := by simp
    rw [hcalcY.deriv] at hzero
    exact hzero
  unfold differential
  linear_combination dx * hxRel + dy * hyRel

theorem gap2 (a b c x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hz : z x y ≠ 0)
    (hFirst :
      (2 * x / a ^ 2) * dx + (2 * y / b ^ 2) * dy +
        (2 * z x y / c ^ 2) * differential z x y dx dy = 0) :
    differential z x y dx dy =
      solvedDifferential a b c z x y dx dy := by
  unfold solvedDifferential
  field_simp [ha, hb, hc, hz] at hFirst ⊢
  nlinarith

theorem gap3 (a b c x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hz : z x y ≠ 0)
    (hzC2 : ContDiffAt ℝ 2 (Function.uncurry z) (x, y))
    (hSurface :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 +
          (z p.1 p.2) ^ 2 / c ^ 2 = 1) :
    secondDifferential z x y dx dy =
      intermediateSecond a b c z x y dx dy := by
  have hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y) :=
    hzC2.differentiableAt (by decide)
  have hzx : DifferentiableAt ℝ (fun t : ℝ => z t y) x := by
    fun_prop
  have hzy : DifferentiableAt ℝ (fun t : ℝ => z x t) y := by
    fun_prop
  let S : Set (ℝ × ℝ) :=
    {p | p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 + (z p.1 p.2) ^ 2 / c ^ 2 = 1}
  have hS : S ∈ nhds (x, y) := by
    simpa [S] using hSurface
  rcases mem_nhds_iff.1 hS with ⟨U, hUS, hUopen, hxyU⟩
  have htx : ContinuousAt (fun t : ℝ => (t, y)) x := by
    fun_prop
  have hty : ContinuousAt (fun t : ℝ => (x, t)) y := by
    fun_prop
  have hUx : ∀ᶠ t in nhds x, (t, y) ∈ U :=
    htx.eventually (hUopen.mem_nhds hxyU)
  have hUy : ∀ᶠ t in nhds y, (x, t) ∈ U :=
    hty.eventually (hUopen.mem_nhds hxyU)
  have hC2xy :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        ContDiffAt ℝ 2 (Function.uncurry z) p :=
    hzC2.eventually (by norm_num)
  have hC2x : ∀ᶠ t in nhds x, ContDiffAt ℝ 2 (Function.uncurry z) (t, y) := by
    simpa using htx.eventually hC2xy
  have hC2y : ∀ᶠ t in nhds y, ContDiffAt ℝ 2 (Function.uncurry z) (x, t) := by
    simpa using hty.eventually hC2xy
  have hznx : ∀ᶠ t in nhds x, z t y ≠ 0 :=
    hzx.continuousAt.eventually_ne hz
  have hzny : ∀ᶠ t in nhds y, z x t ≠ 0 :=
    hzy.continuousAt.eventually_ne hz
  have hPXx :
      (fun t : ℝ => partialX z t y) =ᶠ[nhds x]
        (fun t : ℝ => (-(c ^ 2)) * t / (a ^ 2 * z t y)) := by
    filter_upwards [hUx, hC2x, hznx] with t htU htC2 hzt
    have hst :
        ∀ᶠ p : ℝ × ℝ in nhds (t, y),
          p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 + (z p.1 p.2) ^ 2 / c ^ 2 = 1 := by
      filter_upwards [hUopen.mem_nhds htU] with p hp
      simpa [S] using hUS hp
    have hgFirst := gap1 a b c t y 1 0 z ha hb hc
      (htC2.differentiableAt (by decide)) hst
    have hgSolved := gap2 a b c t y 1 0 z ha hb hc hzt hgFirst
    calc
      partialX z t y = solvedDifferential a b c z t y 1 0 := by
        simpa [differential] using hgSolved
      _ = (-(c ^ 2)) * t / (a ^ 2 * z t y) := by
        unfold solvedDifferential
        field_simp [ha, hb, hzt] <;> ring
  have hPXy :
      (fun t : ℝ => partialX z x t) =ᶠ[nhds y]
        (fun t : ℝ => (-(c ^ 2)) * x / (a ^ 2 * z x t)) := by
    filter_upwards [hUy, hC2y, hzny] with t htU htC2 hzt
    have hst :
        ∀ᶠ p : ℝ × ℝ in nhds (x, t),
          p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 + (z p.1 p.2) ^ 2 / c ^ 2 = 1 := by
      filter_upwards [hUopen.mem_nhds htU] with p hp
      simpa [S] using hUS hp
    have hgFirst := gap1 a b c x t 1 0 z ha hb hc
      (htC2.differentiableAt (by decide)) hst
    have hgSolved := gap2 a b c x t 1 0 z ha hb hc hzt hgFirst
    calc
      partialX z x t = solvedDifferential a b c z x t 1 0 := by
        simpa [differential] using hgSolved
      _ = (-(c ^ 2)) * x / (a ^ 2 * z x t) := by
        unfold solvedDifferential
        field_simp [ha, hb, hzt] <;> ring
  have hPYy :
      (fun t : ℝ => partialY z x t) =ᶠ[nhds y]
        (fun t : ℝ => (-(c ^ 2)) * t / (b ^ 2 * z x t)) := by
    filter_upwards [hUy, hC2y, hzny] with t htU htC2 hzt
    have hst :
        ∀ᶠ p : ℝ × ℝ in nhds (x, t),
          p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 + (z p.1 p.2) ^ 2 / c ^ 2 = 1 := by
      filter_upwards [hUopen.mem_nhds htU] with p hp
      simpa [S] using hUS hp
    have hgFirst := gap1 a b c x t 0 1 z ha hb hc
      (htC2.differentiableAt (by decide)) hst
    have hgSolved := gap2 a b c x t 0 1 z ha hb hc hzt hgFirst
    calc
      partialY z x t = solvedDifferential a b c z x t 0 1 := by
        simpa [differential] using hgSolved
      _ = (-(c ^ 2)) * t / (b ^ 2 * z x t) := by
        unfold solvedDifferential
        field_simp [ha, hb, hzt] <;> ring
  have hDerivXX : HasDerivAt
      (fun t : ℝ => (-(c ^ 2)) * t / (a ^ 2 * z t y))
      (-(c ^ 2) * (z x y - x * partialX z x y) /
        (a ^ 2 * (z x y) ^ 2)) x := by
    convert
      (((hasDerivAt_const x (-(c ^ 2))).mul (hasDerivAt_id x)).div
        ((hasDerivAt_const x (a ^ 2)).mul hzx.hasDerivAt)
        (mul_ne_zero (pow_ne_zero 2 ha) hz)) using 1 <;>
      simp [partialX] <;> field_simp [ha, hz] <;> ring
  have hDerivXY : HasDerivAt
      (fun t : ℝ => (-(c ^ 2)) * x / (a ^ 2 * z x t))
      (c ^ 2 * x * partialY z x y / (a ^ 2 * (z x y) ^ 2)) y := by
    convert
      ((hasDerivAt_const y ((-(c ^ 2)) * x)).div
        ((hasDerivAt_const y (a ^ 2)).mul hzy.hasDerivAt)
        (mul_ne_zero (pow_ne_zero 2 ha) hz)) using 1 <;>
      simp [partialY] <;> field_simp [ha, hz] <;> ring
  have hDerivYY : HasDerivAt
      (fun t : ℝ => (-(c ^ 2)) * t / (b ^ 2 * z x t))
      (-(c ^ 2) * (z x y - y * partialY z x y) /
        (b ^ 2 * (z x y) ^ 2)) y := by
    convert
      (((hasDerivAt_const y (-(c ^ 2))).mul (hasDerivAt_id y)).div
        ((hasDerivAt_const y (b ^ 2)).mul hzy.hasDerivAt)
        (mul_ne_zero (pow_ne_zero 2 hb) hz)) using 1 <;>
      simp [partialY] <;> field_simp [hb, hz] <;> ring
  have hXX : partialXX z x y =
      -(c ^ 2) * (z x y - x * partialX z x y) /
        (a ^ 2 * (z x y) ^ 2) := by
    calc
      partialXX z x y =
          deriv (fun t : ℝ => (-(c ^ 2)) * t / (a ^ 2 * z t y)) x := by
            simpa [partialXX] using hPXx.deriv_eq
      _ = _ := hDerivXX.deriv
  have hXY : partialXY z x y =
      c ^ 2 * x * partialY z x y / (a ^ 2 * (z x y) ^ 2) := by
    calc
      partialXY z x y =
          deriv (fun t : ℝ => (-(c ^ 2)) * x / (a ^ 2 * z x t)) y := by
            simpa [partialXY] using hPXy.deriv_eq
      _ = _ := hDerivXY.deriv
  have hYY : partialYY z x y =
      -(c ^ 2) * (z x y - y * partialY z x y) /
        (b ^ 2 * (z x y) ^ 2) := by
    calc
      partialYY z x y =
          deriv (fun t : ℝ => (-(c ^ 2)) * t / (b ^ 2 * z x t)) y := by
            simpa [partialYY] using hPYy.deriv_eq
      _ = _ := hDerivYY.deriv
  have hPX0 : partialX z x y =
      (-(c ^ 2)) * x / (a ^ 2 * z x y) := hPXx.self_of_nhds
  have hPY0 : partialY z x y =
      (-(c ^ 2)) * y / (b ^ 2 * z x y) := hPYy.self_of_nhds
  unfold secondDifferential intermediateSecond differential
  rw [hXX, hXY, hYY, hPX0, hPY0]
  field_simp [ha, hb, hc, hz]
  ring

theorem gap4 (a b c x y dx dy : ℝ) (z : ℝ → ℝ → ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hz : z x y ≠ 0)
    (hSurface :
      x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 + (z x y) ^ 2 / c ^ 2 = 1)
    (hFirst :
      differential z x y dx dy =
        solvedDifferential a b c z x y dx dy)
    (hSecond :
      secondDifferential z x y dx dy =
        intermediateSecond a b c z x y dx dy) :
    secondDifferential z x y dx dy =
      closedSecond a b c z x y dx dy := by
  rw [hSecond]
  unfold intermediateSecond closedSecond
  rw [hFirst]
  unfold solvedDifferential
  field_simp [ha, hb, hc, hz]
  ring

end

end ProofGap.Exercise3390
