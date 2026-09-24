import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped Interval

namespace ProofGap.Exercise2451

noncomputable section

def radius (a φ : ℝ) : ℝ := a * Real.tanh (φ / 2)

def radiusDeriv (a φ : ℝ) : ℝ :=
  a / 2 * (1 / Real.cosh (φ / 2) ^ 2)

def polarSpeed (a φ : ℝ) : ℝ :=
  Real.sqrt (radius a φ ^ 2 + radiusDeriv a φ ^ 2)

def arcLength (a : ℝ) : ℝ :=
  ∫ φ in 0..(2 * Real.pi), polarSpeed a φ

private theorem proofgap_hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hq :=
    (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have heq :
      Real.tanh = fun y : ℝ => Real.sinh y / Real.cosh y := by
    funext y
    exact Real.tanh_eq_sinh_div_cosh y
  have hnum :
      Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  rw [heq]
  convert hq using 1
  rw [hnum]

theorem gap1 (a φ : ℝ) :
    deriv (radius a) φ = radiusDeriv a φ := by
  have hinner : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) φ := by
    simpa using (hasDerivAt_id φ).div_const 2
  have hraw :=
    ((proofgap_hasDerivAt_tanh (φ / 2)).comp φ hinner).const_mul a
  have h : HasDerivAt (radius a) (radiusDeriv a φ) φ := by
    unfold radius radiusDeriv
    convert hraw using 1 <;> ring
  exact h.deriv

theorem gap2 (a φ : ℝ) (ha : 0 ≤ a) :
    polarSpeed a φ =
      a / (2 * Real.cosh (φ / 2) ^ 2) *
        Real.sqrt
          (4 * Real.sinh (φ / 2) ^ 2 * Real.cosh (φ / 2) ^ 2 + 1) := by
  unfold polarSpeed radius radiusDeriv
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh (φ / 2) ≠ 0 :=
    ne_of_gt (Real.cosh_pos (φ / 2))
  have h₁ :
      0 ≤
        (a * (Real.sinh (φ / 2) / Real.cosh (φ / 2))) ^ 2 +
          (a / 2 * (1 / Real.cosh (φ / 2) ^ 2)) ^ 2 := by
    positivity
  have h₂ :
      0 ≤ 4 * Real.sinh (φ / 2) ^ 2 * Real.cosh (φ / 2) ^ 2 + 1 := by
    positivity
  have heq :
      (a * (Real.sinh (φ / 2) / Real.cosh (φ / 2))) ^ 2 +
          (a / 2 * (1 / Real.cosh (φ / 2) ^ 2)) ^ 2 =
        (a / (2 * Real.cosh (φ / 2) ^ 2)) ^ 2 *
          (4 * Real.sinh (φ / 2) ^ 2 * Real.cosh (φ / 2) ^ 2 + 1) := by
    field_simp [hc]
    <;> ring
  have hsq :
      (Real.sqrt
          ((a * (Real.sinh (φ / 2) / Real.cosh (φ / 2))) ^ 2 +
            (a / 2 * (1 / Real.cosh (φ / 2) ^ 2)) ^ 2)) ^ 2 =
        (a / (2 * Real.cosh (φ / 2) ^ 2) *
          Real.sqrt
            (4 * Real.sinh (φ / 2) ^ 2 * Real.cosh (φ / 2) ^ 2 + 1)) ^ 2 := by
    calc
      (Real.sqrt
          ((a * (Real.sinh (φ / 2) / Real.cosh (φ / 2))) ^ 2 +
            (a / 2 * (1 / Real.cosh (φ / 2) ^ 2)) ^ 2)) ^ 2 =
          (a * (Real.sinh (φ / 2) / Real.cosh (φ / 2))) ^ 2 +
            (a / 2 * (1 / Real.cosh (φ / 2) ^ 2)) ^ 2 :=
        Real.sq_sqrt h₁
      _ =
          (a / (2 * Real.cosh (φ / 2) ^ 2)) ^ 2 *
            (4 * Real.sinh (φ / 2) ^ 2 * Real.cosh (φ / 2) ^ 2 + 1) := heq
      _ =
          (a / (2 * Real.cosh (φ / 2) ^ 2) *
            Real.sqrt
              (4 * Real.sinh (φ / 2) ^ 2 * Real.cosh (φ / 2) ^ 2 + 1)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt h₂]
  have hleft :
      0 ≤ Real.sqrt
        ((a * (Real.sinh (φ / 2) / Real.cosh (φ / 2))) ^ 2 +
          (a / 2 * (1 / Real.cosh (φ / 2) ^ 2)) ^ 2) :=
    Real.sqrt_nonneg _
  have hright :
      0 ≤ a / (2 * Real.cosh (φ / 2) ^ 2) *
        Real.sqrt
          (4 * Real.sinh (φ / 2) ^ 2 * Real.cosh (φ / 2) ^ 2 + 1) := by
    positivity
  nlinarith

theorem gap3 (a φ : ℝ) (ha : 0 ≤ a) :
    polarSpeed a φ = a * Real.cosh φ / (1 + Real.cosh φ) := by
  rw [gap2 a φ ha]
  have hcs := Real.cosh_sq_sub_sinh_sq (φ / 2)
  have hs :
      Real.sinh (φ / 2) ^ 2 = Real.cosh (φ / 2) ^ 2 - 1 := by
    nlinarith
  have hct :
      Real.cosh φ = 2 * Real.cosh (φ / 2) ^ 2 - 1 := by
    calc
      Real.cosh φ = Real.cosh (2 * (φ / 2)) := by
        congr 1
        ring
      _ = Real.cosh (φ / 2) ^ 2 + Real.sinh (φ / 2) ^ 2 :=
        Real.cosh_two_mul (φ / 2)
      _ = 2 * Real.cosh (φ / 2) ^ 2 - 1 := by
        nlinarith
  have hrad :
      4 * Real.sinh (φ / 2) ^ 2 * Real.cosh (φ / 2) ^ 2 + 1 =
        Real.cosh φ ^ 2 := by
    rw [hs, hct]
    ring
  have hsqrt :
      Real.sqrt
          (4 * Real.sinh (φ / 2) ^ 2 * Real.cosh (φ / 2) ^ 2 + 1) =
        Real.cosh φ := by
    rw [hrad]
    exact Real.sqrt_sq (le_of_lt (Real.cosh_pos φ))
  have hden :
      1 + Real.cosh φ = 2 * Real.cosh (φ / 2) ^ 2 := by
    rw [hct]
    ring
  rw [hsqrt, hden]
  ring

theorem gap4 (a φ : ℝ) (ha : 0 ≤ a) :
    polarSpeed a φ =
      a * (1 - 1 / (2 * Real.cosh (φ / 2) ^ 2)) := by
  rw [gap3 a φ ha]
  have hc : Real.cosh (φ / 2) ≠ 0 :=
    ne_of_gt (Real.cosh_pos (φ / 2))
  have hcs := Real.cosh_sq_sub_sinh_sq (φ / 2)
  have hct :
      Real.cosh φ = 2 * Real.cosh (φ / 2) ^ 2 - 1 := by
    calc
      Real.cosh φ = Real.cosh (2 * (φ / 2)) := by
        congr 1
        ring
      _ = Real.cosh (φ / 2) ^ 2 + Real.sinh (φ / 2) ^ 2 :=
        Real.cosh_two_mul (φ / 2)
      _ = 2 * Real.cosh (φ / 2) ^ 2 - 1 := by
        nlinarith
  rw [hct]
  field_simp [hc]
  <;> ring

theorem gap5 (a s : ℝ) (ha : 0 ≤ a) (hs : s = arcLength a) :
    s = ∫ φ in 0..(2 * Real.pi),
      a * (1 - 1 / (2 * Real.cosh (φ / 2) ^ 2)) := by
  rw [hs, arcLength]
  apply intervalIntegral.integral_congr
  intro φ _
  exact gap4 a φ ha

theorem gap6 (a s : ℝ) (ha : 0 ≤ a) (hs : s = arcLength a) :
    s =
      (a * ((2 * Real.pi) - Real.tanh ((2 * Real.pi) / 2))) -
        (a * (0 - Real.tanh (0 / 2))) := by
  rw [gap5 a s ha hs]
  let F : ℝ → ℝ := fun x => a * (x - Real.tanh (x / 2))
  let g : ℝ → ℝ :=
    fun x => a * (1 - 1 / (2 * Real.cosh (x / 2) ^ 2))
  have hderiv : ∀ x : ℝ, HasDerivAt F (g x) x := by
    intro x
    have hinner : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
      simpa using (hasDerivAt_id x).div_const 2
    have ht := (proofgap_hasDerivAt_tanh (x / 2)).comp x hinner
    have hc : Real.cosh (x / 2) ≠ 0 :=
      ne_of_gt (Real.cosh_pos (x / 2))
    dsimp [F, g]
    convert ((hasDerivAt_id x).sub ht).const_mul a using 1 <;>
      field_simp [hc] <;> ring
  have hxdiv : Continuous (fun x : ℝ => x / 2) :=
    continuous_id.div_const 2
  have hcosh : Continuous (fun x : ℝ => Real.cosh (x / 2)) :=
    Real.continuous_cosh.comp hxdiv
  have hden :
      Continuous (fun x : ℝ => 2 * Real.cosh (x / 2) ^ 2) :=
    continuous_const.mul (hcosh.pow 2)
  have hden_ne : ∀ x : ℝ, 2 * Real.cosh (x / 2) ^ 2 ≠ 0 := by
    intro x
    positivity
  have hinv :
      Continuous (fun x : ℝ => 1 / (2 * Real.cosh (x / 2) ^ 2)) :=
    continuous_const.div hden hden_ne
  have hg : Continuous g := by
    dsimp [g]
    exact continuous_const.mul (continuous_const.sub hinv)
  have hderiv_eq : deriv F = g := by
    funext x
    exact (hderiv x).deriv
  have hint :
      IntervalIntegrable (deriv F) MeasureTheory.volume 0 (2 * Real.pi) := by
    rw [hderiv_eq]
    exact hg.intervalIntegrable 0 (2 * Real.pi)
  have hFTC :
      (∫ x in 0..(2 * Real.pi), deriv F x) =
        F (2 * Real.pi) - F 0 :=
    intervalIntegral.integral_deriv_eq_sub
      (fun x _ => (hderiv x).differentiableAt) hint
  calc
    (∫ x in 0..(2 * Real.pi),
        a * (1 - 1 / (2 * Real.cosh (x / 2) ^ 2))) =
        ∫ x in 0..(2 * Real.pi), deriv F x := by
      apply intervalIntegral.integral_congr
      intro x _
      symm
      exact (hderiv x).deriv
    _ = F (2 * Real.pi) - F 0 := hFTC
    _ =
        (a * ((2 * Real.pi) - Real.tanh ((2 * Real.pi) / 2))) -
          (a * (0 - Real.tanh (0 / 2))) := by
      rfl

theorem gap7 (a : ℝ) :
    (a * ((2 * Real.pi) - Real.tanh ((2 * Real.pi) / 2))) -
        (a * (0 - Real.tanh (0 / 2))) =
      a * (2 * Real.pi - Real.tanh Real.pi) := by
  have hhalf : (2 * Real.pi) / 2 = Real.pi := by
    ring
  rw [hhalf]
  simp

theorem gap8 (a s : ℝ) (ha : 0 ≤ a) (hs : s = arcLength a) :
    s = a * (2 * Real.pi - Real.tanh Real.pi) := by
  calc
    s =
        (a * ((2 * Real.pi) - Real.tanh ((2 * Real.pi) / 2))) -
          (a * (0 - Real.tanh (0 / 2))) :=
      gap6 a s ha hs
    _ = a * (2 * Real.pi - Real.tanh Real.pi) := gap7 a

end

end ProofGap.Exercise2451
