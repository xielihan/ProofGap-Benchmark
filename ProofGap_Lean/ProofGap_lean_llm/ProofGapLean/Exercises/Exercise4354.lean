import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise4354

noncomputable section

open scoped Interval

def coneHeight (a b x y : ℝ) : ℝ :=
  b / a * Real.sqrt (x ^ 2 + y ^ 2)

def conePatch (a b : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  {p |
    p.2.2 = coneHeight a b p.1 p.2.1 ∧
      p.1 ^ 2 + p.2.1 ^ 2 ≤ a ^ 2}

def distanceToAxis (a b x y : ℝ) : ℝ :=
  Real.sqrt ((coneHeight a b x y - b) ^ 2 + y ^ 2)

def graphAreaFactor (a b x y : ℝ) : ℝ :=
  Real.sqrt
    (1 + (deriv (fun s => coneHeight a b s y) x) ^ 2 +
      (deriv (fun s => coneHeight a b x s) y) ^ 2)

def coneInertia (a b ρ₀ : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 + b ^ 2) / a * ρ₀ *
    ∫ φ in (0 : ℝ)..2 * Real.pi,
      ∫ r in (0 : ℝ)..a,
        ((b / a * r - b) ^ 2 +
          r ^ 2 * Real.sin φ ^ 2) * r

theorem gap1 (a b x y : ℝ) :
    distanceToAxis a b x y =
      Real.sqrt
        ((b / a * Real.sqrt (x ^ 2 + y ^ 2) - b) ^ 2 +
          y ^ 2) := by
  rfl

theorem gap2
    (a b x y : ℝ) (ha : 0 < a) (hne : (x, y) ≠ (0, 0)) :
    graphAreaFactor a b x y =
      Real.sqrt (a ^ 2 + b ^ 2) / a := by
  have hqpos : 0 < x ^ 2 + y ^ 2 := by
    rcases eq_or_ne x 0 with hx | hx
    · have hy : y ≠ 0 := by
        intro hy
        apply hne
        simp [hx, hy]
      have hy2 : 0 < y * y := mul_self_pos.mpr hy
      simp [hx, pow_two, hy2]
    · have hx2 : 0 < x * x := mul_self_pos.mpr hx
      nlinarith [sq_nonneg y]
  have hsqrtpos : 0 < Real.sqrt (x ^ 2 + y ^ 2) := Real.sqrt_pos.2 hqpos
  have hpowx : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
    simpa [id, mul_comm] using ((hasDerivAt_id x).pow 2)
  have hpowy : HasDerivAt (fun s : ℝ => s ^ 2) (2 * y) y := by
    simpa [id, mul_comm] using ((hasDerivAt_id y).pow 2)
  have hradx :
      HasDerivAt (fun s : ℝ => s ^ 2 + y ^ 2) (2 * x) x :=
    hpowx.add_const (y ^ 2)
  have hrady :
      HasDerivAt (fun s : ℝ => x ^ 2 + s ^ 2) (2 * y) y :=
    hpowy.const_add (x ^ 2)
  have hdxHas :
      HasDerivAt (fun s : ℝ => coneHeight a b s y)
        (b / a * (x / Real.sqrt (x ^ 2 + y ^ 2))) x := by
    convert
      ((Real.hasDerivAt_sqrt (ne_of_gt hqpos)).comp x hradx).const_mul (b / a)
      using 1 <;>
      field_simp [ne_of_gt hsqrtpos] <;>
      ring
  have hdyHas :
      HasDerivAt (fun s : ℝ => coneHeight a b x s)
        (b / a * (y / Real.sqrt (x ^ 2 + y ^ 2))) y := by
    convert
      ((Real.hasDerivAt_sqrt (ne_of_gt hqpos)).comp y hrady).const_mul (b / a)
      using 1 <;>
      field_simp [ne_of_gt hsqrtpos] <;>
      ring
  have hsq : (Real.sqrt (x ^ 2 + y ^ 2)) ^ 2 = x ^ 2 + y ^ 2 :=
    Real.sq_sqrt (le_of_lt hqpos)
  have hinside :
      1 + (b / a * (x / Real.sqrt (x ^ 2 + y ^ 2))) ^ 2 +
          (b / a * (y / Real.sqrt (x ^ 2 + y ^ 2))) ^ 2 =
        (a ^ 2 + b ^ 2) / a ^ 2 := by
    field_simp [ne_of_gt ha, ne_of_gt hsqrtpos]
    nlinarith
  unfold graphAreaFactor
  rw [hdxHas.deriv, hdyHas.deriv, hinside]
  rw [Real.sqrt_div (by positivity : 0 ≤ a ^ 2 + b ^ 2)]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ha]

theorem gap3
    (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    coneInertia a b ρ₀ =
      Real.sqrt (a ^ 2 + b ^ 2) / a * ρ₀ *
        (∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..a,
            ((b / a * r - b) ^ 2 +
              r ^ 2 * Real.sin φ ^ 2) * r) := by
  rfl

theorem gap4
    (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    coneInertia a b ρ₀ =
      Real.sqrt (a ^ 2 + b ^ 2) / a * ρ₀ *
        (∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..a,
            ((b / a * r - b) ^ 2 +
              r ^ 2 * Real.sin φ ^ 2) * r) := by
  rfl

theorem gap5
    (a b ρ₀ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    coneInertia a b ρ₀ =
      Real.pi * a * ρ₀ * (3 * a ^ 2 + 2 * b ^ 2) *
        Real.sqrt (a ^ 2 + b ^ 2) / 12 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hinner (φ : ℝ) :
      (∫ r in (0 : ℝ)..a,
        ((b / a * r - b) ^ 2 + r ^ 2 * Real.sin φ ^ 2) * r) =
        b ^ 2 * a ^ 2 / 12 + a ^ 4 / 4 * Real.sin φ ^ 2 := by
    let F : ℝ → ℝ := fun r =>
      (b ^ 2 / a ^ 2 + Real.sin φ ^ 2) * r ^ 4 / 4 -
        (2 * b ^ 2 / a) * r ^ 3 / 3 +
        b ^ 2 * r ^ 2 / 2
    have hF (r : ℝ) :
        HasDerivAt F
          (((b / a * r - b) ^ 2 + r ^ 2 * Real.sin φ ^ 2) * r) r := by
      have hp2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
        simpa [id, mul_comm] using ((hasDerivAt_id r).pow 2)
      have hp3 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * r ^ 2) r := by
        simpa [id, mul_comm] using ((hasDerivAt_id r).pow 3)
      have hp4 : HasDerivAt (fun s : ℝ => s ^ 4) (4 * r ^ 3) r := by
        simpa [id, mul_comm] using ((hasDerivAt_id r).pow 4)
      have h4 :
          HasDerivAt
            (fun s : ℝ =>
              (b ^ 2 / a ^ 2 + Real.sin φ ^ 2) * s ^ 4 / 4)
            ((b ^ 2 / a ^ 2 + Real.sin φ ^ 2) *
              (4 * r ^ 3) / 4) r := by
        exact
          ((hp4.const_mul
            (b ^ 2 / a ^ 2 + Real.sin φ ^ 2)).div_const 4)
      have h3 :
          HasDerivAt
            (fun s : ℝ => (2 * b ^ 2 / a) * s ^ 3 / 3)
            ((2 * b ^ 2 / a) * (3 * r ^ 2) / 3) r := by
        exact
          ((hp3.const_mul (2 * b ^ 2 / a)).div_const 3)
      have h2 :
          HasDerivAt
            (fun s : ℝ => b ^ 2 * s ^ 2 / 2)
            (b ^ 2 * (2 * r) / 2) r := by
        exact
          ((hp2.const_mul (b ^ 2)).div_const 2)
      have hpoly :
          HasDerivAt F
            (((b ^ 2 / a ^ 2 + Real.sin φ ^ 2) *
                (4 * r ^ 3) / 4 -
              (2 * b ^ 2 / a) * (3 * r ^ 2) / 3) +
              b ^ 2 * (2 * r) / 2) r := by
        dsimp [F]
        exact (h4.sub h3).add h2
      have hvalue :
          (((b ^ 2 / a ^ 2 + Real.sin φ ^ 2) *
                (4 * r ^ 3) / 4 -
              (2 * b ^ 2 / a) * (3 * r ^ 2) / 3) +
              b ^ 2 * (2 * r) / 2) =
            ((b / a * r - b) ^ 2 +
              r ^ 2 * Real.sin φ ^ 2) * r := by
        field_simp [ha0] <;> ring
      rw [hvalue] at hpoly
      exact hpoly
    calc
      (∫ r in (0 : ℝ)..a,
          ((b / a * r - b) ^ 2 + r ^ 2 * Real.sin φ ^ 2) * r) =
          F a - F 0 := by
            exact intervalIntegral.integral_eq_sub_of_hasDerivAt
              (fun r _ => hF r)
              (by
                apply Continuous.intervalIntegrable
                continuity)
      _ = b ^ 2 * a ^ 2 / 12 + a ^ 4 / 4 * Real.sin φ ^ 2 := by
        dsimp [F]
        field_simp [ha0] <;> ring
  have hsinAnti (φ : ℝ) :
      HasDerivAt
        (fun t : ℝ => t / 2 - Real.sin t * Real.cos t / 2)
        (Real.sin φ ^ 2) φ := by
    have hraw :
        HasDerivAt
          (fun t : ℝ => t / 2 - Real.sin t * Real.cos t / 2)
          (1 / 2 -
            (Real.cos φ * Real.cos φ +
              Real.sin φ * (-Real.sin φ)) / 2) φ := by
      simpa [id] using
        (((hasDerivAt_id φ).div_const 2).sub
          (((Real.hasDerivAt_sin φ).mul
            (Real.hasDerivAt_cos φ)).div_const 2))
    have hcoeff :
        (1 / 2 -
          (Real.cos φ * Real.cos φ +
            Real.sin φ * (-Real.sin φ)) / 2 : ℝ) =
          Real.sin φ ^ 2 := by
      rw [← Real.sin_sq_add_cos_sq φ]
      ring
    rw [hcoeff] at hraw
    exact hraw
  have htotal :
      (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..a,
          ((b / a * r - b) ^ 2 + r ^ 2 * Real.sin φ ^ 2) * r) =
        Real.pi * a ^ 2 * (3 * a ^ 2 + 2 * b ^ 2) / 12 := by
    let G : ℝ → ℝ := fun φ =>
      (b ^ 2 * a ^ 2 / 12) * φ +
        (a ^ 4 / 4) *
          (φ / 2 - Real.sin φ * Real.cos φ / 2)
    have hG (φ : ℝ) :
        HasDerivAt G
          (b ^ 2 * a ^ 2 / 12 + a ^ 4 / 4 * Real.sin φ ^ 2) φ := by
      have hlinear :
          HasDerivAt
            (fun t : ℝ => (b ^ 2 * a ^ 2 / 12) * t)
            (b ^ 2 * a ^ 2 / 12) φ := by
        simpa [id] using
          ((hasDerivAt_id φ).const_mul (b ^ 2 * a ^ 2 / 12))
      have htrig :
          HasDerivAt
            (fun t : ℝ =>
              (a ^ 4 / 4) *
                (t / 2 - Real.sin t * Real.cos t / 2))
            ((a ^ 4 / 4) * Real.sin φ ^ 2) φ := by
        simpa using
          ((hsinAnti φ).const_mul (a ^ 4 / 4))
      simpa [G] using (hlinear.add htrig)
    calc
      (∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..a,
            ((b / a * r - b) ^ 2 + r ^ 2 * Real.sin φ ^ 2) * r) =
          ∫ φ in (0 : ℝ)..2 * Real.pi,
            (b ^ 2 * a ^ 2 / 12 + a ^ 4 / 4 * Real.sin φ ^ 2) := by
              apply intervalIntegral.integral_congr
              intro φ _
              exact hinner φ
      _ = G (2 * Real.pi) - G 0 := by
            exact intervalIntegral.integral_eq_sub_of_hasDerivAt
              (fun φ _ => hG φ)
              (by
                apply Continuous.intervalIntegrable
                continuity)
      _ = Real.pi * a ^ 2 * (3 * a ^ 2 + 2 * b ^ 2) / 12 := by
        dsimp [G]
        rw [Real.sin_two_pi, Real.sin_zero]
        ring
  unfold coneInertia
  rw [htotal]
  field_simp [ha0] <;> ring

end

end ProofGap.Exercise4354
