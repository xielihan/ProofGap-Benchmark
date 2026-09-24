import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

open scoped Interval

namespace ProofGap.Exercise2528

noncomputable section

def decayRate : ℝ := -Real.log 2 / 1600
def charge (Q₀ t : ℝ) : ℝ := Q₀ * Real.rpow 2 (-t / 1600)

private lemma ode_solution (Q : ℝ → ℝ) (k : ℝ)
    (hODE : ∀ t, HasDerivAt Q (k * Q t) t) (t : ℝ) :
    Q t = Q 0 * Real.exp (k * t) := by
  have hzero : ∀ x, HasDerivAt
      (fun y : ℝ => Q y * Real.exp (-k * y)) 0 x := by
    intro x
    have hlin : HasDerivAt (fun y : ℝ => -k * y) (-k) x := by
      simpa using (hasDerivAt_id x).const_mul (-k)
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-k * y))
        (Real.exp (-k * x) * (-k)) x :=
      (Real.hasDerivAt_exp (-k * x)).comp x hlin
    convert (hODE x).mul hexp using 1 <;> ring
  have hdiff : Differentiable ℝ
      (fun y : ℝ => Q y * Real.exp (-k * y)) :=
    fun x => (hzero x).differentiableAt
  have hderiv : ∀ x, deriv
      (fun y : ℝ => Q y * Real.exp (-k * y)) x = 0 :=
    fun x => (hzero x).deriv
  have hc := is_const_of_deriv_eq_zero hdiff hderiv 0 t
  have hc' : Q 0 = Q t * Real.exp (-k * t) := by
    simpa using hc
  have hexpmul : Real.exp (-k * t) * Real.exp (k * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    Q t = (Q t * Real.exp (-k * t)) * Real.exp (k * t) := by
      rw [mul_assoc, hexpmul, mul_one]
    _ = Q 0 * Real.exp (k * t) := by rw [← hc']

theorem gap1 (Q : ℝ → ℝ) (k t : ℝ) (hQ : Q t ≠ 0)
    (hODE : HasDerivAt Q (k * Q t) t) :
    HasDerivAt Q (k * Q t) t := by
  exact hODE

theorem gap2 (Q : ℝ → ℝ) (Q₀ k : ℝ) (hQ₀ : 0 < Q₀)
    (hQ0 : Q 0 = Q₀) (hQ1600 : Q 1600 = Q₀ / 2)
    (hODE : ∀ t, HasDerivAt Q (k * Q t) t) :
    Real.log (Q 1600 / Q₀) = k * 1600 := by
  have hs := ode_solution Q k hODE 1600
  have hQ₀ne : Q₀ ≠ 0 := ne_of_gt hQ₀
  have hratio : Q 1600 / Q₀ = Real.exp (k * 1600) := by
    rw [hs, hQ0]
    field_simp
  rw [hratio, Real.log_exp]

theorem gap3 (Q : ℝ → ℝ) (Q₀ k : ℝ) (hQ₀ : 0 < Q₀)
    (hQ0 : Q 0 = Q₀) (hQ1600 : Q 1600 = Q₀ / 2)
    (hODE : ∀ t, HasDerivAt Q (k * Q t) t) :
    k = decayRate := by
  have h := gap2 Q Q₀ k hQ₀ hQ0 hQ1600 hODE
  have hQ₀ne : Q₀ ≠ 0 := ne_of_gt hQ₀
  have hratio : Q₀ / 2 / Q₀ = (1 : ℝ) / 2 := by
    field_simp
  rw [hQ1600, hratio] at h
  have hlog : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hlog] at h
  unfold decayRate
  linarith

theorem gap4 (Q : ℝ → ℝ) (Q₀ t : ℝ) (hQ₀ : 0 < Q₀)
    (hQ0 : Q 0 = Q₀)
    (hODE : ∀ u, HasDerivAt Q (decayRate * Q u) u) :
    Real.log (Q t / Q₀) = decayRate * t := by
  have hs := ode_solution Q decayRate hODE t
  have hQ₀ne : Q₀ ≠ 0 := ne_of_gt hQ₀
  have hratio : Q t / Q₀ = Real.exp (decayRate * t) := by
    rw [hs, hQ0]
    field_simp
  rw [hratio, Real.log_exp]

theorem gap5 (Q : ℝ → ℝ) (Q₀ t : ℝ) (hQ₀ : 0 < Q₀)
    (hQt : 0 < Q t)
    (hlog : Real.log (Q t / Q₀) = decayRate * t) :
    Real.log (Q t / Q₀) =
      Real.log (Real.rpow 2 (-t / 1600)) := by
  calc
    Real.log (Q t / Q₀) = decayRate * t := hlog
    _ = (-t / 1600) * Real.log 2 := by
      unfold decayRate
      ring
    _ = Real.log ((2 : ℝ) ^ (-t / 1600 : ℝ)) := by
      rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    _ = Real.log (Real.rpow 2 (-t / 1600)) := by rfl

theorem gap6 (Q : ℝ → ℝ) (Q₀ t : ℝ) (hQ₀ : 0 < Q₀)
    (hQt : 0 < Q t)
    (hlog : Real.log (Q t / Q₀) =
      Real.log (Real.rpow 2 (-t / 1600))) :
    Q t = charge Q₀ t := by
  have ha : 0 < Q t / Q₀ := div_pos hQt hQ₀
  have hb : 0 < Real.rpow 2 (-t / 1600) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hquot : Q t / Q₀ = Real.rpow 2 (-t / 1600) := by
    have h := congrArg Real.exp hlog
    rw [Real.exp_log ha, Real.exp_log hb] at h
    exact h
  simpa [charge, mul_comm] using
    (div_eq_iff (ne_of_gt hQ₀)).mp hquot

end

end ProofGap.Exercise2528
