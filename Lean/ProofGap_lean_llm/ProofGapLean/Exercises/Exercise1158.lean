import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Finite
import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1158

open scoped BigOperators

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (x : ℝ) : ℝ := Real.sqrt x
def oddDF17 : ℕ := ∏ k ∈ Finset.range 9, (2 * k + 1)
def rawCoeff : ℝ :=
  (1 / 2 : ℝ) * (-1 / 2) * (-3 / 2) * (-5 / 2) * (-7 / 2) *
    (-9 / 2) * (-11 / 2) * (-13 / 2) * (-15 / 2) * (-17 / 2)

private def sqrtCoeff : ℕ → ℝ
  | 0 => 1
  | n + 1 => sqrtCoeff n * ((1 / 2 : ℝ) - n)

private theorem deriv_congr_on_pos {f g : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (h : ∀ z, 0 < z → f z = g z) :
    deriv f x = deriv g x := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hx] with z hz
  exact h z hz

private theorem nthDeriv_sqrt_formula (n : ℕ) (x : ℝ) (hx : 0 < x) :
    nthDeriv n y x =
      sqrtCoeff n * Real.rpow x ((1 / 2 : ℝ) - n) := by
  induction n generalizing x with
  | zero =>
      simp [nthDeriv, y, sqrtCoeff, Real.sqrt_eq_rpow]
  | succ n ih =>
      let a : ℝ := (1 / 2 : ℝ) - n
      simp only [nthDeriv]
      calc
        deriv (nthDeriv n y) x =
            deriv (fun z => sqrtCoeff n * Real.rpow z a) x := by
              apply deriv_congr_on_pos hx
              intro z hz
              simpa [a] using ih z hz
        _ = deriv (fun z =>
              sqrtCoeff n * Real.exp (Real.log z * a)) x := by
              apply deriv_congr_on_pos hx
              intro z hz
              have hr :
                  Real.rpow z a = Real.exp (Real.log z * a) := by
                simpa only using (Real.rpow_def_of_pos hz a)
              rw [hr]
        _ = sqrtCoeff n *
              (Real.exp (Real.log x * a) * (x⁻¹ * a)) := by
              have hlog := (Real.hasDerivAt_log hx.ne').mul_const a
              have hexp :=
                (Real.hasDerivAt_exp (Real.log x * a)).comp x hlog
              exact (hexp.const_mul (sqrtCoeff n)).deriv
        _ = sqrtCoeff (n + 1) *
              Real.rpow x ((1 / 2 : ℝ) - ((n + 1 : ℕ) : ℝ)) := by
              have hr :
                  Real.rpow x
                      ((1 / 2 : ℝ) - ((n + 1 : ℕ) : ℝ)) =
                    Real.exp
                      (Real.log x *
                        ((1 / 2 : ℝ) - ((n + 1 : ℕ) : ℝ))) := by
                simpa only using
                  (Real.rpow_def_of_pos hx
                    ((1 / 2 : ℝ) - ((n + 1 : ℕ) : ℝ)))
              rw [hr]
              simp only [sqrtCoeff]
              have hexponent :
                  Real.log x * ((1 / 2 : ℝ) - ((n + 1 : ℕ) : ℝ)) =
                    Real.log x * a - Real.log x := by
                simp [a]
                ring
              rw [hexponent, Real.exp_sub, Real.exp_log hx]
              field_simp [hx.ne']
              <;> ring

private theorem rpow_nineteen_halves (x : ℝ) (hx : 0 < x) :
    Real.rpow x (19 / 2 : ℝ) = x ^ 9 * Real.sqrt x := by
  have hxpow : x ^ 9 = Real.exp (Real.log x * 9) := by
    calc
      x ^ 9 = (Real.exp (Real.log x)) ^ 9 := by
        rw [Real.exp_log hx]
      _ = Real.exp (Real.log x * 9) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hr19 :
      Real.rpow x (19 / 2 : ℝ) =
        Real.exp (Real.log x * (19 / 2 : ℝ)) := by
    simpa only using (Real.rpow_def_of_pos hx (19 / 2 : ℝ))
  have hrhalf :
      Real.rpow x (1 / 2 : ℝ) =
        Real.exp (Real.log x * (1 / 2 : ℝ)) := by
    simpa only using (Real.rpow_def_of_pos hx (1 / 2 : ℝ))
  have hsqrt : Real.rpow x (1 / 2 : ℝ) = Real.sqrt x := by
    symm
    simpa only using (Real.sqrt_eq_rpow x)
  calc
    Real.rpow x (19 / 2 : ℝ) =
        Real.exp (Real.log x * (19 / 2 : ℝ)) := hr19
    _ = Real.exp (Real.log x * 9) *
        Real.exp (Real.log x * (1 / 2 : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = x ^ 9 * Real.exp (Real.log x * (1 / 2 : ℝ)) := by
      rw [hxpow]
    _ = x ^ 9 * Real.rpow x (1 / 2 : ℝ) := by
      rw [hrhalf]
    _ = x ^ 9 * Real.sqrt x := by
      rw [hsqrt]

private theorem oddDF17_value : oddDF17 = 34459425 := by
  norm_num [oddDF17, Finset.prod_range_succ]

theorem gap1 (x : ℝ) (hx : 0 < x) :
    nthDeriv 10 y x = rawCoeff / Real.rpow x (19 / 2 : ℝ) := by
  rw [nthDeriv_sqrt_formula 10 x hx]
  have hc : sqrtCoeff 10 = rawCoeff := by
    norm_num [sqrtCoeff, rawCoeff]
  have hp :
      Real.rpow x ((1 / 2 : ℝ) - (10 : ℕ)) =
        1 / Real.rpow x (19 / 2 : ℝ) := by
    have hneg :
        (1 / 2 : ℝ) - (10 : ℕ) = -(19 / 2 : ℝ) := by
      norm_num
    have hrneg :
        Real.rpow x (-(19 / 2 : ℝ)) =
          Real.exp (Real.log x * (-(19 / 2 : ℝ))) := by
      simpa only using
        (Real.rpow_def_of_pos hx (-(19 / 2 : ℝ)))
    have hrpos :
        Real.rpow x (19 / 2 : ℝ) =
          Real.exp (Real.log x * (19 / 2 : ℝ)) := by
      simpa only using
        (Real.rpow_def_of_pos hx (19 / 2 : ℝ))
    calc
      Real.rpow x ((1 / 2 : ℝ) - (10 : ℕ)) =
          Real.rpow x (-(19 / 2 : ℝ)) := by rw [hneg]
      _ = Real.exp (Real.log x * (-(19 / 2 : ℝ))) := hrneg
      _ = (Real.exp (Real.log x * (19 / 2 : ℝ)))⁻¹ := by
        rw [show Real.log x * (-(19 / 2 : ℝ)) =
            -(Real.log x * (19 / 2 : ℝ)) by ring]
        rw [Real.exp_neg]
      _ = (Real.rpow x (19 / 2 : ℝ))⁻¹ := by rw [hrpos]
      _ = 1 / Real.rpow x (19 / 2 : ℝ) := by
        simp [div_eq_mul_inv]
  rw [hc, hp]
  simp [div_eq_mul_inv]

theorem gap2 (x : ℝ) (hx : 0 < x) :
    nthDeriv 10 y x =
      -(oddDF17 : ℝ) / (2 ^ 10 * x ^ 9 * Real.sqrt x) := by
  rw [gap1 x hx, rpow_nineteen_halves x hx, oddDF17_value]
  have hsqrt : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hden : x ^ 9 * Real.sqrt x ≠ 0 :=
    mul_ne_zero (pow_ne_zero 9 hx.ne') hsqrt
  norm_num [rawCoeff]
  field_simp [hden, hx.ne', hsqrt]
  <;> ring

theorem gap3 :
    oddDF17 = 1 * 3 * 5 * 7 * 9 * 11 * 13 * 15 * 17 := by
  norm_num [oddDF17, Finset.prod_range_succ]

end

end ProofGap.Exercise1158
