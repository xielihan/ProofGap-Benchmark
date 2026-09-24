import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1390

noncomputable section

open Filter

def y (a x : ℝ) : ℝ := a * Real.cosh (x / a)
def polynomial (a x : ℝ) : ℝ := a + x ^ 2 / (2 * a)
def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) g

def AgreesToOrderAt (g p : ℝ → ℝ) (a : ℝ) (n : ℕ) : Prop :=
  Asymptotics.IsLittleO (nhds a) (fun x => g x - p x)
    (fun x => (x - a) ^ n)

theorem gap1 (a : ℝ) (ha : 0 < a) :
    y a 0 = a := by
  simp [y]

theorem gap2 (a x : ℝ) (ha : 0 < a) :
    iterDeriv 1 (y a) x = Real.sinh (x / a) := by
  change deriv (fun z : ℝ => a * Real.cosh (z / a)) x = Real.sinh (x / a)
  have hinner : HasDerivAt (fun z : ℝ => z / a) (1 / a) x :=
    (hasDerivAt_id x).div_const a
  have h :=
    ((Real.hasDerivAt_cosh (x / a)).comp x hinner).const_mul a
  have h' :
      HasDerivAt (fun z : ℝ => a * Real.cosh (z / a))
        (a * (Real.sinh (x / a) * (1 / a))) x := by
    simpa only [Function.comp_apply] using h
  rw [h'.deriv]
  field_simp [ha.ne']
  <;> ring

theorem gap3 (a : ℝ) :
    Real.sinh (0 / a) = 0 := by
  simp

theorem gap4 (a : ℝ) (ha : 0 < a) :
    iterDeriv 1 (y a) 0 = 0 := by
  simpa using gap2 a 0 ha

theorem gap5 (a x : ℝ) (ha : 0 < a) :
    iterDeriv 2 (y a) x = (1 / a) * Real.cosh (x / a) := by
  change deriv (deriv (y a)) x = (1 / a) * Real.cosh (x / a)
  have hfun : deriv (y a) = fun z : ℝ => Real.sinh (z / a) := by
    funext z
    exact gap2 a z ha
  rw [hfun]
  have hinner : HasDerivAt (fun z : ℝ => z / a) (1 / a) x :=
    (hasDerivAt_id x).div_const a
  have h := (Real.hasDerivAt_sinh (x / a)).comp x hinner
  have h' :
      HasDerivAt (fun z : ℝ => Real.sinh (z / a))
        (Real.cosh (x / a) * (1 / a)) x := by
    simpa only [Function.comp_apply] using h
  rw [h'.deriv]
  ring

theorem gap6 (a : ℝ) (ha : 0 < a) :
    (1 / a) * Real.cosh (0 / a) = 1 / a := by
  simp

theorem gap7 (a : ℝ) (ha : 0 < a) :
    iterDeriv 2 (y a) 0 = 1 / a := by
  calc
    iterDeriv 2 (y a) 0 = (1 / a) * Real.cosh (0 / a) := gap5 a 0 ha
    _ = 1 / a := gap6 a ha

theorem gap8 (a : ℝ) (ha : 0 < a) :
    AgreesToOrderAt (y a) (polynomial a) 0 2 := by
  have hd :
      HasDerivAt (fun x : ℝ => Real.sinh (x / (2 * a))) (1 / (2 * a)) 0 := by
    have hinner :
        HasDerivAt (fun x : ℝ => x / (2 * a)) (1 / (2 * a)) 0 :=
      (hasDerivAt_id 0).div_const (2 * a)
    have h := (Real.hasDerivAt_sinh (0 / (2 * a))).comp 0 hinner
    simpa [mul_comm] using h
  have hu :
      (fun x : ℝ => Real.sinh (x / (2 * a)) - x / (2 * a))
        =o[nhds 0] (fun x : ℝ => x) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hd.isLittleO
  have hx :
      (fun x : ℝ => x / (2 * a)) =O[nhds 0] (fun x : ℝ => x) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Asymptotics.isBigO_refl (fun x : ℝ => x) (nhds 0)).const_mul_left
        (1 / (2 * a))
  have htwo :
      (fun x : ℝ => 2 * (x / (2 * a))) =O[nhds 0] (fun x : ℝ => x) :=
    hx.const_mul_left 2
  have hp := hu.mul_isBigO (hu.isBigO.add htwo)
  have hp' :
      (fun x : ℝ =>
        2 * a *
          ((Real.sinh (x / (2 * a)) - x / (2 * a)) *
            ((Real.sinh (x / (2 * a)) - x / (2 * a)) +
              2 * (x / (2 * a)))))
        =o[nhds 0] (fun x : ℝ => x ^ 2) := by
    simpa [pow_two] using hp.const_mul_left (2 * a)
  have hcosh (z : ℝ) :
      Real.cosh z - 1 = 2 * Real.sinh (z / 2) ^ 2 := by
    calc
      Real.cosh z - 1 = Real.cosh (z / 2 + z / 2) - 1 := by
        rw [show z / 2 + z / 2 = z by ring]
      _ = Real.cosh (z / 2) * Real.cosh (z / 2) +
            Real.sinh (z / 2) * Real.sinh (z / 2) - 1 := by
        rw [Real.cosh_add]
      _ = 2 * Real.sinh (z / 2) ^ 2 := by
        nlinarith [Real.cosh_sq_sub_sinh_sq (z / 2)]
  have hremfun :
      (fun x : ℝ => y a x - polynomial a x) =
        (fun x : ℝ =>
          2 * a *
            ((Real.sinh (x / (2 * a)) - x / (2 * a)) *
              ((Real.sinh (x / (2 * a)) - x / (2 * a)) +
                2 * (x / (2 * a))))) := by
    funext x
    dsimp [y, polynomial]
    have hc :
        Real.cosh (x / a) =
          1 + 2 * Real.sinh ((x / a) / 2) ^ 2 := by
      calc
        Real.cosh (x / a) = (Real.cosh (x / a) - 1) + 1 := by ring
        _ = 1 + 2 * Real.sinh ((x / a) / 2) ^ 2 := by
          rw [hcosh]
          ring
    rw [hc]
    have hq : (x / a) / 2 = x / (2 * a) := by
      field_simp [ha.ne'] <;> ring
    rw [hq]
    field_simp [ha.ne'] <;> ring
  unfold AgreesToOrderAt
  rw [hremfun]
  simpa [pow_two] using hp'

end

end ProofGap.Exercise1390
