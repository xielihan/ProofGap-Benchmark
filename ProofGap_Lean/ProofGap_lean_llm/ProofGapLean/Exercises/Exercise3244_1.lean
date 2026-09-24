import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3244_1

noncomputable section

def f (m n x y : ℝ) : ℝ :=
  Real.rpow (1 + x) m * Real.rpow (1 + y) n

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => g t y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => g x t) y

def linearTaylorFromPartials (m n x y : ℝ) : ℝ :=
  f m n 0 0 +
    partialX (f m n) 0 0 * x +
    partialY (f m n) 0 0 * y

def linearTaylor (m n x y : ℝ) : ℝ :=
  1 + m * x + n * y

def AgreesToFirstOrder (g p : ℝ × ℝ → ℝ) : Prop :=
  Asymptotics.IsLittleO (nhds (0, 0))
    (fun q => g q - p q)
    (fun q => ‖q‖)

theorem gap1 (m n x : ℝ) (hx : |x| < 1) :
    partialX (f m n) x 0 =
      m * Real.rpow (1 + x) (m - 1) := by
  have hxpos : 0 < 1 + x := by
    have h := (abs_lt.mp hx).1
    linarith
  have hpow :
      HasDerivAt (fun t : ℝ => Real.rpow (1 + t) m)
        (m * Real.rpow (1 + x) (m - 1)) x := by
    simpa using
      (Real.hasDerivAt_rpow_const (p := m)
        (Or.inl (ne_of_gt hxpos))).comp x
          ((hasDerivAt_id x).const_add (1 : ℝ))
  simpa [partialX, f] using hpow.deriv

theorem gap2 (m n : ℝ) :
    partialX (f m n) 0 0 = m := by
  have hzero : |(0 : ℝ)| < 1 := by simp
  simpa using gap1 m n 0 hzero

theorem gap3 (m n y : ℝ) (hy : |y| < 1) :
    partialY (f m n) 0 y =
      n * Real.rpow (1 + y) (n - 1) := by
  have hypos : 0 < 1 + y := by
    have h := (abs_lt.mp hy).1
    linarith
  have hpow :
      HasDerivAt (fun t : ℝ => Real.rpow (1 + t) n)
        (n * Real.rpow (1 + y) (n - 1)) y := by
    simpa using
      (Real.hasDerivAt_rpow_const (p := n)
        (Or.inl (ne_of_gt hypos))).comp y
          ((hasDerivAt_id y).const_add (1 : ℝ))
  simpa [partialY, f] using hpow.deriv

theorem gap4 (m n : ℝ) :
    partialY (f m n) 0 0 = n := by
  have hzero : |(0 : ℝ)| < 1 := by simp
  simpa using gap3 m n 0 hzero

theorem gap5 (m n : ℝ) :
    AgreesToFirstOrder
      (fun q => f m n q.1 q.2)
      (fun q => linearTaylorFromPartials m n q.1 q.2) := by
  let z : ℝ × ℝ := (0, 0)
  have hx1 : 1 + z.1 ≠ 0 := by simp [z]
  have hy1 : 1 + z.2 ≠ 0 := by simp [z]
  have hfst :
      HasFDerivAt (fun q : ℝ × ℝ => q.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) z := by
    simpa using (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hsnd :
      HasFDerivAt (fun q : ℝ × ℝ => q.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) z := by
    simpa using (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have hxi :
      HasFDerivAt (fun q : ℝ × ℝ => 1 + q.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) z := by
    simpa using (hfst.const_add (1 : ℝ))
  have hyi :
      HasFDerivAt (fun q : ℝ × ℝ => 1 + q.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) z := by
    simpa using (hsnd.const_add (1 : ℝ))
  have hxm :=
    ((Real.hasDerivAt_rpow_const (p := m)
      (Or.inl hx1)).hasFDerivAt).comp z hxi
  have hyn :=
    ((Real.hasDerivAt_rpow_const (p := n)
      (Or.inl hy1)).hasFDerivAt).comp z hyi
  have hprod := hxm.mul hyn
  have hlin (q : ℝ × ℝ) :
      linearTaylorFromPartials m n q.1 q.2 =
        1 + m * q.1 + n * q.2 := by
    unfold linearTaylorFromPartials
    rw [gap2 m n, gap4 m n]
    simp [f]
  have hrem :
      Asymptotics.IsLittleO (nhds (0, 0))
        (fun q =>
          f m n q.1 q.2 -
            linearTaylorFromPartials m n q.1 q.2)
        (fun q : ℝ × ℝ => q + (0, 0)) := by
    simpa [z, hlin, f, Function.comp_def,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hprod.isLittleO
  unfold AgreesToFirstOrder
  have hz : ((0, 0) : ℝ × ℝ) = 0 := rfl
  simpa only [hz, add_zero] using hrem.norm_right

theorem gap6 (m n x y : ℝ) :
    linearTaylorFromPartials m n x y = linearTaylor m n x y := by
  unfold linearTaylorFromPartials linearTaylor
  rw [gap2 m n, gap4 m n]
  simp [f]

theorem gap7 (m n : ℝ) :
    AgreesToFirstOrder
      (fun q => f m n q.1 q.2)
      (fun q => linearTaylor m n q.1 q.2) := by
  simpa only [gap6] using gap5 m n

theorem gap8 (m n : ℝ) :
    AgreesToFirstOrder
      (fun q =>
        Real.rpow (1 + q.1) m * Real.rpow (1 + q.2) n)
      (fun q => 1 + m * q.1 + n * q.2) := by
  simpa only [f, linearTaylor] using gap7 m n

end

end ProofGap.Exercise3244_1
