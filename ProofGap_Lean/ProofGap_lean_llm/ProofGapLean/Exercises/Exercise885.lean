import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise885

noncomputable section

def y (a x : ℝ) : ℝ :=
  Real.rpow x (Real.rpow a a) +
    Real.rpow a (Real.rpow x a) +
      Real.rpow a (Real.rpow a x)

theorem gap1 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    deriv (y a) x =
      Real.rpow a a * Real.rpow x (Real.rpow a a - 1) +
      a * Real.rpow x (a - 1) * Real.rpow a (Real.rpow x a) *
        Real.log a +
      Real.rpow a x * Real.rpow a (Real.rpow a x) *
        Real.log a ^ 2 := by
  unfold y
  have h₁ :
      HasDerivAt
        (fun t : ℝ => Real.rpow t (Real.rpow a a))
        (Real.rpow a a * Real.rpow x (Real.rpow a a - 1)) x := by
    exact Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have hxa :
      HasDerivAt
        (fun t : ℝ => Real.rpow t a)
        (a * Real.rpow x (a - 1)) x := by
    exact Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have hconst (u : ℝ) :
      HasDerivAt
        (fun t : ℝ => Real.rpow a t)
        (Real.rpow a u * Real.log a) u := by
    have hlin :
        HasDerivAt (fun t : ℝ => Real.log a * t) (Real.log a) u := by
      simpa using (hasDerivAt_id u).const_mul (Real.log a)
    simpa [Real.rpow_def_of_pos ha] using
      (Real.hasDerivAt_exp (Real.log a * u)).comp u hlin
  have h₂ := (hconst (Real.rpow x a)).comp x hxa
  have hax := hconst x
  have h₃ := (hconst (Real.rpow a x)).comp x hax
  have hy :
      HasDerivAt
        (fun t : ℝ =>
          Real.rpow t (Real.rpow a a) +
            Real.rpow a (Real.rpow t a) +
              Real.rpow a (Real.rpow a t))
        (Real.rpow a a * Real.rpow x (Real.rpow a a - 1) +
          a * Real.rpow x (a - 1) * Real.rpow a (Real.rpow x a) *
            Real.log a +
          Real.rpow a x * Real.rpow a (Real.rpow a x) *
            Real.log a ^ 2) x := by
    convert (h₁.add h₂).add h₃ using 1 <;> ring
  exact hy.deriv

end

end ProofGap.Exercise885
