import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1715

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def integrand (n x : ℝ) :=
  Real.rpow x (n / 2) / Real.sqrt (1 + Real.rpow x (n + 2))
def specialIntegrand (x : ℝ) := 1 / (x * Real.sqrt 2)
def substitution (n x : ℝ) := Real.rpow x ((n + 2) / 2)
def substitutedIntegrand (n x : ℝ) :=
  2 / (n + 2) *
    (deriv (substitution n) x / Real.sqrt (1 + (substitution n x) ^ 2))
def specialPrimitive (x : ℝ) := 1 / Real.sqrt 2 * Real.log |x|
def generalPrimitive (n x : ℝ) :=
  2 / (n + 2) *
    Real.log (substitution n x + Real.sqrt (1 + Real.rpow x (n + 2)))
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem antiderivatives_eq_primitive
    (f p : ℝ → ℝ)
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    AntiderivativesOn f = PrimitiveFamily p := by
  ext F
  constructor
  · intro hF
    have hzero :
        ∀ x ∈ branch, HasDerivAt (fun y => F y - p y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hp x hx)
    have hdiff :
        DifferentiableOn ℝ (fun y => F y - p y) branch := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv :
        ∀ x ∈ branch, deriv (fun y => F y - p y) x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    refine ⟨F 1 - p 1, ?_⟩
    intro x hx
    have hxp : x ∈ Set.Ioi (0 : ℝ) := by simpa [branch] using hx
    have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
    have hc :
        (fun y => F y - p y) x = (fun y => F y - p y) 1 :=
      isOpen_Ioi.is_const_of_deriv_eq_zero
        (convex_Ioi (0 : ℝ)).isPreconnected
        (by simpa [branch] using hdiff)
        (by simpa [branch] using hderiv)
        hxp h1
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hxpos : 0 < x := by simpa [branch] using hx
    have hlocal : F =ᶠ[nhds x] (fun y => p y + C) := by
      filter_upwards [Ioi_mem_nhds hxpos] with y hy
      exact hC y (by simpa [branch] using hy)
    exact (hlocal.hasDerivAt_iff).2 ((hp x hx).add_const C)

private theorem substitution_derivative_and_square
    (n x : ℝ) (hn : n ≠ -2) (hxpos : 0 < x) :
    2 / (n + 2) * deriv (substitution n) x = Real.rpow x (n / 2) ∧
      (substitution n x) ^ 2 = Real.rpow x (n + 2) := by
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hn2 : n + 2 ≠ 0 := by
    intro h
    apply hn
    linarith
  let a : ℝ := (n + 2) / 2
  have hevent :
      substitution n =ᶠ[nhds x]
        (fun y : ℝ => Real.exp (Real.log y * a)) := by
    filter_upwards [Ioi_mem_nhds hxpos] with y hy
    simp [substitution, a, Real.rpow_def_of_pos hy]
  have hu0 :
      HasDerivAt (fun y : ℝ => Real.exp (Real.log y * a))
        (Real.exp (Real.log x * a) * (x⁻¹ * a)) x :=
    (Real.hasDerivAt_exp _).comp x
      ((Real.hasDerivAt_log hx0).mul_const a)
  have hu :
      HasDerivAt (substitution n)
        (Real.exp (Real.log x * a) * (x⁻¹ * a)) x :=
    (hevent.hasDerivAt_iff).2 hu0
  have hderiv :
      deriv (substitution n) x =
        Real.exp (Real.log x * a) * (x⁻¹ * a) := hu.deriv
  have hexp :
      Real.exp (Real.log x * a) =
        Real.exp (Real.log x * (n / 2)) * x := by
    calc
      Real.exp (Real.log x * a) =
          Real.exp (Real.log x * (n / 2) + Real.log x) := by
            congr 1
            dsimp [a]
            ring
      _ = Real.exp (Real.log x * (n / 2)) * Real.exp (Real.log x) := by
            rw [Real.exp_add]
      _ = Real.exp (Real.log x * (n / 2)) * x := by
            rw [Real.exp_log hxpos]
  have hrpowHalf :
      Real.rpow x (n / 2) = Real.exp (Real.log x * (n / 2)) := by
    exact Real.rpow_def_of_pos hxpos (n / 2)
  have hnum :
      2 / (n + 2) * deriv (substitution n) x =
        Real.rpow x (n / 2) := by
    rw [hderiv, hexp]
    calc
      2 / (n + 2) *
          (Real.exp (Real.log x * (n / 2)) * x * (x⁻¹ * a)) =
          Real.exp (Real.log x * (n / 2)) := by
            dsimp [a]
            field_simp [hn2, hx0]
      _ = Real.rpow x (n / 2) := hrpowHalf.symm
  have hsub :
      substitution n x = Real.exp (Real.log x * a) := by
    unfold substitution
    dsimp [a]
    exact Real.rpow_def_of_pos hxpos ((n + 2) / 2)
  have hrpowFull :
      Real.rpow x (n + 2) = Real.exp (Real.log x * (n + 2)) := by
    exact Real.rpow_def_of_pos hxpos (n + 2)
  have hpow :
      (substitution n x) ^ 2 = Real.rpow x (n + 2) := by
    rw [hsub, pow_two, ← Real.exp_add]
    calc
      Real.exp (Real.log x * a + Real.log x * a) =
          Real.exp (Real.log x * (n + 2)) := by
            congr 1
            dsimp [a]
            ring
      _ = Real.rpow x (n + 2) := hrpowFull.symm
  exact ⟨hnum, hpow⟩

theorem gap1 (n : ℝ) (hn : n = -2) :
    AntiderivativesOn (integrand n) =
      AntiderivativesOn specialIntegrand := by
  subst n
  ext F
  constructor
  · intro hF x hx
    have hxpos : 0 < x := by simpa [branch] using hx
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have heq : integrand (-2) x = specialIntegrand x := by
      norm_num [integrand, specialIntegrand, Real.rpow_neg_one, div_eq_mul_inv,
        hx0, mul_comm]
    rw [← heq]
    exact hF x hx
  · intro hF x hx
    have hxpos : 0 < x := by simpa [branch] using hx
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have heq : integrand (-2) x = specialIntegrand x := by
      norm_num [integrand, specialIntegrand, Real.rpow_neg_one, div_eq_mul_inv,
        hx0, mul_comm]
    rw [heq]
    exact hF x hx
theorem gap2 (n : ℝ) (hn : n = -2) :
    AntiderivativesOn specialIntegrand =
      PrimitiveFamily specialPrimitive := by
  apply antiderivatives_eq_primitive
  intro x hx
  have hxpos : 0 < x := by simpa [branch] using hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hbase := (Real.hasDerivAt_log hx0).const_mul (1 / Real.sqrt 2)
  have hevent :
      specialPrimitive =ᶠ[nhds x]
        (fun y : ℝ => 1 / Real.sqrt 2 * Real.log y) := by
    filter_upwards [Ioi_mem_nhds hxpos] with y hy
    have hypos : 0 < y := by exact hy
    simp [specialPrimitive, abs_of_pos hypos]
  have hsp :
      HasDerivAt specialPrimitive
        (1 / Real.sqrt 2 * x⁻¹) x :=
    (hevent.hasDerivAt_iff).2 hbase
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have heq : specialIntegrand x = 1 / Real.sqrt 2 * x⁻¹ := by
    change 1 / (x * Real.sqrt 2) = 1 / Real.sqrt 2 * x⁻¹
    field_simp [hsqrt, hx0]
    <;> ring
  rw [heq]
  exact hsp
theorem gap3 (n : ℝ) (hn : n = -2) :
    AntiderivativesOn (integrand n) =
      PrimitiveFamily specialPrimitive := by
  exact (gap1 n hn).trans (gap2 n hn)
theorem gap4 (n : ℝ) (hn : n ≠ -2) :
    AntiderivativesOn (integrand n) =
      AntiderivativesOn (substitutedIntegrand n) := by
  have heq : ∀ x ∈ branch, substitutedIntegrand n x = integrand n x := by
    intro x hx
    have hxpos : 0 < x := by simpa [branch] using hx
    have hfacts := substitution_derivative_and_square n x hn hxpos
    unfold substitutedIntegrand integrand
    rw [hfacts.2]
    calc
      2 / (n + 2) *
          (deriv (substitution n) x /
            Real.sqrt (1 + Real.rpow x (n + 2))) =
          (2 / (n + 2) * deriv (substitution n) x) /
            Real.sqrt (1 + Real.rpow x (n + 2)) := by ring
      _ = Real.rpow x (n / 2) /
            Real.sqrt (1 + Real.rpow x (n + 2)) := by rw [hfacts.1]
  ext F
  constructor
  · intro hF x hx
    rw [heq x hx]
    exact hF x hx
  · intro hF x hx
    rw [← heq x hx]
    exact hF x hx
theorem gap5 (n : ℝ) (hn : n ≠ -2) :
    AntiderivativesOn (substitutedIntegrand n) =
      PrimitiveFamily (generalPrimitive n) := by
  apply antiderivatives_eq_primitive
  intro x hx
  have hxpos : 0 < x := by simpa [branch] using hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  let a : ℝ := (n + 2) / 2
  let d : ℝ := deriv (substitution n) x
  let u : ℝ := substitution n x
  let s : ℝ := Real.sqrt (1 + u ^ 2)
  have heventSub :
      substitution n =ᶠ[nhds x]
        (fun y : ℝ => Real.exp (Real.log y * a)) := by
    filter_upwards [Ioi_mem_nhds hxpos] with y hy
    simp [substitution, a, Real.rpow_def_of_pos hy]
  have hu0 :
      HasDerivAt (fun y : ℝ => Real.exp (Real.log y * a))
        (Real.exp (Real.log x * a) * (x⁻¹ * a)) x :=
    (Real.hasDerivAt_exp _).comp x
      ((Real.hasDerivAt_log hx0).mul_const a)
  have hudiff : DifferentiableAt ℝ (substitution n) x :=
    ((heventSub.hasDerivAt_iff).2 hu0).differentiableAt
  have hu : HasDerivAt (substitution n) d x := by
    simpa [d] using hudiff.hasDerivAt
  have hv :
      HasDerivAt (fun y : ℝ => 1 + (substitution n y) ^ 2)
        (2 * u * d) x := by
    simpa [u, pow_two, mul_assoc] using (hu.pow 2).const_add 1
  have hvpos : 0 < 1 + u ^ 2 := by positivity
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 hvpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hsquare : s ^ 2 = 1 + u ^ 2 := by
    dsimp [s]
    exact Real.sq_sqrt (le_of_lt hvpos)
  have hsderiv :
      HasDerivAt
        (fun y : ℝ => Real.sqrt (1 + (substitution n y) ^ 2))
        (1 / (2 * s) * (2 * u * d)) x := by
    simpa [s] using
      (Real.hasDerivAt_sqrt (ne_of_gt hvpos)).comp x hv
  have hsum :
      HasDerivAt
        (fun y : ℝ =>
          substitution n y + Real.sqrt (1 + (substitution n y) ^ 2))
        (d + 1 / (2 * s) * (2 * u * d)) x := by
    simpa [u, s] using hu.add hsderiv
  have hsumpos : 0 < u + s := by
    have huPos : 0 < u := by
      dsimp [u, substitution]
      exact Real.rpow_pos_of_pos hxpos _
    positivity
  have hraw :=
    (Real.hasDerivAt_log (ne_of_gt hsumpos)).comp x hsum
  have hlog :
      HasDerivAt
        (fun y : ℝ =>
          Real.log
            (substitution n y +
              Real.sqrt (1 + (substitution n y) ^ 2)))
        (d / s) x := by
    convert hraw using 1
    field_simp [hsne, ne_of_gt hsumpos]
    nlinarith [hsquare]
  have hscaled :
      HasDerivAt
        (fun y : ℝ =>
          2 / (n + 2) *
            Real.log
              (substitution n y +
                Real.sqrt (1 + (substitution n y) ^ 2)))
        (2 / (n + 2) * (d / s)) x :=
    hlog.const_mul (2 / (n + 2))
  have heventGeneral :
      generalPrimitive n =ᶠ[nhds x]
        (fun y : ℝ =>
          2 / (n + 2) *
            Real.log
              (substitution n y +
                Real.sqrt (1 + (substitution n y) ^ 2))) := by
    filter_upwards [Ioi_mem_nhds hxpos] with y hy
    have hypos : 0 < y := by exact hy
    have hpow :
        (substitution n y) ^ 2 = Real.rpow y (n + 2) :=
      (substitution_derivative_and_square n y hn hypos).2
    simp only [generalPrimitive]
    rw [hpow]
  have hgeneral :
      HasDerivAt (generalPrimitive n) (2 / (n + 2) * (d / s)) x :=
    (heventGeneral.hasDerivAt_iff).2 hscaled
  simpa [substitutedIntegrand, d, u, s, div_eq_mul_inv, mul_assoc] using hgeneral
theorem gap6 (n : ℝ) (hn : n ≠ -2) :
    AntiderivativesOn (integrand n) =
      PrimitiveFamily (generalPrimitive n) := by
  exact (gap4 n hn).trans (gap5 n hn)

end
end ProofGap.Exercise1715
