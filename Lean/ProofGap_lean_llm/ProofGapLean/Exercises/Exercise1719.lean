import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1719

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def powBase (a x : ℝ) := Real.rpow a x
def ratioPower (x : ℝ) := powBase (3 / 2) x
def integrand (x : ℝ) :=
  powBase 2 x * powBase 3 x / (powBase 9 x - powBase 4 x)
def rewrittenIntegrand (x : ℝ) :=
  ratioPower x / ((ratioPower x) ^ 2 - 1)
def substitutedIntegrand (x : ℝ) :=
  1 / (Real.log 3 - Real.log 2) *
    (deriv ratioPower x / ((ratioPower x) ^ 2 - 1))
def primitive (x : ℝ) :=
  1 / (2 * (Real.log 3 - Real.log 2)) *
    Real.log
      |(powBase 3 x - powBase 2 x) /
        (powBase 3 x + powBase 2 x)|
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private lemma ratioPower_eq_div (x : ℝ) :
    ratioPower x = powBase 3 x / powBase 2 x := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  simp only [ratioPower, powBase]
  exact Real.div_rpow h3 h2 x

private lemma powBase_nine (x : ℝ) :
    powBase 9 x = (powBase 3 x) ^ 2 := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  simp only [powBase]
  calc
    Real.rpow 9 x = Real.rpow (3 * 3) x := by norm_num
    _ = Real.rpow 3 x * Real.rpow 3 x := by
      exact Real.mul_rpow h3 h3
    _ = (Real.rpow 3 x) ^ 2 := by ring

private lemma powBase_four (x : ℝ) :
    powBase 4 x = (powBase 2 x) ^ 2 := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  simp only [powBase]
  calc
    Real.rpow 4 x = Real.rpow (2 * 2) x := by norm_num
    _ = Real.rpow 2 x * Real.rpow 2 x := by
      exact Real.mul_rpow h2 h2
    _ = (Real.rpow 2 x) ^ 2 := by ring

private lemma integrand_eq_rewritten (x : ℝ) :
    integrand x = rewrittenIntegrand x := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hp2 : powBase 2 x ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos h2 x)
  have hp3 : powBase 3 x ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos h3 x)
  simp only [integrand, rewrittenIntegrand]
  rw [ratioPower_eq_div, powBase_nine, powBase_four]
  field_simp [hp2, hp3]

private lemma log_sub_ne_zero : Real.log 3 - Real.log 2 ≠ 0 := by
  have hlt : Real.log 2 < Real.log 3 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  linarith

private lemma ratioPower_hasDerivAt (x : ℝ) :
    HasDerivAt ratioPower
      ((Real.log 3 - Real.log 2) * ratioPower x) x := by
  have hbase : (0 : ℝ) < 3 / 2 := by norm_num
  have hinner :
      HasDerivAt (fun y : ℝ => Real.log (3 / 2) * y)
        (Real.log (3 / 2)) x := by
    simpa only [mul_one] using
      (hasDerivAt_id x).const_mul (Real.log (3 / 2))
  have hd :
      HasDerivAt
        (fun y : ℝ => Real.exp (Real.log (3 / 2) * y))
        (Real.log (3 / 2) *
          Real.exp (Real.log (3 / 2) * x)) x := by
    convert
      (Real.hasDerivAt_exp (Real.log (3 / 2) * x)).comp x hinner
      using 1
    ring
  have heq :
      ratioPower =
        (fun y : ℝ => Real.exp (Real.log (3 / 2) * y)) := by
    funext y
    simp only [ratioPower, powBase]
    change (3 / 2) ^ y = Real.exp (Real.log (3 / 2) * y)
    exact Real.rpow_def_of_pos hbase y
  have hlog : Real.log (3 / 2) = Real.log 3 - Real.log 2 := by
    exact Real.log_div (by norm_num) (by norm_num)
  rw [heq]
  convert hd using 1
  rw [hlog]

private lemma ratioPower_one_lt {x : ℝ} (hx : x ∈ branch) :
    1 < ratioPower x := by
  have hx0 : 0 < x := hx
  simpa only [ratioPower, powBase] using
    (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3 / 2) hx0)

private lemma abs_power_quotient_eq_ratio {x : ℝ} (hx : x ∈ branch) :
    |(powBase 3 x - powBase 2 x) /
      (powBase 3 x + powBase 2 x)| =
      (ratioPower x - 1) / (ratioPower x + 1) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hp2 : 0 < powBase 2 x := Real.rpow_pos_of_pos h2 x
  have hp3 : 0 < powBase 3 x := Real.rpow_pos_of_pos h3 x
  have ht : 1 < ratioPower x := ratioPower_one_lt hx
  rw [ratioPower_eq_div] at ht
  have hlt : powBase 2 x < powBase 3 x := by
    simpa only [one_mul] using (lt_div_iff₀ hp2).mp ht
  rw [abs_of_pos (div_pos (sub_pos.mpr hlt) (add_pos hp3 hp2))]
  rw [ratioPower_eq_div]
  field_simp [ne_of_gt hp2]

private lemma primitive_eq_ratio {x : ℝ} (hx : x ∈ branch) :
    primitive x =
      1 / (2 * (Real.log 3 - Real.log 2)) *
        Real.log ((ratioPower x - 1) / (ratioPower x + 1)) := by
  simp only [primitive]
  rw [abs_power_quotient_eq_ratio hx]

private lemma primitive_hasDerivAt {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt primitive (substitutedIntegrand x) x := by
  have ht : 1 < ratioPower x := ratioPower_one_lt hx
  have hrm : ratioPower x - 1 ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  have hrp : ratioPower x + 1 ≠ 0 := by linarith
  have hsq : (ratioPower x) ^ 2 - 1 ≠ 0 := by nlinarith
  have hd := ratioPower_hasDerivAt x
  have hfrac :=
    (hd.sub_const 1).div (hd.add_const 1) hrp
  have hfracpos :
      0 < (ratioPower x - 1) / (ratioPower x + 1) :=
    div_pos (sub_pos.mpr ht) (by linarith)
  have hlogderiv :=
    (Real.hasDerivAt_log hfracpos.ne').comp x hfrac
  have hcore :
      HasDerivAt
        (fun y => 1 / (2 * (Real.log 3 - Real.log 2)) *
          Real.log ((ratioPower y - 1) / (ratioPower y + 1)))
        (ratioPower x / ((ratioPower x) ^ 2 - 1)) x := by
    convert hlogderiv.const_mul
      (1 / (2 * (Real.log 3 - Real.log 2))) using 1 <;>
      field_simp [log_sub_ne_zero, hrm, hrp, hsq] <;> ring
  have hevent : primitive =ᶠ[nhds x]
      (fun y => 1 / (2 * (Real.log 3 - Real.log 2)) *
        Real.log ((ratioPower y - 1) / (ratioPower y + 1))) := by
    filter_upwards
      [IsOpen.eventually_mem (isOpen_Ioi : IsOpen branch) hx] with y hy
    exact primitive_eq_ratio hy
  have hpraw := hcore.congr_of_eventuallyEq hevent
  have hs : substitutedIntegrand x =
      ratioPower x / ((ratioPower x) ^ 2 - 1) := by
    simp only [substitutedIntegrand]
    rw [hd.deriv]
    field_simp [log_sub_ne_zero]
  simpa only [hs] using hpraw

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn rewrittenIntegrand := by
  ext F
  constructor
  · intro hF x hx
    simpa only [integrand_eq_rewritten x] using hF x hx
  · intro hF x hx
    simpa only [integrand_eq_rewritten x] using hF x hx
theorem gap2 :
    AntiderivativesOn rewrittenIntegrand =
      AntiderivativesOn substitutedIntegrand := by
  ext F
  have hcancel :
      1 / (Real.log 3 - Real.log 2) *
        (Real.log 3 - Real.log 2) = 1 := by
    field_simp [log_sub_ne_zero]
  have heq : ∀ x : ℝ,
      rewrittenIntegrand x = substitutedIntegrand x := by
    intro x
    have hderiv := (ratioPower_hasDerivAt x).deriv
    simp only [rewrittenIntegrand, substitutedIntegrand]
    rw [hderiv]
    calc
      ratioPower x / (ratioPower x ^ 2 - 1) =
          1 * (ratioPower x / (ratioPower x ^ 2 - 1)) := by ring
      _ = (1 / (Real.log 3 - Real.log 2) *
            (Real.log 3 - Real.log 2)) *
            (ratioPower x / (ratioPower x ^ 2 - 1)) := by rw [hcancel]
      _ = 1 / (Real.log 3 - Real.log 2) *
            ((Real.log 3 - Real.log 2) * ratioPower x /
              (ratioPower x ^ 2 - 1)) := by ring
  constructor
  · intro hF x hx
    simpa only [heq x] using hF x hx
  · intro hF x hx
    simpa only [heq x] using hF x hx
theorem gap3 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  ext F
  constructor
  · intro hF
    have hz : ∀ x ∈ branch,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      convert (hF x hx).sub (primitive_hasDerivAt hx) using 1
      ring
    have hdiff :
        DifferentiableOn ℝ (fun y => F y - primitive y) branch := by
      intro x hx
      exact (hz x hx).differentiableAt.differentiableWithinAt
    have hzero :
        ∀ x ∈ branch, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hz x hx).deriv
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have h1 : (1 : ℝ) ∈ branch := by
      norm_num [branch]
    have heq :
        F x - primitive x = F 1 - primitive 1 :=
      (isOpen_Ioi : IsOpen branch).is_const_of_deriv_eq_zero
        (isPreconnected_Ioi : IsPreconnected branch) hdiff hzero hx h1
    linarith
  · rintro ⟨C, hC⟩ x hx
    have heq : F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards
        [IsOpen.eventually_mem (isOpen_Ioi : IsOpen branch) hx] with y hy
      exact hC y hy
    exact ((primitive_hasDerivAt hx).add_const C).congr_of_eventuallyEq heq
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  rw [gap1, gap2, gap3]

end
end ProofGap.Exercise1719
