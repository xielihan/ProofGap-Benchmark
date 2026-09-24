import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2009
noncomputable section

def branch : Set ℝ := Set.Ioo 0 (Real.pi / 4)
def t (x : ℝ) := Real.sqrt (Real.tan x)
def integrand (x : ℝ) := 1 / Real.sqrt (Real.tan x)
def rational (u : ℝ) := 2 / (1 + u ^ 4)
def primitiveT (u : ℝ) :=
  1 / (2 * Real.sqrt 2) *
      Real.log |(u ^ 2 + u * Real.sqrt 2 + 1) /
        (u ^ 2 - u * Real.sqrt 2 + 1)| +
    1 / Real.sqrt 2 * Real.arctan (u * Real.sqrt 2 / (1 - u ^ 2))
def primitive (x : ℝ) := primitiveT (t x)
def Family (f : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x ∈ branch, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) := {F : ℝ → ℝ | ∃ C, ∀ x ∈ branch, F x = p x + C}

theorem gap1 (x : ℝ) (hx : x ∈ branch) :
    x = Real.arctan (t x ^ 2) := by
  change x ∈ Set.Ioo 0 (Real.pi / 4) at hx
  have hxlt : x < Real.pi / 2 := by
    nlinarith [hx.2, Real.pi_pos]
  have hxneg : -(Real.pi / 2) < x := by
    nlinarith [hx.1, Real.pi_pos]
  have htan : 0 ≤ Real.tan x :=
    (Real.tan_pos_of_pos_of_lt_pi_div_two hx.1 hxlt).le
  have ht_sq : t x ^ 2 = Real.tan x := by
    simpa [t] using Real.sq_sqrt htan
  calc
    x = Real.arctan (Real.tan x) :=
      (Real.arctan_tan hxneg hxlt).symm
    _ = Real.arctan (t x ^ 2) := by rw [ht_sq]
theorem gap2 (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun u : ℝ => Real.arctan (u ^ 2))
      (2 * t x / (1 + t x ^ 4)) (t x) := by
  have h :
      HasDerivAt (fun u : ℝ => Real.arctan (u ^ 2))
        (1 / (1 + (t x ^ 2) ^ 2) * (2 * t x)) (t x) := by
    simpa using (((hasDerivAt_id (t x)).pow 2).arctan)
  have hpow : (t x ^ 2) ^ 2 = t x ^ 4 := by
    ring
  rw [hpow] at h
  convert h using 1
  ring
theorem gap3 (x : ℝ) (hx : x ∈ branch) :
    integrand x = rational (t x) * deriv t x := by
  change x ∈ Set.Ioo 0 (Real.pi / 4) at hx
  have hxlt : x < Real.pi / 2 := by
    nlinarith [hx.2, Real.pi_pos]
  have hxneg : -(Real.pi / 2) < x := by
    nlinarith [hx.1, Real.pi_pos]
  have htan_pos : 0 < Real.tan x :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hx.1 hxlt
  have hcos_pos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨hxneg, hxlt⟩
  have hcos : Real.cos x ≠ 0 := hcos_pos.ne'
  have htderiv :
      HasDerivAt t
        ((1 / (2 * Real.sqrt (Real.tan x))) *
          (1 / Real.cos x ^ 2)) x := by
    unfold t
    exact
      (Real.hasDerivAt_sqrt htan_pos.ne').comp x
        (Real.hasDerivAt_tan hcos)
  have ht_sq : t x ^ 2 = Real.tan x := by
    simpa [t] using Real.sq_sqrt htan_pos.le
  have ht_four : t x ^ 4 = Real.tan x ^ 2 := by
    calc
      t x ^ 4 = (t x ^ 2) ^ 2 := by ring
      _ = Real.tan x ^ 2 := by rw [ht_sq]
  have hident : 1 + t x ^ 4 = 1 / Real.cos x ^ 2 := by
    rw [ht_four, Real.tan_eq_sin_div_cos]
    field_simp [hcos]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have htne : t x ≠ 0 := by
    exact ne_of_gt (by simpa [t] using Real.sqrt_pos.2 htan_pos)
  change
    1 / Real.sqrt (Real.tan x) =
      2 / (1 + t x ^ 4) * deriv t x
  rw [htderiv.deriv, hident]
  change
    1 / t x =
      2 / (1 / Real.cos x ^ 2) *
        ((1 / (2 * t x)) * (1 / Real.cos x ^ 2))
  field_simp [htne, hcos]
  <;> ring
theorem gap4 (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt primitiveT (rational u) u := by
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by
    simpa using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hAall : ∀ z : ℝ, 0 < z ^ 2 + z * Real.sqrt 2 + 1 := by
    intro z
    nlinarith [sq_nonneg (z + Real.sqrt 2 / 2), hsqrt_sq]
  have hBall : ∀ z : ℝ, 0 < z ^ 2 - z * Real.sqrt 2 + 1 := by
    intro z
    nlinarith [sq_nonneg (z - Real.sqrt 2 / 2), hsqrt_sq]
  have hApos : 0 < u ^ 2 + u * Real.sqrt 2 + 1 := hAall u
  have hBpos : 0 < u ^ 2 - u * Real.sqrt 2 + 1 := hBall u
  have hDpos : 0 < 1 - u ^ 2 := by
    have hprod :=
      mul_pos (sub_pos.mpr hu.2) (add_pos hu.1 (by norm_num : (0 : ℝ) < 1))
    nlinarith
  have hquart : 0 < 1 + u ^ 4 := by
    nlinarith [sq_nonneg (u ^ 2)]
  have hA :
      HasDerivAt
        (fun z : ℝ => z ^ 2 + z * Real.sqrt 2 + 1)
        (2 * u + Real.sqrt 2) u := by
    convert
      (((hasDerivAt_id u).pow 2).add
        ((hasDerivAt_id u).mul_const (Real.sqrt 2))).add_const 1 using 1 <;>
      simp <;> ring
  have hB :
      HasDerivAt
        (fun z : ℝ => z ^ 2 - z * Real.sqrt 2 + 1)
        (2 * u - Real.sqrt 2) u := by
    convert
      (((hasDerivAt_id u).pow 2).sub
        ((hasDerivAt_id u).mul_const (Real.sqrt 2))).add_const 1 using 1 <;>
      simp <;> ring
  have hD :
      HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * u) u := by
    convert ((hasDerivAt_id u).pow 2).const_sub 1 using 1 <;>
      simp <;> ring
  have hR := hA.div hB hBpos.ne'
  have hRpos :
      0 <
        (u ^ 2 + u * Real.sqrt 2 + 1) /
          (u ^ 2 - u * Real.sqrt 2 + 1) :=
    div_pos hApos hBpos
  have hRall :
      ∀ z : ℝ,
        0 <
          (z ^ 2 + z * Real.sqrt 2 + 1) /
            (z ^ 2 - z * Real.sqrt 2 + 1) := by
    intro z
    exact div_pos (hAall z) (hBall z)
  have hAB :
      (u ^ 2 + u * Real.sqrt 2 + 1) *
          (u ^ 2 - u * Real.sqrt 2 + 1) =
        1 + u ^ 4 := by
    nlinarith [hsqrt_sq]
  have hLogNum :
      (2 * u + Real.sqrt 2) *
          (u ^ 2 - u * Real.sqrt 2 + 1) -
        (u ^ 2 + u * Real.sqrt 2 + 1) *
          (2 * u - Real.sqrt 2) =
      2 * Real.sqrt 2 * (1 - u ^ 2) := by
    nlinarith [hsqrt_sq]
  have hLogRaw :=
    (Real.hasDerivAt_log hRpos.ne').comp u hR
  have hLogCoeff :
      ((u ^ 2 + u * Real.sqrt 2 + 1) /
          (u ^ 2 - u * Real.sqrt 2 + 1))⁻¹ *
          (((2 * u + Real.sqrt 2) *
                (u ^ 2 - u * Real.sqrt 2 + 1) -
              (u ^ 2 + u * Real.sqrt 2 + 1) *
                (2 * u - Real.sqrt 2)) /
            (u ^ 2 - u * Real.sqrt 2 + 1) ^ 2) =
        2 * Real.sqrt 2 * (1 - u ^ 2) / (1 + u ^ 4) := by
    rw [hLogNum]
    calc
      ((u ^ 2 + u * Real.sqrt 2 + 1) /
            (u ^ 2 - u * Real.sqrt 2 + 1))⁻¹ *
          (2 * Real.sqrt 2 * (1 - u ^ 2) /
            (u ^ 2 - u * Real.sqrt 2 + 1) ^ 2) =
          2 * Real.sqrt 2 * (1 - u ^ 2) /
            ((u ^ 2 + u * Real.sqrt 2 + 1) *
              (u ^ 2 - u * Real.sqrt 2 + 1)) := by
            field_simp [hApos.ne', hBpos.ne']
            <;> ring
      _ = 2 * Real.sqrt 2 * (1 - u ^ 2) / (1 + u ^ 4) := by
        rw [hAB]
  have hLog :
      HasDerivAt
        (fun z : ℝ =>
          Real.log
            |(z ^ 2 + z * Real.sqrt 2 + 1) /
              (z ^ 2 - z * Real.sqrt 2 + 1)|)
        (2 * Real.sqrt 2 * (1 - u ^ 2) / (1 + u ^ 4)) u := by
    convert hLogRaw using 1
    · funext z
      rw [abs_of_pos (hRall z)]
      rfl
    · exact hLogCoeff.symm
  have hN :
      HasDerivAt (fun z : ℝ => z * Real.sqrt 2) (Real.sqrt 2) u := by
    simpa using (hasDerivAt_id u).mul_const (Real.sqrt 2)
  have hQ := hN.div hD hDpos.ne'
  have hAtan0 := hQ.arctan
  have hAtanNum :
      Real.sqrt 2 * (1 - u ^ 2) -
          (u * Real.sqrt 2) * (-2 * u) =
        Real.sqrt 2 * (1 + u ^ 2) := by
    ring
  have hAtanDen :
      (1 - u ^ 2) ^ 2 + (u * Real.sqrt 2) ^ 2 =
        1 + u ^ 4 := by
    nlinarith [hsqrt_sq]
  have hAtanSumPos :
      0 < (1 - u ^ 2) ^ 2 + (u * Real.sqrt 2) ^ 2 := by
    rw [hAtanDen]
    exact hquart
  have hAtanInnerPos :
      0 < 1 + (u * Real.sqrt 2 / (1 - u ^ 2)) ^ 2 := by
    positivity
  have hAtanCoeff :
      1 / (1 + (u * Real.sqrt 2 / (1 - u ^ 2)) ^ 2) *
          ((Real.sqrt 2 * (1 - u ^ 2) -
              (u * Real.sqrt 2) * (-2 * u)) /
            (1 - u ^ 2) ^ 2) =
        Real.sqrt 2 * (1 + u ^ 2) / (1 + u ^ 4) := by
    rw [hAtanNum]
    calc
      1 / (1 + (u * Real.sqrt 2 / (1 - u ^ 2)) ^ 2) *
          (Real.sqrt 2 * (1 + u ^ 2) / (1 - u ^ 2) ^ 2) =
          Real.sqrt 2 * (1 + u ^ 2) /
            ((1 - u ^ 2) ^ 2 + (u * Real.sqrt 2) ^ 2) := by
              field_simp [hDpos.ne', hAtanInnerPos.ne', hAtanSumPos.ne']
              <;> ring
      _ = Real.sqrt 2 * (1 + u ^ 2) / (1 + u ^ 4) := by
        rw [hAtanDen]
  have hAtan :
      HasDerivAt
        (fun z : ℝ => Real.arctan (z * Real.sqrt 2 / (1 - z ^ 2)))
        (Real.sqrt 2 * (1 + u ^ 2) / (1 + u ^ 4)) u := by
    convert hAtan0 using 1
    exact hAtanCoeff.symm
  have hFinal :
      HasDerivAt primitiveT
        (1 / (2 * Real.sqrt 2) *
            (2 * Real.sqrt 2 * (1 - u ^ 2) / (1 + u ^ 4)) +
          1 / Real.sqrt 2 *
            (Real.sqrt 2 * (1 + u ^ 2) / (1 + u ^ 4))) u := by
    simpa only [primitiveT] using
      (hLog.const_mul (1 / (2 * Real.sqrt 2))).add
        (hAtan.const_mul (1 / Real.sqrt 2))
  have hFinalCoeff :
      1 / (2 * Real.sqrt 2) *
            (2 * Real.sqrt 2 * (1 - u ^ 2) / (1 + u ^ 4)) +
          1 / Real.sqrt 2 *
            (Real.sqrt 2 * (1 + u ^ 2) / (1 + u ^ 4)) =
        rational u := by
    unfold rational
    field_simp [hsqrt_pos.ne', hquart.ne']
    <;> ring
  convert hFinal using 1
  exact hFinalCoeff.symm
theorem gap5 : Family integrand = Translates primitive := by
  have hprimitive :
      ∀ x ∈ branch, HasDerivAt primitive (integrand x) x := by
    intro x hx
    have hx' := hx
    change x ∈ Set.Ioo 0 (Real.pi / 4) at hx'
    have hxlt : x < Real.pi / 2 := by
      nlinarith [hx'.2, Real.pi_pos]
    have hxneg : -(Real.pi / 2) < x := by
      nlinarith [hx'.1, Real.pi_pos]
    have htan_pos : 0 < Real.tan x :=
      Real.tan_pos_of_pos_of_lt_pi_div_two hx'.1 hxlt
    have hcos : Real.cos x ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo ⟨hxneg, hxlt⟩).ne'
    have htpos : 0 < t x := by
      simpa [t] using Real.sqrt_pos.2 htan_pos
    have htsq_lt : t x ^ 2 < 1 := by
      have hangle : Real.arctan (t x ^ 2) < Real.arctan 1 := by
        rw [← gap1 x hx, Real.arctan_one]
        exact hx'.2
      by_contra hnot
      have hge : (1 : ℝ) ≤ t x ^ 2 := le_of_not_gt hnot
      have harctan_ge :
          Real.arctan 1 ≤ Real.arctan (t x ^ 2) :=
        Real.arctan_strictMono.monotone hge
      exact (not_lt_of_ge harctan_ge) hangle
    have htmem : t x ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · exact htpos
      · nlinarith [sq_nonneg (t x - 1)]
    have htdiff : DifferentiableAt ℝ t x := by
      unfold t
      exact
        ((Real.hasDerivAt_sqrt htan_pos.ne').comp x
          (Real.hasDerivAt_tan hcos)).differentiableAt
    have hp := (gap4 (t x) htmem).comp x htdiff.hasDerivAt
    rw [← gap3 x hx] at hp
    simpa only [primitive] using hp
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ C, ∀ x ∈ branch, F x = primitive x + C
    have hzero :
        ∀ x ∈ branch,
          HasDerivAt (fun y : ℝ => F y - primitive y) 0 x := by
      intro x hx
      convert (hF x hx).sub (hprimitive x hx) using 1 <;> ring
    have hdiff :
        DifferentiableOn ℝ (fun y : ℝ => F y - primitive y) branch := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hdiffI :
        DifferentiableOn ℝ (fun y : ℝ => F y - primitive y)
          (Set.Ioo 0 (Real.pi / 4)) := by
      simpa only [branch] using hdiff
    have hderivI :
        ∀ x ∈ Set.Ioo 0 (Real.pi / 4),
          deriv (fun y : ℝ => F y - primitive y) x = 0 := by
      intro x hx
      exact (hzero x (by simpa only [branch] using hx)).deriv
    have hconstI :
        ∀ ⦃x y : ℝ⦄,
          x ∈ Set.Ioo 0 (Real.pi / 4) →
          y ∈ Set.Ioo 0 (Real.pi / 4) →
          F x - primitive x = F y - primitive y := by
      intro x y hx hy
      exact
        isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiffI
          hderivI hx hy
    have hconst :
        ∀ ⦃x y : ℝ⦄, x ∈ branch → y ∈ branch →
          F x - primitive x = F y - primitive y := by
      simpa only [branch] using hconstI
    have ha : Real.pi / 8 ∈ branch := by
      change Real.pi / 8 ∈ Set.Ioo 0 (Real.pi / 4)
      constructor <;> nlinarith [Real.pi_pos]
    refine ⟨F (Real.pi / 8) - primitive (Real.pi / 8), ?_⟩
    intro x hx
    have heq :
        F x - primitive x =
          F (Real.pi / 8) - primitive (Real.pi / 8) :=
      hconst hx ha
    linarith
  · rintro ⟨C, hC⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hbranch : branch ∈ nhds x := by
      exact isOpen_Ioo.mem_nhds hx
    have hevent :
        F =ᶠ[nhds x] (fun y : ℝ => primitive y + C) := by
      filter_upwards [hbranch] with y hy
      exact hC y hy
    exact
      ((hprimitive x hx).add_const C).congr_of_eventuallyEq hevent

end
end ProofGap.Exercise2009
