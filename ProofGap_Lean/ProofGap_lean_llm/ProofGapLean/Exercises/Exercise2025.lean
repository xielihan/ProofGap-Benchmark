import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2025
noncomputable section

def branch : Set ℝ := Set.Ioo (-Real.pi) Real.pi
def t (x : ℝ) := Real.tan (x / 2)
def integrand (x : ℝ) := 1 / (2 * Real.sin x - Real.cos x + 5)
def rational (u : ℝ) := 1 / (3 * u ^ 2 + 2 * u + 2)
def primitiveT (u : ℝ) :=
  1 / Real.sqrt 5 * Real.arctan ((3 * u + 1) / Real.sqrt 5)
def primitive (x : ℝ) := primitiveT (t x)
def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ branch, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ branch, F x = p x + C}

private theorem half_mem_branch (x : ℝ) (hx : x ∈ branch) :
    x / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  change -Real.pi < x ∧ x < Real.pi at hx
  constructor
  · have h :=
      (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 hx.1
    simpa [neg_div] using h
  · exact
      (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 hx.2

private theorem hasDerivAt_t_on_branch (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt t
      ((1 / Real.cos (x / 2) ^ 2) * (1 / 2)) x := by
  have hy := half_mem_branch x hx
  have hcpos : 0 < Real.cos (x / 2) := Real.cos_pos_of_mem_Ioo hy
  have hcn : Real.cos (x / 2) ≠ 0 := ne_of_gt hcpos
  simpa [t, div_eq_mul_inv] using
    (Real.hasDerivAt_tan hcn).comp x ((hasDerivAt_id x).div_const 2)

theorem gap1 (x : ℝ) (hx : x ∈ branch) :
    Real.sin x = 2 * t x / (1 + t x ^ 2) := by
  have hy := half_mem_branch x hx
  have hcpos : 0 < Real.cos (x / 2) := Real.cos_pos_of_mem_Ioo hy
  have hcn : Real.cos (x / 2) ≠ 0 := ne_of_gt hcpos
  have hpyth : Real.cos (x / 2) ^ 2 + Real.sin (x / 2) ^ 2 = 1 := by
    simpa [add_comm] using Real.sin_sq_add_cos_sq (x / 2)
  rw [t, Real.tan_eq_sin_div_cos]
  rw [show x = 2 * (x / 2) by ring, Real.sin_two_mul]
  field_simp [hcn]
  simpa [hpyth]
theorem gap2 (x : ℝ) (hx : x ∈ branch) :
    Real.cos x = (1 - t x ^ 2) / (1 + t x ^ 2) := by
  have hy := half_mem_branch x hx
  have hcpos : 0 < Real.cos (x / 2) := Real.cos_pos_of_mem_Ioo hy
  have hcn : Real.cos (x / 2) ≠ 0 := ne_of_gt hcpos
  have hpyth : Real.cos (x / 2) ^ 2 + Real.sin (x / 2) ^ 2 = 1 := by
    simpa [add_comm] using Real.sin_sq_add_cos_sq (x / 2)
  rw [t, Real.tan_eq_sin_div_cos]
  rw [show x = 2 * (x / 2) by ring, Real.cos_two_mul]
  field_simp [hcn]
  rw [hpyth]
  nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
theorem gap3 (x : ℝ) (hx : x ∈ branch) :
    1 = (2 / (1 + t x ^ 2)) * deriv t x := by
  have ht := hasDerivAt_t_on_branch x hx
  rw [ht.deriv]
  have hy := half_mem_branch x hx
  have hcpos : 0 < Real.cos (x / 2) := Real.cos_pos_of_mem_Ioo hy
  have hcn : Real.cos (x / 2) ≠ 0 := ne_of_gt hcpos
  have hpyth : Real.cos (x / 2) ^ 2 + Real.sin (x / 2) ^ 2 = 1 := by
    simpa [add_comm] using Real.sin_sq_add_cos_sq (x / 2)
  rw [t, Real.tan_eq_sin_div_cos]
  field_simp [hcn]
  simpa [hpyth]
theorem gap4 (x : ℝ) (hx : x ∈ branch) :
    integrand x = rational (t x) * deriv t x := by
  have hApos : 0 < 1 + t x ^ 2 := by
    nlinarith [sq_nonneg (t x)]
  have hA : 1 + t x ^ 2 ≠ 0 := ne_of_gt hApos
  have hQpos : 0 < 3 * t x ^ 2 + 2 * t x + 2 := by
    nlinarith [sq_nonneg (3 * t x + 1)]
  have hQ : 3 * t x ^ 2 + 2 * t x + 2 ≠ 0 := ne_of_gt hQpos
  have hderiv : deriv t x = (1 + t x ^ 2) / 2 := by
    have h := gap3 x hx
    field_simp [hA] at h
    linarith
  unfold integrand rational
  rw [gap1 x hx, gap2 x hx]
  have hden :
      2 * (2 * t x / (1 + t x ^ 2)) -
          (1 - t x ^ 2) / (1 + t x ^ 2) + 5 =
        2 * (3 * t x ^ 2 + 2 * t x + 2) / (1 + t x ^ 2) := by
    field_simp [hA] <;> ring
  rw [hden, hderiv]
  field_simp [hA, hQ] <;> ring
theorem gap5 (u : ℝ) : HasDerivAt primitiveT (rational u) u := by
  have hspos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hs : Real.sqrt 5 ≠ 0 := ne_of_gt hspos
  have hsquare : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hQpos : 0 < 3 * u ^ 2 + 2 * u + 2 := by
    nlinarith [sq_nonneg (3 * u + 1)]
  have hQ : 3 * u ^ 2 + 2 * u + 2 ≠ 0 := ne_of_gt hQpos
  have hzpos : 0 < 1 + ((3 * u + 1) / Real.sqrt 5) ^ 2 := by
    nlinarith [sq_nonneg ((3 * u + 1) / Real.sqrt 5)]
  have hz : 1 + ((3 * u + 1) / Real.sqrt 5) ^ 2 ≠ 0 := ne_of_gt hzpos
  have hin :
      HasDerivAt (fun v : ℝ => (3 * v + 1) / Real.sqrt 5)
        (3 / Real.sqrt 5) u := by
    simpa [div_eq_mul_inv] using
      ((((hasDerivAt_id u).const_mul 3).add_const 1).div_const (Real.sqrt 5))
  have hden :
      Real.sqrt 5 ^ 2 *
          (1 + ((3 * u + 1) / Real.sqrt 5) ^ 2) =
        3 * (3 * u ^ 2 + 2 * u + 2) := by
    calc
      Real.sqrt 5 ^ 2 *
            (1 + ((3 * u + 1) / Real.sqrt 5) ^ 2) =
          Real.sqrt 5 ^ 2 + (3 * u + 1) ^ 2 := by
        field_simp [hs] <;> ring
      _ = 3 * (3 * u ^ 2 + 2 * u + 2) := by
        rw [hsquare]
        ring
  have hcoeff :
      (1 / Real.sqrt 5) *
          ((1 / (1 + ((3 * u + 1) / Real.sqrt 5) ^ 2)) *
            (3 / Real.sqrt 5)) = rational u := by
    unfold rational
    calc
      (1 / Real.sqrt 5) *
            ((1 / (1 + ((3 * u + 1) / Real.sqrt 5) ^ 2)) *
              (3 / Real.sqrt 5)) =
          3 /
            (Real.sqrt 5 ^ 2 *
              (1 + ((3 * u + 1) / Real.sqrt 5) ^ 2)) := by
        field_simp [hs, hz] <;> ring
      _ = 3 / (3 * (3 * u ^ 2 + 2 * u + 2)) := by
        rw [hden]
      _ = 1 / (3 * u ^ 2 + 2 * u + 2) := by
        field_simp [hQ] <;> ring
  have h :
      HasDerivAt
        (fun v : ℝ =>
          (1 / Real.sqrt 5) *
            Real.arctan ((3 * v + 1) / Real.sqrt 5))
        ((1 / Real.sqrt 5) *
          ((1 / (1 + ((3 * u + 1) / Real.sqrt 5) ^ 2)) *
            (3 / Real.sqrt 5))) u := by
    simpa [one_div] using
      (((Real.hasDerivAt_arctan ((3 * u + 1) / Real.sqrt 5)).comp u hin).const_mul
        (1 / Real.sqrt 5))
  change HasDerivAt
    (fun v : ℝ =>
      (1 / Real.sqrt 5) * Real.arctan ((3 * v + 1) / Real.sqrt 5))
    (rational u) u
  rw [← hcoeff]
  exact h
theorem gap6 : Family integrand = Translates primitive := by
  have hopen : IsOpen branch := by
    unfold branch
    exact isOpen_Ioo
  have hconn : IsPreconnected branch := by
    unfold branch
    exact isPreconnected_Ioo
  have hprimitive (x : ℝ) (hx : x ∈ branch) :
      HasDerivAt primitive (integrand x) x := by
    have ht0 := hasDerivAt_t_on_branch x hx
    have ht : HasDerivAt t (deriv t x) x := by
      rw [ht0.deriv]
      exact ht0
    simpa [primitive, gap4 x hx] using (gap5 (t x)).comp x ht
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ C, ∀ x ∈ branch, F x = primitive x + C
    have hzero : ∀ x ∈ branch,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hprimitive x hx)
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) branch := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ branch, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    have hconst : ∀ x ∈ branch, ∀ y ∈ branch,
        F x - primitive x = F y - primitive y := by
      intro x hx y hy
      exact hopen.is_const_of_deriv_eq_zero hconn hdiff hderiv hx hy
    have h0 : (0 : ℝ) ∈ branch := by
      change -Real.pi < 0 ∧ 0 < Real.pi
      constructor <;> linarith [Real.pi_pos]
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have heq : F x - primitive x = F 0 - primitive 0 :=
      hconst x hx 0 h0
    linarith
  · intro hF
    change ∃ C, ∀ x ∈ branch, F x = primitive x + C at hF
    rcases hF with ⟨C, hC⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hev : F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((hprimitive x hx).add_const C).congr_of_eventuallyEq hev

end
end ProofGap.Exercise2025
