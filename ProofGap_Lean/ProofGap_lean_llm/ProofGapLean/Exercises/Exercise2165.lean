import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2165

noncomputable section

def branch : Set ℝ := Set.Ioo (-Real.pi) Real.pi
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}
def integrand (x : ℝ) :=
  (1 + Real.sin x) / (1 + Real.cos x) * Real.exp x
def halfAngleRewrite (x : ℝ) :=
  (1 + 2 * Real.sin (x / 2) * Real.cos (x / 2)) /
    (2 * Real.cos (x / 2) ^ 2) * Real.exp x
def SplitFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn
      (fun x => Real.exp x / (2 * Real.cos (x / 2) ^ 2)),
    ∃ H ∈ AntiderivativesOn
      (fun x => Real.exp x * Real.tan (x / 2)),
    ∀ x ∈ branch, F x = G x + H x}
def ProductRuleFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
      (∀ x ∈ branch,
        HasDerivAt G
          (Real.exp x * deriv (fun y : ℝ => Real.tan (y / 2)) x) x) ∧
    ∃ H : ℝ → ℝ,
      (∀ x ∈ branch,
        HasDerivAt H
          (Real.tan (x / 2) * deriv Real.exp x) x) ∧
    ∀ x ∈ branch, F x = G x + H x}
def CancellationFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn
      (fun x => Real.tan (x / 2) * deriv Real.exp x),
    ∃ H ∈ AntiderivativesOn
      (fun x => Real.tan (x / 2) * deriv Real.exp x),
    ∀ x ∈ branch,
      F x = Real.exp x * Real.tan (x / 2) - G x + H x}
def primitive (x : ℝ) := Real.exp x * Real.tan (x / 2)

private lemma branch_isOpen : IsOpen branch := by
  simpa only [branch] using isOpen_Ioo

private lemma branch_isPreconnected : IsPreconnected branch := by
  simpa only [branch] using isPreconnected_Ioo

private lemma zero_mem_branch : (0 : ℝ) ∈ branch := by
  change -Real.pi < 0 ∧ 0 < Real.pi
  exact ⟨neg_neg_of_pos Real.pi_pos, Real.pi_pos⟩

private lemma cos_half_pos (x : ℝ) (hx : x ∈ branch) :
    0 < Real.cos (x / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  change -(Real.pi / 2) < x / 2 ∧ x / 2 < Real.pi / 2
  change -Real.pi < x ∧ x < Real.pi at hx
  constructor <;> linarith

private lemma cos_half_ne_zero (x : ℝ) (hx : x ∈ branch) :
    Real.cos (x / 2) ≠ 0 :=
  ne_of_gt (cos_half_pos x hx)

private lemma integrand_eq_halfAngleRewrite (x : ℝ) (hx : x ∈ branch) :
    integrand x = halfAngleRewrite x := by
  have hs :
      Real.sin x =
        2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    calc
      Real.sin x = Real.sin (2 * (x / 2)) := by
        congr 1
        ring
      _ = 2 * Real.sin (x / 2) * Real.cos (x / 2) :=
        Real.sin_two_mul (x / 2)
  have hc :
      1 + Real.cos x = 2 * Real.cos (x / 2) ^ 2 := by
    calc
      1 + Real.cos x = 1 + Real.cos (2 * (x / 2)) := by
        congr 2
        ring
      _ = 2 * Real.cos (x / 2) ^ 2 := by
        rw [Real.cos_two_mul]
        ring
  unfold integrand halfAngleRewrite
  rw [hs, hc]

private lemma tan_half_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => Real.tan (y / 2))
      (1 / (2 * Real.cos (x / 2) ^ 2)) x := by
  have h :=
    (Real.hasDerivAt_tan (cos_half_ne_zero x hx)).comp x
      ((hasDerivAt_id x).div_const 2)
  convert h using 1 <;> field_simp

private lemma deriv_tan_half (x : ℝ) (hx : x ∈ branch) :
    deriv (fun y : ℝ => Real.tan (y / 2)) x =
      1 / (2 * Real.cos (x / 2) ^ 2) :=
  (tan_half_hasDerivAt x hx).deriv

private lemma deriv_exp (x : ℝ) : deriv Real.exp x = Real.exp x :=
  (Real.hasDerivAt_exp x).deriv

private lemma integrand_eq_derivative_sum (x : ℝ) (hx : x ∈ branch) :
    integrand x =
      Real.exp x / (2 * Real.cos (x / 2) ^ 2) +
        Real.exp x * Real.tan (x / 2) := by
  rw [integrand_eq_halfAngleRewrite x hx]
  unfold halfAngleRewrite
  rw [Real.tan_eq_sin_div_cos]
  field_simp [cos_half_ne_zero x hx]

private lemma primitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (integrand x) x := by
  unfold primitive
  have h := (Real.hasDerivAt_exp x).mul (tan_half_hasDerivAt x hx)
  convert h using 1
  rw [integrand_eq_derivative_sum x hx]
  ring

private lemma hasDerivAt_of_eqOn_branch
    {F G : ℝ → ℝ} {d x : ℝ}
    (hx : x ∈ branch)
    (hFG : ∀ y ∈ branch, F y = G y)
    (hG : HasDerivAt G d x) :
    HasDerivAt F d x := by
  apply hG.congr_of_eventuallyEq
  filter_upwards [branch_isOpen.mem_nhds hx] with y hy
  exact hFG y hy

private lemma uIcc_zero_subset_branch {x : ℝ} (hx : x ∈ branch) :
    Set.uIcc 0 x ⊆ branch := by
  intro y hy
  change -Real.pi < x ∧ x < Real.pi at hx
  change -Real.pi < y ∧ y < Real.pi
  rcases Set.mem_uIcc.mp hy with hy | hy
  · constructor <;> linarith [Real.pi_pos]
  · constructor <;> linarith [Real.pi_pos]

private lemma tangent_integrand_continuousAt (x : ℝ) (hx : x ∈ branch) :
    ContinuousAt (fun y : ℝ => Real.exp y * Real.tan (y / 2)) x := by
  exact (Real.hasDerivAt_exp x).continuousAt.mul
    (tan_half_hasDerivAt x hx).continuousAt

private lemma exists_tangent_antiderivative :
    ∃ H : ℝ → ℝ,
      ∀ x ∈ branch,
        HasDerivAt H (Real.exp x * Real.tan (x / 2)) x := by
  refine ⟨fun x => ∫ t in (0 : ℝ)..x,
    Real.exp t * Real.tan (t / 2), ?_⟩
  intro x hx
  apply intervalIntegral.integral_hasDerivAt_right
  · have hc :
        ContinuousOn
          (fun y : ℝ => Real.exp y * Real.tan (y / 2))
          (Set.uIcc 0 x) := by
      intro y hy
      exact (tangent_integrand_continuousAt y
        (uIcc_zero_subset_branch hx hy)).continuousWithinAt
    exact hc.intervalIntegrable
  · exact ContinuousAt.stronglyMeasurableAtFilter
      branch_isOpen
      (fun y hy => tangent_integrand_continuousAt y hy)
      x hx
  · exact tangent_integrand_continuousAt x hx

private theorem antiderivatives_eq_primitive :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      (∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C)
  constructor
  · intro hF
    have hdiff :
        DifferentiableOn ℝ (fun x => F x - primitive x) branch := by
      intro x hx
      exact ((hF x hx).sub (primitive_hasDerivAt x hx)).differentiableAt.differentiableWithinAt
    have hzero :
        ∀ x ∈ branch, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      simpa using ((hF x hx).sub (primitive_hasDerivAt x hx)).deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have heq :
        F x - primitive x = F 0 - primitive 0 :=
      branch_isOpen.is_const_of_deriv_eq_zero branch_isPreconnected
        hdiff hzero hx zero_mem_branch
    linarith
  · rintro ⟨C, hF⟩
    intro x hx
    apply hasDerivAt_of_eqOn_branch hx hF
    exact (primitive_hasDerivAt x hx).add_const C

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn halfAngleRewrite := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      (∀ x ∈ branch, HasDerivAt F (halfAngleRewrite x) x)
  constructor
  · intro hF x hx
    simpa only [integrand_eq_halfAngleRewrite x hx] using hF x hx
  · intro hF x hx
    simpa only [integrand_eq_halfAngleRewrite x hx] using hF x hx
theorem gap2 :
    AntiderivativesOn integrand = SplitFamily := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      (∃ G,
        (∀ x ∈ branch,
          HasDerivAt G
            (Real.exp x / (2 * Real.cos (x / 2) ^ 2)) x) ∧
        ∃ H,
          (∀ x ∈ branch,
            HasDerivAt H
              (Real.exp x * Real.tan (x / 2)) x) ∧
          ∀ x ∈ branch, F x = G x + H x)
  constructor
  · intro hF
    rcases exists_tangent_antiderivative with ⟨H, hH⟩
    refine ⟨fun x => F x - H x, ?_, H, hH, ?_⟩
    · intro x hx
      convert (hF x hx).sub (hH x hx) using 1
      rw [integrand_eq_derivative_sum x hx]
      ring
    · intro x hx
      ring
  · rintro ⟨G, hG, H, hH, hF⟩
    intro x hx
    apply hasDerivAt_of_eqOn_branch hx hF
    simpa only [integrand_eq_derivative_sum x hx] using
      (hG x hx).add (hH x hx)
theorem gap3 :
    AntiderivativesOn integrand = ProductRuleFamily := by
  rw [gap2]
  ext F
  change
    (∃ G,
        (∀ x ∈ branch,
          HasDerivAt G
            (Real.exp x / (2 * Real.cos (x / 2) ^ 2)) x) ∧
        ∃ H,
          (∀ x ∈ branch,
            HasDerivAt H
              (Real.exp x * Real.tan (x / 2)) x) ∧
          ∀ x ∈ branch, F x = G x + H x) ↔
      (∃ G,
        (∀ x ∈ branch,
          HasDerivAt G
            (Real.exp x * deriv (fun y : ℝ => Real.tan (y / 2)) x) x) ∧
        ∃ H,
          (∀ x ∈ branch,
            HasDerivAt H
              (Real.tan (x / 2) * deriv Real.exp x) x) ∧
          ∀ x ∈ branch, F x = G x + H x)
  constructor
  · rintro ⟨G, hG, H, hH, hF⟩
    refine ⟨G, ?_, H, ?_, hF⟩
    · intro x hx
      rw [deriv_tan_half x hx]
      simpa only [div_eq_mul_inv, one_mul] using hG x hx
    · intro x hx
      simpa only [deriv_exp, mul_comm] using hH x hx
  · rintro ⟨G, hG, H, hH, hF⟩
    refine ⟨G, ?_, H, ?_, hF⟩
    · intro x hx
      have h := hG x hx
      rw [deriv_tan_half x hx] at h
      simpa only [div_eq_mul_inv, one_mul] using h
    · intro x hx
      simpa only [deriv_exp, mul_comm] using hH x hx
theorem gap4 :
    AntiderivativesOn integrand = CancellationFamily := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      (∃ G,
        (∀ x ∈ branch,
          HasDerivAt G
            (Real.tan (x / 2) * deriv Real.exp x) x) ∧
        ∃ H,
          (∀ x ∈ branch,
            HasDerivAt H
              (Real.tan (x / 2) * deriv Real.exp x) x) ∧
          ∀ x ∈ branch,
            F x = Real.exp x * Real.tan (x / 2) - G x + H x)
  constructor
  · intro hF
    rcases exists_tangent_antiderivative with ⟨G, hG⟩
    refine ⟨G, ?_, fun x => F x - primitive x + G x, ?_, ?_⟩
    · intro x hx
      simpa only [deriv_exp, mul_comm] using hG x hx
    · intro x hx
      have h := ((hF x hx).sub (primitive_hasDerivAt x hx)).add (hG x hx)
      simpa only [sub_self, zero_add, deriv_exp, mul_comm] using h
    · intro x hx
      unfold primitive
      ring
  · rintro ⟨G, hG, H, hH, hF⟩
    intro x hx
    apply hasDerivAt_of_eqOn_branch hx hF
    have hG' : HasDerivAt G (Real.exp x * Real.tan (x / 2)) x := by
      simpa only [deriv_exp, mul_comm] using hG x hx
    have hH' : HasDerivAt H (Real.exp x * Real.tan (x / 2)) x := by
      simpa only [deriv_exp, mul_comm] using hH x hx
    have h := ((primitive_hasDerivAt x hx).sub hG').add hH'
    simpa only [primitive, sub_add_cancel] using h
theorem gap5 :
    CancellationFamily = PrimitiveFamily primitive := by
  calc
    CancellationFamily = AntiderivativesOn integrand := gap4.symm
    _ = PrimitiveFamily primitive := antiderivatives_eq_primitive
theorem gap6 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  exact antiderivatives_eq_primitive

end
end ProofGap.Exercise2165
