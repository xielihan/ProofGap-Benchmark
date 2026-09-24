import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace ProofGap.Exercise1705

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def halfTanh (x : ℝ) := Real.tanh (x / 2)
def integrand (x : ℝ) := 1 / Real.sinh x
def rewrittenIntegrand (x : ℝ) :=
  (1 / (2 * (Real.cosh (x / 2)) ^ 2)) / halfTanh x
def substitutedIntegrand (x : ℝ) := deriv halfTanh x / halfTanh x
def primitive (x : ℝ) := Real.log |halfTanh x|
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private lemma integrand_eq_rewritten (x : ℝ) (hx : x ∈ branch) :
    integrand x = rewrittenIntegrand x := by
  change 0 < x at hx
  have hx2 : 0 < x / 2 := by linarith
  have hs : Real.sinh (x / 2) ≠ 0 := by
    exact ne_of_gt (Real.sinh_pos_iff.mpr hx2)
  have hc : Real.cosh (x / 2) ≠ 0 :=
    (Real.cosh_pos (x / 2)).ne'
  have hsinh :
      Real.sinh x =
        2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
    rw [show x = x / 2 + x / 2 by ring_nf, Real.sinh_add]
    ring
  simp only [integrand, rewrittenIntegrand, halfTanh,
    Real.tanh_eq_sinh_div_cosh]
  rw [hsinh]
  field_simp [hs, hc]

private lemma halfTanh_hasDeriv (x : ℝ) :
    HasDerivAt halfTanh
      (1 / (2 * (Real.cosh (x / 2)) ^ 2)) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
    convert (hasDerivAt_id x).div_const 2 using 1 <;> ring
  have hbase :
      HasDerivAt (fun z : ℝ => Real.sinh z / Real.cosh z)
        (1 / (Real.cosh (x / 2)) ^ 2) (x / 2) := by
    have hc : Real.cosh (x / 2) ≠ 0 :=
      (Real.cosh_pos (x / 2)).ne'
    convert
      (Real.hasDerivAt_sinh (x / 2)).div
        (Real.hasDerivAt_cosh (x / 2)) hc using 1
    field_simp [hc] <;>
      nlinarith [Real.cosh_sq_sub_sinh_sq (x / 2)]
  convert hbase.comp x hinner using 1 <;> try ring
  funext y
  simp [halfTanh, Real.tanh_eq_sinh_div_cosh, Function.comp_def,
    div_eq_mul_inv]

private lemma rewritten_eq_substituted (x : ℝ) :
    rewrittenIntegrand x = substitutedIntegrand x := by
  unfold rewrittenIntegrand substitutedIntegrand
  rw [(halfTanh_hasDeriv x).deriv]

private lemma primitive_hasDeriv (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (substitutedIntegrand x) x := by
  change 0 < x at hx
  have hx2 : 0 < x / 2 := by linarith
  have htpos : 0 < halfTanh x := by
    unfold halfTanh
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hx2) (Real.cosh_pos (x / 2))
  have ht : halfTanh x ≠ 0 := ne_of_gt htpos
  have hlog :
      HasDerivAt (fun y => Real.log (halfTanh y))
        (substitutedIntegrand x) x := by
    rw [← rewritten_eq_substituted x]
    unfold rewrittenIntegrand
    convert
      (Real.hasDerivAt_log ht).comp x (halfTanh_hasDeriv x) using 1 <;>
      ring
  have hevent_pos : ∀ᶠ y in nhds x, 0 < halfTanh y :=
    (halfTanh_hasDeriv x).continuousAt (Ioi_mem_nhds htpos)
  apply hlog.congr_of_eventuallyEq
  filter_upwards [hevent_pos] with y hy
  simp only [primitive, abs_of_pos hy]

private lemma eq_one_of_hasDerivAt_zero_on_branch
    {g : ℝ → ℝ}
    (hg : ∀ x ∈ branch, HasDerivAt g 0 x) :
    ∀ x ∈ branch, g x = g 1 := by
  intro x hx
  change 0 < x at hx
  by_cases hxeq : x = 1
  · simp [hxeq]
  rcases lt_or_gt_of_ne hxeq with hlt | hgt
  · have hcont : ContinuousOn g (Set.Icc x 1) := by
      intro y hy
      have hyb : y ∈ branch := by
        change 0 < y
        exact lt_of_lt_of_le hx hy.1
      exact (hg y hyb).continuousAt.continuousWithinAt
    have hderiv : ∀ y ∈ Set.Ioo x 1, HasDerivAt g 0 y := by
      intro y hy
      exact hg y (by
        change 0 < y
        exact lt_trans hx hy.1)
    obtain ⟨c, hc, hcderiv⟩ :=
      exists_hasDerivAt_eq_slope (f := g) (fun _ : ℝ => 0)
        hlt hcont hderiv
    have hslope : (g 1 - g x) / (1 - x) = 0 := by
      simpa [slope] using hcderiv.symm
    have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlt)
    have hnum : g 1 - g x = 0 :=
      (div_eq_zero_iff.mp hslope).resolve_right hden
    linarith
  · have hcont : ContinuousOn g (Set.Icc 1 x) := by
      intro y hy
      have hyb : y ∈ branch := by
        change 0 < y
        linarith [hy.1]
      exact (hg y hyb).continuousAt.continuousWithinAt
    have hderiv : ∀ y ∈ Set.Ioo 1 x, HasDerivAt g 0 y := by
      intro y hy
      exact hg y (by
        change 0 < y
        linarith [hy.1])
    obtain ⟨c, hc, hcderiv⟩ :=
      exists_hasDerivAt_eq_slope (f := g) (fun _ : ℝ => 0)
        hgt hcont hderiv
    have hslope : (g x - g 1) / (x - 1) = 0 := by
      simpa [slope] using hcderiv.symm
    have hden : x - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hgt)
    have hnum : g x - g 1 = 0 :=
      (div_eq_zero_iff.mp hslope).resolve_right hden
    linarith

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn rewrittenIntegrand := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∀ x ∈ branch, HasDerivAt F (rewrittenIntegrand x) x
  constructor <;> intro h x hx
  · simpa only [integrand_eq_rewritten x hx] using h x hx
  · simpa only [integrand_eq_rewritten x hx] using h x hx
theorem gap2 :
    AntiderivativesOn rewrittenIntegrand =
      AntiderivativesOn substitutedIntegrand := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (rewrittenIntegrand x) x) ↔
      ∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x
  constructor <;> intro h x hx
  · simpa only [rewritten_eq_substituted x] using h x hx
  · simpa only [rewritten_eq_substituted x] using h x hx
theorem gap3 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x) ↔
      ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
  constructor
  · intro hF
    have hzero :
        ∀ x ∈ branch,
          HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      convert (hF x hx).sub (primitive_hasDeriv x hx) using 1 <;> ring
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have hc := eq_one_of_hasDerivAt_zero_on_branch hzero x hx
    linarith
  · rintro ⟨C, hF⟩ x hx
    have hevent :
        F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact hF y hy
    exact
      ((primitive_hasDeriv x hx).add_const C).congr_of_eventuallyEq
        hevent
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  rw [gap1, gap2, gap3]

end
end ProofGap.Exercise1705
