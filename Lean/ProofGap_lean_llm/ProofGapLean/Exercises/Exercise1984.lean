import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise1984

noncomputable section

def branch : Set ℝ := Set.Ioo 0 1
def z (x : ℝ) := Real.sqrt (1 - x ^ 2)
def xOfZ (y : ℝ) := Real.sqrt (1 - y ^ 2)
def originalIntegrand (x : ℝ) :=
  x ^ 5 / Real.sqrt (1 - x ^ 2)
def powerFormIntegrand (x : ℝ) :=
  x ^ 5 * (1 / Real.sqrt (1 - x ^ 2))
def transformedIntegrand (x : ℝ) :=
  (1 - z x ^ 2) ^ 2 * deriv z x
def primitive (x : ℝ) :=
  -z x + 2 / 3 * z x ^ 3 - 1 / 5 * z x ^ 5
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def NegatedFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn transformedIntegrand,
    ∀ x ∈ branch, F x = -G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem hasDerivAt_z_on_branch (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt z (-x / Real.sqrt (1 - x ^ 2)) x := by
  have hxp : 0 < x ∧ x < 1 := by
    simpa [branch] using hx
  have hprod : 0 < (1 - x) * (1 + x) :=
    mul_pos (sub_pos.mpr hxp.2) (by linarith)
  have hrad : 0 < 1 - x ^ 2 := by
    nlinarith
  have hinner : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp <;> ring
  have hcomp := (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp x hinner
  convert hcomp using 1 <;>
    simp [z, Function.comp_def] <;>
    field_simp [ne_of_gt (Real.sqrt_pos.2 hrad)] <;>
    ring

private theorem const_on_branch_of_hasDerivAt_zero
    (H : ℝ → ℝ) (hH : ∀ x ∈ branch, HasDerivAt H 0 x)
    {a b : ℝ} (ha : a ∈ branch) (hb : b ∈ branch) : H a = H b := by
  have ha' : 0 < a ∧ a < 1 := by
    simpa [branch] using ha
  have hb' : 0 < b ∧ b < 1 := by
    simpa [branch] using hb
  rcases lt_trichotomy a b with hab | hab | hab
  · have hcont : ContinuousOn H (Set.Icc a b) := by
      intro y hy
      have hybranch : y ∈ branch := by
        simpa [branch] using
          And.intro (lt_of_lt_of_le ha'.1 hy.1)
            (lt_of_le_of_lt hy.2 hb'.2)
      exact (hH y hybranch).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ H (Set.Ioo a b) := by
      intro y hy
      have hybranch : y ∈ branch := by
        simpa [branch] using
          And.intro (lt_trans ha'.1 hy.1) (lt_trans hy.2 hb'.2)
      exact (hH y hybranch).differentiableAt.differentiableWithinAt
    obtain ⟨y, hy, hslope⟩ :=
      exists_deriv_eq_slope H hab hcont hdiff
    have hybranch : y ∈ branch := by
      simpa [branch] using
        And.intro (lt_trans ha'.1 hy.1) (lt_trans hy.2 hb'.2)
    have hzero : deriv H y = 0 := (hH y hybranch).deriv
    rw [hzero] at hslope
    have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    field_simp [hne] at hslope
    linarith
  · exact congrArg H hab
  · have hcont : ContinuousOn H (Set.Icc b a) := by
      intro y hy
      have hybranch : y ∈ branch := by
        simpa [branch] using
          And.intro (lt_of_lt_of_le hb'.1 hy.1)
            (lt_of_le_of_lt hy.2 ha'.2)
      exact (hH y hybranch).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ H (Set.Ioo b a) := by
      intro y hy
      have hybranch : y ∈ branch := by
        simpa [branch] using
          And.intro (lt_trans hb'.1 hy.1) (lt_trans hy.2 ha'.2)
      exact (hH y hybranch).differentiableAt.differentiableWithinAt
    obtain ⟨y, hy, hslope⟩ :=
      exists_deriv_eq_slope H hab hcont hdiff
    have hybranch : y ∈ branch := by
      simpa [branch] using
        And.intro (lt_trans hb'.1 hy.1) (lt_trans hy.2 ha'.2)
    have hzero : deriv H y = 0 := (hH y hybranch).deriv
    rw [hzero] at hslope
    have hne : a - b ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    field_simp [hne] at hslope
    linarith

theorem gap1 (x : ℝ) (hx : x ∈ branch) :
    originalIntegrand x = powerFormIntegrand x := by
  simp [originalIntegrand, powerFormIntegrand, div_eq_mul_inv]
theorem gap2 (x : ℝ) (hx : x ∈ branch) :
    x = xOfZ (z x) := by
  have hxp : 0 < x ∧ x < 1 := by
    simpa [branch] using hx
  have hprod : 0 < (1 - x) * (1 + x) :=
    mul_pos (sub_pos.mpr hxp.2) (by linarith)
  have hrad : 0 ≤ 1 - x ^ 2 := by
    nlinarith
  have hsq : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt hrad
  symm
  calc
    xOfZ (z x) = Real.sqrt (1 - (Real.sqrt (1 - x ^ 2)) ^ 2) := rfl
    _ = Real.sqrt (x ^ 2) := by rw [hsq]; congr 1 <;> ring
    _ = x := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hxp.1]
theorem gap3 (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt xOfZ (-z x / Real.sqrt (1 - z x ^ 2)) (z x) := by
  have hxp : 0 < x ∧ x < 1 := by
    simpa [branch] using hx
  have hprod : 0 < (1 - x) * (1 + x) :=
    mul_pos (sub_pos.mpr hxp.2) (by linarith)
  have hrad : 0 < 1 - x ^ 2 := by
    nlinarith
  have hzsq : z x ^ 2 = 1 - x ^ 2 := by
    simp [z, Real.sq_sqrt (le_of_lt hrad)]
  have hznonneg : 0 ≤ z x := by
    simp [z]
  have hzpos : 0 < z x := by
    simpa [z] using Real.sqrt_pos.2 hrad
  have hzlt : z x < 1 := by
    nlinarith
  have hzbranch : z x ∈ branch := by
    simpa [branch] using And.intro hzpos hzlt
  simpa [z, xOfZ] using hasDerivAt_z_on_branch (z x) hzbranch
theorem gap4 :
    AntiderivativesOn originalIntegrand = NegatedFamily := by
  have htrans : ∀ x ∈ branch,
      transformedIntegrand x = -originalIntegrand x := by
    intro x hx
    have hxp : 0 < x ∧ x < 1 := by
      simpa [branch] using hx
    have hprod : 0 < (1 - x) * (1 + x) :=
      mul_pos (sub_pos.mpr hxp.2) (by linarith)
    have hrad : 0 ≤ 1 - x ^ 2 := by
      nlinarith
    have hzsq : z x ^ 2 = 1 - x ^ 2 := by
      simp [z, Real.sq_sqrt hrad]
    have hzd := (hasDerivAt_z_on_branch x hx).deriv
    calc
      transformedIntegrand x = (1 - z x ^ 2) ^ 2 *
          (-x / Real.sqrt (1 - x ^ 2)) := by
            rw [transformedIntegrand, hzd]
      _ = -originalIntegrand x := by
            rw [hzsq]
            unfold originalIntegrand
            ring
  ext F
  change (∀ x ∈ branch, HasDerivAt F (originalIntegrand x) x) ↔
    ∃ G, (∀ x ∈ branch, HasDerivAt G (transformedIntegrand x) x) ∧
      ∀ x ∈ branch, F x = -G x
  constructor
  · intro hF
    refine ⟨fun y => -F y, ?_, ?_⟩
    · intro x hx
      simpa [htrans x hx] using (hF x hx).neg
    · intro x hx
      simp
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hneg : HasDerivAt (fun y => -G y)
        (-transformedIntegrand x) x := (hG x hx).neg
    have hopen : ∀ᶠ y in nhds x, y ∈ branch :=
      (show IsOpen branch by simpa [branch] using isOpen_Ioo).mem_nhds hx
    have hlocal : F =ᶠ[nhds x] fun y => -G y :=
      Filter.Eventually.mono hopen (fun y hy => hFG y hy)
    have hder := hneg.congr_of_eventuallyEq hlocal
    simpa [htrans x hx] using hder
theorem gap5 :
    NegatedFamily = PrimitiveFamily := by
  have hprimitive : ∀ x ∈ branch,
      HasDerivAt primitive (originalIntegrand x) x := by
    intro x hx
    have hxp : 0 < x ∧ x < 1 := by
      simpa [branch] using hx
    have hprod : 0 < (1 - x) * (1 + x) :=
      mul_pos (sub_pos.mpr hxp.2) (by linarith)
    have hrad : 0 ≤ 1 - x ^ 2 := by
      nlinarith
    have hzsq : z x ^ 2 = 1 - x ^ 2 := by
      simp [z, Real.sq_sqrt hrad]
    have hpoly : HasDerivAt
        (fun t : ℝ => -t + (2 / 3 : ℝ) * t ^ 3 - (1 / 5 : ℝ) * t ^ 5)
        (-1 + 2 * z x ^ 2 - z x ^ 4) (z x) := by
      convert
        (((hasDerivAt_id (z x)).neg.add
          ((hasDerivAt_const (z x) (2 / 3 : ℝ)).mul
            ((hasDerivAt_id (z x)).pow 3))).sub
          ((hasDerivAt_const (z x) (1 / 5 : ℝ)).mul
            ((hasDerivAt_id (z x)).pow 5))) using 1 <;>
        simp <;> ring
    have hcomp := hpoly.comp x (hasDerivAt_z_on_branch x hx)
    have hcoef :
        (-1 + 2 * z x ^ 2 - z x ^ 4) *
            (-x / Real.sqrt (1 - x ^ 2)) = originalIntegrand x := by
      rw [show z x ^ 4 = (z x ^ 2) ^ 2 by ring, hzsq]
      unfold originalIntegrand
      ring
    rw [hcoef] at hcomp
    change HasDerivAt
      (fun y : ℝ => -z y + 2 / 3 * z y ^ 3 - 1 / 5 * z y ^ 5)
      (originalIntegrand x) x
    exact hcomp
  rw [← gap4]
  ext F
  change (∀ x ∈ branch, HasDerivAt F (originalIntegrand x) x) ↔
    ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
  constructor
  · intro hF
    let c : ℝ := 1 / 2
    have hc : c ∈ branch := by
      norm_num [c, branch]
    have hzero : ∀ y ∈ branch,
        HasDerivAt (fun t => F t - primitive t) 0 y := by
      intro y hy
      simpa using (hF y hy).sub (hprimitive y hy)
    refine ⟨F c - primitive c, ?_⟩
    intro x hx
    have heq : F x - primitive x = F c - primitive c :=
      const_on_branch_of_hasDerivAt_zero
        (fun t => F t - primitive t) hzero hx hc
    linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    have hmodel : HasDerivAt (fun y => primitive y + C)
        (originalIntegrand x) x := by
      change HasDerivAt (primitive + fun _ : ℝ => C)
        (originalIntegrand x) x
      simpa only [add_zero] using
        (hprimitive x hx).add (hasDerivAt_const x C)
    have hopen : ∀ᶠ y in nhds x, y ∈ branch :=
      (show IsOpen branch by simpa [branch] using isOpen_Ioo).mem_nhds hx
    have hlocal : F =ᶠ[nhds x] fun y => primitive y + C :=
      Filter.Eventually.mono hopen (fun y hy => hFC y hy)
    exact hmodel.congr_of_eventuallyEq hlocal
theorem gap6 :
    AntiderivativesOn originalIntegrand = PrimitiveFamily := by
  exact gap4.trans gap5
theorem gap7 (x : ℝ) (hx : x ∈ branch) :
    z x = Real.sqrt (1 - x ^ 2) := by
  rfl

end
end ProofGap.Exercise1984
