import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2158

noncomputable section

def branch : Set ℝ := Set.Ioo (-1) 1
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}
def s (x : ℝ) := Real.sqrt (1 - x ^ 2)
def integrand (x : ℝ) := s x * Real.arcsin x
def FirstReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn
      (fun x => x * (1 - x / s x * Real.arcsin x)),
    ∀ x ∈ branch, F x = x * s x * Real.arcsin x - G x}
def RecurrenceFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn integrand,
    ∃ H ∈ AntiderivativesOn (fun x => Real.arcsin x / s x),
    ∀ x ∈ branch,
      F x = x * s x * Real.arcsin x - x ^ 2 / 2 - G x + H x}
def ReducedRecurrenceFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn integrand,
    ∀ x ∈ branch,
      F x = x * s x * Real.arcsin x - x ^ 2 / 2 +
        1 / 2 * Real.arcsin x ^ 2 - G x}
def primitive (x : ℝ) :=
  x / 2 * s x * Real.arcsin x -
    x ^ 2 / 4 + 1 / 4 * Real.arcsin x ^ 2

private theorem hasDerivAt_of_eqOn_branch
    {f g : ℝ → ℝ} {f' x : ℝ} (hx : x ∈ branch)
    (hg : HasDerivAt g f' x)
    (hfg : ∀ y ∈ branch, f y = g y) :
    HasDerivAt f f' x := by
  apply hg.congr_of_eventuallyEq
  have hb : ∀ᶠ y in nhds x, y ∈ branch := by
    exact isOpen_Ioo.mem_nhds hx
  filter_upwards [hb] with y hy
  exact hfg y hy

private theorem branch_derivative_bundle (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => y * s y * Real.arcsin y)
      (integrand x + x * (1 - x / s x * Real.arcsin x)) x ∧
    HasDerivAt
      (fun y : ℝ => y * s y * Real.arcsin y - y ^ 2 / 2)
      (2 * integrand x - Real.arcsin x / s x) x ∧
    HasDerivAt (fun y : ℝ => 1 / 2 * Real.arcsin y ^ 2)
      (Real.arcsin x / s x) x ∧
    HasDerivAt
      (fun y : ℝ => y * s y * Real.arcsin y - y ^ 2 / 2 +
        1 / 2 * Real.arcsin y ^ 2)
      (2 * integrand x) x ∧
    HasDerivAt primitive (integrand x) x := by
  have hq : 0 < 1 - x ^ 2 := by
    have hp : 0 < (1 - x) * (1 + x) :=
      mul_pos (by linarith [hx.2]) (by linarith [hx.1])
    nlinarith
  have hs_pos : 0 < s x := by
    exact Real.sqrt_pos.2 hq
  have hs_ne : s x ≠ 0 := ne_of_gt hs_pos
  have hs_sq : s x ^ 2 = 1 - x ^ 2 := by
    simp only [s]
    exact Real.sq_sqrt (le_of_lt hq)
  have hinner : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub
      ((hasDerivAt_id x).pow 2) using 1 <;> norm_num <;> ring
  have hs0 : HasDerivAt
      (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      ((1 / (2 * Real.sqrt (1 - x ^ 2))) * (-2 * x)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hinner
  have hs : HasDerivAt s (-x / s x) x := by
    have hc :
        (1 / (2 * Real.sqrt (1 - x ^ 2))) * (-2 * x) =
          -x / s x := by
      simp only [s]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hq)]
    rw [← hc]
    simpa only [s] using hs0
  have ha : HasDerivAt Real.arcsin (1 / s x) x := by
    unfold s
    exact Real.hasDerivAt_arcsin (by linarith [hx.1]) (by linarith [hx.2])
  have hP0 : HasDerivAt
      (fun y : ℝ => y * s y * Real.arcsin y)
      (((1 * s x + x * (-x / s x)) * Real.arcsin x) +
        (x * s x) * (1 / s x)) x :=
    ((hasDerivAt_id x).mul hs).mul ha
  have hPcoef :
      ((1 * s x + x * (-x / s x)) * Real.arcsin x) +
          (x * s x) * (1 / s x) =
        integrand x + x * (1 - x / s x * Real.arcsin x) := by
    unfold integrand
    field_simp [hs_ne]
    rw [hs_sq]
    ring
  have hP : HasDerivAt (fun y : ℝ => y * s y * Real.arcsin y)
      (integrand x + x * (1 - x / s x * Real.arcsin x)) x :=
    hPcoef ▸ hP0
  have hx2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    convert ((hasDerivAt_id x).pow 2).div_const 2 using 1 <;> norm_num <;> ring
  have hA : HasDerivAt (fun y : ℝ => 1 / 2 * Real.arcsin y ^ 2)
      (Real.arcsin x / s x) x := by
    convert (ha.pow 2).const_mul (1 / 2) using 1 <;> ring
  have hBcoef :
      (integrand x + x * (1 - x / s x * Real.arcsin x)) - x =
        2 * integrand x - Real.arcsin x / s x := by
    unfold integrand
    field_simp [hs_ne]
    rw [hs_sq]
    ring
  have hB : HasDerivAt
      (fun y : ℝ => y * s y * Real.arcsin y - y ^ 2 / 2)
      (2 * integrand x - Real.arcsin x / s x) x :=
    hBcoef ▸ hP.sub hx2
  have hR : HasDerivAt
      (fun y : ℝ => y * s y * Real.arcsin y - y ^ 2 / 2 +
        1 / 2 * Real.arcsin y ^ 2)
      (2 * integrand x) x := by
    convert hB.add hA using 1 <;> ring
  have heq :
      (fun y : ℝ =>
        (1 / 2) *
          (y * s y * Real.arcsin y - y ^ 2 / 2 +
            1 / 2 * Real.arcsin y ^ 2)) = primitive := by
    funext y
    unfold primitive
    ring
  have hprim : HasDerivAt primitive (integrand x) x := by
    rw [← heq]
    convert hR.const_mul (1 / 2) using 1 <;> ring
  exact ⟨hP, hB, hA, hR, hprim⟩

theorem gap1 :
    AntiderivativesOn integrand = FirstReductionFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ G, (∀ x ∈ branch,
      HasDerivAt G (x * (1 - x / s x * Real.arcsin x)) x) ∧
      ∀ x ∈ branch,
        F x = x * s x * Real.arcsin x - G x
    let G := fun y : ℝ =>
      y * s y * Real.arcsin y - F y
    refine ⟨G, ?_, ?_⟩
    · intro x hx
      have hP := (branch_derivative_bundle x hx).1
      simpa [G] using hP.sub (hF x hx)
    · intro x hx
      dsimp [G]
      ring
  · intro h
    change ∃ G, (∀ x ∈ branch,
      HasDerivAt G (x * (1 - x / s x * Real.arcsin x)) x) ∧
      ∀ x ∈ branch,
        F x = x * s x * Real.arcsin x - G x at h
    rcases h with ⟨G, hG, hEq⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hP := (branch_derivative_bundle x hx).1
    have hd : HasDerivAt
        (fun y : ℝ => y * s y * Real.arcsin y - G y)
        (integrand x) x := by
      convert hP.sub (hG x hx) using 1 <;> ring
    exact hasDerivAt_of_eqOn_branch hx hd hEq
theorem gap2 :
    AntiderivativesOn integrand = RecurrenceFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ G, (∀ x ∈ branch, HasDerivAt G (integrand x) x) ∧
      ∃ H, (∀ x ∈ branch,
        HasDerivAt H (Real.arcsin x / s x) x) ∧
        ∀ x ∈ branch,
          F x = x * s x * Real.arcsin x - x ^ 2 / 2 - G x + H x
    let G := fun y : ℝ =>
      (y * s y * Real.arcsin y - y ^ 2 / 2 +
        1 / 2 * Real.arcsin y ^ 2) - F y
    let H := fun y : ℝ => 1 / 2 * Real.arcsin y ^ 2
    refine ⟨G, ?_, H, ?_, ?_⟩
    · intro x hx
      have hR := (branch_derivative_bundle x hx).2.2.2.1
      have hsub := hR.sub (hF x hx)
      have hcoef : 2 * integrand x - integrand x = integrand x := by
        ring
      rw [hcoef] at hsub
      simpa [G] using hsub
    · intro x hx
      have hA := (branch_derivative_bundle x hx).2.2.1
      simpa [H] using hA
    · intro x hx
      dsimp [G, H]
      ring
  · intro h
    change ∃ G, (∀ x ∈ branch, HasDerivAt G (integrand x) x) ∧
      ∃ H, (∀ x ∈ branch,
        HasDerivAt H (Real.arcsin x / s x) x) ∧
        ∀ x ∈ branch,
          F x = x * s x * Real.arcsin x - x ^ 2 / 2 - G x + H x at h
    rcases h with ⟨G, hG, H, hH, hEq⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hB := (branch_derivative_bundle x hx).2.1
    have hd : HasDerivAt
        (fun y : ℝ =>
          y * s y * Real.arcsin y - y ^ 2 / 2 - G y + H y)
        (integrand x) x := by
      convert (hB.sub (hG x hx)).add (hH x hx) using 1 <;> ring
    exact hasDerivAt_of_eqOn_branch hx hd hEq
theorem gap3 :
    AntiderivativesOn integrand = ReducedRecurrenceFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ G, (∀ x ∈ branch, HasDerivAt G (integrand x) x) ∧
      ∀ x ∈ branch,
        F x = x * s x * Real.arcsin x - x ^ 2 / 2 +
          1 / 2 * Real.arcsin x ^ 2 - G x
    let G := fun y : ℝ =>
      (y * s y * Real.arcsin y - y ^ 2 / 2 +
        1 / 2 * Real.arcsin y ^ 2) - F y
    refine ⟨G, ?_, ?_⟩
    · intro x hx
      have hR := (branch_derivative_bundle x hx).2.2.2.1
      have hsub := hR.sub (hF x hx)
      have hcoef : 2 * integrand x - integrand x = integrand x := by
        ring
      rw [hcoef] at hsub
      simpa [G] using hsub
    · intro x hx
      dsimp [G]
      ring
  · intro h
    change ∃ G, (∀ x ∈ branch, HasDerivAt G (integrand x) x) ∧
      ∀ x ∈ branch,
        F x = x * s x * Real.arcsin x - x ^ 2 / 2 +
          1 / 2 * Real.arcsin x ^ 2 - G x at h
    rcases h with ⟨G, hG, hEq⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hR := (branch_derivative_bundle x hx).2.2.2.1
    have hd : HasDerivAt
        (fun y : ℝ =>
          y * s y * Real.arcsin y - y ^ 2 / 2 +
            1 / 2 * Real.arcsin y ^ 2 - G y)
        (integrand x) x := by
      convert hR.sub (hG x hx) using 1 <;> ring
    exact hasDerivAt_of_eqOn_branch hx hd hEq
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
    let D := fun y : ℝ => F y - primitive y
    have hD : ∀ x ∈ branch, HasDerivAt D 0 x := by
      intro x hx
      have hp := (branch_derivative_bundle x hx).2.2.2.2
      simpa [D] using (hF x hx).sub hp
    have hdiff : DifferentiableOn ℝ D branch := by
      intro x hx
      exact (hD x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ branch, deriv D x = 0 := by
      intro x hx
      exact (hD x hx).deriv
    have hzero : (0 : ℝ) ∈ branch := by
      norm_num [branch]
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hc : D x = D 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiff hderiv hx hzero
    dsimp [D] at hc
    linarith
  · intro h
    change ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C at h
    rcases h with ⟨C, hEq⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hp := (branch_derivative_bundle x hx).2.2.2.2
    have hd : HasDerivAt (fun y : ℝ => primitive y + C)
        (integrand x) x := hp.add_const C
    exact hasDerivAt_of_eqOn_branch hx hd hEq

end
end ProofGap.Exercise2158
