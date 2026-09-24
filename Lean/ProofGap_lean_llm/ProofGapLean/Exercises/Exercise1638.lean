import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1638

noncomputable section

def domain : Set ℝ := Set.Ioi 0
def original (x : ℝ) : ℝ :=
  Real.sqrt (x ^ 4 + x ^ (-4 : ℤ) + 2) / x ^ 3
def middle (x : ℝ) : ℝ := (x ^ 2 + 1 / x ^ 2) / x ^ 3
def simple (x : ℝ) : ℝ := 1 / x + 1 / x ^ 5
def primitive (x : ℝ) : ℝ := Real.log |x| - 1 / (4 * x ^ 4)
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem antiderivativesOn_congr {g h : ℝ → ℝ}
    (heq : ∀ x ∈ domain, g x = h x) :
    AntiderivativesOn g = AntiderivativesOn h := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hd⟩
    exact ⟨hF, fun x hx => (hd x hx).trans (heq x hx)⟩
  · rintro ⟨hF, hd⟩
    exact ⟨hF, fun x hx => (hd x hx).trans (heq x hx).symm⟩

private theorem primitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive (simple x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hlog : HasDerivAt (fun y : ℝ => Real.log y) (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hx0
  have hden : HasDerivAt (fun y : ℝ => 4 * y ^ 4) (16 * x ^ 3) x := by
    convert ((hasDerivAt_id x).pow 4).const_mul 4 using 1 <;> norm_num <;> ring
  have hden0 : 4 * x ^ 4 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 4 hx0)
  have hfrac :
      HasDerivAt (fun y : ℝ => 1 / (4 * y ^ 4)) (-1 / x ^ 5) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div hden hden0 using 1 <;>
      field_simp [hx0] <;> ring
  have hbase :
      HasDerivAt (fun y : ℝ => Real.log y - 1 / (4 * y ^ 4))
        (1 / x - (-1 / x ^ 5)) x :=
    hlog.sub hfrac
  have hsimple : simple x = 1 / x - (-1 / x ^ 5) := by
    unfold simple
    ring
  have hev :
      (fun y : ℝ => Real.log y - 1 / (4 * y ^ 4)) =ᶠ[nhds x] primitive := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    have hypos : 0 < y := hy
    simp only [primitive]
    rw [abs_of_pos hypos]
  rw [hsimple]
  exact hbase.congr_of_eventuallyEq hev.symm

theorem gap1 : AntiderivativesOn original = AntiderivativesOn middle := by
  apply antiderivativesOn_congr
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hxneg : x ^ (-4 : ℤ) = 1 / x ^ 4 := by
    rw [zpow_neg]
    norm_num [one_div]
    rfl
  have hsquare :
      x ^ 4 + x ^ (-4 : ℤ) + 2 = (x ^ 2 + 1 / x ^ 2) ^ 2 := by
    rw [hxneg]
    field_simp [hx0] <;> ring
  have hnonneg : 0 ≤ x ^ 2 + 1 / x ^ 2 :=
    add_nonneg (sq_nonneg x) (div_nonneg zero_le_one (sq_nonneg x))
  unfold original middle
  rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]

theorem gap2 : AntiderivativesOn middle = AntiderivativesOn simple := by
  apply antiderivativesOn_congr
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  unfold middle simple
  field_simp [hx0] <;> ring

theorem gap3 : AntiderivativesOn simple = PrimitiveFamily primitive := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hpdiff : DifferentiableOn ℝ primitive domain := by
      intro x hx
      apply DifferentiableAt.differentiableWithinAt
      exact (primitive_hasDerivAt hx).differentiableAt
    have hdiff : DifferentiableOn ℝ (fun x => F x - primitive x) domain :=
      hFdiff.sub hpdiff
    have hzero : ∀ x ∈ domain, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hFa : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
      have hz : HasDerivAt (fun y => F y - primitive y) 0 x := by
        convert hFa.hasDerivAt.sub (primitive_hasDerivAt hx) using 1
        rw [hFderiv x hx]
        ring
      exact hz.deriv
    have hone : (1 : ℝ) ∈ domain := by
      norm_num [domain]
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have heq : F x - primitive x = F 1 - primitive 1 :=
      isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hzero hx hone
    linarith
  · rintro ⟨C, hFC⟩
    have hhas : ∀ x ∈ domain, HasDerivAt F (simple x) x := by
      intro x hx
      have hev :
          F =ᶠ[nhds x] (fun y => primitive y + C) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact hFC y hy
      exact ((primitive_hasDerivAt hx).add_const C).congr_of_eventuallyEq hev
    refine ⟨?_, ?_⟩
    · intro x hx
      apply DifferentiableAt.differentiableWithinAt
      exact (hhas x hx).differentiableAt
    · intro x hx
      exact (hhas x hx).deriv

theorem gap4 : AntiderivativesOn original = PrimitiveFamily primitive := by
  calc
    AntiderivativesOn original = AntiderivativesOn middle := gap1
    _ = AntiderivativesOn simple := gap2
    _ = PrimitiveFamily primitive := gap3

end
end ProofGap.Exercise1638
