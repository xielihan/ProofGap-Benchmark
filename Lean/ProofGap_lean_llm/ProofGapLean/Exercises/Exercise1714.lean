import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1714

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def substitution (x : ℝ) := 1 + x ^ (-5 : ℤ)
def integrand (x : ℝ) := x ^ 14 / (x ^ 5 + 1) ^ 4
def rewrittenIntegrand (x : ℝ) :=
  x ^ 14 / (x ^ 20 * (1 + x ^ (-5 : ℤ)) ^ 4)
def substitutedIntegrand (x : ℝ) :=
  -(1 / 5 : ℝ) *
    ((substitution x) ^ (-4 : ℤ) * deriv substitution x)
def primitive₁ (x : ℝ) :=
  (1 / 15 : ℝ) * (substitution x) ^ (-3 : ℤ)
def primitive₂ (x : ℝ) :=
  x ^ 15 / (15 * (x ^ 5 + 1) ^ 3)
def primitive₃ (x : ℝ) :=
  ((x ^ 5 + 1) ^ 3 - 3 * x ^ 10 - 3 * x ^ 5 - 1) /
    (15 * (x ^ 5 + 1) ^ 3)
def primitive₄ (x : ℝ) :=
  -(3 * x ^ 10 + 3 * x ^ 5 + 1) /
    (15 * (x ^ 5 + 1) ^ 3)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem hasDerivAt_substitution (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt substitution (-5 * x ^ (-6 : ℤ)) x := by
  have hxpos : 0 < x := by simpa [branch] using hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have h :=
    (hasDerivAt_const (x := x) (c := (1 : ℝ))).add
      (((hasDerivAt_id x).pow 5).inv (pow_ne_zero 5 hx0))
  convert h using 1 <;>
    simp [substitution, zpow_neg, hx0] <;>
    field_simp [hx0] <;>
    ring

private theorem antiderivativesOn_congr {f g : ℝ → ℝ}
    (h : ∀ x ∈ branch, f x = g x) :
    AntiderivativesOn f = AntiderivativesOn g := by
  ext F
  change (∀ x ∈ branch, HasDerivAt F (f x) x) ↔
    ∀ x ∈ branch, HasDerivAt F (g x) x
  constructor
  · intro hF x hx
    rw [← h x hx]
    exact hF x hx
  · intro hF x hx
    rw [h x hx]
    exact hF x hx

private theorem eq_one_of_hasDerivAt_zero
    (q : ℝ → ℝ) (hq : ∀ x ∈ branch, HasDerivAt q 0 x)
    {x : ℝ} (hx : x ∈ branch) : q x = q 1 := by
  have hxpos : 0 < x := by simpa [branch] using hx
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · have hcont : ContinuousOn q (Set.Icc x 1) := by
      intro y hy
      have hypos : 0 < y := lt_of_lt_of_le hxpos hy.1
      exact (hq y (by simpa [branch] using hypos)).continuousAt.continuousWithinAt
    have hhas : ∀ y ∈ Set.Ioo x 1,
        HasDerivAt q ((fun _ : ℝ => 0) y) y := by
      intro y hy
      have hypos : 0 < y := lt_trans hxpos hy.1
      simpa using hq y (by simpa [branch] using hypos)
    obtain ⟨c, hc, hs⟩ :=
      exists_hasDerivAt_eq_slope q (fun _ : ℝ => 0) hlt hcont hhas
    have hslope : (q 1 - q x) / (1 - x) = 0 := by
      linarith
    have hne : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
    have hn : q 1 - q x = 0 :=
      (div_eq_zero_iff.mp hslope).resolve_right hne
    exact (sub_eq_zero.mp hn).symm
  · simpa [heq]
  · have hcont : ContinuousOn q (Set.Icc 1 x) := by
      intro y hy
      have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy.1
      exact (hq y (by simpa [branch] using hypos)).continuousAt.continuousWithinAt
    have hhas : ∀ y ∈ Set.Ioo 1 x,
        HasDerivAt q ((fun _ : ℝ => 0) y) y := by
      intro y hy
      have hypos : 0 < y := lt_trans zero_lt_one hy.1
      simpa using hq y (by simpa [branch] using hypos)
    obtain ⟨c, hc, hs⟩ :=
      exists_hasDerivAt_eq_slope q (fun _ : ℝ => 0) hgt hcont hhas
    have hslope : (q x - q 1) / (x - 1) = 0 := by
      linarith
    have hne : x - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hgt)
    have hn : q x - q 1 = 0 :=
      (div_eq_zero_iff.mp hslope).resolve_right hne
    exact sub_eq_zero.mp hn

private theorem antiderivativesOn_eq_primitiveFamily
    (f p : ℝ → ℝ)
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    AntiderivativesOn f = PrimitiveFamily p := by
  ext F
  change (∀ x ∈ branch, HasDerivAt F (f x) x) ↔
    ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C
  constructor
  · intro hF
    refine ⟨F 1 - p 1, ?_⟩
    intro x hx
    have hzero : ∀ y ∈ branch,
        HasDerivAt (fun z => F z - p z) 0 y := by
      intro y hy
      convert (hF y hy).sub (hp y hy) using 1 <;> ring
    have hconst := eq_one_of_hasDerivAt_zero (fun z => F z - p z) hzero hx
    dsimp only at hconst
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hopen : IsOpen branch := by
      simpa [branch] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    have heq : F =ᶠ[nhds x] (fun y => p y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

private theorem primitiveFamily_eq_of_eq_add_const
    (p q : ℝ → ℝ) (K : ℝ)
    (h : ∀ x ∈ branch, p x = q x + K) :
    PrimitiveFamily p = PrimitiveFamily q := by
  ext F
  change (∃ C : ℝ, ∀ x ∈ branch, F x = p x + C) ↔
    ∃ C : ℝ, ∀ x ∈ branch, F x = q x + C
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨K + C, ?_⟩
    intro x hx
    rw [hC x hx, h x hx]
    ring
  · rintro ⟨C, hC⟩
    refine ⟨C - K, ?_⟩
    intro x hx
    rw [hC x hx, h x hx]
    ring

private theorem hasDerivAt_primitive₁ (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive₁ (substitutedIntegrand x) x := by
  have hs := hasDerivAt_substitution x hx
  have hxpos : 0 < x := by simpa [branch] using hx
  have hzpos : 0 < x ^ (-5 : ℤ) := zpow_pos hxpos _
  have hspos : 0 < substitution x := by
    simp only [substitution]
    linarith
  have hsne : substitution x ≠ 0 := ne_of_gt hspos
  have h := ((hs.pow 3).inv (pow_ne_zero 3 hsne)).const_mul (1 / 15 : ℝ)
  convert h using 1
  simp only [substitutedIntegrand, Pi.pow_apply]
  rw [hs.deriv]
  field_simp [zpow_neg, hsne]
  <;> ring

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn rewrittenIntegrand := by
  apply antiderivativesOn_congr
  intro x hx
  have hxpos : 0 < x := by simpa [branch] using hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  simp only [integrand, rewrittenIntegrand]
  field_simp [zpow_neg, hx0]
  <;> ring
theorem gap2 :
    AntiderivativesOn rewrittenIntegrand =
      AntiderivativesOn substitutedIntegrand := by
  apply antiderivativesOn_congr
  intro x hx
  have hxpos : 0 < x := by simpa [branch] using hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hden : x ^ 5 + 1 ≠ 0 := by
    have : 0 < x ^ 5 := pow_pos hxpos 5
    linarith
  have hsraw :
      1 + x ^ (-5 : ℤ) = (x ^ 5 + 1) / x ^ 5 := by
    field_simp [zpow_neg, hx0]
  have hs : substitution x = (x ^ 5 + 1) / x ^ 5 := by
    simpa [substitution] using hsraw
  have hd := (hasDerivAt_substitution x hx).deriv
  simp only [rewrittenIntegrand, substitutedIntegrand]
  rw [hd, hs, hsraw]
  field_simp [zpow_neg, hx0, hden]
  <;> ring
theorem gap3 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive₁ := by
  apply antiderivativesOn_eq_primitiveFamily
  intro x hx
  exact hasDerivAt_primitive₁ x hx
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily primitive₁ := by
  exact gap1.trans (gap2.trans gap3)
theorem gap5 :
    AntiderivativesOn integrand = PrimitiveFamily primitive₂ := by
  rw [gap4]
  apply primitiveFamily_eq_of_eq_add_const primitive₁ primitive₂ 0
  intro x hx
  have hxpos : 0 < x := by simpa [branch] using hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hpow : 0 < x ^ 5 := pow_pos hxpos 5
  have hden : x ^ 5 + 1 ≠ 0 := ne_of_gt (by linarith)
  simp only [add_zero, primitive₁, primitive₂, substitution]
  field_simp [zpow_neg, hx0, hden]
  <;> ring
theorem gap6 :
    PrimitiveFamily primitive₂ = PrimitiveFamily primitive₃ := by
  apply primitiveFamily_eq_of_eq_add_const primitive₂ primitive₃ 0
  intro x hx
  simp only [add_zero, primitive₂, primitive₃]
  ring
theorem gap7 :
    PrimitiveFamily primitive₃ = PrimitiveFamily primitive₄ := by
  apply primitiveFamily_eq_of_eq_add_const primitive₃ primitive₄ (1 / 15 : ℝ)
  intro x hx
  have hxpos : 0 < x := by simpa [branch] using hx
  have hpow : 0 < x ^ 5 := pow_pos hxpos 5
  have hden : x ^ 5 + 1 ≠ 0 := ne_of_gt (by linarith)
  simp only [primitive₃, primitive₄]
  field_simp [hden]
  <;> ring
theorem gap8 :
    AntiderivativesOn integrand = PrimitiveFamily primitive₄ := by
  exact gap5.trans (gap6.trans gap7)

end
end ProofGap.Exercise1714
