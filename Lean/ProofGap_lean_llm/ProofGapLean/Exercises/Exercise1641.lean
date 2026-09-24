import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1641

noncomputable section

def domain : Set ℝ := Set.Ioi 1
def original (x : ℝ) : ℝ := (x ^ 2 + 3) / (x ^ 2 - 1)
def simple (x : ℝ) : ℝ := 1 + 4 / (x ^ 2 - 1)
def primitive (x : ℝ) : ℝ :=
  x + 2 * Real.log |(x - 1) / (x + 1)|
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem primitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive (simple x) x := by
  have hopen : IsOpen domain := by
    simpa [domain] using isOpen_Ioi
  have hx1 : 1 < x := by simpa [domain] using hx
  have hxm : 0 < x - 1 := by linarith
  have hxp : 0 < x + 1 := by linarith
  have hxp0 : x + 1 ≠ 0 := ne_of_gt hxp
  have hq : 0 < (x - 1) / (x + 1) := div_pos hxm hxp
  have hden : x ^ 2 - 1 ≠ 0 := by
    have : 0 < x ^ 2 - 1 := by nlinarith
    exact ne_of_gt this
  have hn : HasDerivAt (fun y : ℝ => y - 1) 1 x := by
    simpa only [sub_zero] using
      ((hasDerivAt_id x).sub (hasDerivAt_const x (1 : ℝ)))
  have hd : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
    simpa only [add_zero] using
      ((hasDerivAt_id x).add (hasDerivAt_const x (1 : ℝ)))
  have hr0 : HasDerivAt (fun y : ℝ => (y - 1) / (y + 1))
      (((x + 1) - (x - 1)) / (x + 1) ^ 2) x := by
    simpa only [one_mul, mul_one] using hn.div hd hxp0
  have hcalc : ((x + 1) - (x - 1)) / (x + 1) ^ 2 =
      2 / (x + 1) ^ 2 := by
    ring
  have hr : HasDerivAt (fun y : ℝ => (y - 1) / (y + 1))
      (2 / (x + 1) ^ 2) x := by
    rw [hcalc] at hr0
    exact hr0
  have hl : HasDerivAt (fun y : ℝ => Real.log ((y - 1) / (y + 1)))
      (((x - 1) / (x + 1))⁻¹ * (2 / (x + 1) ^ 2)) x := by
    exact (Real.hasDerivAt_log hq.ne').comp x hr
  have heq : primitive =ᶠ[nhds x]
      ((id : ℝ → ℝ) + fun y : ℝ => 2 * Real.log ((y - 1) / (y + 1))) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    have hy1 : 1 < y := by simpa [domain] using hy
    have hym : 0 < y - 1 := by linarith
    have hyp : 0 < y + 1 := by linarith
    have hyq : 0 < (y - 1) / (y + 1) := div_pos hym hyp
    simp [primitive, abs_of_pos hyq]
  have hp : HasDerivAt primitive
      (1 + 2 * (((x - 1) / (x + 1))⁻¹ * (2 / (x + 1) ^ 2))) x := by
    exact ((hasDerivAt_id x).add (hl.const_mul 2)).congr_of_eventuallyEq heq
  convert hp using 1
  dsimp [simple]
  field_simp [hxp0, hden, ne_of_gt hxm]
  <;> ring

theorem gap1 : AntiderivativesOn original = AntiderivativesOn simple := by
  have hEq : ∀ x ∈ domain, original x = simple x := by
    intro x hx
    have hx1 : 1 < x := by simpa [domain] using hx
    have hxm : 0 < x - 1 := by linarith
    have hxp : 0 < x + 1 := by linarith
    have hprod : 0 < (x - 1) * (x + 1) := mul_pos hxm hxp
    have hden : x ^ 2 - 1 ≠ 0 := by
      have : 0 < x ^ 2 - 1 := by nlinarith
      exact ne_of_gt this
    unfold original simple
    field_simp [hden]
    ring
  ext F
  constructor
  · rintro ⟨hF, hder⟩
    refine ⟨hF, ?_⟩
    intro x hx
    simpa [hEq x hx] using hder x hx
  · rintro ⟨hF, hder⟩
    refine ⟨hF, ?_⟩
    intro x hx
    simpa [hEq x hx] using hder x hx

theorem gap2 : AntiderivativesOn simple = PrimitiveFamily primitive := by
  have hopen : IsOpen domain := by
    simpa [domain] using isOpen_Ioi
  have htwo : (2 : ℝ) ∈ domain := by
    norm_num [domain]
  ext F
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    let H : ℝ → ℝ := fun y => F y - primitive y
    have hH : ∀ y ∈ domain, HasDerivAt H 0 y := by
      intro y hy
      have hFat : HasDerivAt F (simple y) y := by
        have hd := (hFdiff y hy).differentiableAt (hopen.mem_nhds hy)
        simpa [hFderiv y hy] using hd.hasDerivAt
      simpa [H] using hFat.sub (primitive_hasDerivAt hy)
    have hconst : ∀ x ∈ domain, H x = H 2 := by
      intro x hx
      rcases lt_trichotomy x 2 with hlt | heq | hgt
      · have hcont : ContinuousOn H (Set.Icc x 2) := by
          intro y hy
          have hydom : y ∈ domain := by
            have hx1 : 1 < x := by simpa [domain] using hx
            simpa [domain] using lt_of_lt_of_le hx1 hy.1
          exact (hH y hydom).continuousAt.continuousWithinAt
        have hdiff : DifferentiableOn ℝ H (Set.Ioo x 2) := by
          intro y hy
          have hydom : y ∈ domain := by
            have hx1 : 1 < x := by simpa [domain] using hx
            simpa [domain] using lt_trans hx1 hy.1
          exact (hH y hydom).differentiableAt.differentiableWithinAt
        obtain ⟨c, hc, hcder⟩ := exists_deriv_eq_slope H hlt hcont hdiff
        have hcdom : c ∈ domain := by
          have hx1 : 1 < x := by simpa [domain] using hx
          simpa [domain] using lt_trans hx1 hc.1
        have hzero : deriv H c = 0 := (hH c hcdom).deriv
        rw [hzero] at hcder
        have hne : (2 : ℝ) - x ≠ 0 := by linarith
        field_simp [hne] at hcder
        linarith
      · subst x
        rfl
      · have hcont : ContinuousOn H (Set.Icc 2 x) := by
          intro y hy
          have hydom : y ∈ domain := by
            have : (1 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy.1
            simpa [domain] using this
          exact (hH y hydom).continuousAt.continuousWithinAt
        have hdiff : DifferentiableOn ℝ H (Set.Ioo 2 x) := by
          intro y hy
          have hydom : y ∈ domain := by
            have : (1 : ℝ) < y := lt_trans (by norm_num) hy.1
            simpa [domain] using this
          exact (hH y hydom).differentiableAt.differentiableWithinAt
        obtain ⟨c, hc, hcder⟩ := exists_deriv_eq_slope H hgt hcont hdiff
        have hcdom : c ∈ domain := by
          have : (1 : ℝ) < c := lt_trans (by norm_num) hc.1
          simpa [domain] using this
        have hzero : deriv H c = 0 := (hH c hcdom).deriv
        rw [hzero] at hcder
        have hne : x - (2 : ℝ) ≠ 0 := by linarith
        field_simp [hne] at hcder
        linarith
    refine ⟨H 2, ?_⟩
    intro x hx
    have heq := hconst x hx
    dsimp [H] at heq ⊢
    linarith
  · rintro ⟨C, hFC⟩
    have hFat : ∀ x ∈ domain, HasDerivAt F (simple x) x := by
      intro x hx
      have heq :
          (primitive + fun _ : ℝ => C) =ᶠ[nhds x] F := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        exact (hFC y hy).symm
      have hb := ((primitive_hasDerivAt hx).add
        (hasDerivAt_const x C)).congr_of_eventuallyEq heq.symm
      simpa only [add_zero] using hb
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hFat x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFat x hx).deriv

theorem gap3 : AntiderivativesOn original = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1641
