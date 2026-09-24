import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1692

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (x : ℝ) := 1 / Real.sqrt (1 + Real.exp (2 * x))
def substitutedIntegrand (x : ℝ) :=
  -(deriv (fun t : ℝ => Real.exp (-t)) x /
    Real.sqrt (1 + (Real.exp (-x)) ^ 2))
def primitive (x : ℝ) :=
  -Real.log (Real.exp (-x) + Real.sqrt (1 + Real.exp (-2 * x)))
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private lemma exp_neg_sq_eq (x : ℝ) :
    Real.exp (-2 * x) = (Real.exp (-x)) ^ 2 := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

private lemma integrand_eq_exp_neg_div (x : ℝ) :
    integrand x =
      Real.exp (-x) / Real.sqrt (1 + (Real.exp (-x)) ^ 2) := by
  have hmul : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    norm_num
  have htwo : Real.exp (2 * x) = (Real.exp x) ^ 2 := by
    calc
      Real.exp (2 * x) = Real.exp (x + x) := by congr 1 <;> ring
      _ = Real.exp x * Real.exp x := by rw [Real.exp_add]
      _ = (Real.exp x) ^ 2 := by ring
  have hprod : (Real.exp (-x)) ^ 2 * Real.exp (2 * x) = 1 := by
    calc
      (Real.exp (-x)) ^ 2 * Real.exp (2 * x) =
          (Real.exp (-x)) ^ 2 * (Real.exp x) ^ 2 := by rw [htwo]
      _ = (Real.exp (-x) * Real.exp x) ^ 2 := by ring
      _ = 1 := by rw [hmul]; norm_num
  have ha_sq :
      (Real.sqrt (1 + Real.exp (2 * x))) ^ 2 = 1 + Real.exp (2 * x) :=
    Real.sq_sqrt (by positivity)
  have hb_sq :
      (Real.sqrt (1 + (Real.exp (-x)) ^ 2)) ^ 2 =
        1 + (Real.exp (-x)) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hsq :
      (Real.exp (-x) * Real.sqrt (1 + Real.exp (2 * x))) ^ 2 =
        (Real.sqrt (1 + (Real.exp (-x)) ^ 2)) ^ 2 := by
    calc
      (Real.exp (-x) * Real.sqrt (1 + Real.exp (2 * x))) ^ 2 =
          (Real.exp (-x)) ^ 2 *
            (Real.sqrt (1 + Real.exp (2 * x))) ^ 2 := by ring
      _ = (Real.exp (-x)) ^ 2 * (1 + Real.exp (2 * x)) := by rw [ha_sq]
      _ = (Real.exp (-x)) ^ 2 + 1 := by
        rw [mul_add, hprod]
        ring
      _ = 1 + (Real.exp (-x)) ^ 2 := by ring
      _ = (Real.sqrt (1 + (Real.exp (-x)) ^ 2)) ^ 2 := by rw [hb_sq]
  have hcross :
      Real.exp (-x) * Real.sqrt (1 + Real.exp (2 * x)) =
        Real.sqrt (1 + (Real.exp (-x)) ^ 2) := by
    have hl :
        0 ≤ Real.exp (-x) * Real.sqrt (1 + Real.exp (2 * x)) :=
      mul_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _)
    have hr : 0 ≤ Real.sqrt (1 + (Real.exp (-x)) ^ 2) :=
      Real.sqrt_nonneg _
    nlinarith
  have ha0 : Real.sqrt (1 + Real.exp (2 * x)) ≠ 0 := by positivity
  have hb0 : Real.sqrt (1 + (Real.exp (-x)) ^ 2) ≠ 0 := by positivity
  unfold integrand
  apply (div_eq_div_iff ha0 hb0).2
  simpa using hcross.symm

private lemma substitutedIntegrand_eq_integrand (x : ℝ) :
    substitutedIntegrand x = integrand x := by
  have he :
      HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
    convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg using 1 <;> ring
  rw [integrand_eq_exp_neg_div]
  unfold substitutedIntegrand
  rw [he.deriv]
  ring

private lemma primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (substitutedIntegrand x) x := by
  have he :
      HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
    convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg using 1 <;> ring
  have hinner :
      HasDerivAt
        (fun t : ℝ => 1 + (Real.exp (-t)) ^ 2)
        (-2 * (Real.exp (-x)) ^ 2) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add (he.pow 2) using 1 <;> ring
  have hsqrt :
      HasDerivAt
        (fun t : ℝ => Real.sqrt (1 + (Real.exp (-t)) ^ 2))
        (-((Real.exp (-x)) ^ 2) /
          Real.sqrt (1 + (Real.exp (-x)) ^ 2)) x := by
    convert hinner.sqrt (by positivity) using 1 <;> ring
  have harg :
      HasDerivAt
        (fun t : ℝ =>
          Real.exp (-t) + Real.sqrt (1 + (Real.exp (-t)) ^ 2))
        (-Real.exp (-x) -
          (Real.exp (-x)) ^ 2 /
            Real.sqrt (1 + (Real.exp (-x)) ^ 2)) x := by
    convert he.add hsqrt using 1 <;> ring
  have hspos : 0 < Real.sqrt (1 + (Real.exp (-x)) ^ 2) := by positivity
  have hap :
      0 < Real.exp (-x) + Real.sqrt (1 + (Real.exp (-x)) ^ 2) := by
    positivity
  have hderiv :
      -((-Real.exp (-x) -
            (Real.exp (-x)) ^ 2 /
              Real.sqrt (1 + (Real.exp (-x)) ^ 2)) /
          (Real.exp (-x) + Real.sqrt (1 + (Real.exp (-x)) ^ 2))) =
        Real.exp (-x) / Real.sqrt (1 + (Real.exp (-x)) ^ 2) := by
    field_simp [ne_of_gt hspos, ne_of_gt hap]
    ring
  have halt :
      HasDerivAt
        (fun t : ℝ =>
          -Real.log
            (Real.exp (-t) + Real.sqrt (1 + (Real.exp (-t)) ^ 2)))
        (Real.exp (-x) / Real.sqrt (1 + (Real.exp (-x)) ^ 2)) x := by
    convert (harg.log (ne_of_gt hap)).neg using 1
    exact hderiv.symm
  have hp :
      primitive = fun t : ℝ =>
        -Real.log
          (Real.exp (-t) + Real.sqrt (1 + (Real.exp (-t)) ^ 2)) := by
    funext t
    unfold primitive
    rw [exp_neg_sq_eq]
  have hv :
      substitutedIntegrand x =
        Real.exp (-x) / Real.sqrt (1 + (Real.exp (-x)) ^ 2) :=
    (substitutedIntegrand_eq_integrand x).trans
      (integrand_eq_exp_neg_div x)
  rw [hp]
  simpa only [hv] using halt

private lemma eq_of_hasDerivAt_zero
    (G : ℝ → ℝ) (hG : ∀ x : ℝ, HasDerivAt G 0 x) (a b : ℝ) :
    G a = G b := by
  have hd : Differentiable ℝ G := fun x => (hG x).differentiableAt
  rcases lt_trichotomy a b with hab | hab | hba
  · obtain ⟨c, hc, hslope⟩ :=
      exists_hasDerivAt_eq_slope G (fun _ : ℝ => 0) hab
        hd.continuous.continuousOn
        (fun x hx => hG x)
    have hden : b - a ≠ 0 := by linarith
    field_simp [hden] at hslope
    linarith
  · simpa [hab]
  · obtain ⟨c, hc, hslope⟩ :=
      exists_hasDerivAt_eq_slope G (fun _ : ℝ => 0) hba
        hd.continuous.continuousOn
        (fun x hx => hG x)
    have hden : a - b ≠ 0 := by linarith
    field_simp [hden] at hslope
    linarith

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn substitutedIntegrand := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    simpa only [substitutedIntegrand_eq_integrand] using h x hx
  · intro h x hx
    simpa only [substitutedIntegrand_eq_integrand] using h x hx
theorem gap2 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro h
    let G : ℝ → ℝ := fun x => F x - primitive x
    have hG : ∀ x : ℝ, HasDerivAt G 0 x := by
      intro x
      dsimp [G]
      convert (h x (by simp [branch])).sub (primitive_hasDerivAt x) using 1 <;> ring
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hconst := eq_of_hasDerivAt_zero G hG x 0
    dsimp [G] at hconst
    linarith
  · rintro ⟨C, hC⟩
    have hfun : F = fun y => primitive y + C := by
      funext y
      exact hC y (by simp [branch])
    subst F
    intro x hx
    exact (primitive_hasDerivAt x).add_const C
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  rw [gap1, gap2]

end
end ProofGap.Exercise1692
