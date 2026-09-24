import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1821

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (x : ℝ) := x * (Real.sin x) ^ 2
def doubledIntegrand (x : ℝ) := x * (1 - Real.cos (2 * x))
def linearIntegrand (x : ℝ) := x
def oscillatoryIntegrand (x : ℝ) := x * Real.cos (2 * x)
def sineChainIntegrand (x : ℝ) :=
  x * deriv (fun t : ℝ => Real.sin (2 * t)) x
def sineIntegrand (x : ℝ) := Real.sin (2 * x)
def boundary₁ (x : ℝ) := (1 / 4 : ℝ) * x ^ 2
def boundary₂ (x : ℝ) :=
  boundary₁ x - x / 4 * Real.sin (2 * x)
def primitive (x : ℝ) :=
  boundary₂ x - (1 / 8 : ℝ) * Real.cos (2 * x)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def HalfFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn doubledIntegrand,
    ∀ x ∈ branch, F x = (1 / 2 : ℝ) * G x}
def SplitFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn linearIntegrand,
    ∃ H ∈ AntiderivativesOn oscillatoryIntegrand,
      ∀ x ∈ branch, F x = (1 / 2 : ℝ) * G x - (1 / 2 : ℝ) * H x}
def FirstByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn sineChainIntegrand,
    ∀ x ∈ branch, F x = boundary₁ x - (1 / 4 : ℝ) * G x}
def SecondByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn sineIntegrand,
    ∀ x ∈ branch, F x = boundary₂ x + (1 / 4 : ℝ) * G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private lemma doubled_eq_two_integrand (x : ℝ) :
    doubledIntegrand x = 2 * integrand x := by
  have htrig : 1 - Real.cos (2 * x) = 2 * (Real.sin x) ^ 2 := by
    rw [Real.cos_two_mul]
    have h := Real.sin_sq_add_cos_sq x
    nlinarith
  simp only [doubledIntegrand, integrand, htrig]
  ring

private lemma doubled_eq_linear_sub_oscillatory (x : ℝ) :
    doubledIntegrand x = linearIntegrand x - oscillatoryIntegrand x := by
  simp [doubledIntegrand, linearIntegrand, oscillatoryIntegrand]
  ring

private lemma integrand_eq_half_angle (x : ℝ) :
    integrand x = (1 / 2 : ℝ) * x * (1 - Real.cos (2 * x)) := by
  have h := doubled_eq_two_integrand x
  rw [doubled_eq_linear_sub_oscillatory] at h
  simp only [linearIntegrand, oscillatoryIntegrand] at h
  calc
    integrand x = (1 / 2 : ℝ) * (2 * integrand x) := by ring
    _ = (1 / 2 : ℝ) * (x - x * Real.cos (2 * x)) := by rw [← h]
    _ = (1 / 2 : ℝ) * x * (1 - Real.cos (2 * x)) := by ring

private lemma hasDerivAt_sine_chain (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (2 * t))
      (2 * Real.cos (2 * x)) x := by
  convert (Real.hasDerivAt_sin (2 * x)).comp x
    ((hasDerivAt_id x).const_mul 2) using 1 <;> ring

private lemma hasDerivAt_cosine_chain (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos (2 * t))
      (-2 * Real.sin (2 * x)) x := by
  convert (Real.hasDerivAt_cos (2 * x)).comp x
    ((hasDerivAt_id x).const_mul 2) using 1 <;> ring

private lemma sineChainIntegrand_eq (x : ℝ) :
    sineChainIntegrand x = 2 * oscillatoryIntegrand x := by
  rw [sineChainIntegrand, (hasDerivAt_sine_chain x).deriv]
  simp [oscillatoryIntegrand]
  ring

private def linearPrimitive (x : ℝ) : ℝ := x * x / 2

private lemma hasDerivAt_linearPrimitive (x : ℝ) :
    HasDerivAt linearPrimitive (linearIntegrand x) x := by
  convert ((hasDerivAt_id x).mul (hasDerivAt_id x)).div_const 2 using 1 <;>
    simp [linearPrimitive, linearIntegrand] <;> ring

private lemma hasDerivAt_boundary₁ (x : ℝ) :
    HasDerivAt boundary₁ ((1 / 2 : ℝ) * x) x := by
  convert ((hasDerivAt_id x).pow 2).const_mul (1 / 4 : ℝ) using 1 <;>
    simp [boundary₁] <;> ring

private lemma hasDerivAt_boundary₂ (x : ℝ) :
    HasDerivAt boundary₂
      (integrand x - (1 / 4 : ℝ) * sineIntegrand x) x := by
  have hp := ((hasDerivAt_id x).div_const 4).mul
    (hasDerivAt_sine_chain x)
  have h := (hasDerivAt_boundary₁ x).sub hp
  convert h using 1 <;>
    simp [boundary₂, sineIntegrand, integrand_eq_half_angle x] <;> ring

private lemma hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have h := (hasDerivAt_boundary₂ x).sub
    ((hasDerivAt_cosine_chain x).const_mul (1 / 8 : ℝ))
  convert h using 1 <;>
    simp [primitive, sineIntegrand] <;> ring

private theorem antiderivative_difference_constant
    {f g f' : ℝ → ℝ}
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (hg : ∀ x : ℝ, HasDerivAt g (f' x) x) :
    ∃ C : ℝ, ∀ x : ℝ, f x = g x + C := by
  let q : ℝ → ℝ := fun x => f x - g x
  have hq : ∀ x : ℝ, HasDerivAt q 0 x := by
    intro x
    convert (hf x).sub (hg x) using 1 <;> simp [q]
  have hdiff : Differentiable ℝ q := by
    intro x
    exact (hq x).differentiableAt
  have hzero : ∀ x : ℝ, deriv q x = 0 := by
    intro x
    exact (hq x).deriv
  refine ⟨q 0, fun x => ?_⟩
  have hx : q x = q 0 := by
    apply is_const_of_deriv_eq_zero hdiff hzero
  calc
    f x = q x + g x := by simp [q]
    _ = q 0 + g x := by rw [hx]
    _ = g x + q 0 := by ring

private theorem half_eq_antiderivatives :
    HalfFamily = AntiderivativesOn integrand := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    change ∀ x ∈ branch, HasDerivAt G (doubledIntegrand x) x at hG
    have hfun : F = fun t => (1 / 2 : ℝ) * G t := by
      funext t
      exact hFG t (Set.mem_univ t)
    intro x hx
    rw [hfun]
    have h := (hG x hx).const_mul (1 / 2 : ℝ)
    convert h using 1
    rw [doubled_eq_two_integrand]
    ring
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ G ∈ AntiderivativesOn doubledIntegrand,
      ∀ x ∈ branch, F x = (1 / 2 : ℝ) * G x
    refine ⟨fun t => 2 * F t, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun t => 2 * F t) (doubledIntegrand x) x
      intro x hx
      have h := (hF x hx).const_mul 2
      convert h using 1
      rw [doubled_eq_two_integrand]
    · intro x hx
      ring

private theorem split_eq_antiderivatives :
    SplitFamily = AntiderivativesOn integrand := by
  ext F
  constructor
  · rintro ⟨G, hG, H, hH, hFGH⟩
    change ∀ x ∈ branch, HasDerivAt G (linearIntegrand x) x at hG
    change ∀ x ∈ branch, HasDerivAt H (oscillatoryIntegrand x) x at hH
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    have hfun : F = fun t =>
        (1 / 2 : ℝ) * G t - (1 / 2 : ℝ) * H t := by
      funext t
      exact hFGH t (Set.mem_univ t)
    intro x hx
    rw [hfun]
    have h := ((hG x hx).const_mul (1 / 2 : ℝ)).sub
      ((hH x hx).const_mul (1 / 2 : ℝ))
    convert h using 1
    have hd : 2 * integrand x =
        linearIntegrand x - oscillatoryIntegrand x := by
      rw [← doubled_eq_two_integrand x]
      exact doubled_eq_linear_sub_oscillatory x
    linarith
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ G ∈ AntiderivativesOn linearIntegrand,
      ∃ H ∈ AntiderivativesOn oscillatoryIntegrand,
        ∀ x ∈ branch,
          F x = (1 / 2 : ℝ) * G x - (1 / 2 : ℝ) * H x
    refine ⟨linearPrimitive, ?_,
      (fun t => linearPrimitive t - 2 * F t), ?_, ?_⟩
    · intro x hx
      exact hasDerivAt_linearPrimitive x
    · intro x hx
      have h := (hasDerivAt_linearPrimitive x).sub
        ((hF x hx).const_mul 2)
      convert h using 1
      have hd : 2 * integrand x =
          linearIntegrand x - oscillatoryIntegrand x := by
        rw [← doubled_eq_two_integrand x]
        exact doubled_eq_linear_sub_oscillatory x
      linarith
    · intro x hx
      ring

private theorem first_eq_antiderivatives :
    FirstByPartsFamily = AntiderivativesOn integrand := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    change ∀ x ∈ branch,
      HasDerivAt G (sineChainIntegrand x) x at hG
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    have hfun : F = fun t =>
        boundary₁ t - (1 / 4 : ℝ) * G t := by
      funext t
      exact hFG t (Set.mem_univ t)
    intro x hx
    rw [hfun]
    have h := (hasDerivAt_boundary₁ x).sub
      ((hG x hx).const_mul (1 / 4 : ℝ))
    convert h using 1
    rw [sineChainIntegrand_eq]
    simp [oscillatoryIntegrand, integrand_eq_half_angle x]
    ring
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ G ∈ AntiderivativesOn sineChainIntegrand,
      ∀ x ∈ branch,
        F x = boundary₁ x - (1 / 4 : ℝ) * G x
    refine ⟨fun t => 4 * (boundary₁ t - F t), ?_, ?_⟩
    · intro x hx
      have h := ((hasDerivAt_boundary₁ x).sub (hF x hx)).const_mul 4
      convert h using 1
      rw [sineChainIntegrand_eq]
      simp [oscillatoryIntegrand, integrand_eq_half_angle x]
      ring
    · intro x hx
      ring

private theorem second_eq_antiderivatives :
    SecondByPartsFamily = AntiderivativesOn integrand := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    change ∀ x ∈ branch,
      HasDerivAt G (sineIntegrand x) x at hG
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    have hfun : F = fun t =>
        boundary₂ t + (1 / 4 : ℝ) * G t := by
      funext t
      exact hFG t (Set.mem_univ t)
    intro x hx
    rw [hfun]
    have h := (hasDerivAt_boundary₂ x).add
      ((hG x hx).const_mul (1 / 4 : ℝ))
    convert h using 1 <;> ring
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ G ∈ AntiderivativesOn sineIntegrand,
      ∀ x ∈ branch,
        F x = boundary₂ x + (1 / 4 : ℝ) * G x
    refine ⟨fun t => 4 * (F t - boundary₂ t), ?_, ?_⟩
    · intro x hx
      have h := ((hF x hx).sub (hasDerivAt_boundary₂ x)).const_mul 4
      convert h using 1 <;> ring
    · intro x hx
      ring

private theorem antiderivatives_eq_primitive :
    AntiderivativesOn integrand = PrimitiveFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
    have hfAll : ∀ x : ℝ, HasDerivAt F (integrand x) x := by
      intro x
      exact hF x (Set.mem_univ x)
    obtain ⟨C, hC⟩ := antiderivative_difference_constant
      hfAll hasDerivAt_primitive
    exact ⟨C, fun x hx => hC x⟩
  · rintro ⟨C, hFC⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    have hfun : F = fun t => primitive t + C := by
      funext t
      exact hFC t (Set.mem_univ t)
    intro x hx
    rw [hfun]
    simpa using (hasDerivAt_primitive x).const_add C

theorem gap1 :
    AntiderivativesOn integrand = HalfFamily := by
  exact half_eq_antiderivatives.symm
theorem gap2 :
    HalfFamily = SplitFamily := by
  exact half_eq_antiderivatives.trans split_eq_antiderivatives.symm
theorem gap3 :
    SplitFamily = FirstByPartsFamily := by
  exact split_eq_antiderivatives.trans first_eq_antiderivatives.symm
theorem gap4 :
    AntiderivativesOn integrand = FirstByPartsFamily := by
  exact gap1.trans (gap2.trans gap3)
theorem gap5 :
    AntiderivativesOn integrand = SecondByPartsFamily := by
  exact second_eq_antiderivatives.symm
theorem gap6 :
    SecondByPartsFamily = PrimitiveFamily := by
  exact second_eq_antiderivatives.trans antiderivatives_eq_primitive
theorem gap7 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  exact antiderivatives_eq_primitive

end
end ProofGap.Exercise1821
