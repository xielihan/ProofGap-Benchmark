import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ProofGap.Exercise1960

noncomputable section

def sec (t : ℝ) := 1 / Real.cos t
def angleBranch : Set ℝ := Set.Ioo (-Real.pi / 2) (Real.pi / 2)
def nonzeroBranch : Set ℝ := {x | x ≠ 0}
def substitution (x t : ℝ) : Prop :=
  t ∈ angleBranch ∧ x = Real.sqrt 2 * Real.tan t
def originalIntegrand (x : ℝ) :=
  Real.sqrt (x ^ 2 + 2) / (x ^ 2 + 1)
def rationalizedIntegrand (x : ℝ) :=
  (x ^ 2 + 2) / ((x ^ 2 + 1) * Real.sqrt (x ^ 2 + 2))
def splitIntegrand (x : ℝ) :=
  (1 + 1 / (x ^ 2 + 1)) / Real.sqrt (x ^ 2 + 2)
def logarithmicIntegrand (x : ℝ) := 1 / Real.sqrt (x ^ 2 + 2)
def residualIntegrand (x : ℝ) :=
  1 / ((x ^ 2 + 1) * Real.sqrt (x ^ 2 + 2))
def residualSecIntegrand (t : ℝ) :=
  sec t / (1 + 2 * Real.tan t ^ 2)
def residualCosIntegrand (t : ℝ) :=
  Real.cos t / (1 + Real.sin t ^ 2)
def residualSinIntegrand (t : ℝ) :=
  deriv Real.sin t / (1 + Real.sin t ^ 2)
def logarithmicPrimitive (x : ℝ) :=
  Real.log (x + Real.sqrt (x ^ 2 + 2))
def residualPrimitiveT (t : ℝ) := Real.arctan (Real.sin t)
def residualPrimitiveX (x : ℝ) :=
  Real.arctan (x / Real.sqrt (2 + x ^ 2))
def residualAlternative (x : ℝ) :=
  -Real.arctan (Real.sqrt (x ^ 2 + 2) / x)
def finalPrimitive (x : ℝ) :=
  logarithmicPrimitive x + residualAlternative x
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def PullbackFamily (map : ℝ → ℝ) (s : Set ℝ)
    (T : Set (ℝ → ℝ)) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ T, ∀ t ∈ s, F (map t) = G t}
def PiecewisePrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ Cneg Cpos : ℝ, ∀ x ∈ nonzeroBranch,
    F x = p x + if x < 0 then Cneg else Cpos}
def SplitFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn Set.univ logarithmicIntegrand,
    ∃ H ∈ AntiderivativesOn Set.univ residualIntegrand,
      ∀ x, F x = G x + H x}
def LogResidualFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn Set.univ residualIntegrand,
    ∀ x, F x = logarithmicPrimitive x + G x}

private theorem residualPrimitiveX_hasDerivAt (x : ℝ) :
    HasDerivAt residualPrimitiveX (residualIntegrand x) x := by
  have hrad : 0 < 2 + x ^ 2 := by positivity
  have hr : Real.sqrt (2 + x ^ 2) ≠ 0 := (Real.sqrt_pos.2 hrad).ne'
  have hinner : HasDerivAt (fun y : ℝ => 2 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (2 : ℝ)).add ((hasDerivAt_id x).pow 2) using 1 <;>
      simp <;> ring
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (2 + y ^ 2))
      (x / Real.sqrt (2 + x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt (by positivity : 2 + x ^ 2 ≠ 0)).comp x hinner
      using 1 <;>
      field_simp [hr] <;> ring
  unfold residualPrimitiveX residualIntegrand
  convert (Real.hasDerivAt_arctan
    (x / Real.sqrt (2 + x ^ 2))).comp x
      ((hasDerivAt_id x).div hs hr) using 1
  simp only [id]
  rw [show x ^ 2 + 2 = 2 + x ^ 2 by ring]
  field_simp [hr]
  nlinarith [Real.sq_sqrt hrad.le]

private theorem logarithmicPrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt logarithmicPrimitive (logarithmicIntegrand x) x := by
  have hrad : 0 < x ^ 2 + 2 := by positivity
  have hr : Real.sqrt (x ^ 2 + 2) ≠ 0 := (Real.sqrt_pos.2 hrad).ne'
  have hrsq : Real.sqrt (x ^ 2 + 2) ^ 2 = x ^ 2 + 2 :=
    Real.sq_sqrt hrad.le
  have harg : 0 < x + Real.sqrt (x ^ 2 + 2) := by
    have hnonneg := Real.sqrt_nonneg (x ^ 2 + 2)
    nlinarith
  have hinner : HasDerivAt (fun y : ℝ => y ^ 2 + 2) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).add_const 2 using 1 <;>
      simp <;> ring
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 + 2))
      (x / Real.sqrt (x ^ 2 + 2)) x := by
    convert (Real.hasDerivAt_sqrt (by positivity : x ^ 2 + 2 ≠ 0)).comp x hinner
      using 1 <;>
      field_simp [hr] <;> ring
  unfold logarithmicPrimitive logarithmicIntegrand
  convert (Real.hasDerivAt_log harg.ne').comp x ((hasDerivAt_id x).add hs) using 1
  field_simp [hr]
  nlinarith

theorem gap1 :
    AntiderivativesOn Set.univ originalIntegrand =
      AntiderivativesOn Set.univ rationalizedIntegrand := by
  have hfun : originalIntegrand = rationalizedIntegrand := by
    funext x
    have hq : 0 < x ^ 2 + 2 := by positivity
    have hs : Real.sqrt (x ^ 2 + 2) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
    have hd : x ^ 2 + 1 ≠ 0 := by positivity
    unfold originalIntegrand rationalizedIntegrand
    field_simp [hs, hd]
    nlinarith [Real.sq_sqrt hq.le]
  rw [hfun]
theorem gap2 :
    AntiderivativesOn Set.univ rationalizedIntegrand =
      AntiderivativesOn Set.univ splitIntegrand := by
  have hfun : rationalizedIntegrand = splitIntegrand := by
    funext x
    have hq : 0 < x ^ 2 + 2 := by positivity
    have hs : Real.sqrt (x ^ 2 + 2) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
    have hd : x ^ 2 + 1 ≠ 0 := by positivity
    unfold rationalizedIntegrand splitIntegrand
    field_simp [hs, hd]
    ring
  rw [hfun]
theorem gap3 :
    AntiderivativesOn Set.univ originalIntegrand =
      AntiderivativesOn Set.univ splitIntegrand := by
  rw [gap1, gap2]
theorem gap4 :
    AntiderivativesOn Set.univ originalIntegrand = SplitFamily := by
  have hp : residualPrimitiveX ∈
      AntiderivativesOn Set.univ residualIntegrand := by
    exact fun x _ => residualPrimitiveX_hasDerivAt x
  have hcoef : ∀ x,
      originalIntegrand x =
        logarithmicIntegrand x + residualIntegrand x := by
    intro x
    have hq : 0 < x ^ 2 + 2 := by positivity
    have hs : Real.sqrt (x ^ 2 + 2) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
    have hd : x ^ 2 + 1 ≠ 0 := by positivity
    unfold originalIntegrand logarithmicIntegrand residualIntegrand
    field_simp [hs, hd]
    nlinarith [Real.sq_sqrt hq.le]
  ext F
  constructor
  · intro hF
    refine ⟨fun x => F x - residualPrimitiveX x, ?_,
      residualPrimitiveX, hp, ?_⟩
    · intro x _
      convert (hF x (Set.mem_univ x)).sub (hp x (Set.mem_univ x)) using 1
      rw [hcoef x]
      ring
    · intro x
      ring
  · rintro ⟨G, hG, H, hH, hF⟩ x _
    have heq : F = fun y => G y + H y := by
      funext y
      exact hF y
    rw [heq]
    convert (hG x (Set.mem_univ x)).add (hH x (Set.mem_univ x)) using 1
    rw [hcoef x]
theorem gap5 :
    SplitFamily = LogResidualFamily := by
  ext F
  constructor
  · rintro ⟨G, hG, H, hH, hF⟩
    have hz : ∀ x, HasDerivAt
        (fun y => G y - logarithmicPrimitive y) 0 x := by
      intro x
      convert (hG x (Set.mem_univ x)).sub
        (logarithmicPrimitive_hasDerivAt x) using 1 <;> ring
    have hdiff : Differentiable ℝ
        (fun y => G y - logarithmicPrimitive y) :=
      fun x => (hz x).differentiableAt
    have hzero : ∀ x, deriv
        (fun y => G y - logarithmicPrimitive y) x = 0 :=
      fun x => (hz x).deriv
    let C := G 0 - logarithmicPrimitive 0
    have hC : ∀ x, G x - logarithmicPrimitive x = C :=
      fun x => is_const_of_deriv_eq_zero hdiff hzero x 0
    refine ⟨fun x => H x + C, ?_, ?_⟩
    · intro x _
      exact (hH x (Set.mem_univ x)).add_const C
    · intro x
      rw [hF x]
      have hxC := hC x
      dsimp [C] at hxC ⊢
      linarith
  · rintro ⟨G, hG, hF⟩
    exact ⟨logarithmicPrimitive,
      (fun x _ => logarithmicPrimitive_hasDerivAt x), G, hG, hF⟩
theorem gap6 :
    AntiderivativesOn Set.univ originalIntegrand = LogResidualFamily := by
  rw [gap4, gap5]
theorem gap7 (x t : ℝ) (h : substitution x t) :
    -Real.pi / 2 < t := by
  exact h.1.1
theorem gap8 (x t : ℝ) (h : substitution x t) :
    t < Real.pi / 2 := by
  exact h.1.2
theorem gap9 (x t : ℝ) (h : substitution x t) :
    -Real.pi / 2 < Real.pi / 2 := by
  exact (gap7 x t h).trans (gap8 x t h)
theorem gap10 (t : ℝ) (ht : t ∈ angleBranch) :
    HasDerivAt (fun u : ℝ => Real.sqrt 2 * Real.tan u)
      (Real.sqrt 2 * sec t ^ 2) t := by
  have hc : Real.cos t ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo (by simpa [angleBranch, neg_div] using ht)).ne'
  convert (Real.hasDerivAt_tan hc).const_mul (Real.sqrt 2) using 1 <;>
    simp [sec] <;> ring
theorem gap11 (x t : ℝ) (h : substitution x t) :
    Real.sqrt (x ^ 2 + 2) = Real.sqrt 2 * sec t := by
  rcases h with ⟨ht, rfl⟩
  have hcpos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo (by simpa [angleBranch, neg_div] using ht)
  have hc : Real.cos t ≠ 0 := hcpos.ne'
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq :
      (Real.sqrt 2 * sec t) ^ 2 =
        (Real.sqrt 2 * Real.tan t) ^ 2 + 2 := by
    unfold sec
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hc]
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hleft : 0 ≤ Real.sqrt ((Real.sqrt 2 * Real.tan t) ^ 2 + 2) :=
    Real.sqrt_nonneg _
  have hright : 0 ≤ Real.sqrt 2 * sec t := by
    exact mul_nonneg (Real.sqrt_nonneg _) (le_of_lt (one_div_pos.mpr hcpos))
  have hrad : 0 ≤ (Real.sqrt 2 * Real.tan t) ^ 2 + 2 := by positivity
  nlinarith [Real.sq_sqrt hrad]

private lemma sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
private lemma sqrt_two_ne : Real.sqrt 2 ≠ 0 := sqrt_two_pos.ne'
private lemma sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private lemma inverse_mem_branch (x : ℝ) :
    Real.arctan (x / Real.sqrt 2) ∈ angleBranch := by
  simpa [angleBranch, neg_div] using
    ⟨Real.neg_pi_div_two_lt_arctan (x / Real.sqrt 2),
      Real.arctan_lt_pi_div_two (x / Real.sqrt 2)⟩

private lemma map_inverse (x : ℝ) :
    Real.sqrt 2 * Real.tan (Real.arctan (x / Real.sqrt 2)) = x := by
  rw [Real.tan_arctan]
  field_simp [sqrt_two_ne]

private lemma inverse_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.arctan (y / Real.sqrt 2))
      ((1 / (1 + (x / Real.sqrt 2) ^ 2)) * (1 / Real.sqrt 2)) x := by
  exact (Real.hasDerivAt_arctan (x / Real.sqrt 2)).comp x
    ((hasDerivAt_id x).div_const (Real.sqrt 2))

private lemma inverse_coefficient (x : ℝ) :
    residualSecIntegrand (Real.arctan (x / Real.sqrt 2)) *
        ((1 / (1 + (x / Real.sqrt 2) ^ 2)) * (1 / Real.sqrt 2)) =
      residualIntegrand x := by
  let t := Real.arctan (x / Real.sqrt 2)
  have ht : t ∈ angleBranch := inverse_mem_branch x
  have hsub : substitution x t := ⟨ht, (map_inverse x).symm⟩
  have hsqrt := gap11 x t hsub
  have hcpos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo (by simpa [angleBranch, neg_div] using ht)
  have hc : Real.cos t ≠ 0 := hcpos.ne'
  have hx : x = Real.sqrt 2 * Real.tan t := hsub.2
  have hxtan : x / Real.sqrt 2 = Real.tan t := by
    rw [hx]
    field_simp [sqrt_two_ne]
  change residualSecIntegrand t *
      ((1 / (1 + (x / Real.sqrt 2) ^ 2)) * (1 / Real.sqrt 2)) =
    residualIntegrand x
  unfold residualSecIntegrand residualIntegrand
  rw [hxtan, hsqrt, hx, Real.tan_eq_sin_div_cos]
  unfold sec
  field_simp [sqrt_two_ne, hc]
  rw [sqrt_two_sq]
  nlinarith [Real.sin_sq_add_cos_sq t]
theorem gap12 :
    AntiderivativesOn Set.univ residualIntegrand =
      PullbackFamily (fun t => Real.sqrt 2 * Real.tan t) angleBranch
        (AntiderivativesOn angleBranch residualSecIntegrand) := by
  ext F
  constructor
  · intro hF
    refine ⟨fun t => F (Real.sqrt 2 * Real.tan t), ?_, ?_⟩
    · intro t ht
      have hsub : substitution (Real.sqrt 2 * Real.tan t) t := ⟨ht, rfl⟩
      convert (hF _ (Set.mem_univ _)).comp t (gap10 t ht) using 1
      unfold residualIntegrand residualSecIntegrand
      have hsqrt := gap11 _ t hsub
      have hrad : 0 < (Real.sqrt 2 * Real.tan t) ^ 2 + 2 := by positivity
      have hs : Real.sqrt ((Real.sqrt 2 * Real.tan t) ^ 2 + 2) ≠ 0 :=
        (Real.sqrt_pos.2 hrad).ne'
      rw [hsqrt]
      field_simp [sqrt_two_ne, hs]
      rw [sqrt_two_sq]
      ring
    · exact fun t _ => rfl
  · rintro ⟨G, hG, hEq⟩
    have hrepr : F = fun x => G (Real.arctan (x / Real.sqrt 2)) := by
      funext x
      have hx := hEq (Real.arctan (x / Real.sqrt 2)) (inverse_mem_branch x)
      change F (Real.sqrt 2 * Real.tan (Real.arctan (x / Real.sqrt 2))) =
        G (Real.arctan (x / Real.sqrt 2)) at hx
      rw [map_inverse x] at hx
      exact hx
    rw [hrepr]
    intro x _
    convert (hG _ (inverse_mem_branch x)).comp x (inverse_hasDerivAt x) using 1
    exact (inverse_coefficient x).symm
theorem gap13 :
    AntiderivativesOn angleBranch residualSecIntegrand =
      AntiderivativesOn angleBranch residualCosIntegrand := by
  have hfun : residualSecIntegrand = residualCosIntegrand := by
    funext t
    unfold residualSecIntegrand residualCosIntegrand sec
    rw [Real.tan_eq_sin_div_cos]
    by_cases hc : Real.cos t = 0
    · simp [hc]
    · field_simp [hc]
      nlinarith [Real.sin_sq_add_cos_sq t]
  rw [hfun]
theorem gap14 :
    AntiderivativesOn angleBranch residualCosIntegrand =
      AntiderivativesOn angleBranch residualSinIntegrand := by
  have hfun : residualCosIntegrand = residualSinIntegrand := by
    funext t
    unfold residualCosIntegrand residualSinIntegrand
    rw [(Real.hasDerivAt_sin t).deriv]
  rw [hfun]
theorem gap15 :
    AntiderivativesOn angleBranch residualSinIntegrand =
      PrimitiveFamilyOn angleBranch residualPrimitiveT := by
  have hp : ∀ t, HasDerivAt residualPrimitiveT (residualSinIntegrand t) t := by
    intro t
    unfold residualPrimitiveT residualSinIntegrand
    convert (Real.hasDerivAt_arctan (Real.sin t)).comp t
      (Real.hasDerivAt_sin t) using 1 <;>
      simp <;> ring
  ext F
  constructor
  · intro hF
    have hz : ∀ x ∈ angleBranch,
        HasDerivAt (fun y => F y - residualPrimitiveT y) 0 x := by
      intro x hx
      convert (hF x hx).sub (hp x) using 1 <;> ring
    have hdiff : DifferentiableOn ℝ
        (fun y => F y - residualPrimitiveT y) angleBranch :=
      fun x hx => (hz x hx).differentiableAt.differentiableWithinAt
    have hderiv : angleBranch.EqOn
        (deriv (fun y => F y - residualPrimitiveT y)) 0 :=
      fun x hx => (hz x hx).deriv
    obtain ⟨C, hC⟩ :=
      (show IsOpen angleBranch from by
        unfold angleBranch
        exact isOpen_Ioo).exists_is_const_of_deriv_eq_zero
        (show IsPreconnected angleBranch from by
          unfold angleBranch
          exact isPreconnected_Ioo) hdiff hderiv
    exact ⟨C, fun x hx => by
      have hxC : F x - residualPrimitiveT x = C := hC x hx
      linarith⟩
  · rintro ⟨C, hC⟩ x hx
    have heq : F =ᶠ[nhds x] (fun y => residualPrimitiveT y + C) := by
      filter_upwards [(show IsOpen angleBranch from by
        unfold angleBranch
        exact isOpen_Ioo).mem_nhds hx] with y hy
      exact hC y hy
    exact ((hp x).add_const C).congr_of_eventuallyEq heq
theorem gap16 :
    AntiderivativesOn Set.univ residualIntegrand =
      PullbackFamily (fun t => Real.sqrt 2 * Real.tan t) angleBranch
        (PrimitiveFamilyOn angleBranch residualPrimitiveT) := by
  rw [gap12, gap13, gap14, gap15]
theorem gap17 :
    AntiderivativesOn Set.univ residualIntegrand =
      PrimitiveFamilyOn Set.univ residualPrimitiveX := by
  have hp : ∀ x, HasDerivAt residualPrimitiveX (residualIntegrand x) x :=
    residualPrimitiveX_hasDerivAt
  ext F
  constructor
  · intro hF
    have hz : ∀ x, HasDerivAt (fun y => F y - residualPrimitiveX y) 0 x := by
      intro x
      convert (hF x (Set.mem_univ x)).sub (hp x) using 1 <;> ring
    obtain ⟨C, hC⟩ := (isOpen_univ : IsOpen (Set.univ : Set ℝ))
      |>.exists_is_const_of_deriv_eq_zero isPreconnected_univ
        (fun x _ => (hz x).differentiableAt.differentiableWithinAt)
        (fun x _ => (hz x).deriv)
    exact ⟨C, fun x _ => by
      have hxC : F x - residualPrimitiveX x = C := hC x (Set.mem_univ x)
      linarith⟩
  · rintro ⟨C, hC⟩ x _
    have hFx : F = fun y => residualPrimitiveX y + C := by
      funext y
      exact hC y (Set.mem_univ y)
    rw [hFx]
    exact (hp x).add_const C

private lemma residualAlternative_eq (x : ℝ) (hx : x ≠ 0) :
    residualAlternative x =
      residualPrimitiveX x + if x < 0 then Real.pi / 2 else -(Real.pi / 2) := by
  let u : ℝ := x / Real.sqrt (2 + x ^ 2)
  have hrpos : 0 < Real.sqrt (2 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hr : Real.sqrt (2 + x ^ 2) ≠ 0 := hrpos.ne'
  have hinv : u⁻¹ = Real.sqrt (x ^ 2 + 2) / x := by
    dsimp [u]
    rw [show x ^ 2 + 2 = 2 + x ^ 2 by ring]
    field_simp [hx, hr]
  by_cases hneg : x < 0
  · have hu : u < 0 := div_neg_of_neg_of_pos hneg hrpos
    rw [if_pos hneg]
    unfold residualAlternative residualPrimitiveX
    rw [show x / Real.sqrt (2 + x ^ 2) = u by rfl, ← hinv,
      Real.arctan_inv_of_neg hu]
    ring
  · have hpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hneg) hx.symm
    have hu : 0 < u := div_pos hpos hrpos
    rw [if_neg hneg]
    unfold residualAlternative residualPrimitiveX
    rw [show x / Real.sqrt (2 + x ^ 2) = u by rfl, ← hinv,
      Real.arctan_inv_of_pos hu]
    ring
theorem gap18 :
    PiecewisePrimitiveFamily residualPrimitiveX =
      PiecewisePrimitiveFamily residualAlternative := by
  ext F
  constructor
  · rintro ⟨Cneg, Cpos, hF⟩
    refine ⟨Cneg - Real.pi / 2, Cpos + Real.pi / 2, ?_⟩
    intro x hx
    have hrel := residualAlternative_eq x hx
    have hFx := hF x hx
    by_cases hneg : x < 0
    · rw [if_pos hneg] at hrel hFx ⊢
      linarith
    · rw [if_neg hneg] at hrel hFx ⊢
      linarith
  · rintro ⟨Cneg, Cpos, hF⟩
    refine ⟨Cneg + Real.pi / 2, Cpos - Real.pi / 2, ?_⟩
    intro x hx
    have hrel := residualAlternative_eq x hx
    have hFx := hF x hx
    by_cases hneg : x < 0
    · rw [if_pos hneg] at hrel hFx ⊢
      linarith
    · rw [if_neg hneg] at hrel hFx ⊢
      linarith
theorem gap19 :
    AntiderivativesOn nonzeroBranch residualIntegrand =
      PiecewisePrimitiveFamily residualAlternative := by
  rw [← gap18]
  ext F
  constructor
  · intro hF
    have hz : ∀ x ∈ nonzeroBranch,
        HasDerivAt (fun y => F y - residualPrimitiveX y) 0 x := by
      intro x hx
      convert (hF x hx).sub (residualPrimitiveX_hasDerivAt x) using 1 <;> ring
    obtain ⟨Cneg, hCneg⟩ := isOpen_Iio.exists_is_const_of_deriv_eq_zero
      isPreconnected_Iio
      (fun x hx => (hz x (by simpa [nonzeroBranch] using hx.ne)).differentiableAt
        |>.differentiableWithinAt)
      (fun x hx => (hz x (by simpa [nonzeroBranch] using hx.ne)).deriv)
    obtain ⟨Cpos, hCpos⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero
      isPreconnected_Ioi
      (fun x hx => (hz x (by simpa [nonzeroBranch] using hx.ne')).differentiableAt
        |>.differentiableWithinAt)
      (fun x hx => (hz x (by simpa [nonzeroBranch] using hx.ne')).deriv)
    refine ⟨Cneg, Cpos, ?_⟩
    intro x hx
    by_cases hneg : x < 0
    · rw [if_pos hneg]
      have h := hCneg x hneg
      linarith
    · rw [if_neg hneg]
      have hpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hneg) hx.symm
      have h := hCpos x hpos
      linarith
  · rintro ⟨Cneg, Cpos, hF⟩ x hx
    by_cases hneg : x < 0
    · have heq : F =ᶠ[nhds x] (fun y => residualPrimitiveX y + Cneg) := by
        filter_upwards [isOpen_Iio.mem_nhds hneg] with y hy
        have hh := hF y (by simpa [nonzeroBranch] using hy.ne)
        have hylt : y < 0 := hy
        rw [if_pos hylt] at hh
        exact hh
      exact ((residualPrimitiveX_hasDerivAt x).add_const Cneg).congr_of_eventuallyEq heq
    · have hxne : x ≠ 0 := by simpa [nonzeroBranch] using hx
      have hpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hneg) hxne.symm
      have heq : F =ᶠ[nhds x] (fun y => residualPrimitiveX y + Cpos) := by
        filter_upwards [isOpen_Ioi.mem_nhds hpos] with y hy
        have hh := hF y (by simpa [nonzeroBranch] using hy.ne')
        have hypos : 0 < y := hy
        rw [if_neg (not_lt_of_ge hypos.le)] at hh
        exact hh
      exact ((residualPrimitiveX_hasDerivAt x).add_const Cpos).congr_of_eventuallyEq heq

private lemma original_split (x : ℝ) :
    originalIntegrand x = logarithmicIntegrand x + residualIntegrand x := by
  have hq : 0 < x ^ 2 + 2 := by positivity
  have hs : Real.sqrt (x ^ 2 + 2) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hd : x ^ 2 + 1 ≠ 0 := by positivity
  unfold originalIntegrand logarithmicIntegrand residualIntegrand
  field_simp [hs, hd]
  nlinarith [Real.sq_sqrt hq.le]
theorem gap20 :
    AntiderivativesOn nonzeroBranch originalIntegrand =
      PiecewisePrimitiveFamily finalPrimitive := by
  ext F
  constructor
  · intro hF
    have hH : (fun y => F y - logarithmicPrimitive y) ∈
        AntiderivativesOn nonzeroBranch residualIntegrand := by
      intro x hx
      convert (hF x hx).sub (logarithmicPrimitive_hasDerivAt x) using 1
      rw [original_split x]
      ring
    rw [gap19] at hH
    rcases hH with ⟨Cneg, Cpos, hH⟩
    refine ⟨Cneg, Cpos, ?_⟩
    intro x hx
    have hh := hH x hx
    unfold finalPrimitive
    linarith
  · rintro ⟨Cneg, Cpos, hF⟩
    have hH : (fun y => F y - logarithmicPrimitive y) ∈
        PiecewisePrimitiveFamily residualAlternative := by
      refine ⟨Cneg, Cpos, ?_⟩
      intro x hx
      have hh := hF x hx
      unfold finalPrimitive at hh
      linarith
    rw [← gap19] at hH
    intro x hx
    have h := (logarithmicPrimitive_hasDerivAt x).add (hH x hx)
    convert h using 1
    · funext y
      simp [Pi.add_apply]
    · rw [original_split x]

end
end ProofGap.Exercise1960
