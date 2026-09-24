import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1859

noncomputable section

def domain : Set ℝ := Set.Ioi (Real.sqrt 2)

def integrand (x : ℝ) : ℝ :=
  1 / ((x - 1) * Real.sqrt (x ^ 2 - 2))

def transformedIntegrand (x : ℝ) : ℝ :=
  (1 / (x - 1) ^ 2) /
    Real.sqrt (1 + 2 / (x - 1) - 1 / (x - 1) ^ 2)

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def substitutionPrimitive (x : ℝ) : ℝ :=
  -Real.arcsin ((1 / (x - 1) - 1) / Real.sqrt 2)

def primitive (x : ℝ) : ℝ :=
  Real.arcsin ((x - 2) / (|x - 1| * Real.sqrt 2))

private lemma domain_sub_pos {x : ℝ} (hx : x ∈ domain) : 0 < x - 1 := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  change Real.sqrt 2 < x at hx
  nlinarith

private lemma radicand_pos {x : ℝ} (hx : x ∈ domain) : 0 < x ^ 2 - 2 := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  change Real.sqrt 2 < x at hx
  nlinarith [sq_nonneg (x - Real.sqrt 2)]

private lemma transformed_arg_pos {x : ℝ} (hx : x ∈ domain) :
    0 < 1 + 2 / (x - 1) - 1 / (x - 1) ^ 2 := by
  have hy : 0 < x - 1 := domain_sub_pos hx
  have hb : 0 < x ^ 2 - 2 := radicand_pos hx
  have hid :
      1 + 2 / (x - 1) - 1 / (x - 1) ^ 2 =
        (x ^ 2 - 2) / (x - 1) ^ 2 := by
    field_simp [hy.ne']
    ring
  rw [hid]
  positivity

private lemma sqrt_transformed_eq (x : ℝ) (hx : x ∈ domain) :
    Real.sqrt (1 + 2 / (x - 1) - 1 / (x - 1) ^ 2) =
      Real.sqrt (x ^ 2 - 2) / (x - 1) := by
  have hy : 0 < x - 1 := domain_sub_pos hx
  have hb : 0 < x ^ 2 - 2 := radicand_pos hx
  have ha : 0 < 1 + 2 / (x - 1) - 1 / (x - 1) ^ 2 :=
    transformed_arg_pos hx
  have hsq :
      ((x - 1) * Real.sqrt
        (1 + 2 / (x - 1) - 1 / (x - 1) ^ 2)) ^ 2 =
        (Real.sqrt (x ^ 2 - 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt ha), Real.sq_sqrt (le_of_lt hb)]
    field_simp [hy.ne']
    ring
  have hmul :
      (x - 1) * Real.sqrt
        (1 + 2 / (x - 1) - 1 / (x - 1) ^ 2) =
        Real.sqrt (x ^ 2 - 2) := by
    have hsa : 0 ≤ Real.sqrt
        (1 + 2 / (x - 1) - 1 / (x - 1) ^ 2) := Real.sqrt_nonneg _
    have hsb : 0 ≤ Real.sqrt (x ^ 2 - 2) := Real.sqrt_nonneg _
    have hleft : 0 ≤ (x - 1) * Real.sqrt
        (1 + 2 / (x - 1) - 1 / (x - 1) ^ 2) :=
      mul_nonneg (le_of_lt hy) hsa
    nlinarith
  apply (eq_div_iff hy.ne').2
  simpa [mul_comm] using hmul

private lemma integrands_eq (x : ℝ) (hx : x ∈ domain) :
    integrand x = transformedIntegrand x := by
  have hy : 0 < x - 1 := domain_sub_pos hx
  have hb : 0 < x ^ 2 - 2 := radicand_pos hx
  have hsb : Real.sqrt (x ^ 2 - 2) ≠ 0 :=
    (Real.sqrt_pos.2 hb).ne'
  unfold integrand transformedIntegrand
  rw [sqrt_transformed_eq x hx]
  field_simp [hy.ne', hsb]

private lemma substitution_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt substitutionPrimitive (transformedIntegrand x) x := by
  have hy : 0 < x - 1 := domain_sub_pos hx
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ha : 0 < 1 + 2 / (x - 1) - 1 / (x - 1) ^ 2 :=
    transformed_arg_pos hx
  let q : ℝ := (1 / (x - 1) - 1) / Real.sqrt 2
  have haeq :
      1 + 2 / (x - 1) - 1 / (x - 1) ^ 2 = 2 * (1 - q ^ 2) := by
    dsimp [q]
    field_simp [hy.ne', hs2.ne']
    rw [hs2sq]
    ring
  have hq_sq : q ^ 2 < 1 := by
    nlinarith
  have hq_lower : -1 < q := by
    nlinarith [sq_nonneg (q + 1)]
  have hq_upper : q < 1 := by
    nlinarith [sq_nonneg (q - 1)]
  have hbase :
      HasDerivAt (fun u : ℝ => 1 / (u - 1))
        (-1 / (x - 1) ^ 2) x := by
    simpa [one_div] using (((hasDerivAt_id x).sub_const 1).inv hy.ne')
  have hq_deriv :
      HasDerivAt
        (fun u : ℝ => (1 / (u - 1) - 1) / Real.sqrt 2)
        ((-1 / (x - 1) ^ 2) / Real.sqrt 2) x := by
    simpa using (hbase.sub_const 1).div_const (Real.sqrt 2)
  have hcomp :
      HasDerivAt
        (fun u : ℝ => Real.arcsin
          ((1 / (u - 1) - 1) / Real.sqrt 2))
        ((1 / Real.sqrt (1 - q ^ 2)) *
          ((-1 / (x - 1) ^ 2) / Real.sqrt 2)) x := by
    simpa [q] using
      (Real.hasDerivAt_arcsin (ne_of_gt hq_lower) (ne_of_lt hq_upper)).comp
        x hq_deriv
  have hone : 0 < 1 - q ^ 2 := by
    linarith
  have hroot :
      Real.sqrt (1 + 2 / (x - 1) - 1 / (x - 1) ^ 2) =
        Real.sqrt 2 * Real.sqrt (1 - q ^ 2) := by
    have hsq :
        (Real.sqrt (1 + 2 / (x - 1) - 1 / (x - 1) ^ 2)) ^ 2 =
          (Real.sqrt 2 * Real.sqrt (1 - q ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt (le_of_lt ha), mul_pow, hs2sq,
        Real.sq_sqrt (le_of_lt hone)]
      exact haeq
    have hl : 0 ≤ Real.sqrt
        (1 + 2 / (x - 1) - 1 / (x - 1) ^ 2) := Real.sqrt_nonneg _
    have hr : 0 ≤ Real.sqrt 2 * Real.sqrt (1 - q ^ 2) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  have hcoef :
      -((1 / Real.sqrt (1 - q ^ 2)) *
          ((-1 / (x - 1) ^ 2) / Real.sqrt 2)) =
        transformedIntegrand x := by
    unfold transformedIntegrand
    rw [hroot]
    field_simp [hy.ne', hs2.ne', (Real.sqrt_pos.2 hone).ne']
  have hn := hcomp.neg
  rw [hcoef] at hn
  have hfun : substitutionPrimitive =
      -(fun u : ℝ => Real.arcsin
        ((1 / (u - 1) - 1) / Real.sqrt 2)) := by
    funext u
    rfl
  rw [hfun]
  exact hn

private lemma primitives_eq (x : ℝ) (hx : x ∈ domain) :
    substitutionPrimitive x = primitive x := by
  have hy : 0 < x - 1 := domain_sub_pos hx
  have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  unfold substitutionPrimitive primitive
  rw [← Real.arcsin_neg, abs_of_pos hy]
  congr 1
  field_simp [hy.ne', hs2]
  ring

theorem gap1 (x t : ℝ) (hx : x ∈ domain) (ht : x - 1 = 1 / t) :
    (x - 1) * Real.sqrt (x ^ 2 - 2) =
      Real.sqrt (1 + 2 * t - t ^ 2) / (t * |t|) := by
  have hy : 0 < x - 1 := domain_sub_pos hx
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    norm_num at ht
    linarith
  have hmul : (x - 1) * t = 1 := by
    calc
      (x - 1) * t = (1 / t) * t := by rw [ht]
      _ = 1 := one_div_mul_cancel ht0
  have ht' : t = 1 / (x - 1) := by
    apply (eq_div_iff hy.ne').2
    simpa [mul_comm] using hmul
  have harg :
      1 + 2 * (1 / (x - 1)) - (1 / (x - 1)) ^ 2 =
        1 + 2 / (x - 1) - 1 / (x - 1) ^ 2 := by
    field_simp [hy.ne']
  rw [ht', abs_of_pos (one_div_pos.mpr hy), harg,
    sqrt_transformed_eq x hx]
  field_simp [hy.ne']

theorem gap2 (t : ℝ) (ht : t ≠ 0) :
    deriv (fun u : ℝ => 1 + 1 / u) t = -1 / t ^ 2 := by
  have hinv :
      HasDerivAt (fun u : ℝ => 1 / u) (-1 / t ^ 2) t := by
    simpa [one_div] using (hasDerivAt_id t).inv ht
  exact (hinv.const_add 1).deriv

theorem gap3 :
    antiderivatives integrand = antiderivatives transformedIntegrand := by
  apply Set.ext
  intro F
  simp only [antiderivatives, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, fun x hx => ?_⟩
    calc
      deriv F x = integrand x := hderiv x hx
      _ = transformedIntegrand x := integrands_eq x hx
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, fun x hx => ?_⟩
    calc
      deriv F x = transformedIntegrand x := hderiv x hx
      _ = integrand x := (integrands_eq x hx).symm

theorem gap4 :
    antiderivatives transformedIntegrand = primitiveFamily substitutionPrimitive := by
  apply Set.ext
  intro F
  simp only [antiderivatives, primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hPdiff : DifferentiableOn ℝ substitutionPrimitive domain := by
      intro x hx
      exact (substitution_hasDerivAt x hx).differentiableAt.differentiableWithinAt
    have hdiff :
        DifferentiableOn ℝ (fun x => F x - substitutionPrimitive x) domain :=
      hFdiff.sub hPdiff
    have hzero : ∀ x ∈ domain,
        deriv (fun y => F y - substitutionPrimitive y) x = 0 := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
      have hPat : DifferentiableAt ℝ substitutionPrimitive x :=
        (substitution_hasDerivAt x hx).differentiableAt
      change deriv (F - substitutionPrimitive) x = 0
      rw [deriv_sub hFat hPat, hFderiv x hx,
        (substitution_hasDerivAt x hx).deriv]
      ring
    have hopen : IsOpen domain := by
      unfold domain
      exact isOpen_Ioi
    have hpre : IsPreconnected domain := by
      unfold domain
      exact isPreconnected_Ioi
    have htwo : (2 : ℝ) ∈ domain := by
      change Real.sqrt 2 < 2
      have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith
    refine ⟨F 2 - substitutionPrimitive 2, fun x hx => ?_⟩
    have hc :
        F x - substitutionPrimitive x =
          F 2 - substitutionPrimitive 2 :=
      hopen.is_const_of_deriv_eq_zero hpre hdiff hzero hx htwo
    linarith
  · rintro ⟨C, hC⟩
    have hFderiv : ∀ x ∈ domain,
        HasDerivAt F (transformedIntegrand x) x := by
      intro x hx
      have hevent :
          F =ᶠ[nhds x] (fun y => substitutionPrimitive y + C) :=
        Filter.mem_of_superset (isOpen_Ioi.mem_nhds hx)
          (fun y hy => hC y hy)
      exact ((substitution_hasDerivAt x hx).add_const C).congr_of_eventuallyEq
        hevent
    constructor
    · intro x hx
      exact (hFderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFderiv x hx).deriv

theorem gap5 :
    primitiveFamily substitutionPrimitive = primitiveFamily primitive := by
  apply Set.ext
  intro F
  simp only [primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun x hx => ?_⟩
    rw [← primitives_eq x hx]
    exact hC x hx
  · rintro ⟨C, hC⟩
    refine ⟨C, fun x hx => ?_⟩
    rw [primitives_eq x hx]
    exact hC x hx

theorem gap6 : antiderivatives integrand = primitiveFamily primitive := by
  exact gap3.trans (gap4.trans gap5)

end

end ProofGap.Exercise1859
