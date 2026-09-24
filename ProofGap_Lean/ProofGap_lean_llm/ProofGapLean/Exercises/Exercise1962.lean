import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1962

noncomputable section

def branch : Set ℝ :=
  Set.Ioo (1 - Real.sqrt 3) (1 + Real.sqrt 3)
def angleBranch : Set ℝ := Set.Ioo (-Real.pi / 2) (Real.pi / 2)
def substitution (x t : ℝ) : Prop :=
  x ∈ branch ∧ t ∈ angleBranch ∧ x - 1 = Real.sqrt 3 * Real.sin t
def substitutionMap (t : ℝ) := 1 + Real.sqrt 3 * Real.sin t
def originalIntegrand (x : ℝ) :=
  x ^ 2 / ((4 - 2 * x + x ^ 2) * Real.sqrt (2 + 2 * x - x ^ 2))
def shiftedIntegrand (x : ℝ) :=
  ((x - 1) ^ 2 + 2 * (x - 1) + 1) /
    ((3 + (x - 1) ^ 2) * Real.sqrt (3 - (x - 1) ^ 2))
def substitutedIntegrand (t : ℝ) :=
  (1 + 2 * Real.sqrt 3 * Real.sin t + 3 * Real.sin t ^ 2) /
    (3 * (1 + Real.sin t ^ 2))
def sinFraction (t : ℝ) := Real.sin t / (1 + Real.sin t ^ 2)
def reciprocalSinFraction (t : ℝ) := 1 / (1 + Real.sin t ^ 2)
def cosDerivativeFraction (t : ℝ) :=
  deriv Real.cos t / (2 - Real.cos t ^ 2)
def tanDerivativeFraction (t : ℝ) :=
  deriv Real.tan t / (1 + 2 * Real.tan t ^ 2)
def primitiveT (t : ℝ) :=
  t -
    1 / Real.sqrt 6 *
      Real.log |(Real.sqrt 2 + Real.cos t) / (Real.sqrt 2 - Real.cos t)| -
    Real.sqrt 2 / 3 * Real.arctan (Real.sqrt 2 * Real.tan t)
def primitiveX (x : ℝ) :=
  Real.arcsin ((x - 1) / Real.sqrt 3) -
    1 / Real.sqrt 6 *
      Real.log
        ((Real.sqrt 6 + Real.sqrt (2 + 2 * x - x ^ 2)) /
          (Real.sqrt 6 - Real.sqrt (2 + 2 * x - x ^ 2))) -
    Real.sqrt 2 / 3 *
      Real.arctan
        ((x - 1) * Real.sqrt 2 / Real.sqrt (2 + 2 * x - x ^ 2))
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def PullbackFamily (map : ℝ → ℝ) (s : Set ℝ)
    (T : Set (ℝ → ℝ)) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ T, ∀ t ∈ s, F (map t) = G t}
def FirstDecompositionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G₀ ∈ AntiderivativesOn angleBranch (fun _ => 1),
    ∃ G₁ ∈ AntiderivativesOn angleBranch sinFraction,
    ∃ G₂ ∈ AntiderivativesOn angleBranch reciprocalSinFraction,
      ∀ t ∈ angleBranch,
        F t = G₀ t + 2 / Real.sqrt 3 * G₁ t - 2 / 3 * G₂ t}
def SecondDecompositionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G₁ ∈ AntiderivativesOn angleBranch cosDerivativeFraction,
    ∃ G₂ ∈ AntiderivativesOn angleBranch tanDerivativeFraction,
      ∀ t ∈ angleBranch,
        F t = t - 2 / Real.sqrt 3 * G₁ t - 2 / 3 * G₂ t}

private theorem angle_cos_pos {t : ℝ} (ht : t ∈ angleBranch) :
    0 < Real.cos t := by
  apply Real.cos_pos_of_mem_Ioo
  simpa only [angleBranch, neg_div] using ht

private theorem angle_sin_bounds {t : ℝ} (ht : t ∈ angleBranch) :
    -1 < Real.sin t ∧ Real.sin t < 1 := by
  have hc := angle_cos_pos ht
  have htrig := Real.sin_sq_add_cos_sq t
  have hc2 : 0 < Real.cos t ^ 2 := sq_pos_of_pos hc
  constructor <;> nlinarith [sq_nonneg (Real.sin t + 1),
    sq_nonneg (Real.sin t - 1)]

private theorem substitutionMap_mem_branch {t : ℝ} (ht : t ∈ angleBranch) :
    substitutionMap t ∈ branch := by
  have hs := angle_sin_bounds ht
  have ha : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  simp only [substitutionMap, branch, Set.mem_Ioo]
  constructor <;> nlinarith

private theorem branch_scaled_bounds {x : ℝ} (hx : x ∈ branch) :
    -1 < (x - 1) / Real.sqrt 3 ∧ (x - 1) / Real.sqrt 3 < 1 := by
  have ha : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  simp only [branch, Set.mem_Ioo] at hx
  constructor
  · apply (lt_div_iff₀ ha).2
    nlinarith
  · apply (div_lt_iff₀ ha).2
    nlinarith

private theorem substitution_radical (t : ℝ) (ht : t ∈ angleBranch) :
    Real.sqrt (2 + 2 * substitutionMap t - substitutionMap t ^ 2) =
      Real.sqrt 3 * Real.cos t := by
  have hc := angle_cos_pos ht
  have hs3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hrad :
      2 + 2 * substitutionMap t - substitutionMap t ^ 2 =
        (Real.sqrt 3 * Real.cos t) ^ 2 := by
    unfold substitutionMap
    calc
      2 + 2 * (1 + Real.sqrt 3 * Real.sin t) -
          (1 + Real.sqrt 3 * Real.sin t) ^ 2 =
          3 - (Real.sqrt 3) ^ 2 * Real.sin t ^ 2 := by ring
      _ = 3 - 3 * Real.sin t ^ 2 := by rw [hs3]
      _ = 3 * Real.cos t ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq t]
      _ = (Real.sqrt 3 * Real.cos t) ^ 2 := by
        rw [mul_pow, hs3]
  rw [hrad]
  exact Real.sqrt_sq
    (mul_nonneg (Real.sqrt_nonneg 3) (le_of_lt hc))

private theorem transformed_integrand_identity (t : ℝ) (ht : t ∈ angleBranch) :
    originalIntegrand (substitutionMap t) *
        (Real.sqrt 3 * Real.cos t) = substitutedIntegrand t := by
  have hroot := substitution_radical t ht
  have hs3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have ha : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hc := angle_cos_pos ht
  unfold originalIntegrand substitutedIntegrand
  rw [hroot]
  unfold substitutionMap
  have hden :
      4 - 2 * (1 + Real.sqrt 3 * Real.sin t) +
          (1 + Real.sqrt 3 * Real.sin t) ^ 2 =
        3 * (1 + Real.sin t ^ 2) := by
    calc
      4 - 2 * (1 + Real.sqrt 3 * Real.sin t) +
          (1 + Real.sqrt 3 * Real.sin t) ^ 2 =
          3 + (Real.sqrt 3) ^ 2 * Real.sin t ^ 2 := by ring
      _ = 3 * (1 + Real.sin t ^ 2) := by rw [hs3]; ring
  have hnum :
      (1 + Real.sqrt 3 * Real.sin t) ^ 2 =
        1 + 2 * Real.sqrt 3 * Real.sin t + 3 * Real.sin t ^ 2 := by
    calc
      (1 + Real.sqrt 3 * Real.sin t) ^ 2 =
          1 + 2 * Real.sqrt 3 * Real.sin t +
            (Real.sqrt 3) ^ 2 * Real.sin t ^ 2 := by ring
      _ = 1 + 2 * Real.sqrt 3 * Real.sin t +
            3 * Real.sin t ^ 2 := by rw [hs3]
  rw [hden, hnum]
  field_simp [ne_of_gt ha, ne_of_gt hc]

private theorem substituted_integrand_split (t : ℝ) :
    substitutedIntegrand t =
      1 + 2 / Real.sqrt 3 * sinFraction t -
        2 / 3 * reciprocalSinFraction t := by
  unfold substitutedIntegrand sinFraction reciprocalSinFraction
  have hs3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have ha : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hdiv : 2 / Real.sqrt 3 = 2 * Real.sqrt 3 / 3 := by
    field_simp [ne_of_gt ha]
    nlinarith [hs3]
  rw [hdiv]
  have hpos : 0 < 1 + Real.sin t ^ 2 := by positivity
  field_simp [ne_of_gt hpos]
  ring

private theorem cos_derivative_fraction_eq (t : ℝ) :
    cosDerivativeFraction t = -sinFraction t := by
  unfold cosDerivativeFraction sinFraction
  rw [(Real.hasDerivAt_cos t).deriv]
  have htrig := Real.sin_sq_add_cos_sq t
  have hden : 2 - Real.cos t ^ 2 = 1 + Real.sin t ^ 2 := by
    nlinarith
  rw [hden]
  ring

private theorem tan_derivative_fraction_eq (t : ℝ) (ht : t ∈ angleBranch) :
    tanDerivativeFraction t = reciprocalSinFraction t := by
  have hc := angle_cos_pos ht
  unfold tanDerivativeFraction reciprocalSinFraction
  rw [(Real.hasDerivAt_tan (ne_of_gt hc)).deriv,
    Real.tan_eq_sin_div_cos t]
  field_simp [ne_of_gt hc]
  nlinarith [Real.sin_sq_add_cos_sq t]

private theorem reciprocal_primitive_deriv (t : ℝ) (ht : t ∈ angleBranch) :
    HasDerivAt
      (fun y => Real.arctan (Real.sqrt 2 * Real.tan y) / Real.sqrt 2)
      (reciprocalSinFraction t) t := by
  have hc := angle_cos_pos ht
  have ha : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hraw :=
    ((Real.hasDerivAt_arctan (Real.sqrt 2 * Real.tan t)).comp t
      ((Real.hasDerivAt_tan (ne_of_gt hc)).const_mul (Real.sqrt 2))).div_const
        (Real.sqrt 2)
  convert hraw using 1 <;> try rfl
  unfold reciprocalSinFraction
  rw [Real.tan_eq_sin_div_cos t]
  have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  field_simp [ne_of_gt hc, ne_of_gt ha]
  ring_nf
  rw [hs2]
  nlinarith [Real.sin_sq_add_cos_sq t]

private theorem logarithmic_primitive_deriv (t : ℝ) (ht : t ∈ angleBranch) :
    HasDerivAt
      (fun y => Real.log |(Real.sqrt 2 + Real.cos y) /
        (Real.sqrt 2 - Real.cos y)| / (2 * Real.sqrt 2))
      (cosDerivativeFraction t) t := by
  have ha : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hplus : ∀ y : ℝ, 0 < Real.sqrt 2 + Real.cos y := by
    intro y
    nlinarith [Real.neg_one_le_cos y, Real.one_lt_sqrt_two]
  have hminus : ∀ y : ℝ, 0 < Real.sqrt 2 - Real.cos y := by
    intro y
    nlinarith [Real.cos_le_one y, Real.one_lt_sqrt_two]
  have hfun :
      (fun y => Real.log |(Real.sqrt 2 + Real.cos y) /
        (Real.sqrt 2 - Real.cos y)| / (2 * Real.sqrt 2)) =
      (fun y => Real.log ((Real.sqrt 2 + Real.cos y) /
        (Real.sqrt 2 - Real.cos y)) / (2 * Real.sqrt 2)) := by
    funext y
    rw [abs_of_pos (div_pos (hplus y) (hminus y))]
  rw [hfun]
  have hnum := (hasDerivAt_const t (Real.sqrt 2)).add (Real.hasDerivAt_cos t)
  have hden := (hasDerivAt_const t (Real.sqrt 2)).sub (Real.hasDerivAt_cos t)
  have hquot := hnum.div hden (ne_of_gt (hminus t))
  have hlog :=
    (Real.hasDerivAt_log
      (ne_of_gt (div_pos (hplus t) (hminus t)))).comp t hquot
  have hraw := hlog.div_const (2 * Real.sqrt 2)
  simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply,
    zero_add, zero_sub, neg_neg] at hraw
  convert hraw using 1 <;> try rfl
  unfold cosDerivativeFraction
  rw [(Real.hasDerivAt_cos t).deriv]
  have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hs2cube : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
    calc
      (Real.sqrt 2) ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hs2]
  have hcubesin :
      Real.sin t * (Real.sqrt 2) ^ 3 =
        2 * Real.sin t * Real.sqrt 2 := by
    rw [hs2cube]
    ring
  have htwo : 0 < 2 - Real.cos t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (Real.sin t)]
  field_simp [ne_of_gt ha, ne_of_gt (hplus t), ne_of_gt (hminus t),
    ne_of_gt htwo]
  ring_nf
  nlinarith [hcubesin]

private theorem primitiveT_deriv (t : ℝ) (ht : t ∈ angleBranch) :
    HasDerivAt primitiveT (substitutedIntegrand t) t := by
  have hL := logarithmic_primitive_deriv t ht
  have hJ := reciprocal_primitive_deriv t ht
  have hraw :=
    ((hasDerivAt_id t).sub (hL.const_mul (2 / Real.sqrt 3))).sub
      (hJ.const_mul (2 / 3))
  have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs6 : (Real.sqrt 6) ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
  have hp : (Real.sqrt 3 * Real.sqrt 2) ^ 2 = (6 : ℝ) := by
    rw [mul_pow, hs3, hs2]
    norm_num
  have hs6mul : Real.sqrt 6 = Real.sqrt 3 * Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 6,
      mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2)]
  convert hraw using 1
  · ext y
    simp only [Pi.sub_apply, id_eq]
    unfold primitiveT
    rw [hs6mul]
    field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)),
      ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
    rw [hs2]
    ring
  · rw [substituted_integrand_split, cos_derivative_fraction_eq t]
    ring

private theorem primitive_substitution_identity (t : ℝ) (ht : t ∈ angleBranch) :
    primitiveX (substitutionMap t) = primitiveT t := by
  have ha3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hc := angle_cos_pos ht
  have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs6 : (Real.sqrt 6) ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
  have hp : (Real.sqrt 3 * Real.sqrt 2) ^ 2 = (6 : ℝ) := by
    rw [mul_pow, hs3, hs2]
    norm_num
  have hs6mul : Real.sqrt 6 = Real.sqrt 3 * Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 6,
      mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2)]
  have hquot : (substitutionMap t - 1) / Real.sqrt 3 = Real.sin t := by
    unfold substitutionMap
    field_simp [ne_of_gt ha3]
    ring
  have harcsin : Real.arcsin (Real.sin t) = t := by
    have hlow : -(Real.pi / 2) ≤ t := by
      simpa only [neg_div] using (le_of_lt ht.1)
    exact Real.arcsin_sin hlow (le_of_lt ht.2)
  have hroot := substitution_radical t ht
  have hden : 0 < Real.sqrt 2 - Real.cos t := by
    nlinarith [Real.cos_le_one t, Real.one_lt_sqrt_two]
  have hnum : 0 < Real.sqrt 2 + Real.cos t := by
    nlinarith [Real.neg_one_le_cos t, Real.one_lt_sqrt_two]
  have hratio :
      (Real.sqrt 6 + Real.sqrt 3 * Real.cos t) /
          (Real.sqrt 6 - Real.sqrt 3 * Real.cos t) =
        (Real.sqrt 2 + Real.cos t) / (Real.sqrt 2 - Real.cos t) := by
    rw [hs6mul]
    field_simp [ne_of_gt ha3, ne_of_gt hden] <;> ring
  have hratio_pos :
      0 < (Real.sqrt 2 + Real.cos t) / (Real.sqrt 2 - Real.cos t) :=
    div_pos hnum hden
  have htan :
      (substitutionMap t - 1) * Real.sqrt 2 /
          (Real.sqrt 3 * Real.cos t) =
        Real.sqrt 2 * Real.tan t := by
    unfold substitutionMap
    rw [Real.tan_eq_sin_div_cos t]
    field_simp [ne_of_gt ha3, ne_of_gt hc] <;> ring
  unfold primitiveX primitiveT
  rw [hquot, harcsin, hroot, hratio, abs_of_pos hratio_pos, htan]

theorem gap1 :
    AntiderivativesOn branch originalIntegrand =
      AntiderivativesOn branch shiftedIntegrand := by
  apply congrArg (AntiderivativesOn branch)
  funext x
  unfold originalIntegrand shiftedIntegrand
  have hnum : (x - 1) ^ 2 + 2 * (x - 1) + 1 = x ^ 2 := by ring
  have hden : 3 + (x - 1) ^ 2 = 4 - 2 * x + x ^ 2 := by ring
  have hrad : 3 - (x - 1) ^ 2 = 2 + 2 * x - x ^ 2 := by ring
  rw [hnum, hden, hrad]
theorem gap2 (x t : ℝ) (h : substitution x t) :
    -Real.pi / 2 < t := by
  simpa only [substitution, angleBranch, Set.mem_Ioo] using h.2.1.1
theorem gap3 (x t : ℝ) (h : substitution x t) :
    t < Real.pi / 2 := by
  simpa only [substitution, angleBranch, Set.mem_Ioo] using h.2.1.2
theorem gap4 (x t : ℝ) (h : substitution x t) :
    -Real.pi / 2 < Real.pi / 2 := by
  exact lt_trans (gap2 x t h) (gap3 x t h)
theorem gap5 (t : ℝ) (ht : t ∈ angleBranch) :
    HasDerivAt substitutionMap (Real.sqrt 3 * Real.cos t) t := by
  simpa only [substitutionMap] using
    (((Real.hasDerivAt_sin t).const_mul (Real.sqrt 3)).const_add (1 : ℝ))
theorem gap6 (x t : ℝ) (h : substitution x t) :
    Real.sqrt (2 + 2 * x - x ^ 2) = Real.sqrt 3 * Real.cos t := by
  have ht : t ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2) := by
    simpa only [substitution, angleBranch] using h.2.1
  have hcos : 0 < Real.cos t := by
    apply Real.cos_pos_of_mem_Ioo
    simpa only [neg_div] using ht
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hx : x = 1 + Real.sqrt 3 * Real.sin t := by
    linarith [h.2.2]
  have hrad :
      2 + 2 * x - x ^ 2 = (Real.sqrt 3 * Real.cos t) ^ 2 := by
    rw [hx]
    nlinarith [Real.sin_sq_add_cos_sq t, hsqrt_sq]
  calc
    Real.sqrt (2 + 2 * x - x ^ 2) =
        Real.sqrt ((Real.sqrt 3 * Real.cos t) ^ 2) := by rw [hrad]
    _ = Real.sqrt 3 * Real.cos t := by
      exact Real.sqrt_sq
        (mul_nonneg (Real.sqrt_nonneg 3) (le_of_lt hcos))
theorem gap7 :
    AntiderivativesOn branch originalIntegrand =
      PullbackFamily substitutionMap angleBranch
        (AntiderivativesOn angleBranch substitutedIntegrand) := by
  classical
  ext F
  simp only [AntiderivativesOn, PullbackFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨F ∘ substitutionMap, ?_, ?_⟩
    · intro t ht
      have hmap := substitutionMap_mem_branch ht
      have hchain := (hF (substitutionMap t) hmap).comp t (gap5 t ht)
      simpa only [transformed_integrand_identity t ht] using hchain
    · intro t ht
      rfl
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    let t := Real.arcsin ((x - 1) / Real.sqrt 3)
    have hsqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have hu := branch_scaled_bounds hx
    have ht : t ∈ angleBranch := by
      simp only [t, angleBranch, Set.mem_Ioo]
      constructor
      · simpa only [neg_div] using
          (Real.neg_pi_div_two_lt_arcsin.mpr hu.1)
      · exact (Real.arcsin_lt_pi_div_two).2 hu.2
    have hmap : substitutionMap t = x := by
      simp only [substitutionMap, t,
        Real.sin_arcsin (le_of_lt hu.1) (le_of_lt hu.2)]
      field_simp [ne_of_gt hsqrt_pos]
      ring
    have hlocal :
        F =ᶠ[nhds x] G ∘ fun y => Real.arcsin ((y - 1) / Real.sqrt 3) := by
      filter_upwards [IsOpen.eventually_mem (isOpen_Ioo : IsOpen branch) hx] with y hy
      have huy := branch_scaled_bounds hy
      have hty : Real.arcsin ((y - 1) / Real.sqrt 3) ∈ angleBranch := by
        simp only [angleBranch, Set.mem_Ioo]
        constructor
        · simpa only [neg_div] using
            (Real.neg_pi_div_two_lt_arcsin.mpr huy.1)
        · exact (Real.arcsin_lt_pi_div_two).2 huy.2
      have hm :
          substitutionMap (Real.arcsin ((y - 1) / Real.sqrt 3)) = y := by
        simp only [substitutionMap,
          Real.sin_arcsin (le_of_lt huy.1) (le_of_lt huy.2)]
        field_simp [ne_of_gt hsqrt_pos]
        ring
      calc
        F y = F (substitutionMap (Real.arcsin ((y - 1) / Real.sqrt 3))) := by
          rw [hm]
        _ = G (Real.arcsin ((y - 1) / Real.sqrt 3)) := hFG _ hty
    have hinv :=
      (Real.hasDerivAt_arcsin (ne_of_gt hu.1) (ne_of_lt hu.2)).comp x
        (((hasDerivAt_id x).sub_const 1).div_const (Real.sqrt 3))
    have hcomp := (hG t ht).comp x hinv
    have hcomp' :
        HasDerivAt (G ∘ fun y => Real.arcsin ((y - 1) / Real.sqrt 3))
          (substitutedIntegrand t *
            (1 / Real.sqrt (1 - ((x - 1) / Real.sqrt 3) ^ 2) *
              (1 / Real.sqrt 3))) x := by
      simpa only [Function.comp_def, id_eq] using hcomp
    have hfinal := hcomp'.congr_of_eventuallyEq hlocal
    have hu_eq : (x - 1) / Real.sqrt 3 = Real.sin t := by
      rw [← hmap]
      unfold substitutionMap
      field_simp [ne_of_gt hsqrt_pos]
      ring
    have hc := angle_cos_pos ht
    have hsqrtu :
        Real.sqrt (1 - ((x - 1) / Real.sqrt 3) ^ 2) = Real.cos t := by
      rw [hu_eq]
      have htrig := Real.sin_sq_add_cos_sq t
      rw [show 1 - Real.sin t ^ 2 = Real.cos t ^ 2 by nlinarith]
      exact Real.sqrt_sq (le_of_lt hc)
    rw [hsqrtu] at hfinal
    have hid := transformed_integrand_identity t ht
    rw [hmap] at hid
    have hvalue :
        substitutedIntegrand t * (1 / Real.cos t * (1 / Real.sqrt 3)) =
          originalIntegrand x := by
      rw [← hid]
      field_simp [ne_of_gt hc, ne_of_gt hsqrt_pos] <;> ring
    rw [hvalue] at hfinal
    exact hfinal
theorem gap8 :
    AntiderivativesOn branch originalIntegrand =
      PullbackFamily substitutionMap angleBranch
        FirstDecompositionFamily := by
  rw [gap7]
  apply congrArg (PullbackFamily substitutionMap angleBranch)
  ext F
  simp only [AntiderivativesOn, FirstDecompositionFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    let J : ℝ → ℝ := fun t =>
      Real.arctan (Real.sqrt 2 * Real.tan t) / Real.sqrt 2
    refine ⟨fun t => t, ?_,
      fun t => Real.sqrt 3 / 2 * (F t - t + 2 / 3 * J t), ?_,
      J, ?_, ?_⟩
    · intro t ht
      exact hasDerivAt_id t
    · intro t ht
      have hJ : HasDerivAt J (reciprocalSinFraction t) t := by
        simpa only [J] using reciprocal_primitive_deriv t ht
      have hraw :=
        (((hF t ht).sub (hasDerivAt_id t)).add
          (hJ.const_mul (2 / 3))).const_mul (Real.sqrt 3 / 2)
      convert hraw using 1
      rw [substituted_integrand_split]
      have hs3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
        Real.sq_sqrt (by norm_num)
      field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
      nlinarith
    · intro t ht
      simpa only [J] using reciprocal_primitive_deriv t ht
    · intro t ht
      dsimp only [J]
      field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))] <;>
        ring
  · rintro ⟨G₀, hG₀, G₁, hG₁, G₂, hG₂, hF⟩
    intro t ht
    rw [substituted_integrand_split]
    have hder :=
      ((hG₀ t ht).add ((hG₁ t ht).const_mul (2 / Real.sqrt 3))).sub
        ((hG₂ t ht).const_mul (2 / 3))
    apply hder.congr_of_eventuallyEq
    filter_upwards [IsOpen.eventually_mem (isOpen_Ioo : IsOpen angleBranch) ht] with y hy
    exact hF y hy
theorem gap9 :
    AntiderivativesOn branch originalIntegrand =
      PullbackFamily substitutionMap angleBranch
        SecondDecompositionFamily := by
  rw [gap8]
  apply congrArg (PullbackFamily substitutionMap angleBranch)
  ext F
  simp only [FirstDecompositionFamily, SecondDecompositionFamily,
    Set.mem_setOf_eq, AntiderivativesOn]
  constructor
  · rintro ⟨G₀, hG₀, G₁, hG₁, G₂, hG₂, hF⟩
    refine ⟨fun t => -G₁ t - Real.sqrt 3 / 2 * (G₀ t - t), ?_,
      G₂, ?_, ?_⟩
    · intro t ht
      have hraw := (hG₁ t ht).neg.sub
        (((hG₀ t ht).sub (hasDerivAt_id t)).const_mul (Real.sqrt 3 / 2))
      convert hraw using 1
      rw [cos_derivative_fraction_eq t]
      ring
    · intro t ht
      rw [tan_derivative_fraction_eq t ht]
      exact hG₂ t ht
    · intro t ht
      rw [hF t ht]
      field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
      ring
  · rintro ⟨G₁, hG₁, G₂, hG₂, hF⟩
    refine ⟨fun t => t, ?_, fun t => -G₁ t, ?_, G₂, ?_, ?_⟩
    · intro t ht
      exact hasDerivAt_id t
    · intro t ht
      have hraw := (hG₁ t ht).neg
      have hcoef : -cosDerivativeFraction t = sinFraction t := by
        rw [cos_derivative_fraction_eq t]
        ring
      simpa only [hcoef] using hraw
    · intro t ht
      rw [← tan_derivative_fraction_eq t ht]
      exact hG₂ t ht
    · intro t ht
      rw [hF t ht]
      ring
theorem gap10 :
    AntiderivativesOn branch originalIntegrand =
      PullbackFamily substitutionMap angleBranch
        (PrimitiveFamilyOn angleBranch primitiveT) := by
  rw [gap9]
  apply congrArg (PullbackFamily substitutionMap angleBranch)
  ext F
  simp only [SecondDecompositionFamily, PrimitiveFamilyOn,
    Set.mem_setOf_eq, AntiderivativesOn]
  constructor
  · rintro ⟨G₁, hG₁, G₂, hG₂, hF⟩
    have hFder : ∀ t ∈ angleBranch,
        HasDerivAt F (substitutedIntegrand t) t := by
      intro t ht
      have hraw :=
        ((hasDerivAt_id t).sub ((hG₁ t ht).const_mul (2 / Real.sqrt 3))).sub
          ((hG₂ t ht).const_mul (2 / 3))
      have hder :
          HasDerivAt
            ((fun y => y) - (fun y => 2 / Real.sqrt 3 * G₁ y) -
              fun y => 2 / 3 * G₂ y)
            (substitutedIntegrand t) t := by
        convert hraw using 1
        rw [substituted_integrand_split, cos_derivative_fraction_eq t,
          tan_derivative_fraction_eq t ht]
        ring
      apply hder.congr_of_eventuallyEq
      filter_upwards [IsOpen.eventually_mem (isOpen_Ioo : IsOpen angleBranch) ht] with y hy
      exact hF y hy
    have hd : ∀ t ∈ angleBranch,
        HasDerivAt (fun y => F y - primitiveT y) 0 t := by
      intro t ht
      convert (hFder t ht).sub (primitiveT_deriv t ht) using 1 <;> ring
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitiveT y) angleBranch := by
      intro t ht
      exact (hd t ht).differentiableAt.differentiableWithinAt
    have hzero : ∀ t ∈ angleBranch,
        deriv (fun y => F y - primitiveT y) t = 0 := by
      intro t ht
      exact (hd t ht).deriv
    have hpre : IsPreconnected angleBranch := by
      unfold angleBranch
      exact isPreconnected_Ioo
    have hz : (0 : ℝ) ∈ angleBranch := by
      simp only [angleBranch, Set.mem_Ioo]
      constructor <;> nlinarith [Real.pi_pos]
    refine ⟨F 0 - primitiveT 0, ?_⟩
    intro t ht
    have heq : F 0 - primitiveT 0 = F t - primitiveT t := by
      exact isOpen_Ioo.is_const_of_deriv_eq_zero hpre hdiff hzero hz ht
    linarith
  · rintro ⟨C, hF⟩
    refine ⟨fun t => Real.log |(Real.sqrt 2 + Real.cos t) /
        (Real.sqrt 2 - Real.cos t)| / (2 * Real.sqrt 2), ?_,
      fun t => Real.arctan (Real.sqrt 2 * Real.tan t) / Real.sqrt 2 - 3 * C / 2,
      ?_, ?_⟩
    · intro t ht
      exact logarithmic_primitive_deriv t ht
    · intro t ht
      rw [tan_derivative_fraction_eq t ht]
      exact (reciprocal_primitive_deriv t ht).sub_const (3 * C / 2)
    · intro t ht
      rw [hF t ht]
      unfold primitiveT
      have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
      have hs3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
      have hs6 : (Real.sqrt 6) ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
      have hp : (Real.sqrt 3 * Real.sqrt 2) ^ 2 = (6 : ℝ) := by
        rw [mul_pow, hs3, hs2]
        norm_num
      have hs6mul : Real.sqrt 6 = Real.sqrt 3 * Real.sqrt 2 := by
        nlinarith [Real.sqrt_nonneg 6,
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2)]
      rw [hs6mul]
      field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)),
        ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
      rw [hs2]
      ring
theorem gap11 :
    AntiderivativesOn branch originalIntegrand =
      PrimitiveFamilyOn branch primitiveX := by
  rw [gap10]
  ext F
  simp only [PullbackFamily, PrimitiveFamilyOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, ⟨C, hG⟩, hFG⟩
    refine ⟨C, ?_⟩
    intro x hx
    let t := Real.arcsin ((x - 1) / Real.sqrt 3)
    have hu := branch_scaled_bounds hx
    have ht : t ∈ angleBranch := by
      simp only [t, angleBranch, Set.mem_Ioo]
      constructor
      · simpa only [neg_div] using
          (Real.neg_pi_div_two_lt_arcsin.mpr hu.1)
      · exact (Real.arcsin_lt_pi_div_two).2 hu.2
    have hmap : substitutionMap t = x := by
      simp only [substitutionMap, t,
        Real.sin_arcsin (le_of_lt hu.1) (le_of_lt hu.2)]
      field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
      ring
    calc
      F x = F (substitutionMap t) := by rw [hmap]
      _ = G t := hFG t ht
      _ = primitiveT t + C := hG t ht
      _ = primitiveX (substitutionMap t) + C := by
        rw [primitive_substitution_identity t ht]
      _ = primitiveX x + C := by rw [hmap]
  · rintro ⟨C, hF⟩
    refine ⟨fun t => primitiveT t + C, ⟨C, by simp⟩, ?_⟩
    intro t ht
    have hmap := substitutionMap_mem_branch ht
    calc
      F (substitutionMap t) = primitiveX (substitutionMap t) + C := hF _ hmap
      _ = primitiveT t + C := by rw [primitive_substitution_identity t ht]

end
end ProofGap.Exercise1962
