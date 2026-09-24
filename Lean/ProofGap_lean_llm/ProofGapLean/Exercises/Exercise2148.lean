import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2148

noncomputable section

def xBranch : Set ℝ := Set.Ioo 0 Real.pi
def tBranch : Set ℝ := Set.Ioo 0 (Real.sqrt 2)
def t (x : ℝ) := Real.sqrt (1 + Real.cos x)
def integrand (x : ℝ) :=
  1 / (Real.sin x * Real.sqrt (1 + Real.cos x))
def parameterIntegrand (u : ℝ) := 2 / (u ^ 2 * (2 - u ^ 2))
def splitParameterIntegrand (u : ℝ) := 1 / u ^ 2 + 1 / (2 - u ^ 2)
def AntiderivativesX (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ xBranch, HasDerivAt F (f x) x}
def AntiderivativesT (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ u ∈ tBranch, HasDerivAt F (f u) u}
def PrimitiveFamilyX (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ xBranch, F x = p x + C}
def PrimitiveFamilyT (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ u ∈ tBranch, F u = p u + C}
def PullbackFamily (A : Set (ℝ → ℝ)) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ A, ∀ x ∈ xBranch, F x = G (t x)}
def NegativeFamily (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesT f,
    ∀ u ∈ tBranch, F u = -G u}
def primitiveT (u : ℝ) :=
  1 / u -
    1 / (2 * Real.sqrt 2) *
      Real.log ((Real.sqrt 2 + u) / (Real.sqrt 2 - u))
def primitive (x : ℝ) :=
  1 / t x -
    1 / (2 * Real.sqrt 2) *
      Real.log ((Real.sqrt 2 + t x) / (Real.sqrt 2 - t x))

private theorem image_mem_tBranch (x : ℝ) (hx : x ∈ xBranch) : t x ∈ tBranch := by
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hrad : 0 < 1 + Real.cos x := by
    have htrig := Real.sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (Real.cos x + 1)]
  have hcos_lt : Real.cos x < 1 := by
    have htrig := Real.sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (Real.cos x - 1)]
  have ht_sq : t x ^ 2 = 1 + Real.cos x := by
    unfold t
    exact Real.sq_sqrt (le_of_lt hrad)
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht_nonneg : 0 ≤ t x := by
    unfold t
    exact Real.sqrt_nonneg _
  have hsqrt2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  constructor
  · unfold t
    exact Real.sqrt_pos.2 hrad
  · nlinarith [sq_nonneg (Real.sqrt 2 - t x)]

private theorem t_hasDerivAt (x : ℝ) (hx : x ∈ xBranch) :
    HasDerivAt t (-Real.sin x / (2 * t x)) x := by
  have hrad : 0 < 1 + Real.cos x := by
    have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
    have htrig := Real.sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (Real.cos x + 1)]
  have hinner : HasDerivAt (fun y : ℝ => 1 + Real.cos y) (-Real.sin x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add (Real.hasDerivAt_cos x) using 1 <;> ring
  have hsqrt := (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp x hinner
  unfold t
  convert hsqrt using 1
  field_simp [ne_of_gt (Real.sqrt_pos.2 hrad)]
  <;> ring

private theorem parameter_eq_split {u : ℝ} (hu : u ∈ tBranch) :
    parameterIntegrand u = splitParameterIntegrand u := by
  have hu0 : 0 < u := hu.1
  have hua : u < Real.sqrt 2 := hu.2
  have ha2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ha0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hq : 0 < 2 - u ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt 2 - u)]
  unfold parameterIntegrand splitParameterIntegrand
  field_simp [ne_of_gt hu0, ne_of_gt hq]
  <;> ring

private theorem primitiveT_hasDerivAt (u : ℝ) (hu : u ∈ tBranch) :
    HasDerivAt primitiveT (-splitParameterIntegrand u) u := by
  let a : ℝ := Real.sqrt 2
  have hu0 : 0 < u := hu.1
  have hua : u < a := hu.2
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have ha2 : a ^ 2 = 2 := by
    dsimp [a]
    exact Real.sq_sqrt (by norm_num)
  have hp : 0 < a + u := by linarith
  have hm : 0 < a - u := by linarith
  have hq : 0 < 2 - u ^ 2 := by
    nlinarith [sq_nonneg (a - u)]
  have hnum : HasDerivAt (fun v : ℝ => a + v) 1 u := by
    simpa using (hasDerivAt_const u a).add (hasDerivAt_id u)
  have hden : HasDerivAt (fun v : ℝ => a - v) (-1) u := by
    simpa using (hasDerivAt_const u a).sub (hasDerivAt_id u)
  have hquot := hnum.div hden (ne_of_gt hm)
  have hlog := (Real.hasDerivAt_log (ne_of_gt (div_pos hp hm))).comp u hquot
  change HasDerivAt
    (fun v : ℝ => Real.log ((a + v) / (a - v))) _ u at hlog
  have hdenprod : (a + u) * (a - u) = 2 - u ^ 2 := by
    calc
      (a + u) * (a - u) = a ^ 2 - u ^ 2 := by ring
      _ = 2 - u ^ 2 := by rw [ha2]
  have hlog' : HasDerivAt
      (fun v : ℝ => Real.log ((a + v) / (a - v)))
      (2 * a / (2 - u ^ 2)) u := by
    convert hlog using 1
    rw [inv_div, ← hdenprod]
    field_simp [ne_of_gt hp, ne_of_gt hm]
    <;> ring
  have hinv : HasDerivAt (fun v : ℝ => 1 / v) (-1 / u ^ 2) u := by
    convert (hasDerivAt_const u (1 : ℝ)).div (hasDerivAt_id u)
      (ne_of_gt hu0) using 1 <;> simp
  have hscale :
      1 / (2 * a) * (2 * a / (2 - u ^ 2)) = 1 / (2 - u ^ 2) := by
    field_simp [ne_of_gt ha, ne_of_gt hq]
    <;> ring
  have hcomb := hinv.sub (hlog'.const_mul (1 / (2 * a)))
  have hcomb' : HasDerivAt
      (fun v : ℝ =>
        1 / v - 1 / (2 * a) * Real.log ((a + v) / (a - v)))
      (-1 / u ^ 2 - 1 / (2 - u ^ 2)) u := by
    rw [← hscale]
    exact hcomb
  dsimp [a] at hcomb'
  unfold primitiveT splitParameterIntegrand
  convert hcomb' using 1 <;> ring

private theorem negative_parameter_eq_split :
    NegativeFamily parameterIntegrand = NegativeFamily splitParameterIntegrand := by
  have hA : AntiderivativesT parameterIntegrand =
      AntiderivativesT splitParameterIntegrand := by
    apply Set.ext
    intro G
    simp only [AntiderivativesT, Set.mem_setOf_eq]
    constructor
    · intro hG u hu
      simpa only [parameter_eq_split hu] using hG u hu
    · intro hG u hu
      simpa only [parameter_eq_split hu] using hG u hu
  unfold NegativeFamily
  rw [hA]

private theorem negative_split_eq_primitive :
    NegativeFamily splitParameterIntegrand = PrimitiveFamilyT primitiveT := by
  apply Set.ext
  intro F
  simp only [NegativeFamily, PrimitiveFamilyT, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, hFG⟩
    have hOne : (1 : ℝ) ∈ tBranch := by
      change 0 < (1 : ℝ) ∧ (1 : ℝ) < Real.sqrt 2
      exact ⟨by norm_num, Real.one_lt_sqrt_two⟩
    have hdiff : DifferentiableOn ℝ
        (fun u => G u + primitiveT u) tBranch := by
      intro u hu
      exact ((hG u hu).add (primitiveT_hasDerivAt u hu)).differentiableAt.differentiableWithinAt
    have hderiv : ∀ u ∈ tBranch,
        deriv (fun v => G v + primitiveT v) u = 0 := by
      intro u hu
      simpa using ((hG u hu).add (primitiveT_hasDerivAt u hu)).deriv
    refine ⟨-(G 1 + primitiveT 1), ?_⟩
    intro u hu
    have hc := isOpen_Ioo.is_const_of_deriv_eq_zero
      isPreconnected_Ioo hdiff hderiv hu hOne
    have hfu := hFG u hu
    linarith
  · rintro ⟨C, hF⟩
    refine ⟨fun u => -primitiveT u - C, ?_, ?_⟩
    · intro u hu
      simpa using (primitiveT_hasDerivAt u hu).neg.sub_const C
    · intro u hu
      rw [hF u hu]
      ring

private theorem pullback_primitive_family :
    PullbackFamily (PrimitiveFamilyT primitiveT) =
      PrimitiveFamilyX (fun x => primitiveT (t x)) := by
  apply Set.ext
  intro F
  simp only [PullbackFamily, PrimitiveFamilyT, PrimitiveFamilyX,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, ⟨C, hG⟩, hFG⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hFG x hx, hG (t x) (image_mem_tBranch x hx)]
  · rintro ⟨C, hF⟩
    refine ⟨fun u => primitiveT u + C, ?_, ?_⟩
    · exact ⟨C, by intro u hu; rfl⟩
    · intro x hx
      exact hF x hx

theorem gap1 (x : ℝ) (hx : x ∈ xBranch) :
    0 < t x := by
  exact (image_mem_tBranch x hx).1
theorem gap2 (x : ℝ) (hx : x ∈ xBranch) :
    Real.sin x = t x * Real.sqrt (2 - t x ^ 2) := by
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have ht : 0 < t x := gap1 x hx
  have ht_sq : t x ^ 2 = 1 + Real.cos x := by
    unfold t
    rw [Real.sq_sqrt]
    have htrig := Real.sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (Real.sin x), sq_nonneg (Real.cos x + 1)]
  have hcos_lt : Real.cos x < 1 := by
    have htrig := Real.sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (Real.cos x - 1)]
  have hq : 0 < 2 - t x ^ 2 := by
    rw [ht_sq]
    linarith
  have hq_sq : Real.sqrt (2 - t x ^ 2) ^ 2 = 2 - t x ^ 2 :=
    Real.sq_sqrt (le_of_lt hq)
  have hr : 0 ≤ Real.sqrt (2 - t x ^ 2) := Real.sqrt_nonneg _
  have hsquares : Real.sin x ^ 2 =
      (t x * Real.sqrt (2 - t x ^ 2)) ^ 2 := by
    rw [mul_pow, hq_sq, ht_sq]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hprod : 0 ≤ t x * Real.sqrt (2 - t x ^ 2) :=
    mul_nonneg (le_of_lt ht) hr
  nlinarith [hsquares]
theorem gap3 (x : ℝ) (hx : x ∈ xBranch) :
    1 = -2 / Real.sqrt (2 - t x ^ 2) * deriv t x := by
  have ht : 0 < t x := gap1 x hx
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hfactor := gap2 x hx
  have hroot : 0 < Real.sqrt (2 - t x ^ 2) := by
    nlinarith [Real.sqrt_nonneg (2 - t x ^ 2)]
  rw [(t_hasDerivAt x hx).deriv, hfactor]
  field_simp [ne_of_gt ht, ne_of_gt hroot]
  <;> ring
theorem gap4 :
    AntiderivativesX integrand =
      PullbackFamily (NegativeFamily parameterIntegrand) := by
  have hcomp : ∀ x ∈ xBranch,
      HasDerivAt (fun y => primitiveT (t y)) (integrand x) x := by
    intro x hx
    have htx := image_mem_tBranch x hx
    have ht : 0 < t x := htx.1
    have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
    have hfactor := gap2 x hx
    have hroot : 0 < Real.sqrt (2 - t x ^ 2) := by
      nlinarith [Real.sqrt_nonneg (2 - t x ^ 2)]
    have hq : 0 < 2 - t x ^ 2 := (Real.sqrt_pos).mp hroot
    have hrsq : Real.sqrt (2 - t x ^ 2) ^ 2 = 2 - t x ^ 2 :=
      Real.sq_sqrt (le_of_lt hq)
    have hs_sq : Real.sin x ^ 2 = t x ^ 2 * (2 - t x ^ 2) := by
      calc
        Real.sin x ^ 2 =
            (t x * Real.sqrt (2 - t x ^ 2)) ^ 2 :=
          congrArg (fun z : ℝ => z ^ 2) hfactor
        _ = t x ^ 2 * (2 - t x ^ 2) := by
          rw [mul_pow, hrsq]
    have hc := (primitiveT_hasDerivAt (t x) htx).comp x (t_hasDerivAt x hx)
    convert hc using 1
    change 1 / (Real.sin x * t x) =
        -splitParameterIntegrand (t x) *
          (-Real.sin x / (2 * t x))
    rw [← parameter_eq_split htx]
    unfold parameterIntegrand
    field_simp [ne_of_gt hs, ne_of_gt ht, ne_of_gt hq]
    nlinarith [hs_sq]
  have hAX : AntiderivativesX integrand =
      PrimitiveFamilyX (fun x => primitiveT (t x)) := by
    apply Set.ext
    intro F
    simp only [AntiderivativesX, PrimitiveFamilyX, Set.mem_setOf_eq]
    constructor
    · intro hF
      let x₀ : ℝ := Real.pi / 2
      have hx₀ : x₀ ∈ xBranch := by
        change 0 < Real.pi / 2 ∧ Real.pi / 2 < Real.pi
        constructor <;> nlinarith [Real.pi_pos]
      have hdiff : DifferentiableOn ℝ
          (fun y => F y - primitiveT (t y)) xBranch := by
        intro y hy
        exact ((hF y hy).sub (hcomp y hy)).differentiableAt.differentiableWithinAt
      have hderiv : ∀ y ∈ xBranch,
          deriv (fun z => F z - primitiveT (t z)) y = 0 := by
        intro y hy
        simpa using ((hF y hy).sub (hcomp y hy)).deriv
      refine ⟨F x₀ - primitiveT (t x₀), ?_⟩
      intro y hy
      have hc := isOpen_Ioo.is_const_of_deriv_eq_zero
        isPreconnected_Ioo hdiff hderiv hy hx₀
      dsimp [x₀] at hc ⊢
      linarith
    · rintro ⟨C, hF⟩
      intro x hx
      have heq : F =ᶠ[nhds x] (fun y => primitiveT (t y) + C) := by
        filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
        exact hF y hy
      exact ((hcomp x hx).add_const C).congr_of_eventuallyEq heq
  calc
    AntiderivativesX integrand =
        PrimitiveFamilyX (fun x => primitiveT (t x)) := hAX
    _ = PullbackFamily (PrimitiveFamilyT primitiveT) :=
      pullback_primitive_family.symm
    _ = PullbackFamily (NegativeFamily splitParameterIntegrand) := by
      rw [negative_split_eq_primitive]
    _ = PullbackFamily (NegativeFamily parameterIntegrand) := by
      rw [negative_parameter_eq_split]
theorem gap5 :
    PullbackFamily (NegativeFamily parameterIntegrand) =
      PullbackFamily (NegativeFamily splitParameterIntegrand) := by
  rw [negative_parameter_eq_split]
theorem gap6 :
    NegativeFamily splitParameterIntegrand =
      PrimitiveFamilyT primitiveT := by
  exact negative_split_eq_primitive
theorem gap7 :
    AntiderivativesX integrand =
      PrimitiveFamilyX (fun x => primitiveT (t x)) := by
  calc
    AntiderivativesX integrand =
        PullbackFamily (NegativeFamily parameterIntegrand) := gap4
    _ = PullbackFamily (NegativeFamily splitParameterIntegrand) := gap5
    _ = PullbackFamily (PrimitiveFamilyT primitiveT) := by rw [gap6]
    _ = PrimitiveFamilyX (fun x => primitiveT (t x)) :=
      pullback_primitive_family
theorem gap8 :
    AntiderivativesX integrand = PrimitiveFamilyX primitive := by
  simpa [primitive] using gap7

end
end ProofGap.Exercise2148
