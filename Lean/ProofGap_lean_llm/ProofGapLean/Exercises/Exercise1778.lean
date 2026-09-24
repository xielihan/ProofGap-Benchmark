import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise1778

noncomputable section

def xOf (t : ℝ) : ℝ := Real.sin t
def integrand (x : ℝ) : ℝ := 1 / (Real.sqrt (1 - x ^ 2)) ^ 3
def primitive (x : ℝ) : ℝ := x / Real.sqrt (1 - x ^ 2)
def angleDomain : Set ℝ := Set.Ioo (-Real.pi / 2) (Real.pi / 2)
def domain : Set ℝ := Set.Ioo (-1) 1
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  change -1 < x ∧ x < 1 at hx
  have hq : 0 < 1 - x ^ 2 := by
    nlinarith
  have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hq
  have hinner : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x 1).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hsqrt := (Real.hasDerivAt_sqrt hq.ne').comp x hinner
  have hquot := (hasDerivAt_id x).div hsqrt hs.ne'
  unfold primitive integrand
  convert hquot using 1 <;> simp only [Function.comp_apply, id_eq]
  field_simp [hs.ne']
  rw [Real.sq_sqrt (le_of_lt hq)]
  ring

private theorem eq_of_hasDerivAt_zero_on_domain
    {f : ℝ → ℝ} {a b : ℝ}
    (ha : a ∈ domain) (hb : b ∈ domain)
    (hf : ∀ x ∈ domain, HasDerivAt f 0 x) :
    f a = f b := by
  have hdiff : DifferentiableOn ℝ f domain := by
    intro x hx
    exact (hf x hx).differentiableAt.differentiableWithinAt
  have hzero : ∀ x ∈ domain, deriv f x = 0 := by
    intro x hx
    exact (hf x hx).deriv
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero ha hb

theorem gap1 (t : ℝ) (ht : t ∈ angleDomain) :
    -1 < xOf t := by
  have ht' : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    simpa only [angleDomain, neg_div] using ht
  change -1 < Real.sin t
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ht'
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem gap2 (t : ℝ) (ht : t ∈ angleDomain) :
    xOf t < 1 := by
  have ht' : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    simpa only [angleDomain, neg_div] using ht
  change Real.sin t < 1
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ht'
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem gap3 :
    (-1 : ℝ) < 1 := by
  norm_num

theorem gap4 (t : ℝ) (ht : t ∈ angleDomain) :
    (Real.sqrt (1 - xOf t ^ 2)) ^ 3 = Real.cos t ^ 3 := by
  have ht' : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    simpa only [angleDomain, neg_div] using ht
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ht'
  have hsq : 1 - xOf t ^ 2 = Real.cos t ^ 2 := by
    unfold xOf
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos hc]

theorem gap5 (t : ℝ) (ht : t ∈ angleDomain) :
    deriv xOf t = Real.cos t := by
  simpa only [xOf] using (Real.hasDerivAt_sin t).deriv

theorem gap6 (t : ℝ) (ht : t ∈ angleDomain) :
    integrand (xOf t) * deriv xOf t = 1 / Real.cos t ^ 2 := by
  have ht' : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    simpa only [angleDomain, neg_div] using ht
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ht'
  unfold integrand
  rw [gap4 t ht, gap5 t ht]
  field_simp [ne_of_gt hc] <;> ring

theorem gap7 (t : ℝ) (ht : t ∈ angleDomain) :
    HasDerivAt Real.tan (1 / Real.cos t ^ 2) t := by
  have ht' : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    simpa only [angleDomain, neg_div] using ht
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ht'
  exact Real.hasDerivAt_tan (ne_of_gt hc)

theorem gap8 (t : ℝ) (ht : t ∈ angleDomain) :
    Real.tan t = Real.sin t / Real.sqrt (1 - Real.sin t ^ 2) := by
  have ht' : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    simpa only [angleDomain, neg_div] using ht
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ht'
  have hsq : 1 - Real.sin t ^ 2 = Real.cos t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hsqrt : Real.sqrt (1 - Real.sin t ^ 2) = Real.cos t := by
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos hc]
  rw [Real.tan_eq_sin_div_cos, hsqrt]

theorem gap9 (t : ℝ) (ht : t ∈ angleDomain) :
    Real.sin t / Real.sqrt (1 - Real.sin t ^ 2) = primitive (xOf t) := by
  rfl

theorem gap10 :
    Family integrand domain = Translates primitive domain := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change (∀ x ∈ domain, HasDerivAt F (integrand x) x) at hF
    change ∃ C, ∀ x ∈ domain, F x = primitive x + C
    let h : ℝ → ℝ := fun y => F y - primitive y
    have hh : ∀ x ∈ domain, HasDerivAt h 0 x := by
      intro x hx
      dsimp only [h]
      convert (hF x hx).sub (primitive_hasDerivAt x hx) using 1 <;> ring
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hzero : (0 : ℝ) ∈ domain := by
      change (-1 : ℝ) < 0 ∧ 0 < 1
      norm_num
    have heq : h x = h 0 :=
      eq_of_hasDerivAt_zero_on_domain hx hzero hh
    dsimp only [h] at heq
    linarith
  · intro hT
    change (∃ C, ∀ x ∈ domain, F x = primitive x + C) at hT
    rcases hT with ⟨C, hC⟩
    change ∀ x ∈ domain, HasDerivAt F (integrand x) x
    intro x hx
    have hs : HasDerivAt (fun y => primitive y + C) (integrand x) x :=
      (primitive_hasDerivAt x hx).add_const C
    have hopen : domain ∈ nhds x := by
      apply isOpen_Ioo.mem_nhds
      exact hx
    have hevent : F =ᶠ[nhds x] fun y => primitive y + C := by
      filter_upwards [hopen] with y hy
      exact hC y hy
    exact hs.congr_of_eventuallyEq hevent

end

end ProofGap.Exercise1778
