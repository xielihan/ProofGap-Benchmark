import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1957

noncomputable section

def xOf (t : ℝ) := Real.sin t
def tBranch : Set ℝ := {t | -Real.pi / 2 < t ∧ t < Real.pi / 2}
def xBranch : Set ℝ := {x | -1 < x ∧ x < 1}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def integrandX (x : ℝ) := 1 / ((1 + x ^ 2) * Real.sqrt (1 - x ^ 2))
def transformed₁ (t : ℝ) := 1 / (1 + Real.sin t ^ 2)
def transformed₂ (t : ℝ) :=
  1 / (2 * Real.sin t ^ 2 + Real.cos t ^ 2)
def PullbackFamily : Set (ℝ → ℝ) :=
  {G | ∃ F ∈ AntiderivativesOn xBranch integrandX,
    ∀ t ∈ tBranch, G t = F (xOf t)}
def auxiliaryIntegrand (t : ℝ) :=
  deriv (fun u => Real.sqrt 2 * Real.tan u) t /
    ((Real.sqrt 2 * Real.tan t) ^ 2 + 1)
def ScaledAuxiliaryFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn tBranch auxiliaryIntegrand,
    ∀ t ∈ tBranch, F t = 1 / Real.sqrt 2 * G t}
def primitiveT (t : ℝ) :=
  1 / Real.sqrt 2 * Real.arctan (Real.sqrt 2 * Real.tan t)
def primitiveX (x : ℝ) :=
  1 / Real.sqrt 2 *
    Real.arctan (x * Real.sqrt 2 / Real.sqrt (1 - x ^ 2))

private def _root_.𝓝 {α : Type*} [TopologicalSpace α] (a : α) : Filter α := nhds a

theorem gap1 (t : ℝ) (ht : t ∈ tBranch) :
    -Real.pi / 2 < t := by
  exact ht.1
theorem gap2 (t : ℝ) (ht : t ∈ tBranch) :
    t < Real.pi / 2 := by
  exact ht.2
theorem gap3 :
    -Real.pi / 2 < Real.pi / 2 := by
  nlinarith [Real.pi_pos]
theorem gap4 (t : ℝ) :
    HasDerivAt xOf (Real.cos t) t := by
  simpa [xOf] using Real.hasDerivAt_sin t
theorem gap5 (t : ℝ) (ht : t ∈ tBranch) :
    Real.sqrt (1 - xOf t ^ 2) = Real.cos t := by
  have hlow : -(Real.pi / 2) < t := by
    simpa only [neg_div] using gap1 t ht
  have hc : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨hlow, gap2 t ht⟩
  have hsq : 1 - Real.sin t ^ 2 = Real.cos t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [xOf, hsq, Real.sqrt_sq_eq_abs, abs_of_pos hc]
theorem gap6 :
    PullbackFamily = AntiderivativesOn tBranch transformed₁ := by
  apply Set.ext
  intro G
  constructor
  · rintro ⟨F, hF, hGF⟩
    intro t ht
    have hlow : -(Real.pi / 2) < t := by
      simpa only [neg_div] using gap1 t ht
    have hc : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ⟨hlow, gap2 t ht⟩
    have hxt : xOf t ∈ xBranch := by
      change -1 < Real.sin t ∧ Real.sin t < 1
      constructor <;>
        nlinarith [Real.sin_sq_add_cos_sq t, sq_pos_of_pos hc,
          Real.neg_one_le_sin t, Real.sin_le_one t]
    have hd := (hF (xOf t) hxt).comp t (gap4 t)
    have hcoef : integrandX (xOf t) * Real.cos t = transformed₁ t := by
      rw [integrandX, transformed₁, gap5 t ht, xOf]
      field_simp [ne_of_gt hc]
    rw [hcoef] at hd
    have hopen : IsOpen tBranch := by
      simpa [tBranch] using
        (isOpen_Ioo : IsOpen (Set.Ioo (-Real.pi / 2) (Real.pi / 2)))
    have heq : G =ᶠ[𝓝 t] fun u => F (xOf u) := by
      filter_upwards [hopen.mem_nhds ht] with u hu
      exact hGF u hu
    exact hd.congr_of_eventuallyEq (by
      simpa only [Function.comp_apply] using heq)
  · intro hG
    let F : ℝ → ℝ := fun x => G (Real.arcsin x)
    refine ⟨F, ?_, ?_⟩
    · intro x hx
      have hat : Real.arcsin x ∈ tBranch := by
        constructor
        · simpa only [neg_div] using
            (Real.neg_pi_div_two_lt_arcsin).2 hx.1
        · exact (Real.arcsin_lt_pi_div_two).2 hx.2
      have hd := (hG (Real.arcsin x) hat).comp x
        (Real.hasDerivAt_arcsin (ne_of_gt hx.1) (ne_of_lt hx.2))
      have hs : Real.sin (Real.arcsin x) = x :=
        Real.sin_arcsin (le_of_lt hx.1) (le_of_lt hx.2)
      have hprod : 0 < (1 - x) * (1 + x) :=
        mul_pos (sub_pos.mpr hx.2) (by linarith [hx.1])
      have hrad : 0 < 1 - x ^ 2 := by
        nlinarith [hprod]
      have hsqrt : Real.sqrt (1 - x ^ 2) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 hrad)
      have hone : 1 + x ^ 2 ≠ 0 := by
        nlinarith [sq_nonneg x]
      have hcoef :
          transformed₁ (Real.arcsin x) * (1 / Real.sqrt (1 - x ^ 2)) =
            integrandX x := by
        rw [transformed₁, hs, integrandX]
        field_simp [hsqrt, hone]
      rw [hcoef] at hd
      simpa only [F, Function.comp_apply] using hd
    · intro t ht
      dsimp [F]
      have hlow : -(Real.pi / 2) ≤ t := by
        have hlt : -(Real.pi / 2) < t := by
          simpa only [neg_div] using gap1 t ht
        exact le_of_lt hlt
      have hupp : t ≤ Real.pi / 2 := le_of_lt (gap2 t ht)
      simp only [xOf, Real.arcsin_sin hlow hupp]
theorem gap7 :
    AntiderivativesOn tBranch transformed₁ =
      AntiderivativesOn tBranch transformed₂ := by
  have hfun : transformed₁ = transformed₂ := by
    funext t
    unfold transformed₁ transformed₂
    have hden :
        1 + Real.sin t ^ 2 =
          2 * Real.sin t ^ 2 + Real.cos t ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    rw [hden]
  rw [hfun]
theorem gap8 :
    PullbackFamily = AntiderivativesOn tBranch transformed₂ := by
  exact gap6.trans gap7
theorem gap9 :
    PullbackFamily = ScaledAuxiliaryFamily := by
  have hscale : ∀ t ∈ tBranch,
      1 / Real.sqrt 2 * auxiliaryIntegrand t = transformed₂ t := by
    intro t ht
    have hlow : -(Real.pi / 2) < t := by
      simpa only [neg_div] using gap1 t ht
    have hcpos : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ⟨hlow, gap2 t ht⟩
    have hc : Real.cos t ≠ 0 := ne_of_gt hcpos
    have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hs : Real.sqrt 2 ≠ 0 := ne_of_gt hspos
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hd : deriv (fun u => Real.sqrt 2 * Real.tan u) t =
        Real.sqrt 2 * (1 / Real.cos t ^ 2) := by
      exact ((Real.hasDerivAt_tan hc).const_mul (Real.sqrt 2)).deriv
    rw [auxiliaryIntegrand, transformed₂, hd, Real.tan_eq_sin_div_cos]
    field_simp [hs, hc]
    nlinarith [hs2]
  rw [gap8]
  apply Set.ext
  intro F
  constructor
  · intro hF
    let G : ℝ → ℝ := fun t => Real.sqrt 2 * F t
    refine ⟨G, ?_, ?_⟩
    · intro t ht
      have hd := (hF t ht).const_mul (Real.sqrt 2)
      have hs : Real.sqrt 2 ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 (by norm_num))
      have hcoef : Real.sqrt 2 * transformed₂ t = auxiliaryIntegrand t := by
        rw [← hscale t ht]
        field_simp [hs]
      rw [hcoef] at hd
      exact hd
    · intro t ht
      dsimp [G]
      have hs : Real.sqrt 2 ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 (by norm_num))
      field_simp [hs]
  · rintro ⟨G, hG, hFG⟩
    intro t ht
    have hd := (hG t ht).const_mul (1 / Real.sqrt 2)
    rw [hscale t ht] at hd
    have hopen : IsOpen tBranch := by
      simpa [tBranch] using
        (isOpen_Ioo : IsOpen (Set.Ioo (-Real.pi / 2) (Real.pi / 2)))
    have heq : F =ᶠ[𝓝 t] fun u => 1 / Real.sqrt 2 * G u := by
      filter_upwards [hopen.mem_nhds ht] with u hu
      exact hFG u hu
    exact hd.congr_of_eventuallyEq heq
theorem gap10 :
    PullbackFamily = PrimitiveFamilyOn tBranch primitiveT := by
  have hp : primitiveT ∈ AntiderivativesOn tBranch transformed₁ := by
    let G : ℝ → ℝ := fun t => Real.arctan (Real.sqrt 2 * Real.tan t)
    have hG : G ∈ AntiderivativesOn tBranch auxiliaryIntegrand := by
      intro t ht
      have hlow : -(Real.pi / 2) < t := by
        simpa only [neg_div] using gap1 t ht
      have hcpos : 0 < Real.cos t :=
        Real.cos_pos_of_mem_Ioo ⟨hlow, gap2 t ht⟩
      have hc : Real.cos t ≠ 0 := ne_of_gt hcpos
      have hy := (Real.hasDerivAt_tan hc).const_mul (Real.sqrt 2)
      have hd :=
        (Real.hasDerivAt_arctan (Real.sqrt 2 * Real.tan t)).comp t hy
      have hdy : deriv (fun u => Real.sqrt 2 * Real.tan u) t =
          Real.sqrt 2 * (1 / Real.cos t ^ 2) := hy.deriv
      rw [auxiliaryIntegrand, hdy]
      convert hd using 1 <;> ring
    have hs : primitiveT ∈ ScaledAuxiliaryFamily := by
      refine ⟨G, hG, ?_⟩
      intro t ht
      rfl
    rw [← gap9, gap8, ← gap7] at hs
    exact hs
  apply Set.ext
  intro F
  constructor
  · intro hF
    have hFA : F ∈ AntiderivativesOn tBranch transformed₁ := by
      rw [← gap6]
      exact hF
    refine ⟨F 0 - primitiveT 0, ?_⟩
    have hzero : 0 ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2) := by
      constructor <;> nlinarith [Real.pi_pos]
    have hdiff : DifferentiableOn ℝ (F - primitiveT)
        (Set.Ioo (-Real.pi / 2) (Real.pi / 2)) := by
      intro x hx
      exact ((hFA x hx).sub (hp x hx)).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2),
        deriv (F - primitiveT) x = 0 := by
      intro x hx
      simpa using ((hFA x hx).sub (hp x hx)).deriv
    intro x hx
    have heq : (F - primitiveT) 0 = (F - primitiveT) x :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiff hderiv hzero hx
    change F 0 - primitiveT 0 = F x - primitiveT x at heq
    linarith
  · rintro ⟨C, hFC⟩
    rw [gap6]
    intro x hx
    have hd := (hp x hx).add_const C
    have hopen : IsOpen tBranch := by
      simpa [tBranch] using
        (isOpen_Ioo : IsOpen (Set.Ioo (-Real.pi / 2) (Real.pi / 2)))
    have heq : F =ᶠ[𝓝 x] fun y => primitiveT y + C := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hFC y hy
    exact hd.congr_of_eventuallyEq heq
theorem gap11 (t : ℝ) (ht : t ∈ tBranch) :
    primitiveT t = primitiveX (xOf t) := by
  have hlow : -(Real.pi / 2) < t := by
    simpa only [neg_div] using gap1 t ht
  have hc : Real.cos t ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨hlow, gap2 t ht⟩)
  have hsqrt : Real.sqrt (1 - Real.sin t ^ 2) = Real.cos t := by
    simpa [xOf] using gap5 t ht
  unfold primitiveT primitiveX xOf
  rw [hsqrt, Real.tan_eq_sin_div_cos]
  congr 2
  field_simp [hc]
theorem gap12 :
    AntiderivativesOn xBranch integrandX =
      PrimitiveFamilyOn xBranch primitiveX := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    have hPB : (fun t => F (xOf t)) ∈ PullbackFamily := by
      exact ⟨F, hF, fun t ht => rfl⟩
    rw [gap10] at hPB
    rcases hPB with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    have hat : Real.arcsin x ∈ tBranch := by
      constructor
      · simpa only [neg_div] using
          (Real.neg_pi_div_two_lt_arcsin).2 hx.1
      · exact (Real.arcsin_lt_pi_div_two).2 hx.2
    have hxo : xOf (Real.arcsin x) = x := by
      simp only [xOf, Real.sin_arcsin (le_of_lt hx.1) (le_of_lt hx.2)]
    calc
      F x = F (xOf (Real.arcsin x)) := by rw [hxo]
      _ = primitiveT (Real.arcsin x) + C := hC (Real.arcsin x) hat
      _ = primitiveX (xOf (Real.arcsin x)) + C := by
        rw [gap11 (Real.arcsin x) hat]
      _ = primitiveX x + C := by rw [hxo]
  · rintro ⟨C, hFC⟩
    let G : ℝ → ℝ := fun t => primitiveT t + C
    have hGP : G ∈ PrimitiveFamilyOn tBranch primitiveT := by
      refine ⟨C, ?_⟩
      intro t ht
      rfl
    have hGPB : G ∈ PullbackFamily := by
      rw [gap10]
      exact hGP
    rcases hGPB with ⟨H, hH, hGH⟩
    intro x hx
    have hopen : IsOpen xBranch := by
      simpa [xBranch] using
        (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1))
    have heq : F =ᶠ[𝓝 x] H := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      have hay : Real.arcsin y ∈ tBranch := by
        constructor
        · simpa only [neg_div] using
            (Real.neg_pi_div_two_lt_arcsin).2 hy.1
        · exact (Real.arcsin_lt_pi_div_two).2 hy.2
      have hyo : xOf (Real.arcsin y) = y := by
        simp only [xOf,
          Real.sin_arcsin (le_of_lt hy.1) (le_of_lt hy.2)]
      calc
        F y = primitiveX y + C := hFC y hy
        _ = primitiveT (Real.arcsin y) + C := by
          rw [gap11 (Real.arcsin y) hay, hyo]
        _ = G (Real.arcsin y) := rfl
        _ = H (xOf (Real.arcsin y)) := hGH (Real.arcsin y) hay
        _ = H y := by rw [hyo]
    exact (hH x hx).congr_of_eventuallyEq heq

end
end ProofGap.Exercise1957
