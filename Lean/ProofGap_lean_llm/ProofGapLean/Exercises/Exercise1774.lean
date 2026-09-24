import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1774

noncomputable section

def subst (x : ℝ) : ℝ := 1 + Real.log x
def integrand (x : ℝ) : ℝ := Real.log x / (x * Real.sqrt (subst x))
def intermediate (x : ℝ) : ℝ :=
  (2 / 3 : ℝ) * (Real.sqrt (subst x)) ^ 3 - 2 * Real.sqrt (subst x)
def primitive (x : ℝ) : ℝ :=
  (2 / 3 : ℝ) * (Real.log x - 2) * Real.sqrt (subst x)
def domain : Set ℝ := Set.Ioi (Real.exp (-1))
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem domain_pos {x : ℝ} (hx : x ∈ domain) : 0 < x := by
  change Real.exp (-1) < x at hx
  exact (Real.exp_pos (-1)).trans hx

private theorem subst_pos {x : ℝ} (hx : x ∈ domain) : 0 < subst x := by
  have hx0 : 0 < x := domain_pos hx
  have hlog : (-1 : ℝ) < Real.log x := by
    rw [← Real.exp_lt_exp]
    simpa [Real.exp_log hx0] using hx
  change 0 < 1 + Real.log x
  linarith

private theorem subst_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt subst (1 / x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (domain_pos hx)
  simpa [subst, one_div] using
    (hasDerivAt_const x (1 : ℝ)).add (Real.hasDerivAt_log hx0)

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    Real.log x / x = (1 + Real.log x - 1) * deriv subst x := by
  rw [(subst_hasDerivAt (x := x) hx).deriv]
  ring

theorem gap2 (x : ℝ) :
    (1 + Real.log x - 1) * deriv subst x =
      (subst x - 1) * deriv subst x := by
  rfl

theorem gap3 (x : ℝ) (hx : x ∈ domain) :
    Real.log x / x = (subst x - 1) * deriv subst x := by
  exact (gap1 x hx).trans (gap2 x)

theorem gap4 (x : ℝ) (hx : x ∈ domain) :
    integrand x =
      (subst x - 1) / Real.sqrt (subst x) * deriv subst x := by
  calc
    integrand x = (Real.log x / x) / Real.sqrt (subst x) := by
      simpa [integrand] using
        (div_div (Real.log x) x (Real.sqrt (subst x))).symm
    _ = ((subst x - 1) * deriv subst x) / Real.sqrt (subst x) := by
      rw [gap3 x hx]
    _ = (subst x - 1) / Real.sqrt (subst x) * deriv subst x := by
      ring

theorem gap5 (x : ℝ) (hx : x ∈ domain) :
    (subst x - 1) / Real.sqrt (subst x) =
      Real.sqrt (subst x) - 1 / Real.sqrt (subst x) := by
  have hs : 0 ≤ subst x := (subst_pos hx).le
  have hu : Real.sqrt (subst x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (subst_pos hx))
  calc
    (subst x - 1) / Real.sqrt (subst x) =
        ((Real.sqrt (subst x)) ^ 2 - 1) / Real.sqrt (subst x) := by
      rw [Real.sq_sqrt hs]
    _ = Real.sqrt (subst x) - 1 / Real.sqrt (subst x) := by
      field_simp [hu] <;> ring

theorem gap6 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt intermediate (integrand x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (domain_pos hx)
  have hs0 : subst x ≠ 0 := ne_of_gt (subst_pos hx)
  have hu : Real.sqrt (subst x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (subst_pos hx))
  have hsqrtDeriv :
      HasDerivAt (fun y => Real.sqrt (subst y))
        ((2 * Real.sqrt (subst x))⁻¹ * (1 / x)) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sqrt hs0).comp x (subst_hasDerivAt (x := x) hx)
  have hI :
      HasDerivAt intermediate
        ((2 / 3 : ℝ) *
            (3 * (Real.sqrt (subst x)) ^ 2 *
              ((2 * Real.sqrt (subst x))⁻¹ * (1 / x))) -
          2 * ((2 * Real.sqrt (subst x))⁻¹ * (1 / x))) x := by
    simpa [intermediate] using
      ((hsqrtDeriv.pow 3).const_mul (2 / 3 : ℝ)).sub
        (hsqrtDeriv.const_mul 2)
  have hvalue :
      (2 / 3 : ℝ) *
            (3 * (Real.sqrt (subst x)) ^ 2 *
              ((2 * Real.sqrt (subst x))⁻¹ * (1 / x))) -
          2 * ((2 * Real.sqrt (subst x))⁻¹ * (1 / x)) =
        (Real.sqrt (subst x) - 1 / Real.sqrt (subst x)) * deriv subst x := by
    rw [(subst_hasDerivAt (x := x) hx).deriv]
    field_simp [hx0, hu] <;> ring
  have hint :
      integrand x =
        (Real.sqrt (subst x) - 1 / Real.sqrt (subst x)) * deriv subst x := by
    rw [gap4 x hx, gap5 x hx]
  rw [hint, ← hvalue]
  exact hI

theorem gap7 (x : ℝ) (hx : x ∈ domain) :
    intermediate x = primitive x := by
  have hs : 0 ≤ subst x := (subst_pos hx).le
  have hcub :
      (Real.sqrt (subst x)) ^ 3 = subst x * Real.sqrt (subst x) := by
    calc
      (Real.sqrt (subst x)) ^ 3 =
          (Real.sqrt (subst x)) ^ 2 * Real.sqrt (subst x) := by ring
      _ = subst x * Real.sqrt (subst x) := by
        rw [Real.sq_sqrt hs]
  rw [intermediate, primitive, hcub, subst]
  ring

theorem gap8 :
    Family integrand domain = Translates primitive domain := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand domain at hF
    change ∃ C, ∀ x ∈ domain, F x = primitive x + C
    let G : ℝ → ℝ := fun y => F y - intermediate y
    have hG : ∀ x ∈ domain, HasDerivAt G 0 x := by
      intro x hx
      simpa [G] using (hF x hx).sub (gap6 x hx)
    have hGdiff : DifferentiableOn ℝ G domain := by
      intro x hx
      exact (hG x hx).differentiableAt.differentiableWithinAt
    have hGderiv : ∀ x ∈ domain, deriv G x = 0 := by
      intro x hx
      exact (hG x hx).deriv
    have hconst : Set.Pairwise domain (fun x y => G x = G y) := by
      intro x hx y hy _
      exact
        isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
          hGdiff hGderiv hx hy
    have hone : (1 : ℝ) ∈ domain := by
      change Real.exp (-1) < 1
      have he : Real.exp (-1) < Real.exp 0 :=
        (Real.exp_lt_exp).2 (by norm_num)
      simpa using he
    refine ⟨G 1, ?_⟩
    intro x hx
    have heq : G x = G 1 := by
      by_cases hxeq : x = 1
      · rw [hxeq]
      · exact hconst hx hone hxeq
    rw [← gap7 x hx]
    dsimp [G] at heq ⊢
    linarith
  · rintro ⟨C, hC⟩
    change IsAntiderivativeOn F integrand domain
    intro x hx
    have hopen : IsOpen domain := by
      exact isOpen_Ioi
    have heq :
        F =ᶠ[nhds x] fun y => intermediate y + C :=
      (hopen.eventually_mem hx).mono (by
        intro y hy
        rw [hC y hy, ← gap7 y hy])
    have hbase :
        HasDerivAt (fun y => intermediate y + C) (integrand x) x := by
      simpa using (gap6 x hx).add_const C
    exact hbase.congr_of_eventuallyEq heq

end

end ProofGap.Exercise1774
