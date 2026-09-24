import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1843

noncomputable section

def branch : Set ℝ := Set.Ioo (-1 : ℝ) 1
def denominator (x : ℝ) := x ^ 6 - x ^ 3 - 2
def integrand (x : ℝ) := x ^ 5 / denominator x
def firstSubstitutedIntegrand (x : ℝ) :=
  x ^ 3 * deriv (fun t : ℝ => t ^ 3) x /
    ((x ^ 3 - 1 / 2) ^ 2 - 9 / 4)
def shiftedIntegrand (x : ℝ) :=
  (x ^ 3 - 1 / 2 + 1 / 2) /
    ((x ^ 3 - 1 / 2) ^ 2 - 9 / 4) *
      deriv (fun t : ℝ => t ^ 3 - 1 / 2) x
def logIntegrand (x : ℝ) :=
  deriv (fun t : ℝ => (t ^ 3 - 1 / 2) ^ 2) x /
    ((x ^ 3 - 1 / 2) ^ 2 - 9 / 4)
def hyperbolicIntegrand (x : ℝ) :=
  deriv (fun t : ℝ => t ^ 3 - 1 / 2) x /
    ((3 / 2 : ℝ) ^ 2 - (x ^ 3 - 1 / 2) ^ 2)
def primitiveRaw (x : ℝ) :=
  (1 / 6 : ℝ) * Real.log |denominator x| -
    (1 / 18 : ℝ) *
      Real.log |((3 / 2 : ℝ) + x ^ 3 - 1 / 2) /
        ((3 / 2 : ℝ) - (x ^ 3 - 1 / 2))|
def primitive (x : ℝ) :=
  (1 / 9 : ℝ) *
    Real.log (|x ^ 3 + 1| * (x ^ 3 - 2) ^ 2)
def factoredSubstitutedIntegrand (x : ℝ) :=
  x ^ 3 * deriv (fun t : ℝ => t ^ 3) x /
    ((x ^ 3 - 2) * (x ^ 3 + 1))
def partialFractionIntegrand (x : ℝ) :=
  (2 / (x ^ 3 - 2) + 1 / (x ^ 3 + 1)) *
    deriv (fun t : ℝ => t ^ 3) x
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ScaledFamily (c : ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn f, ∀ x ∈ branch, F x = c * G x}
def SplitFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn logIntegrand,
    ∃ H ∈ AntiderivativesOn hyperbolicIntegrand,
      ∀ x ∈ branch, F x = (1 / 6 : ℝ) * G x - (1 / 6 : ℝ) * H x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem branch_isOpen : IsOpen branch := by
  simpa [branch] using (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1))

private theorem deriv_cube (x : ℝ) :
    deriv (fun t : ℝ => t ^ 3) x = 3 * x ^ 2 := by
  convert ((hasDerivAt_id x).pow 3).deriv using 1 <;> norm_num <;> ring

private theorem deriv_shift_cube (x : ℝ) :
    deriv (fun t : ℝ => t ^ 3 - 1 / 2) x = 3 * x ^ 2 := by
  convert (((hasDerivAt_id x).pow 3).sub_const (1 / 2 : ℝ)).deriv
    using 1 <;> norm_num <;> ring

private theorem deriv_shift_square (x : ℝ) :
    deriv (fun t : ℝ => (t ^ 3 - 1 / 2) ^ 2) x =
      6 * x ^ 2 * (x ^ 3 - 1 / 2) := by
  convert ((((hasDerivAt_id x).pow 3).sub_const (1 / 2 : ℝ)).pow 2).deriv
    using 1 <;> norm_num <;> ring

private theorem cube_bounds {x : ℝ} (hx : x ∈ branch) :
    -1 < x ^ 3 ∧ x ^ 3 < 1 := by
  change -1 < x ∧ x < 1 at hx
  constructor
  · have hp : 0 < x ^ 2 - x + 1 := by
      nlinarith [sq_nonneg (x - 1 / 2)]
    have hx1 : 0 < x + 1 := by linarith
    have hm := mul_pos hx1 hp
    nlinarith
  · have hp : 0 < x ^ 2 + x + 1 := by
      nlinarith [sq_nonneg (x + 1 / 2)]
    have hx1 : 0 < 1 - x := by linarith
    have hm := mul_pos hx1 hp
    nlinarith

private theorem cube_add_one_ne {x : ℝ} (hx : x ∈ branch) :
    x ^ 3 + 1 ≠ 0 := by
  exact ne_of_gt (by linarith [cube_bounds hx |>.1])

private theorem cube_sub_two_ne {x : ℝ} (hx : x ∈ branch) :
    x ^ 3 - 2 ≠ 0 := by
  exact ne_of_lt (by linarith [cube_bounds hx |>.2])

private theorem denominator_factor (x : ℝ) :
    denominator x = (x ^ 3 - 2) * (x ^ 3 + 1) := by
  unfold denominator
  ring

private theorem denominator_ne {x : ℝ} (hx : x ∈ branch) :
    denominator x ≠ 0 := by
  rw [denominator_factor]
  exact mul_ne_zero (cube_sub_two_ne hx) (cube_add_one_ne hx)

private theorem hasDerivAt_congr_branch {F G : ℝ → ℝ} {a x : ℝ}
    (hx : x ∈ branch) (hG : HasDerivAt G a x)
    (hEq : ∀ y ∈ branch, F y = G y) : HasDerivAt F a x := by
  have heq : F =ᶠ[nhds x] G := by
    filter_upwards [branch_isOpen.mem_nhds hx] with y hy
    exact hEq y hy
  exact hG.congr_of_eventuallyEq heq

private theorem antiderivatives_congr {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ branch, f x = g x) :
    AntiderivativesOn f = AntiderivativesOn g := by
  ext F
  constructor
  · intro hF x hx
    convert hF x hx using 1
    exact (hfg x hx).symm
  · intro hF x hx
    convert hF x hx using 1
    exact hfg x hx

private theorem antiderivatives_eq_scaled (f g : ℝ → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hfg : ∀ x ∈ branch, f x = c * g x) :
    AntiderivativesOn f = ScaledFamily c g := by
  ext F
  constructor
  · intro hF
    refine ⟨fun y => c⁻¹ * F y, ?_, ?_⟩
    · intro x hx
      convert (hF x hx).const_mul c⁻¹ using 1
      rw [hfg x hx]
      field_simp [hc]
    · intro x hx
      dsimp
      field_simp [hc]
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hscaled : HasDerivAt (fun y => c * G y) (f x) x := by
      convert (hG x hx).const_mul c using 1
      exact hfg x hx
    exact hasDerivAt_congr_branch hx hscaled hFG

private theorem antiderivatives_eq_primitive {f p : ℝ → ℝ}
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    AntiderivativesOn f = PrimitiveFamily p := by
  ext F
  constructor
  · intro hF
    let D : ℝ → ℝ := fun x => F x - p x
    have hD : ∀ x ∈ branch, HasDerivAt D 0 x := by
      intro x hx
      dsimp [D]
      convert (hF x hx).sub (hp x hx) using 1 <;> ring
    have hdiff : DifferentiableOn ℝ D branch := by
      intro x hx
      exact (hD x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ branch, deriv D x = 0 := by
      intro x hx
      exact (hD x hx).deriv
    have hpre : IsPreconnected branch := by
      simpa [branch] using
        (isPreconnected_Ioo : IsPreconnected (Set.Ioo (-1 : ℝ) 1))
    have hconst : ∀ x ∈ branch, ∀ y ∈ branch, D x = D y := by
      intro x hx y hy
      exact branch_isOpen.is_const_of_deriv_eq_zero hpre hdiff hderiv hx hy
    have hzero : (0 : ℝ) ∈ branch := by
      norm_num [branch]
    refine ⟨D 0, ?_⟩
    intro x hx
    have hsame : D x = D 0 := hconst x hx 0 hzero
    dsimp [D] at hsame ⊢
    linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    exact hasDerivAt_congr_branch hx ((hp x hx).add_const C) hFC

private theorem integrand_eq_first (x : ℝ) (hx : x ∈ branch) :
    integrand x = (1 / 3 : ℝ) * firstSubstitutedIntegrand x := by
  unfold integrand firstSubstitutedIntegrand
  rw [deriv_cube]
  unfold denominator
  ring

private theorem first_eq_shifted (x : ℝ) (hx : x ∈ branch) :
    firstSubstitutedIntegrand x = shiftedIntegrand x := by
  unfold firstSubstitutedIntegrand shiftedIntegrand
  rw [deriv_cube, deriv_shift_cube]
  ring

private theorem integrand_eq_factored (x : ℝ) (hx : x ∈ branch) :
    integrand x = (1 / 3 : ℝ) * factoredSubstitutedIntegrand x := by
  unfold integrand factoredSubstitutedIntegrand
  rw [deriv_cube, denominator_factor]
  ring

private theorem integrand_eq_partial (x : ℝ) (hx : x ∈ branch) :
    integrand x = (1 / 9 : ℝ) * partialFractionIntegrand x := by
  unfold integrand partialFractionIntegrand
  rw [deriv_cube, denominator_factor]
  field_simp [cube_add_one_ne hx, cube_sub_two_ne hx]
  ring

private theorem integrand_split (x : ℝ) (hx : x ∈ branch) :
    integrand x = (1 / 6 : ℝ) * logIntegrand x -
      (1 / 6 : ℝ) * hyperbolicIntegrand x := by
  unfold integrand logIntegrand hyperbolicIntegrand
  rw [deriv_shift_square, deriv_shift_cube]
  rw [show (x ^ 3 - 1 / 2) ^ 2 - 9 / 4 = denominator x by
    unfold denominator; ring]
  rw [show (3 / 2 : ℝ) ^ 2 - (x ^ 3 - 1 / 2) ^ 2 =
      -denominator x by unfold denominator; ring]
  field_simp [denominator_ne hx]
  ring

private def logarithmicPrimitive (x : ℝ) : ℝ :=
  Real.log |denominator x|

private def hyperbolicPrimitive (x : ℝ) : ℝ :=
  (1 / 3 : ℝ) *
    Real.log |((3 / 2 : ℝ) + x ^ 3 - 1 / 2) /
      ((3 / 2 : ℝ) - (x ^ 3 - 1 / 2))|

private theorem hasDerivAt_logarithmicPrimitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt logarithmicPrimitive (logIntegrand x) x := by
  have hD : HasDerivAt denominator (6 * x ^ 5 - 3 * x ^ 2) x := by
    convert ((((hasDerivAt_id x).pow 6).sub
      ((hasDerivAt_id x).pow 3)).sub_const 2) using 1 <;>
      simp [denominator] <;> ring
  have hlog : HasDerivAt logarithmicPrimitive
      ((6 * x ^ 5 - 3 * x ^ 2) / denominator x) x := by
    change HasDerivAt (fun y : ℝ => Real.log |denominator y|)
      ((6 * x ^ 5 - 3 * x ^ 2) / denominator x) x
    simpa only [Real.log_abs] using hD.log (denominator_ne hx)
  convert hlog using 1
  unfold logIntegrand
  rw [deriv_shift_square]
  rw [show (x ^ 3 - 1 / 2) ^ 2 - 9 / 4 = denominator x by
    unfold denominator; ring]
  ring

private theorem hasDerivAt_hyperbolicPrimitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt hyperbolicPrimitive (hyperbolicIntegrand x) x := by
  let A : ℝ → ℝ := fun t => (3 / 2 : ℝ) + t ^ 3 - 1 / 2
  let B : ℝ → ℝ := fun t => (3 / 2 : ℝ) - (t ^ 3 - 1 / 2)
  have hA : HasDerivAt A (3 * x ^ 2) x := by
    dsimp [A]
    convert (((hasDerivAt_id x).pow 3).const_add (3 / 2 : ℝ)).sub_const
      (1 / 2 : ℝ) using 1 <;> norm_num <;> ring
  have hB : HasDerivAt B (-3 * x ^ 2) x := by
    dsimp [B]
    convert ((hasDerivAt_id x).pow 3).neg.const_add (2 : ℝ) using 1 <;>
      norm_num <;> ring
  have hAne : A x ≠ 0 := by
    dsimp [A]
    have h := cube_add_one_ne hx
    convert h using 1 <;> ring
  have hBne : B x ≠ 0 := by
    dsimp [B]
    have h := cube_sub_two_ne hx
    intro hz
    apply h
    linarith
  have hq := hA.div hB hBne
  have hqne : A x / B x ≠ 0 := div_ne_zero hAne hBne
  have hlog := hq.log hqne
  have habs : HasDerivAt
      (fun t => Real.log |A t / B t|)
      (((3 * x ^ 2) * B x - A x * (-3 * x ^ 2)) / B x ^ 2 /
        (A x / B x)) x := by
    simpa only [Real.log_abs] using hlog
  have hscaled := habs.const_mul (1 / 3 : ℝ)
  have hfun : hyperbolicPrimitive =
      (fun t => (1 / 3 : ℝ) * Real.log |A t / B t|) := by
    funext t
    rfl
  have hval : (1 / 3 : ℝ) *
      (((3 * x ^ 2) * B x - A x * (-3 * x ^ 2)) / B x ^ 2 /
        (A x / B x)) = hyperbolicIntegrand x := by
    unfold hyperbolicIntegrand
    rw [deriv_shift_cube]
    rw [show (3 / 2 : ℝ) ^ 2 - (x ^ 3 - 1 / 2) ^ 2 = A x * B x by
      dsimp [A, B]; ring]
    field_simp [hAne, hBne]
    ring
  rw [hfun, ← hval]
  exact hscaled

private theorem hasDerivAt_primitiveRaw (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveRaw (integrand x) x := by
  have h :=
    ((hasDerivAt_logarithmicPrimitive x hx).const_mul (1 / 6 : ℝ)).sub
      ((hasDerivAt_hyperbolicPrimitive x hx).const_mul (1 / 6 : ℝ))
  convert h using 1
  · funext t
    dsimp [primitiveRaw, logarithmicPrimitive, hyperbolicPrimitive]
    ring
  · exact integrand_split x hx

private theorem hasDerivAt_primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (integrand x) x := by
  have hA : HasDerivAt (fun t : ℝ => t ^ 3 + 1) (3 * x ^ 2) x := by
    convert ((hasDerivAt_id x).pow 3).add_const (1 : ℝ) using 1 <;>
      norm_num <;> ring
  have hB : HasDerivAt (fun t : ℝ => t ^ 3 - 2) (3 * x ^ 2) x := by
    convert ((hasDerivAt_id x).pow 3).sub_const (2 : ℝ) using 1 <;>
      norm_num <;> ring
  have hK : HasDerivAt
      (fun t : ℝ => (t ^ 3 + 1) * (t ^ 3 - 2) ^ 2)
      (3 * x ^ 2 * (x ^ 3 - 2) ^ 2 +
        (x ^ 3 + 1) * (2 * (x ^ 3 - 2) * (3 * x ^ 2))) x := by
    convert hA.mul (hB.pow 2) using 1 <;> norm_num <;> ring
  have hKne : (x ^ 3 + 1) * (x ^ 3 - 2) ^ 2 ≠ 0 := by
    exact mul_ne_zero (cube_add_one_ne hx)
      (pow_ne_zero 2 (cube_sub_two_ne hx))
  have hlog := hK.log hKne
  have habs : HasDerivAt
      (fun t : ℝ => Real.log |(t ^ 3 + 1) * (t ^ 3 - 2) ^ 2|)
      ((3 * x ^ 2 * (x ^ 3 - 2) ^ 2 +
        (x ^ 3 + 1) * (2 * (x ^ 3 - 2) * (3 * x ^ 2))) /
        ((x ^ 3 + 1) * (x ^ 3 - 2) ^ 2)) x := by
    simpa only [Real.log_abs] using hlog
  have hscaled := habs.const_mul (1 / 9 : ℝ)
  convert hscaled using 1
  · ext t
    simp only [primitive, abs_mul, abs_sq]
  · unfold integrand
    rw [denominator_factor]
    field_simp [cube_add_one_ne hx, cube_sub_two_ne hx]
    ring

theorem gap1 :
    AntiderivativesOn integrand =
      ScaledFamily (1 / 3) firstSubstitutedIntegrand := by
  exact antiderivatives_eq_scaled
    (f := integrand) (g := firstSubstitutedIntegrand)
    (c := (1 / 3 : ℝ)) (by norm_num) integrand_eq_first
theorem gap2 :
    ScaledFamily (1 / 3) firstSubstitutedIntegrand =
      ScaledFamily (1 / 3) shiftedIntegrand := by
  unfold ScaledFamily
  rw [antiderivatives_congr first_eq_shifted]
theorem gap3 :
    AntiderivativesOn integrand =
      ScaledFamily (1 / 3) shiftedIntegrand := by
  exact gap1.trans gap2
theorem gap4 :
    AntiderivativesOn integrand = SplitFamily := by
  ext F
  constructor
  · intro hF
    rw [antiderivatives_eq_primitive (f := integrand) (p := primitiveRaw)
      hasDerivAt_primitiveRaw] at hF
    rcases hF with ⟨C, hFC⟩
    refine ⟨fun x => logarithmicPrimitive x + 6 * C, ?_,
      hyperbolicPrimitive, ?_, ?_⟩
    · intro x hx
      exact (hasDerivAt_logarithmicPrimitive x hx).add_const (6 * C)
    · intro x hx
      exact hasDerivAt_hyperbolicPrimitive x hx
    · intro x hx
      rw [hFC x hx]
      simp only [primitiveRaw, logarithmicPrimitive, hyperbolicPrimitive]
      ring
  · rintro ⟨G, hG, H, hH, hF⟩
    intro x hx
    have hcomb := ((hG x hx).const_mul (1 / 6 : ℝ)).sub
      ((hH x hx).const_mul (1 / 6 : ℝ))
    have hcomb' : HasDerivAt
        (fun y => (1 / 6 : ℝ) * G y - (1 / 6 : ℝ) * H y)
        (integrand x) x := by
      convert hcomb using 1
      exact integrand_split x hx
    exact hasDerivAt_congr_branch hx hcomb' hF
theorem gap5 :
    AntiderivativesOn integrand = PrimitiveFamily primitiveRaw := by
  exact antiderivatives_eq_primitive (f := integrand) (p := primitiveRaw)
    hasDerivAt_primitiveRaw
theorem gap6 :
    PrimitiveFamily primitiveRaw = PrimitiveFamily primitive := by
  exact
    (antiderivatives_eq_primitive (f := integrand) (p := primitiveRaw)
      hasDerivAt_primitiveRaw).symm.trans
    (antiderivatives_eq_primitive (f := integrand) (p := primitive)
      hasDerivAt_primitive)
theorem gap7 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  exact gap5.trans gap6
theorem gap8 :
    AntiderivativesOn integrand =
      ScaledFamily (1 / 3) factoredSubstitutedIntegrand := by
  exact antiderivatives_eq_scaled
    (f := integrand) (g := factoredSubstitutedIntegrand)
    (c := (1 / 3 : ℝ)) (by norm_num) integrand_eq_factored
theorem gap9 :
    ScaledFamily (1 / 3) factoredSubstitutedIntegrand =
      ScaledFamily (1 / 9) partialFractionIntegrand := by
  exact gap8.symm.trans
    (antiderivatives_eq_scaled
      (f := integrand) (g := partialFractionIntegrand)
      (c := (1 / 9 : ℝ)) (by norm_num) integrand_eq_partial)
theorem gap10 :
    AntiderivativesOn integrand =
      ScaledFamily (1 / 9) partialFractionIntegrand := by
  exact gap8.trans gap9
theorem gap11 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  exact gap7

end
end ProofGap.Exercise1843
