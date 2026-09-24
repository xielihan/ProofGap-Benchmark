import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1983

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def cubeRoot (x : ℝ) :=
  Real.sign x * Real.rpow |x| (1 / 3 : ℝ)
def twoThirdPower (x : ℝ) := cubeRoot x ^ 2
def z (x : ℝ) := Real.sqrt (1 + twoThirdPower x)
def xOfZ (y : ℝ) := (y ^ 2 - 1) * Real.sqrt (y ^ 2 - 1)
def originalIntegrand (x : ℝ) :=
  x / Real.sqrt (1 + cubeRoot (x ^ 2))
def powerFormIntegrand (x : ℝ) :=
  x / Real.sqrt (1 + twoThirdPower x)
def transformedIntegrand (x : ℝ) :=
  (z x ^ 2 - 1) ^ 2 * deriv z x
def primitive (x : ℝ) :=
  3 / 5 * z x ^ 5 - 2 * z x ^ 3 + 3 * z x
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ScaledFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn transformedIntegrand,
    ∀ x ∈ branch, F x = 3 * G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem rpow_third_cube (x : ℝ) (hx : 0 ≤ x) :
    Real.rpow x (1 / 3 : ℝ) ^ 3 = x := by
  calc
    Real.rpow x (1 / 3 : ℝ) ^ 3 =
        Real.rpow (Real.rpow x (1 / 3 : ℝ)) (3 : ℝ) := by
      exact (Real.rpow_natCast _ 3).symm
    _ = Real.rpow x ((1 / 3 : ℝ) * 3) := by
      exact (Real.rpow_mul hx _ _).symm
    _ = x := by norm_num

private theorem cubeRoot_cube (x : ℝ) : cubeRoot x ^ 3 = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [cubeRoot, Real.sign_of_neg hx, abs_of_neg hx]
    change (-1 * Real.rpow (-x) (1 / 3 : ℝ)) ^ 3 = x
    rw [show (-1 * Real.rpow (-x) (1 / 3 : ℝ)) ^ 3 =
      -(Real.rpow (-x) (1 / 3 : ℝ) ^ 3) by ring,
      rpow_third_cube (-x) (by linarith)]
    ring
  · norm_num [cubeRoot]
  · rw [cubeRoot, Real.sign_of_pos hx, abs_of_pos hx, one_mul]
    exact rpow_third_cube x hx.le

private theorem cube_pow_injective {u v : ℝ} (h : u ^ 3 = v ^ 3) : u = v :=
  (show Odd 3 by decide).strictMono_pow.injective h

private theorem cubeRoot_sq (u : ℝ) :
    cubeRoot (u ^ 2) = cubeRoot u ^ 2 := by
  apply cube_pow_injective
  calc
    cubeRoot (u ^ 2) ^ 3 = u ^ 2 := cubeRoot_cube _
    _ = (cubeRoot u ^ 3) ^ 2 := by rw [cubeRoot_cube]
    _ = (cubeRoot u ^ 2) ^ 3 := by ring

private theorem cubeRoot_ne_zero {u : ℝ} (hu : u ≠ 0) : cubeRoot u ≠ 0 := by
  intro h
  have hc := cubeRoot_cube u
  rw [h] at hc
  apply hu
  simpa using hc.symm

private theorem hasDerivAt_twoThird {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt twoThirdPower (2 / (3 * cubeRoot u)) u := by
  have hu2 : 0 < u ^ 2 := sq_pos_of_ne_zero hu
  have hsquare : HasDerivAt (fun z : ℝ => z ^ 2) (2 * u) u := by
    simpa [id, mul_comm] using (hasDerivAt_id u).pow 2
  have houter :
      HasDerivAt (fun w : ℝ => Real.rpow w (1 / 3 : ℝ))
        ((1 / 3 : ℝ) * Real.rpow (u ^ 2) ((1 / 3 : ℝ) - 1))
        (u ^ 2) :=
    Real.hasDerivAt_rpow_const (Or.inl hu2.ne')
  have hraw :
      HasDerivAt (fun z : ℝ => Real.rpow (z ^ 2) (1 / 3 : ℝ))
        (((1 / 3 : ℝ) * Real.rpow (u ^ 2) ((1 / 3 : ℝ) - 1)) *
          (2 * u)) u := by
    convert houter.comp_of_eq u hsquare rfl using 1 <;>
      simp [id, pow_two] <;> ring
  have hfun :
      twoThirdPower = fun z : ℝ => Real.rpow (z ^ 2) (1 / 3 : ℝ) := by
    funext z
    unfold twoThirdPower
    rw [← cubeRoot_sq]
    have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
    by_cases hz : z = 0
    · subst z
      norm_num [cubeRoot]
    · simp [cubeRoot, Real.sign_of_pos (sq_pos_of_ne_zero hz),
        abs_of_nonneg hz2]
  rw [hfun]
  convert hraw using 1
  have hr1 :
      Real.rpow (u ^ 2) (1 / 3 : ℝ) = cubeRoot u ^ 2 := by
    rw [← cubeRoot_sq]
    simp [cubeRoot, Real.sign_of_pos hu2, abs_of_pos hu2]
  have hr2 :
      Real.rpow (u ^ 2) (2 / 3 : ℝ) = (cubeRoot u ^ 2) ^ 2 := by
    calc
      Real.rpow (u ^ 2) (2 / 3 : ℝ) =
          Real.rpow (u ^ 2) ((1 / 3 : ℝ) * 2) := by congr 1 <;> ring
      _ = Real.rpow (Real.rpow (u ^ 2) (1 / 3 : ℝ)) (2 : ℝ) :=
        Real.rpow_mul hu2.le _ _
      _ = (cubeRoot u ^ 2) ^ 2 := by
        rw [hr1]
        exact Real.rpow_two _
  have hneg :
      Real.rpow (u ^ 2) (-(2 / 3 : ℝ)) =
        (Real.rpow (u ^ 2) (2 / 3 : ℝ))⁻¹ :=
    Real.rpow_neg hu2.le _
  rw [show (1 / 3 : ℝ) - 1 = -(2 / 3 : ℝ) by ring, hneg, hr2]
  field_simp [cubeRoot_ne_zero hu]
  have hc := cubeRoot_cube u
  nlinarith

private theorem cubeRoot_pos {x : ℝ} (hx : 0 < x) : 0 < cubeRoot x := by
  simp [cubeRoot, Real.sign_of_pos hx, abs_of_pos hx,
    Real.rpow_pos_of_pos hx]

private theorem z_sq_sub_one (x : ℝ) :
    z x ^ 2 - 1 = twoThirdPower x := by
  unfold z
  rw [Real.sq_sqrt]
  · ring
  · unfold twoThirdPower
    positivity

private theorem hasDerivAt_z (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt z (1 / (3 * cubeRoot x * z x)) x := by
  have hxpos : 0 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hcpos : 0 < cubeRoot x := cubeRoot_pos hxpos
  have hzpos : 0 < z x := by
    unfold z twoThirdPower
    positivity
  have hinner : HasDerivAt (fun y : ℝ => 1 + twoThirdPower y)
      (2 / (3 * cubeRoot x)) x := by
    convert HasDerivAt.add (hasDerivAt_const x 1)
      (hasDerivAt_twoThird hx0) using 1 <;> ring
  have hraw := (Real.hasDerivAt_sqrt (by
    unfold twoThirdPower
    positivity : (1 + twoThirdPower x) ≠ 0)).comp x hinner
  unfold z
  convert hraw using 1 <;>
    field_simp [ne_of_gt hcpos, ne_of_gt hzpos] <;> ring

private theorem antiderivatives_eq_primitive
    (f p : ℝ → ℝ) (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    AntiderivativesOn f = {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C} := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨F 1 - p 1, ?_⟩
    intro x hx
    have hdiff : DifferentiableOn ℝ (fun y : ℝ => F y - p y) branch := by
      intro y hy
      exact ((hF y hy).sub (hp y hy)).differentiableAt.differentiableWithinAt
    have hzero : ∀ y ∈ branch, deriv (fun z : ℝ => F z - p z) y = 0 := by
      intro y hy
      have hd : HasDerivAt (fun z : ℝ => F z - p z) 0 y := by
        convert (hF y hy).sub (hp y hy) using 1 <;> ring
      exact hd.deriv
    have heq := isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      hdiff hzero (by
        show (1 : ℝ) ∈ branch
        norm_num [branch]) hx
    linarith
  · rintro ⟨C, hC⟩ x hx
    have hd : HasDerivAt (fun y : ℝ => p y + C) (f x) x := by
      convert HasDerivAt.add (hp x hx) (hasDerivAt_const x C) using 1 <;> ring
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hC y hy

theorem gap1 (x : ℝ) :
    originalIntegrand x = powerFormIntegrand x := by
  unfold originalIntegrand powerFormIntegrand
  unfold twoThirdPower
  rw [cubeRoot_sq]
theorem gap2 (x : ℝ) (hx : x ∈ branch) :
    x = xOfZ (z x) := by
  have hxpos : 0 < x := hx
  have hcpos : 0 < cubeRoot x := cubeRoot_pos hxpos
  unfold xOfZ
  rw [z_sq_sub_one]
  unfold twoThirdPower
  rw [Real.sqrt_sq hcpos.le]
  rw [show cubeRoot x ^ 2 * cubeRoot x = cubeRoot x ^ 3 by ring,
    cubeRoot_cube]
theorem gap3 (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt xOfZ (3 * z x * Real.sqrt (z x ^ 2 - 1)) (z x) := by
  have hxpos : 0 < x := hx
  have hcpos : 0 < cubeRoot x := cubeRoot_pos hxpos
  have hrad : 0 < z x ^ 2 - 1 := by
    rw [z_sq_sub_one]
    unfold twoThirdPower
    positivity
  have hspos : 0 < Real.sqrt (z x ^ 2 - 1) := Real.sqrt_pos.2 hrad
  have hs0 : Real.sqrt (z x ^ 2 - 1) ≠ 0 := ne_of_gt hspos
  have hinner : HasDerivAt (fun y : ℝ => y ^ 2 - 1)
      (2 * z x) (z x) := by
    convert ((hasDerivAt_id (z x)).pow 2).sub_const 1 using 1 <;>
      simp only [id_eq] <;> ring
  have hsqrt : HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 - 1))
      (z x / Real.sqrt (z x ^ 2 - 1)) (z x) := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp (z x) hinner
      using 1 <;> field_simp [hs0] <;> ring
  have hprod : HasDerivAt
      (fun y : ℝ => (y ^ 2 - 1) * Real.sqrt (y ^ 2 - 1))
      ((2 * z x) * Real.sqrt (z x ^ 2 - 1) +
        (z x ^ 2 - 1) * (z x / Real.sqrt (z x ^ 2 - 1))) (z x) :=
    hinner.mul hsqrt
  unfold xOfZ
  convert hprod using 1
  field_simp [hs0]
  rw [Real.sq_sqrt hrad.le]
  ring
private theorem original_eq_three_transformed (x : ℝ) (hx : x ∈ branch) :
    originalIntegrand x = 3 * transformedIntegrand x := by
  have hxpos : 0 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hcpos : 0 < cubeRoot x := cubeRoot_pos hxpos
  have hc0 : cubeRoot x ≠ 0 := ne_of_gt hcpos
  have hzpos : 0 < z x := by
    unfold z twoThirdPower
    positivity
  have hz0 : z x ≠ 0 := ne_of_gt hzpos
  have hzderiv := (hasDerivAt_z x hx).deriv
  rw [gap1]
  unfold powerFormIntegrand transformedIntegrand
  change x / z x = 3 * ((z x ^ 2 - 1) ^ 2 * deriv z x)
  rw [hzderiv, z_sq_sub_one]
  unfold twoThirdPower
  field_simp [hc0, hz0]
  rw [cubeRoot_cube]

private theorem scaledFamily_eq_antiderivatives :
    ScaledFamily =
      AntiderivativesOn (fun x => 3 * transformedIntegrand x) := by
  apply Set.ext
  intro F
  simp only [ScaledFamily, AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, hFG⟩ x hx
    have hd := (hG x hx).const_mul 3
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hFG y hy
  · intro hF
    refine ⟨(fun y => F y / 3), ?_, ?_⟩
    · intro x hx
      convert (hF x hx).div_const 3 using 1 <;> norm_num
    · intro x hx
      field_simp

private theorem hasDerivAt_primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (3 * transformedIntegrand x) x := by
  have hz := hasDerivAt_z x hx
  have h5 := (hz.pow 5).const_mul (3 / 5)
  have h3 := (hz.pow 3).const_mul 2
  have h1 := hz.const_mul 3
  have hraw := (h5.sub h3).add h1
  have hcoef :
      (3 / 5) * (5 * z x ^ 4 * (1 / (3 * cubeRoot x * z x))) -
          2 * (3 * z x ^ 2 * (1 / (3 * cubeRoot x * z x))) +
          3 * (1 / (3 * cubeRoot x * z x)) =
        3 * transformedIntegrand x := by
    unfold transformedIntegrand
    rw [hz.deriv]
    ring
  have hfinal := hraw.congr_deriv hcoef
  apply hfinal.congr_of_eventuallyEq
  filter_upwards [] with y
  unfold primitive
  simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
theorem gap4 :
    AntiderivativesOn originalIntegrand = ScaledFamily := by
  calc
    AntiderivativesOn originalIntegrand =
        AntiderivativesOn (fun x => 3 * transformedIntegrand x) := by
      apply Set.ext
      intro F
      simp only [AntiderivativesOn, Set.mem_setOf_eq]
      constructor
      · intro hF x hx
        exact (hF x hx).congr_deriv (original_eq_three_transformed x hx)
      · intro hF x hx
        exact (hF x hx).congr_deriv
          (original_eq_three_transformed x hx).symm
    _ = ScaledFamily := scaledFamily_eq_antiderivatives.symm
theorem gap5 :
    ScaledFamily = PrimitiveFamily := by
  rw [scaledFamily_eq_antiderivatives]
  unfold PrimitiveFamily
  exact antiderivatives_eq_primitive
    (fun x => 3 * transformedIntegrand x) primitive hasDerivAt_primitive
theorem gap6 :
    AntiderivativesOn originalIntegrand = PrimitiveFamily := by
  rw [gap4, gap5]
theorem gap7 (x : ℝ) (hx : x ∈ branch) :
    z x = Real.sqrt (1 + cubeRoot (x ^ 2)) := by
  unfold z twoThirdPower
  rw [cubeRoot_sq]

end
end ProofGap.Exercise1983
