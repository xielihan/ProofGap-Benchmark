import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace ProofGap.Exercise1985

noncomputable section

def cubeRoot (x : ℝ) :=
  Real.sign x * Real.rpow |x| (1 / 3 : ℝ)
def branch : Set ℝ := {x | x ≠ -1 ∧ x ≠ 0}
def leftBranch : Set ℝ := Set.Iio (-1)
def middleBranch : Set ℝ := Set.Ioo (-1) 0
def rightBranch : Set ℝ := Set.Ioi 0
def z (x : ℝ) := cubeRoot (1 + x ^ 3) / x
def xOfZ (y : ℝ) := 1 / cubeRoot (y ^ 3 - 1)
def originalIntegrand (x : ℝ) := 1 / cubeRoot (1 + x ^ 3)
def powerFormIntegrand (x : ℝ) := 1 / cubeRoot (1 + x ^ 3)
def transformedIntegrand (x : ℝ) :=
  z x / (z x ^ 3 - 1) * deriv z x
def firstPartialIntegrand (x : ℝ) :=
  1 / (z x - 1) * deriv z x
def secondPartialIntegrand (x : ℝ) :=
  (z x - 1) / (z x ^ 2 + z x + 1) * deriv z x
def primitive (x : ℝ) :=
  -1 / 3 * Real.log |z x - 1| +
    1 / 6 * Real.log (z x ^ 2 + z x + 1) -
    1 / Real.sqrt 3 * Real.arctan ((2 * z x + 1) / Real.sqrt 3)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def NegatedFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn transformedIntegrand,
    ∀ x ∈ branch, F x = -G x}
def PartialFractionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn firstPartialIntegrand,
    ∃ H ∈ AntiderivativesOn secondPartialIntegrand,
      ∀ x ∈ branch, F x = -1 / 3 * G x + 1 / 3 * H x}
def BranchwisePrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ Cleft Cmiddle Cright : ℝ,
    (∀ x ∈ leftBranch, F x = primitive x + Cleft) ∧
    (∀ x ∈ middleBranch, F x = primitive x + Cmiddle) ∧
    (∀ x ∈ rightBranch, F x = primitive x + Cright)}

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

private lemma continuousAt_cubeRoot {a : ℝ} (ha : a ≠ 0) :
    ContinuousAt cubeRoot a := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hc : ContinuousAt (fun y : ℝ => -Real.rpow (-y) (1 / 3 : ℝ)) a :=
      (continuousAt_id.neg.rpow_const (Or.inl (by
        exact neg_ne_zero.mpr ha))).neg
    apply hc.congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hneg] with y hy
    have hylt : y < 0 := hy
    rw [cubeRoot, Real.sign_of_neg hylt, abs_of_neg hylt]
    ring
  · have hc : ContinuousAt (fun y : ℝ => Real.rpow y (1 / 3 : ℝ)) a :=
      continuousAt_id.rpow_const (Or.inl ha)
    apply hc.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hpos] with y hy
    have hypos : 0 < y := hy
    rw [cubeRoot, Real.sign_of_pos hypos, abs_of_pos hypos, one_mul]

private lemma cubeRoot_ne {a : ℝ} (ha : a ≠ 0) : cubeRoot a ≠ 0 := by
  intro h
  have hc := cubeRoot_cube a
  rw [h] at hc
  norm_num at hc
  exact ha hc.symm

private lemma cubeRoot_hasDerivAt {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt cubeRoot (1 / (3 * cubeRoot a ^ 2)) a := by
  have hc := continuousAt_cubeRoot ha
  have hf : HasDerivAt (fun y : ℝ => y ^ 3) (3 * cubeRoot a ^ 2) (cubeRoot a) := by
    convert (hasDerivAt_id (cubeRoot a)).pow 3 using 1 <;> simp [id] <;> ring
  have hne : 3 * cubeRoot a ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (cubeRoot_ne ha))
  have hleft : ∀ᶠ y in nhds a, (fun v : ℝ => v ^ 3) (cubeRoot y) = y :=
    Filter.Eventually.of_forall cubeRoot_cube
  convert hf.of_local_left_inverse hc hne hleft using 1
  simp only [one_div]

private lemma z_cube_sub_one (x : ℝ) (hx : x ≠ 0) :
    z x ^ 3 - 1 = 1 / x ^ 3 := by
  unfold z
  field_simp [hx]
  rw [cubeRoot_cube]
  ring

private lemma xOfZ_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt xOfZ
      (-z x ^ 2 / cubeRoot (z x ^ 3 - 1) ^ 4) (z x) := by
  have ha : z x ^ 3 - 1 ≠ 0 := by
    rw [z_cube_sub_one x hx.2]
    exact one_div_ne_zero (pow_ne_zero 3 hx.2)
  have hinner : HasDerivAt (fun y : ℝ => y ^ 3 - 1) (3 * z x ^ 2) (z x) := by
    convert ((hasDerivAt_id (z x)).pow 3).sub_const 1 using 1 <;>
      simp [id] <;> ring
  have hroot := (cubeRoot_hasDerivAt ha).comp (z x) hinner
  have hroot' : HasDerivAt (fun y : ℝ => cubeRoot (y ^ 3 - 1))
      ((1 / (3 * cubeRoot (z x ^ 3 - 1) ^ 2)) * (3 * z x ^ 2)) (z x) := by
    simpa [Function.comp_def] using hroot
  unfold xOfZ
  convert (hasDerivAt_const (z x) (1 : ℝ)).div hroot' (cubeRoot_ne ha) using 1
  field_simp [cubeRoot_ne ha]
  ring

private lemma one_add_cube_ne (x : ℝ) (hx : x ∈ branch) :
    1 + x ^ 3 ≠ 0 := by
  intro h
  have hp : x ^ 3 = (-1 : ℝ) ^ 3 := by
    norm_num
    linarith
  exact hx.1 ((show Odd 3 by decide).strictMono_pow.injective hp)

private lemma z_hasDerivAt_raw (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt z
      (((x ^ 2 / cubeRoot (1 + x ^ 3) ^ 2) * x -
          cubeRoot (1 + x ^ 3)) / x ^ 2) x := by
  have ha := one_add_cube_ne x hx
  have hinner : HasDerivAt (fun y : ℝ => 1 + y ^ 3) (3 * x ^ 2) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 3) using 1 <;>
      simp [id] <;> ring
  have hroot := (cubeRoot_hasDerivAt ha).comp x hinner
  have hroot' : HasDerivAt (fun y : ℝ => cubeRoot (1 + y ^ 3))
      (x ^ 2 / cubeRoot (1 + x ^ 3) ^ 2) x := by
    convert hroot using 1
    field_simp [cubeRoot_ne ha]
  unfold z
  simpa only [id, Pi.div_apply, mul_one] using
    hroot'.div (hasDerivAt_id x) hx.2

private lemma transformed_eq_neg_original (x : ℝ) (hx : x ∈ branch) :
    transformedIntegrand x = -originalIntegrand x := by
  have ha := one_add_cube_ne x hx
  have hr : cubeRoot (1 + x ^ 3) ≠ 0 := cubeRoot_ne ha
  have hcube := cubeRoot_cube (1 + x ^ 3)
  have hz3 := z_cube_sub_one x hx.2
  have hder := (z_hasDerivAt_raw x hx).deriv
  unfold transformedIntegrand
  rw [hder, hz3]
  unfold originalIntegrand z
  field_simp [hx.2, hr]
  nlinarith

private lemma branch_isOpen : IsOpen branch := by
  have h : branch = ({-1} : Set ℝ)ᶜ ∩ ({0} : Set ℝ)ᶜ := by
    ext x
    simp [branch]
  rw [h]
  exact isOpen_compl_singleton.inter isOpen_compl_singleton

private lemma z_ne_one (x : ℝ) (hx : x ∈ branch) : z x ≠ 1 := by
  intro hz
  have hcube := cubeRoot_cube (1 + x ^ 3)
  unfold z at hz
  have heq : cubeRoot (1 + x ^ 3) = x := by
    field_simp [hx.2] at hz
    linarith
  rw [heq] at hcube
  linarith

private lemma z_quadratic_pos (x : ℝ) : 0 < z x ^ 2 + z x + 1 := by
  nlinarith [sq_nonneg (z x + 1 / 2)]

private lemma transformed_partial (x : ℝ) (hx : x ∈ branch) :
    transformedIntegrand x =
      (1 / 3 : ℝ) * firstPartialIntegrand x -
        (1 / 3 : ℝ) * secondPartialIntegrand x := by
  have h1 := z_ne_one x hx
  have hq : z x ^ 2 + z x + 1 ≠ 0 := (z_quadratic_pos x).ne'
  have hq' : 1 + z x + z x ^ 2 ≠ 0 := by
    intro h
    apply hq
    linarith
  have hq'' : z x * (z x + 1) + 1 ≠ 0 := by
    intro h
    apply hq
    nlinarith
  have hcubic : z x ^ 3 - 1 ≠ 0 := by
    rw [show z x ^ 3 - 1 = (z x - 1) * (z x ^ 2 + z x + 1) by ring]
    exact mul_ne_zero (sub_ne_zero.mpr h1) hq
  have hid : z x / (z x ^ 3 - 1) =
      (1 / 3 : ℝ) * (1 / (z x - 1)) -
        (1 / 3 : ℝ) * ((z x - 1) / (z x ^ 2 + z x + 1)) := by
    rw [div_eq_iff hcubic]
    rw [show z x ^ 3 - 1 = (z x - 1) * (z x ^ 2 + z x + 1) by ring]
    field_simp [sub_ne_zero.mpr h1, hq, hq', hq'']
    ring
  unfold transformedIntegrand firstPartialIntegrand secondPartialIntegrand
  rw [hid]
  ring

private def firstPrimitive (x : ℝ) := Real.log |z x - 1|

private lemma firstPrimitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt firstPrimitive (firstPartialIntegrand x) x := by
  have hz := z_hasDerivAt_raw x hx
  have h1 := z_ne_one x hx
  unfold firstPrimitive firstPartialIntegrand
  simp only [Real.log_abs]
  convert (Real.hasDerivAt_log (sub_ne_zero.mpr h1)).comp x (hz.sub_const 1) using 1
  rw [hz.deriv]
  simp only [one_div]

private def secondPrimitive (x : ℝ) :=
  1 / 2 * Real.log (z x ^ 2 + z x + 1) -
    Real.sqrt 3 * Real.arctan ((2 * z x + 1) / Real.sqrt 3)

private lemma sqrt_three_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
private lemma sqrt_three_ne : Real.sqrt 3 ≠ 0 := sqrt_three_pos.ne'
private lemma sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private lemma secondPrimitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt secondPrimitive (secondPartialIntegrand x) x := by
  have hz := z_hasDerivAt_raw x hx
  let d : ℝ := deriv z x
  have hzd : HasDerivAt z d x := by
    rw [← hz.deriv] at hz
    exact hz
  have hq : HasDerivAt (fun y => z y ^ 2 + z y + 1)
      ((2 * z x + 1) * d) x := by
    convert ((hzd.pow 2).add hzd).add_const 1 using 1 <;> ring
  have hqpos := z_quadratic_pos x
  have hq' : 1 + z x + z x ^ 2 ≠ 0 := by
    intro h
    exact hqpos.ne' (by linarith)
  have hq'' : z x * (z x + 1) + 1 ≠ 0 := by
    intro h
    exact hqpos.ne' (by nlinarith)
  have hlog : HasDerivAt (fun y => Real.log (z y ^ 2 + z y + 1))
      (((2 * z x + 1) * d) / (z x ^ 2 + z x + 1)) x := by
    convert (Real.hasDerivAt_log hqpos.ne').comp x hq using 1
    ring
  have hu : HasDerivAt (fun y => (2 * z y + 1) / Real.sqrt 3)
      (2 * d / Real.sqrt 3) x := by
    convert (((hzd.const_mul 2).add_const 1).div_const (Real.sqrt 3)) using 1 <;>
      ring
  have hatan : HasDerivAt
      (fun y => Real.arctan ((2 * z y + 1) / Real.sqrt 3))
      ((1 / (1 + ((2 * z x + 1) / Real.sqrt 3) ^ 2)) *
        (2 * d / Real.sqrt 3)) x :=
    (Real.hasDerivAt_arctan _).comp x hu
  unfold secondPrimitive secondPartialIntegrand
  convert (hlog.const_mul (1 / 2)).sub (hatan.const_mul (Real.sqrt 3)) using 1
  dsimp [d]
  field_simp [sqrt_three_ne, hqpos.ne', hq', hq'']
  rw [sqrt_three_sq]
  ring

private lemma primitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (originalIntegrand x) x := by
  have hA := firstPrimitive_hasDerivAt x hx
  have hB := secondPrimitive_hasDerivAt x hx
  have hcoef : (1 / 3 : ℝ) * Real.sqrt 3 = 1 / Real.sqrt 3 := by
    field_simp [sqrt_three_ne]
    rw [sqrt_three_sq]
  have hrep : primitive =
      fun y => -1 / 3 * firstPrimitive y + 1 / 3 * secondPrimitive y := by
    funext y
    unfold primitive firstPrimitive secondPrimitive
    rw [← hcoef]
    ring
  rw [hrep]
  convert (hA.const_mul (-1 / 3)).add (hB.const_mul (1 / 3)) using 1
  have ht := transformed_eq_neg_original x hx
  rw [transformed_partial x hx] at ht
  linarith

theorem gap1 (x : ℝ) (hx : x ∈ branch) :
    originalIntegrand x = powerFormIntegrand x := by
  rfl
theorem gap2 (x : ℝ) (hx : x ∈ branch) :
    x = xOfZ (z x) := by
  have hx0 : x ≠ 0 := hx.2
  have hzrel : z x ^ 3 - 1 = 1 / x ^ 3 := by
    unfold z
    field_simp [hx0]
    rw [cubeRoot_cube]
    ring
  have hroot : cubeRoot (z x ^ 3 - 1) = 1 / x := by
    apply (show Odd 3 by decide).strictMono_pow.injective
    change cubeRoot (z x ^ 3 - 1) ^ 3 = (1 / x) ^ 3
    rw [cubeRoot_cube, hzrel]
    field_simp [hx0]
  unfold xOfZ
  rw [hroot]
  field_simp [hx0]
theorem gap3 (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt xOfZ
      (-z x ^ 2 / cubeRoot (z x ^ 3 - 1) ^ 4) (z x) := by
  exact xOfZ_hasDerivAt x hx
theorem gap4 :
    AntiderivativesOn originalIntegrand = NegatedFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨fun x => -F x, ?_, ?_⟩
    · intro x hx
      convert (hF x hx).neg using 1
      exact transformed_eq_neg_original x hx
    · intro x _
      ring
  · rintro ⟨G, hG, hEq⟩ x hx
    have heq : F =ᶠ[nhds x] (fun y => -G y) := by
      filter_upwards [branch_isOpen.mem_nhds hx] with y hy
      exact hEq y hy
    convert (hG x hx).neg.congr_of_eventuallyEq heq using 1
    rw [transformed_eq_neg_original x hx]
    ring
theorem gap5 :
    NegatedFamily = PartialFractionFamily := by
  ext F
  constructor
  · rintro ⟨T, hT, hFT⟩
    let A : ℝ → ℝ := firstPrimitive
    have hA : A ∈ AntiderivativesOn firstPartialIntegrand :=
      fun x hx => firstPrimitive_hasDerivAt x hx
    let B : ℝ → ℝ := fun x => -3 * T x + A x
    have hB : B ∈ AntiderivativesOn secondPartialIntegrand := by
      intro x hx
      convert ((hT x hx).const_mul (-3)).add (hA x hx) using 1
      rw [transformed_partial x hx]
      ring
    refine ⟨A, hA, B, hB, ?_⟩
    intro x hx
    rw [hFT x hx]
    dsimp [B]
    ring
  · rintro ⟨A, hA, B, hB, hF⟩
    let T : ℝ → ℝ := fun x => -(-1 / 3 * A x + 1 / 3 * B x)
    have hT : T ∈ AntiderivativesOn transformedIntegrand := by
      intro x hx
      convert (((hA x hx).const_mul (-1 / 3)).add
        ((hB x hx).const_mul (1 / 3))).neg using 1
      rw [transformed_partial x hx]
      ring
    refine ⟨T, hT, ?_⟩
    intro x hx
    rw [hF x hx]
    dsimp [T]
    ring
theorem gap6 :
    AntiderivativesOn originalIntegrand = PartialFractionFamily := by
  rw [gap4, gap5]
theorem gap7 :
    AntiderivativesOn originalIntegrand =
      BranchwisePrimitiveFamily := by
  ext F
  constructor
  · intro hF
    have hz : ∀ x ∈ branch,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      convert (hF x hx).sub (primitive_hasDerivAt x hx) using 1 <;> ring
    obtain ⟨Cleft, hCleft⟩ :=
      (show IsOpen leftBranch from by
        unfold leftBranch
        exact isOpen_Iio)
      |>.exists_is_const_of_deriv_eq_zero
      (show IsPreconnected leftBranch from by
        unfold leftBranch
        exact isPreconnected_Iio)
      (fun x hx => (hz x (by
        change x ≠ -1 ∧ x ≠ 0
        have hxl : x < -1 := hx
        exact ⟨by linarith, by linarith⟩)).differentiableAt.differentiableWithinAt)
      (fun x hx => (hz x (by
        change x ≠ -1 ∧ x ≠ 0
        have hxl : x < -1 := hx
        exact ⟨by linarith, by linarith⟩)).deriv)
    obtain ⟨Cmiddle, hCmiddle⟩ :=
      (show IsOpen middleBranch from by
        unfold middleBranch
        exact isOpen_Ioo)
      |>.exists_is_const_of_deriv_eq_zero
      (show IsPreconnected middleBranch from by
        unfold middleBranch
        exact isPreconnected_Ioo)
      (fun x hx => (hz x (by
        change x ≠ -1 ∧ x ≠ 0
        exact ⟨hx.1.ne', hx.2.ne⟩)).differentiableAt.differentiableWithinAt)
      (fun x hx => (hz x (by
        change x ≠ -1 ∧ x ≠ 0
        exact ⟨hx.1.ne', hx.2.ne⟩)).deriv)
    obtain ⟨Cright, hCright⟩ :=
      (show IsOpen rightBranch from by
        unfold rightBranch
        exact isOpen_Ioi)
      |>.exists_is_const_of_deriv_eq_zero
      (show IsPreconnected rightBranch from by
        unfold rightBranch
        exact isPreconnected_Ioi)
      (fun x hx => (hz x (by
        change x ≠ -1 ∧ x ≠ 0
        have hxr : 0 < x := hx
        exact ⟨by linarith, hxr.ne'⟩)).differentiableAt.differentiableWithinAt)
      (fun x hx => (hz x (by
        change x ≠ -1 ∧ x ≠ 0
        have hxr : 0 < x := hx
        exact ⟨by linarith, hxr.ne'⟩)).deriv)
    refine ⟨Cleft, Cmiddle, Cright, ?_, ?_, ?_⟩
    · intro x hx
      have h := hCleft x hx
      linarith
    · intro x hx
      have h := hCmiddle x hx
      linarith
    · intro x hx
      have h := hCright x hx
      linarith
  · rintro ⟨Cleft, Cmiddle, Cright, hleft, hmiddle, hright⟩ x hx
    rcases lt_or_gt_of_ne hx.1 with hxl | hxm
    · have heq : F =ᶠ[nhds x] (fun y => primitive y + Cleft) := by
        filter_upwards [isOpen_Iio.mem_nhds hxl] with y hy
        exact hleft y hy
      exact ((primitive_hasDerivAt x hx).add_const Cleft).congr_of_eventuallyEq heq
    · rcases lt_or_gt_of_ne hx.2 with hxmid | hxr
      · have hxmiddle : x ∈ middleBranch := ⟨hxm, hxmid⟩
        have heq : F =ᶠ[nhds x] (fun y => primitive y + Cmiddle) := by
          filter_upwards [isOpen_Ioo.mem_nhds hxmiddle] with y hy
          exact hmiddle y hy
        exact ((primitive_hasDerivAt x hx).add_const Cmiddle).congr_of_eventuallyEq heq
      · have heq : F =ᶠ[nhds x] (fun y => primitive y + Cright) := by
          filter_upwards [isOpen_Ioi.mem_nhds hxr] with y hy
          exact hright y hy
        exact ((primitive_hasDerivAt x hx).add_const Cright).congr_of_eventuallyEq heq
theorem gap8 :
    AntiderivativesOn originalIntegrand =
      BranchwisePrimitiveFamily := by
  exact gap7
theorem gap9 (x : ℝ) (hx : x ∈ branch) :
    z x = cubeRoot (1 + x ^ 3) / x := by
  rfl

end
end ProofGap.Exercise1985
