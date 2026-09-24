import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue

namespace ProofGap.Exercise1986

noncomputable section

def fourthRoot (x : ℝ) := Real.rpow x (1 / 4 : ℝ)
def branch : Set ℝ := Set.Ioi 0
def z (x : ℝ) := fourthRoot (1 + x ^ 4) / x
def xOfZ (y : ℝ) := 1 / fourthRoot (y ^ 4 - 1)
def originalIntegrand (x : ℝ) := 1 / fourthRoot (1 + x ^ 4)
def powerFormIntegrand (x : ℝ) := 1 / fourthRoot (1 + x ^ 4)
def transformedIntegrand (x : ℝ) :=
  z x ^ 2 / (z x ^ 4 - 1) * deriv z x
def partialFractionIntegrand (x : ℝ) :=
  (1 / (4 * (z x + 1)) -
    1 / (4 * (z x - 1)) -
    1 / (2 * (z x ^ 2 + 1))) * deriv z x
def primitive (x : ℝ) :=
  1 / 4 * Real.log |(z x + 1) / (z x - 1)| -
    1 / 2 * Real.arctan (z x)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def NegatedFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn transformedIntegrand,
    ∀ x ∈ branch, F x = -G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem fourthRoot_pos {u : ℝ} (hu : 0 < u) :
    0 < fourthRoot u := by
  unfold fourthRoot
  exact Real.rpow_pos_of_pos hu _

private theorem fourthRoot_pow_four {u : ℝ} (hu : 0 ≤ u) :
    fourthRoot u ^ 4 = u := by
  unfold fourthRoot
  calc
    Real.rpow u (1 / 4 : ℝ) ^ 4 =
        Real.rpow (Real.rpow u (1 / 4 : ℝ)) (4 : ℝ) :=
      (Real.rpow_natCast (Real.rpow u (1 / 4 : ℝ)) 4).symm
    _ = Real.rpow u ((1 / 4 : ℝ) * 4) :=
      (Real.rpow_mul hu (1 / 4 : ℝ) (4 : ℝ)).symm
    _ = u := by norm_num

private theorem rpow_quarter_sub_one_mul_cube {u : ℝ} (hu : 0 < u) :
    Real.rpow u ((1 / 4 : ℝ) - 1) * fourthRoot u ^ 3 = 1 := by
  have hc : fourthRoot u ^ 3 = Real.rpow u (3 / 4 : ℝ) := by
    unfold fourthRoot
    calc
      Real.rpow u (1 / 4 : ℝ) ^ 3 =
          Real.rpow (Real.rpow u (1 / 4 : ℝ)) (3 : ℝ) :=
        (Real.rpow_natCast (Real.rpow u (1 / 4 : ℝ)) 3).symm
      _ = Real.rpow u ((1 / 4 : ℝ) * 3) :=
        (Real.rpow_mul hu.le (1 / 4 : ℝ) (3 : ℝ)).symm
      _ = Real.rpow u (3 / 4 : ℝ) := by norm_num
  rw [hc]
  calc
    Real.rpow u ((1 / 4 : ℝ) - 1) * Real.rpow u (3 / 4 : ℝ) =
        Real.rpow u (((1 / 4 : ℝ) - 1) + 3 / 4) :=
      (Real.rpow_add hu ((1 / 4 : ℝ) - 1) (3 / 4 : ℝ)).symm
    _ = 1 := by norm_num

private theorem fourthRoot_eq_of_pos {u a : ℝ}
    (hu : 0 < u) (ha : 0 < a) (ha4 : a ^ 4 = u) :
    fourthRoot u = a := by
  have hr : 0 < fourthRoot u := fourthRoot_pos hu
  have hr4 : fourthRoot u ^ 4 = u := fourthRoot_pow_four hu.le
  have hfac :
      (fourthRoot u ^ 2 - a ^ 2) *
          (fourthRoot u ^ 2 + a ^ 2) = 0 := by
    calc
      (fourthRoot u ^ 2 - a ^ 2) *
          (fourthRoot u ^ 2 + a ^ 2) =
          fourthRoot u ^ 4 - a ^ 4 := by ring
      _ = 0 := by rw [hr4, ha4]; ring
  have hsum : fourthRoot u ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hsq : fourthRoot u ^ 2 = a ^ 2 := by
    have h := (mul_eq_zero.mp hfac).resolve_right hsum
    linarith
  have hfac' : (fourthRoot u - a) * (fourthRoot u + a) = 0 := by
    calc
      (fourthRoot u - a) * (fourthRoot u + a) =
          fourthRoot u ^ 2 - a ^ 2 := by ring
      _ = 0 := by rw [hsq]; ring
  have hsum' : fourthRoot u + a ≠ 0 := by positivity
  have h := (mul_eq_zero.mp hfac').resolve_right hsum'
  linarith

private theorem fourthRoot_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt fourthRoot (1 / (4 * fourthRoot u ^ 3)) u := by
  have hraw :
      HasDerivAt fourthRoot
        ((1 / 4 : ℝ) * Real.rpow u ((1 / 4 : ℝ) - 1)) u := by
    change HasDerivAt (fun t : ℝ => Real.rpow t (1 / 4 : ℝ))
      ((1 / 4 : ℝ) * Real.rpow u ((1 / 4 : ℝ) - 1)) u
    exact Real.hasDerivAt_rpow_const (p := (1 / 4 : ℝ))
      (Or.inl (ne_of_gt hu))
  have hr : fourthRoot u ≠ 0 := ne_of_gt (fourthRoot_pos hu)
  have hm := rpow_quarter_sub_one_mul_cube hu
  have hs :
      Real.rpow u ((1 / 4 : ℝ) - 1) = 1 / fourthRoot u ^ 3 := by
    apply (eq_div_iff (pow_ne_zero 3 hr)).2
    simpa using hm
  convert hraw using 1
  rw [hs]
  ring

private theorem z_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt z
      (-1 / (x ^ 2 * fourthRoot (1 + x ^ 4) ^ 3)) x := by
  have hxpos : 0 < x := hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hu : 0 < 1 + x ^ 4 := by positivity
  have hr : 0 < fourthRoot (1 + x ^ 4) := fourthRoot_pos hu
  have hrne : fourthRoot (1 + x ^ 4) ≠ 0 := ne_of_gt hr
  have hr4 : fourthRoot (1 + x ^ 4) ^ 4 = 1 + x ^ 4 :=
    fourthRoot_pow_four hu.le
  have hpow :
      HasDerivAt (fun t : ℝ => t ^ 4) (4 * x ^ 3) x := by
    simpa using ((hasDerivAt_id x).pow 4)
  have hinner :
      HasDerivAt (fun t : ℝ => 1 + t ^ 4) (4 * x ^ 3) x := by
    simpa using hpow.const_add 1
  have hroot :
      HasDerivAt (fun t : ℝ => fourthRoot (1 + t ^ 4))
        (x ^ 3 / fourthRoot (1 + x ^ 4) ^ 3) x := by
    convert (fourthRoot_hasDerivAt hu).comp x hinner using 1
    field_simp [hrne]
  have hquot :
      HasDerivAt z
        ((x ^ 3 / fourthRoot (1 + x ^ 4) ^ 3 * x -
            fourthRoot (1 + x ^ 4)) / x ^ 2) x := by
    simpa [z, id] using hroot.div (hasDerivAt_id x) hxne
  convert hquot using 1
  field_simp [hxne, hrne]
  ring_nf at hr4 ⊢
  nlinarith [hr4]

private theorem z_four_sub_one (x : ℝ) (hx : x ∈ branch) :
    z x ^ 4 - 1 = 1 / x ^ 4 := by
  have hxpos : 0 < x := hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hu : 0 < 1 + x ^ 4 := by positivity
  have hr4 : fourthRoot (1 + x ^ 4) ^ 4 = 1 + x ^ 4 :=
    fourthRoot_pow_four hu.le
  unfold z
  field_simp [hxne]
  nlinarith [hr4]

private theorem z_gt_one (x : ℝ) (hx : x ∈ branch) : 1 < z x := by
  have hxpos : 0 < x := hx
  have hu : 0 < 1 + x ^ 4 := by positivity
  have hrpos : 0 < fourthRoot (1 + x ^ 4) := fourthRoot_pos hu
  have hr4 : fourthRoot (1 + x ^ 4) ^ 4 = 1 + x ^ 4 :=
    fourthRoot_pow_four hu.le
  have hroot_gt : x < fourthRoot (1 + x ^ 4) := by
    by_contra h
    have hle : fourthRoot (1 + x ^ 4) ≤ x := le_of_not_gt h
    have hsq : fourthRoot (1 + x ^ 4) ^ 2 ≤ x ^ 2 := by
      nlinarith [mul_self_le_mul_self (le_of_lt hrpos) hle]
    have hfour : fourthRoot (1 + x ^ 4) ^ 4 ≤ x ^ 4 := by
      nlinarith [mul_self_le_mul_self
        (sq_nonneg (fourthRoot (1 + x ^ 4))) hsq]
    nlinarith
  unfold z
  exact (one_lt_div hxpos).2 hroot_gt

private theorem x_eq_xOfZ_z (x : ℝ) (hx : x ∈ branch) :
    x = xOfZ (z x) := by
  have hxpos : 0 < x := hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hu : 0 < z x ^ 4 - 1 := by
    rw [z_four_sub_one x hx]
    exact one_div_pos.mpr (pow_pos hxpos 4)
  have hrecip : 0 < 1 / x := one_div_pos.mpr hxpos
  have hpow : (1 / x) ^ 4 = z x ^ 4 - 1 := by
    rw [z_four_sub_one x hx]
    field_simp [hxne]
  have hroot : fourthRoot (z x ^ 4 - 1) = 1 / x :=
    fourthRoot_eq_of_pos hu hrecip hpow
  unfold xOfZ
  rw [hroot]
  field_simp [hxne]

private theorem xOfZ_hasDerivAt (y : ℝ) (hy : 0 < y ^ 4 - 1) :
    HasDerivAt xOfZ
      (-y ^ 3 / fourthRoot (y ^ 4 - 1) ^ 5) y := by
  have hrpos : 0 < fourthRoot (y ^ 4 - 1) := fourthRoot_pos hy
  have hrne : fourthRoot (y ^ 4 - 1) ≠ 0 := ne_of_gt hrpos
  have hinner :
      HasDerivAt (fun t : ℝ => t ^ 4 - 1) (4 * y ^ 3) y := by
    simpa [id] using ((hasDerivAt_id y).pow 4).sub_const 1
  have hroot :
      HasDerivAt (fun t : ℝ => fourthRoot (t ^ 4 - 1))
        (y ^ 3 / fourthRoot (y ^ 4 - 1) ^ 3) y := by
    convert (fourthRoot_hasDerivAt hy).comp y hinner using 1
    field_simp [hrne]
  have hquot :
      HasDerivAt xOfZ
        ((0 * fourthRoot (y ^ 4 - 1) -
            1 * (y ^ 3 / fourthRoot (y ^ 4 - 1) ^ 3)) /
          fourthRoot (y ^ 4 - 1) ^ 2) y := by
    simpa [xOfZ] using
      (hasDerivAt_const y (1 : ℝ)).div hroot hrne
  convert hquot using 1
  field_simp [hrne]
  ring

private theorem transformed_eq_neg_original (x : ℝ) (hx : x ∈ branch) :
    transformedIntegrand x = -originalIntegrand x := by
  have hxpos : 0 < x := hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hu : 0 < 1 + x ^ 4 := by positivity
  have hrpos : 0 < fourthRoot (1 + x ^ 4) := fourthRoot_pos hu
  have hrne : fourthRoot (1 + x ^ 4) ≠ 0 := ne_of_gt hrpos
  have hzder := (z_hasDerivAt x hx).deriv
  unfold transformedIntegrand originalIntegrand
  rw [hzder, z_four_sub_one x hx]
  unfold z
  field_simp [hxne, hrne]

private theorem partial_eq_neg_transformed (x : ℝ) (hx : x ∈ branch) :
    partialFractionIntegrand x = -transformedIntegrand x := by
  have hzgt : 1 < z x := z_gt_one x hx
  have hp : z x + 1 ≠ 0 := by linarith
  have hm : z x - 1 ≠ 0 := by linarith
  have hq : z x ^ 2 + 1 ≠ 0 := by positivity
  have hfour : z x ^ 4 - 1 ≠ 0 := by
    rw [show z x ^ 4 - 1 =
      (z x - 1) * (z x + 1) * (z x ^ 2 + 1) by ring]
    exact mul_ne_zero (mul_ne_zero hm hp) hq
  unfold partialFractionIntegrand transformedIntegrand
  field_simp [hp, hm, hq, hfour]
  ring

private theorem partial_eq_original (x : ℝ) (hx : x ∈ branch) :
    partialFractionIntegrand x = originalIntegrand x := by
  rw [partial_eq_neg_transformed x hx, transformed_eq_neg_original x hx]
  ring

private def primitiveInZ (y : ℝ) :=
  1 / 4 * Real.log |(y + 1) / (y - 1)| -
    1 / 2 * Real.arctan y

private theorem primitiveInZ_hasDerivAt (y : ℝ) (hy : 1 < y) :
    HasDerivAt primitiveInZ
      (1 / (4 * (y + 1)) -
        1 / (4 * (y - 1)) -
        1 / (2 * (y ^ 2 + 1))) y := by
  have hp : y + 1 ≠ 0 := by linarith
  have hm : y - 1 ≠ 0 := by linarith
  have hqpos : 0 < (y + 1) / (y - 1) :=
    div_pos (by linarith) (by linarith)
  have hquot :
      HasDerivAt (fun t : ℝ => (t + 1) / (t - 1))
        (-2 / (y - 1) ^ 2) y := by
    have h := ((hasDerivAt_id y).add_const 1).div
      ((hasDerivAt_id y).sub_const 1) hm
    simp only [id_eq] at h
    convert h using 1
    field_simp [hm]
    ring
  have hlogq :
      HasDerivAt (fun t : ℝ => Real.log ((t + 1) / (t - 1)))
        ((-2 / (y - 1) ^ 2) / ((y + 1) / (y - 1))) y := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_log (ne_of_gt hqpos)).comp y hquot
  have heq :
      (fun t : ℝ => Real.log |(t + 1) / (t - 1)|) =ᶠ[nhds y]
        (fun t : ℝ => Real.log ((t + 1) / (t - 1))) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    have ht' : 1 < t := ht
    have htp : 0 < t + 1 := by linarith
    have htm : 0 < t - 1 := by linarith
    have hqt : 0 < (t + 1) / (t - 1) := div_pos htp htm
    rw [abs_of_pos hqt]
  have hlog := hlogq.congr_of_eventuallyEq heq
  have hatan := Real.hasDerivAt_arctan y
  unfold primitiveInZ
  have h := hlog.const_mul (1 / 4 : ℝ) |>.sub
    (hatan.const_mul (1 / 2 : ℝ))
  convert h using 1
  field_simp [hp, hm]
  ring

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (partialFractionIntegrand x) x := by
  have hzgt : 1 < z x := z_gt_one x hx
  have hz := z_hasDerivAt x hx
  have hcomp := (primitiveInZ_hasDerivAt (z x) hzgt).comp x hz
  have hzder := hz.deriv
  unfold primitive primitiveInZ at hcomp
  unfold partialFractionIntegrand
  rw [hzder]
  exact hcomp

theorem gap1 (x : ℝ) (hx : x ∈ branch) :
    originalIntegrand x = powerFormIntegrand x := by
  rfl
theorem gap2 (x : ℝ) (hx : x ∈ branch) :
    z x = fourthRoot (1 + x ^ 4) / x := by
  rfl
theorem gap3 (x : ℝ) (hx : x ∈ branch) :
    x = xOfZ (z x) := by
  exact x_eq_xOfZ_z x hx
theorem gap4 (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt xOfZ
      (-z x ^ 3 / fourthRoot (z x ^ 4 - 1) ^ 5) (z x) := by
  have hxpos : 0 < x := hx
  have hpos : 0 < z x ^ 4 - 1 := by
    rw [z_four_sub_one x hx]
    exact one_div_pos.mpr (pow_pos hxpos 4)
  exact xOfZ_hasDerivAt (z x) hpos
theorem gap5 :
    AntiderivativesOn originalIntegrand = NegatedFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (originalIntegrand x) x at hF
    change ∃ G ∈ AntiderivativesOn transformedIntegrand,
      ∀ x ∈ branch, F x = -G x
    refine ⟨fun y => -F y, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun y => -F y) (transformedIntegrand x) x
      intro x hx
      convert (hF x hx).neg using 1
      exact transformed_eq_neg_original x hx
    · intro x hx
      simp
  · rintro ⟨G, hG, hFG⟩
    change ∀ x ∈ branch, HasDerivAt F (originalIntegrand x) x
    change ∀ x ∈ branch,
      HasDerivAt G (transformedIntegrand x) x at hG
    intro x hx
    have heq : F =ᶠ[nhds x] (fun y => -G y) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact hFG y hy
    have hder := (hG x hx).neg.congr_of_eventuallyEq heq
    convert hder using 1
    rw [transformed_eq_neg_original x hx]
    ring
theorem gap6 :
    NegatedFamily =
      AntiderivativesOn partialFractionIntegrand := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    change ∀ x ∈ branch,
      HasDerivAt F (partialFractionIntegrand x) x
    change ∀ x ∈ branch,
      HasDerivAt G (transformedIntegrand x) x at hG
    intro x hx
    have heq : F =ᶠ[nhds x] (fun y => -G y) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact hFG y hy
    have hder := (hG x hx).neg.congr_of_eventuallyEq heq
    convert hder using 1
    exact partial_eq_neg_transformed x hx
  · intro hF
    change ∀ x ∈ branch,
      HasDerivAt F (partialFractionIntegrand x) x at hF
    change ∃ G ∈ AntiderivativesOn transformedIntegrand,
      ∀ x ∈ branch, F x = -G x
    refine ⟨fun y => -F y, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun y => -F y) (transformedIntegrand x) x
      intro x hx
      convert (hF x hx).neg using 1
      rw [partial_eq_neg_transformed x hx]
      ring
    · intro x hx
      simp
theorem gap7 :
    AntiderivativesOn originalIntegrand =
      AntiderivativesOn partialFractionIntegrand := by
  calc
    AntiderivativesOn originalIntegrand = NegatedFamily := gap5
    _ = AntiderivativesOn partialFractionIntegrand := gap6
theorem gap8 :
    AntiderivativesOn originalIntegrand = PrimitiveFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (originalIntegrand x) x at hF
    change ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
    let H : ℝ → ℝ := fun y => F y - primitive y
    have hH : ∀ x ∈ branch, HasDerivAt H 0 x := by
      intro x hx
      dsimp [H]
      have hsub := (hF x hx).sub (primitive_hasDerivAt x hx)
      convert hsub using 1
      rw [partial_eq_original x hx]
      ring
    have hdiff : DifferentiableOn ℝ H branch := by
      intro x hx
      exact (hH x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ branch, deriv H x = 0 := by
      intro x hx
      exact (hH x hx).deriv
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have hone : (1 : ℝ) ∈ branch := by
      change (0 : ℝ) < 1
      norm_num
    have hc : H x = H 1 :=
      isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        hdiff hzero hx hone
    dsimp [H] at hc
    linarith
  · rintro ⟨C, hFC⟩
    change ∀ x ∈ branch, HasDerivAt F (originalIntegrand x) x
    intro x hx
    have heq : F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact hFC y hy
    have hder := (primitive_hasDerivAt x hx).add_const C
    have hder' := hder.congr_of_eventuallyEq heq
    convert hder' using 1
    exact (partial_eq_original x hx).symm
theorem gap9 (x : ℝ) (hx : x ∈ branch) :
    z x = fourthRoot (1 + x ^ 4) / x := by
  rfl

end
end ProofGap.Exercise1986
