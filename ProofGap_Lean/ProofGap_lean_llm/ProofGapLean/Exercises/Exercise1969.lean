import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ProofGap.Exercise1969

noncomputable section

def root (x : ℝ) := Real.sqrt (x ^ 2 + 3 * x + 2)
def xBranch : Set ℝ :=
  {x | 0 < x ^ 2 + 3 * x + 2 ∧ x + root x ≠ 0 ∧ x + 1 ≠ 0}
def zBranch : Set ℝ :=
  {z | z ≠ 0 ∧ 0 < z / (z ^ 2 - 1) ∧ z ≠ 2}
def zLeftBranch : Set ℝ := Set.Ioo (-1) 0
def zMiddleBranch : Set ℝ := Set.Ioo 1 2
def zRightBranch : Set ℝ := Set.Ioi 2
def substitution (x z : ℝ) : Prop :=
  x ∈ xBranch ∧ z ∈ zBranch ∧ root x = z * (x + 1)
def xOfZ (z : ℝ) := (2 - z ^ 2) / (z ^ 2 - 1)
def originalIntegrand (x : ℝ) :=
  (x - root x) / (x + root x)
def substitutedIntegrand (z : ℝ) :=
  2 * z * (2 - z - z ^ 2) /
    ((z ^ 2 - z - 2) * (z ^ 2 - 1) ^ 2)
def partialFractionIntegrand (z : ℝ) :=
  -17 / (108 * (z + 1)) +
    5 / (18 * (z + 1) ^ 2) +
    1 / (3 * (z + 1) ^ 3) +
    3 / (4 * (z - 1)) -
    16 / (27 * (z - 2))
def primitiveZ (z : ℝ) :=
  -17 / 108 * Real.log |z + 1| -
    5 / (18 * (z + 1)) -
    1 / (6 * (z + 1) ^ 2) +
    3 / 4 * Real.log |z - 1| -
    16 / 27 * Real.log |z - 2|
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def PullbackFamily (map : ℝ → ℝ) (s : Set ℝ)
    (T : Set (ℝ → ℝ)) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ T, ∀ z ∈ s, F (map z) = G z}
def BranchwisePrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ Cleft Cmiddle Cright : ℝ,
    (∀ z ∈ zLeftBranch, F z = primitiveZ z + Cleft) ∧
    (∀ z ∈ zMiddleBranch, F z = primitiveZ z + Cmiddle) ∧
    (∀ z ∈ zRightBranch, F z = primitiveZ z + Cright)}

theorem gap1 (x z : ℝ) (h : substitution x z) :
    x = xOfZ z := by
  have hx1 : x + 1 ≠ 0 := h.1.2.2
  have hzden : z ^ 2 - 1 ≠ 0 := by
    intro hzden
    have hzpos := h.2.1.2.1
    rw [hzden] at hzpos
    simp at hzpos
  have hrsq : root x ^ 2 = x ^ 2 + 3 * x + 2 := by
    unfold root
    exact Real.sq_sqrt (le_of_lt h.1.1)
  rw [h.2.2] at hrsq
  have hfac : (x + 1) * (z ^ 2 * (x + 1) - (x + 2)) = 0 := by
    nlinarith
  have hmain : z ^ 2 * (x + 1) = x + 2 := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left hx1)
  unfold xOfZ
  field_simp [hzden]
  nlinarith
theorem gap2 (z : ℝ) (hz : z ∈ zBranch) :
    HasDerivAt xOfZ (-2 * z / (z ^ 2 - 1) ^ 2) z := by
  have hden : z ^ 2 - 1 ≠ 0 := by
    intro hden
    have hzpos := hz.2.1
    rw [hden] at hzpos
    simp at hzpos
  unfold xOfZ
  convert
    ((hasDerivAt_const z (2 : ℝ)).sub ((hasDerivAt_id z).pow 2)).div
      (((hasDerivAt_id z).pow 2).sub (hasDerivAt_const z (1 : ℝ))) hden
      using 1 <;>
    simp [id] <;> field_simp [hden] <;> ring
theorem gap3 (x z : ℝ) (h : substitution x z) :
    root x = z / (z ^ 2 - 1) := by
  have hden : z ^ 2 - 1 ≠ 0 := by
    intro hden
    have hzpos := h.2.1.2.1
    rw [hden] at hzpos
    simp at hzpos
  rw [h.2.2, gap1 x z h]
  unfold xOfZ
  field_simp [hden]
  ring

private def zFromX (x : ℝ) := root x / (x + 1)

private lemma isOpen_xBranch : IsOpen xBranch := by
  have hq : Continuous (fun x : ℝ => x ^ 2 + 3 * x + 2) := by fun_prop
  have hr : Continuous root := by
    unfold root
    exact Real.continuous_sqrt.comp hq
  rw [show xBranch =
      {x : ℝ | 0 < x ^ 2 + 3 * x + 2} ∩
        {x : ℝ | x + root x ≠ 0} ∩ {x : ℝ | x + 1 ≠ 0} by
    ext x
    simp [xBranch, and_assoc]]
  exact ((isOpen_lt continuous_const hq).inter
    (isOpen_ne_fun (continuous_id.add hr) continuous_const)).inter
    (isOpen_ne_fun (continuous_id.add continuous_const) continuous_const)

private lemma zBranch_ne (z : ℝ) (hz : z ∈ zBranch) :
    z + 1 ≠ 0 ∧ z - 1 ≠ 0 ∧ z - 2 ≠ 0 := by
  have hden : z ^ 2 - 1 ≠ 0 := by
    intro h
    have hzpos := hz.2.1
    rw [h] at hzpos
    simp at hzpos
  refine ⟨?_, ?_, sub_ne_zero.mpr hz.2.2⟩
  · intro h
    apply hden
    nlinarith
  · intro h
    apply hden
    nlinarith

private lemma x_to_z_substitution (x : ℝ) (hx : x ∈ xBranch) :
    substitution x (zFromX x) := by
  have hrad : 0 < x ^ 2 + 3 * x + 2 := hx.1
  have hr : 0 < root x := by
    unfold root
    exact Real.sqrt_pos.2 hrad
  have hr2 : root x ^ 2 = x ^ 2 + 3 * x + 2 := by
    unfold root
    exact Real.sq_sqrt hrad.le
  have hx1 : x + 1 ≠ 0 := hx.2.2
  have hz0 : zFromX x ≠ 0 := by
    unfold zFromX
    exact div_ne_zero hr.ne' hx1
  have hden : (zFromX x) ^ 2 - 1 = 1 / (x + 1) := by
    unfold zFromX
    field_simp [hx1]
    nlinarith
  have hzpos : 0 < zFromX x / ((zFromX x) ^ 2 - 1) := by
    rw [hden]
    unfold zFromX
    field_simp [hx1]
    exact hr
  have hz2 : zFromX x ≠ 2 := by
    intro htwo
    have hroot : root x = 2 * (x + 1) := by
      unfold zFromX at htwo
      field_simp [hx1] at htwo
      linarith
    have hfac : (x + 1) * (3 * x + 2) = 0 := by
      rw [hroot] at hr2
      nlinarith
    have hxval : 3 * x + 2 = 0 :=
      (mul_eq_zero.mp hfac).resolve_left hx1
    apply hx.2.1
    rw [hroot]
    nlinarith
  refine ⟨hx, ⟨hz0, hzpos, hz2⟩, ?_⟩
  unfold zFromX
  field_simp [hx1]

private lemma z_to_x_substitution (z : ℝ) (hz : z ∈ zBranch) :
    substitution (xOfZ z) z := by
  have hden : z ^ 2 - 1 ≠ 0 := by
    intro h
    have hzpos := hz.2.1
    rw [h] at hzpos
    simp at hzpos
  have hp1 : z + 1 ≠ 0 := (zBranch_ne z hz).1
  have hrootpos : 0 < z / (z ^ 2 - 1) := hz.2.1
  have hq : (xOfZ z) ^ 2 + 3 * xOfZ z + 2 =
      (z / (z ^ 2 - 1)) ^ 2 := by
    unfold xOfZ
    field_simp [hden]
    ring
  have hroot : root (xOfZ z) = z / (z ^ 2 - 1) := by
    unfold root
    rw [hq, Real.sqrt_sq_eq_abs, abs_of_pos hrootpos]
  have hx1 : xOfZ z + 1 ≠ 0 := by
    rw [show xOfZ z + 1 = 1 / (z ^ 2 - 1) by
      unfold xOfZ
      field_simp [hden]
      ring]
    exact one_div_ne_zero hden
  have hxroot : xOfZ z + root (xOfZ z) ≠ 0 := by
    rw [hroot]
    rw [show xOfZ z + z / (z ^ 2 - 1) =
        -((z - 2) * (z + 1)) / (z ^ 2 - 1) by
      unfold xOfZ
      field_simp [hden]
      ring]
    exact div_ne_zero
      (neg_ne_zero.mpr (mul_ne_zero (sub_ne_zero.mpr hz.2.2) hp1)) hden
  have hx : xOfZ z ∈ xBranch := by
    refine ⟨?_, hxroot, hx1⟩
    rw [hq]
    positivity
  refine ⟨hx, hz, ?_⟩
  rw [hroot]
  unfold xOfZ
  field_simp [hden]
  ring

private lemma substituted_change (x z : ℝ) (h : substitution x z) :
    originalIntegrand x * (-2 * z / (z ^ 2 - 1) ^ 2) =
      substitutedIntegrand z := by
  have hden : z ^ 2 - 1 ≠ 0 := by
    intro hd
    have hp := h.2.1.2.1
    rw [hd] at hp
    simp at hp
  have hp1 : z + 1 ≠ 0 := (zBranch_ne z h.2.1).1
  have hm2 : z - 2 ≠ 0 := sub_ne_zero.mpr h.2.1.2.2
  have hpoly : z ^ 2 - z - 2 ≠ 0 := by
    rw [show z ^ 2 - z - 2 = (z - 2) * (z + 1) by ring]
    exact mul_ne_zero hm2 hp1
  have hpolyA : 2 + z - z ^ 2 ≠ 0 := by
    intro ha
    apply hpoly
    linarith
  have hpolyB : -2 - z + z ^ 2 ≠ 0 := by
    intro hb
    apply hpoly
    linarith
  have hpolyC : 2 + (z - z ^ 2) ≠ 0 := by
    intro hc
    apply hpoly
    linarith
  have hpolyD : z * (z - 1) - 2 ≠ 0 := by
    intro hd
    apply hpoly
    nlinarith
  have hpolyE : 2 - z ^ 2 + z ≠ 0 := by
    intro he
    apply hpoly
    nlinarith
  rw [gap1 x z h]
  unfold originalIntegrand
  rw [show root (xOfZ z) = z / (z ^ 2 - 1) by
    rw [← gap1 x z h]
    exact gap3 x z h]
  unfold substitutedIntegrand xOfZ
  field_simp [hden, hpoly, hpolyA, hpolyB, hpolyC]
  rw [show z * (z - 1) - 2 = -(2 - z ^ 2 + z) by ring]
  field_simp [hpolyE]
  ring

private lemma root_hasDerivAt (x : ℝ) (hx : x ∈ xBranch) :
    HasDerivAt root ((2 * x + 3) / (2 * root x)) x := by
  have hrad : 0 < x ^ 2 + 3 * x + 2 := hx.1
  have hpoly : HasDerivAt (fun y : ℝ => y ^ 2 + 3 * y + 2) (2 * x + 3) x := by
    convert (((hasDerivAt_id x).pow 2).add
      ((hasDerivAt_id x).const_mul 3)).add_const 2 using 1 <;>
        simp [id] <;> ring
  unfold root
  convert (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp x hpoly using 1 <;> ring

private lemma zFromX_hasDerivAt (x : ℝ) (hx : x ∈ xBranch) :
    ∃ dz : ℝ, HasDerivAt zFromX dz x := by
  have hx1 : x + 1 ≠ 0 := hx.2.2
  have hden : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
    convert (hasDerivAt_id x).add_const 1 using 1 <;> simp [id]
  refine ⟨((2 * x + 3) / (2 * root x) * (x + 1) - root x) /
    (x + 1) ^ 2, ?_⟩
  unfold zFromX
  convert (root_hasDerivAt x hx).div hden hx1 using 1 <;> ring
theorem gap4 :
    AntiderivativesOn xBranch originalIntegrand =
      PullbackFamily xOfZ zBranch
        (AntiderivativesOn zBranch substitutedIntegrand) := by
  ext F
  constructor
  · intro hF
    refine ⟨(fun z => F (xOfZ z)), ?_, ?_⟩
    · intro z hz
      have hsub := z_to_x_substitution z hz
      have hcomp := (hF (xOfZ z) hsub.1).comp z (gap2 z hz)
      convert hcomp using 1
      exact (substituted_change (xOfZ z) z hsub).symm
    · intro z hz
      rfl
  · rintro ⟨G, hG, hEq⟩
    intro x hx
    let z := zFromX x
    have hsub : substitution x z := x_to_z_substitution x hx
    have hz : z ∈ zBranch := hsub.2.1
    rcases zFromX_hasDerivAt x hx with ⟨dz, hzder⟩
    have hxder := gap2 z hz
    have hcomp := hxder.comp x hzder
    have hinvEvent : (fun y => y) =ᶠ[nhds x] (fun y => xOfZ (zFromX y)) := by
      filter_upwards [isOpen_xBranch.mem_nhds hx] with y hy
      exact gap1 y (zFromX y) (x_to_z_substitution y hy)
    have hcompId := hcomp.congr_of_eventuallyEq hinvEvent
    have hprod : (-2 * z / (z ^ 2 - 1) ^ 2) * dz = 1 :=
      hcompId.unique (hasDerivAt_id x)
    have hGcomp := (hG z hz).comp x hzder
    have hcoef : substitutedIntegrand z * dz = originalIntegrand x := by
      rw [← substituted_change x z hsub]
      calc
        originalIntegrand x * (-2 * z / (z ^ 2 - 1) ^ 2) * dz =
            originalIntegrand x *
              ((-2 * z / (z ^ 2 - 1) ^ 2) * dz) := by ring
        _ = originalIntegrand x := by rw [hprod]; ring
    have hFEvent :
        F =ᶠ[nhds x] (fun y => G (zFromX y)) := by
      filter_upwards [isOpen_xBranch.mem_nhds hx] with y hy
      have hsy := x_to_z_substitution y hy
      have heq := hEq (zFromX y) hsy.2.1
      calc
        F y = F (xOfZ (zFromX y)) :=
          congrArg F (gap1 y (zFromX y) hsy)
        _ = G (zFromX y) := heq
    exact (hGcomp.congr_deriv hcoef).congr_of_eventuallyEq hFEvent
theorem gap5 :
    AntiderivativesOn xBranch originalIntegrand =
      PullbackFamily xOfZ zBranch
        (AntiderivativesOn zBranch partialFractionIntegrand) := by
  have hpf :
      AntiderivativesOn zBranch substitutedIntegrand =
        AntiderivativesOn zBranch partialFractionIntegrand := by
    ext F
    constructor
    · intro hF z hz
      have hden : z ^ 2 - 1 ≠ 0 := by
        intro hden
        have hzpos := hz.2.1
        rw [hden] at hzpos
        simp at hzpos
      have hm1 : z - 1 ≠ 0 := by
        intro hm1
        apply hden
        nlinarith
      have hp1 : z + 1 ≠ 0 := by
        intro hp1
        apply hden
        nlinarith
      have hm2 : z - 2 ≠ 0 := sub_ne_zero.mpr hz.2.2
      have hpoly : z ^ 2 - z - 2 ≠ 0 := by
        rw [show z ^ 2 - z - 2 = (z - 2) * (z + 1) by ring]
        exact mul_ne_zero hm2 hp1
      have hpoly' : -2 - z + z ^ 2 ≠ 0 := by
        convert hpoly using 1 <;> ring
      have hpoly'' : z * (z - 1) - 2 ≠ 0 := by
        convert hpoly using 1 <;> ring
      convert hF z hz using 1
      unfold substitutedIntegrand partialFractionIntegrand
      field_simp [hden, hm1, hp1, hm2, hpoly, hpoly']
      field_simp [hpoly'']
      ring
    · intro hF z hz
      have hden : z ^ 2 - 1 ≠ 0 := by
        intro hden
        have hzpos := hz.2.1
        rw [hden] at hzpos
        simp at hzpos
      have hm1 : z - 1 ≠ 0 := by
        intro hm1
        apply hden
        nlinarith
      have hp1 : z + 1 ≠ 0 := by
        intro hp1
        apply hden
        nlinarith
      have hm2 : z - 2 ≠ 0 := sub_ne_zero.mpr hz.2.2
      have hpoly : z ^ 2 - z - 2 ≠ 0 := by
        rw [show z ^ 2 - z - 2 = (z - 2) * (z + 1) by ring]
        exact mul_ne_zero hm2 hp1
      have hpoly' : -2 - z + z ^ 2 ≠ 0 := by
        convert hpoly using 1 <;> ring
      have hpoly'' : z * (z - 1) - 2 ≠ 0 := by
        convert hpoly using 1 <;> ring
      convert hF z hz using 1
      unfold substitutedIntegrand partialFractionIntegrand
      field_simp [hden, hm1, hp1, hm2, hpoly, hpoly']
      field_simp [hpoly'']
      ring
  rw [gap4, hpf]

private lemma zBranch_iff (z : ℝ) :
    z ∈ zBranch ↔
      z ∈ zLeftBranch ∨ z ∈ zMiddleBranch ∨ z ∈ zRightBranch := by
  unfold zBranch zLeftBranch zMiddleBranch zRightBranch
  simp only [Set.mem_setOf_eq, Set.mem_Ioo, Set.mem_Ioi]
  constructor
  · rintro ⟨hz0, hzpos, hz2⟩
    rcases (div_pos_iff.mp hzpos) with hpp | hnn
    · right
      have hz1 : 1 < z := by
        by_contra h
        have hzle : z ≤ 1 := le_of_not_gt h
        nlinarith
      rcases lt_or_gt_of_ne hz2 with hlt | hgt
      · exact Or.inl ⟨hz1, hlt⟩
      · exact Or.inr hgt
    · left
      constructor
      · by_contra h
        have hzle : z ≤ -1 := le_of_not_gt h
        nlinarith
      · exact hnn.1
  · rintro (hleft | hmiddle | hright)
    · refine ⟨by linarith, (div_pos_iff.mpr (Or.inr ?_)), by linarith⟩
      constructor
      · exact hleft.2
      · nlinarith [mul_pos (sub_pos.mpr (by linarith : 1 - z > 0))
          (sub_pos.mpr (by linarith : z + 1 > 0))]
    · refine ⟨by linarith, (div_pos_iff.mpr (Or.inl ?_)), by linarith⟩
      constructor
      · linarith
      · nlinarith [mul_pos (sub_pos.mpr (by linarith : z - 1 > 0))
          (add_pos (by linarith : 0 < z) (by norm_num : 0 < (1 : ℝ)))]
    · refine ⟨by linarith, (div_pos_iff.mpr (Or.inl ?_)), by linarith⟩
      constructor
      · linarith
      · nlinarith [mul_pos (sub_pos.mpr (by linarith : z - 1 > 0))
          (add_pos (by linarith : 0 < z) (by norm_num : 0 < (1 : ℝ)))]

private lemma primitiveZ_hasDerivAt (z : ℝ)
    (hm1 : z + 1 ≠ 0) (hp1 : z - 1 ≠ 0) (hp2 : z - 2 ≠ 0) :
    HasDerivAt primitiveZ (partialFractionIntegrand z) z := by
  have hlogm1 : HasDerivAt (fun y : ℝ => Real.log |y + 1|) (1 / (z + 1)) z := by
    have hinner : HasDerivAt (fun y : ℝ => y + 1) 1 z := by
      convert (hasDerivAt_id z).add_const 1 using 1 <;> simp [id]
    have h := (Real.hasDerivAt_log hm1).comp z hinner
    simpa [Function.comp_def, Real.log_abs] using h
  have hlogp1 : HasDerivAt (fun y : ℝ => Real.log |y - 1|) (1 / (z - 1)) z := by
    have hinner : HasDerivAt (fun y : ℝ => y - 1) 1 z := by
      convert (hasDerivAt_id z).sub_const 1 using 1 <;> simp [id]
    have h := (Real.hasDerivAt_log hp1).comp z hinner
    simpa [Function.comp_def, Real.log_abs] using h
  have hlogp2 : HasDerivAt (fun y : ℝ => Real.log |y - 2|) (1 / (z - 2)) z := by
    have hinner : HasDerivAt (fun y : ℝ => y - 2) 1 z := by
      convert (hasDerivAt_id z).sub_const 2 using 1 <;> simp [id]
    have h := (Real.hasDerivAt_log hp2).comp z hinner
    simpa [Function.comp_def, Real.log_abs] using h
  have hinv1 : HasDerivAt (fun y : ℝ => 1 / (y + 1))
      (-1 / (z + 1) ^ 2) z := by
    have hinner : HasDerivAt (fun y : ℝ => y + 1) 1 z := by
      convert (hasDerivAt_id z).add_const 1 using 1 <;> simp [id]
    convert (hasDerivAt_const z (1 : ℝ)).div hinner hm1 using 1 <;>
      field_simp [hm1] <;> ring
  have hinv2 : HasDerivAt (fun y : ℝ => 1 / (y + 1) ^ 2)
      (-2 / (z + 1) ^ 3) z := by
    have hinner : HasDerivAt (fun y : ℝ => (y + 1) ^ 2) (2 * (z + 1)) z := by
      convert ((hasDerivAt_id z).add_const 1).pow 2 using 1 <;> simp [id] <;> ring
    convert (hasDerivAt_const z (1 : ℝ)).div hinner (pow_ne_zero 2 hm1) using 1 <;>
      field_simp [hm1] <;> ring
  have h :=
    (((hlogm1.const_mul (-17 / 108)).sub
      (hinv1.const_mul (5 / 18))).sub
      (hinv2.const_mul (1 / 6))).add
      (hlogp1.const_mul (3 / 4)) |>.sub
      (hlogp2.const_mul (16 / 27))
  convert h using 1
  · funext y
    simp only [Pi.sub_apply, Pi.add_apply, primitiveZ]
    by_cases hy : y + 1 = 0
    · simp [hy]
    · field_simp [hy]
  · unfold partialFractionIntegrand
    field_simp [hm1, hp1, hp2]
    ring

private lemma branch_open_preconnected :
    IsOpen zLeftBranch ∧ IsPreconnected zLeftBranch ∧
    IsOpen zMiddleBranch ∧ IsPreconnected zMiddleBranch ∧
    IsOpen zRightBranch ∧ IsPreconnected zRightBranch := by
  exact ⟨isOpen_Ioo, isPreconnected_Ioo, isOpen_Ioo, isPreconnected_Ioo,
    isOpen_Ioi, isPreconnected_Ioi⟩

private lemma antiderivatives_eq_branchwise :
    AntiderivativesOn zBranch partialFractionIntegrand =
      BranchwisePrimitiveFamily := by
  ext F
  constructor
  · intro hF
    have solveBranch (u : Set ℝ) (huOpen : IsOpen u) (huPre : IsPreconnected u)
        (huSub : u ⊆ zBranch) :
        ∃ C : ℝ, ∀ z ∈ u, F z = primitiveZ z + C := by
      have hP : ∀ z ∈ u, HasDerivAt primitiveZ (partialFractionIntegrand z) z := by
        intro z hz
        have hzb := huSub hz
        rcases (zBranch_iff z).1 hzb with hleft | hmiddle | hright
        · exact primitiveZ_hasDerivAt z (zBranch_ne z hzb).1
            (zBranch_ne z hzb).2.1 (zBranch_ne z hzb).2.2
        · exact primitiveZ_hasDerivAt z (zBranch_ne z hzb).1
            (zBranch_ne z hzb).2.1 (zBranch_ne z hzb).2.2
        · exact primitiveZ_hasDerivAt z (zBranch_ne z hzb).1
            (zBranch_ne z hzb).2.1 (zBranch_ne z hzb).2.2
      have hFd : DifferentiableOn ℝ F u :=
        fun z hz => (hF z (huSub hz)).differentiableAt.differentiableWithinAt
      have hPd : DifferentiableOn ℝ primitiveZ u :=
        fun z hz => (hP z hz).differentiableAt.differentiableWithinAt
      have heq : u.EqOn (deriv F) (deriv primitiveZ) := by
        intro z hz
        rw [(hF z (huSub hz)).deriv, (hP z hz).deriv]
      exact huOpen.exists_eq_add_of_deriv_eq huPre hFd hPd heq
    have hleftSub : zLeftBranch ⊆ zBranch :=
      fun z hz => (zBranch_iff z).2 (Or.inl hz)
    have hmiddleSub : zMiddleBranch ⊆ zBranch :=
      fun z hz => (zBranch_iff z).2 (Or.inr (Or.inl hz))
    have hrightSub : zRightBranch ⊆ zBranch :=
      fun z hz => (zBranch_iff z).2 (Or.inr (Or.inr hz))
    rcases solveBranch zLeftBranch branch_open_preconnected.1
      branch_open_preconnected.2.1 hleftSub with ⟨Cl, hl⟩
    rcases solveBranch zMiddleBranch branch_open_preconnected.2.2.1
      branch_open_preconnected.2.2.2.1 hmiddleSub with ⟨Cm, hm⟩
    rcases solveBranch zRightBranch branch_open_preconnected.2.2.2.2.1
      branch_open_preconnected.2.2.2.2.2 hrightSub with ⟨Cr, hr⟩
    exact ⟨Cl, Cm, Cr, hl, hm, hr⟩
  · rintro ⟨Cl, Cm, Cr, hl, hm, hr⟩
    intro z hz
    rcases (zBranch_iff z).1 hz with hleft | hmiddle | hright
    · have hp := primitiveZ_hasDerivAt z (zBranch_ne z hz).1
        (zBranch_ne z hz).2.1 (zBranch_ne z hz).2.2
      have hevent : F =ᶠ[nhds z] (fun y => primitiveZ y + Cl) := by
        filter_upwards [isOpen_Ioo.mem_nhds hleft] with y hy
        exact hl y hy
      exact (hp.add_const Cl).congr_of_eventuallyEq hevent
    · have hp := primitiveZ_hasDerivAt z (zBranch_ne z hz).1
        (zBranch_ne z hz).2.1 (zBranch_ne z hz).2.2
      have hevent : F =ᶠ[nhds z] (fun y => primitiveZ y + Cm) := by
        filter_upwards [isOpen_Ioo.mem_nhds hmiddle] with y hy
        exact hm y hy
      exact (hp.add_const Cm).congr_of_eventuallyEq hevent
    · have hp := primitiveZ_hasDerivAt z (zBranch_ne z hz).1
        (zBranch_ne z hz).2.1 (zBranch_ne z hz).2.2
      have hevent : F =ᶠ[nhds z] (fun y => primitiveZ y + Cr) := by
        filter_upwards [isOpen_Ioi.mem_nhds hright] with y hy
        exact hr y hy
      exact (hp.add_const Cr).congr_of_eventuallyEq hevent
theorem gap6 :
    AntiderivativesOn xBranch originalIntegrand =
      PullbackFamily xOfZ zBranch
        BranchwisePrimitiveFamily := by
  rw [gap5, antiderivatives_eq_branchwise]
theorem gap7 (x z : ℝ) (h : substitution x z) :
    z = root x / (x + 1) := by
  rw [h.2.2]
  field_simp [h.1.2.2]

end
end ProofGap.Exercise1969
