import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1988

noncomputable section

def fifthRoot (x : ℝ) :=
  Real.sign x * Real.rpow |x| (1 / 5 : ℝ)
def branch : Set ℝ := {x | x ≠ -1 ∧ x ≠ 0}
def leftBranch : Set ℝ := Set.Iio (-1)
def middleBranch : Set ℝ := Set.Ioo (-1) 0
def rightBranch : Set ℝ := Set.Ioi 0
def z (x : ℝ) := fifthRoot (1 + 1 / x)
def xOfZ (y : ℝ) := 1 / (y ^ 5 - 1)
def originalIntegrand (x : ℝ) :=
  1 / (x ^ 3 * fifthRoot (1 + 1 / x))
def powerFormIntegrand (x : ℝ) :=
  (1 / x ^ 3) * (1 / fifthRoot (1 + 1 / x))
def transformedIntegrand (x : ℝ) :=
  z x ^ 3 * (z x ^ 5 - 1) * deriv z x
def primitive (x : ℝ) :=
  -5 / 9 * z x ^ 9 + 5 / 4 * z x ^ 4
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ScaledFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn transformedIntegrand,
    ∀ x ∈ branch, F x = -5 * G x}
def BranchwisePrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ Cleft Cmiddle Cright : ℝ,
    (∀ x ∈ leftBranch, F x = primitive x + Cleft) ∧
    (∀ x ∈ middleBranch, F x = primitive x + Cmiddle) ∧
    (∀ x ∈ rightBranch, F x = primitive x + Cright)}

private theorem eq_of_hasDerivAt_zero_on_uIcc
    (f : ℝ → ℝ) (a b : ℝ)
    (h : ∀ x ∈ Set.uIcc a b, HasDerivAt f 0 x) : f a = f b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hcont : ContinuousOn f (Set.Icc a b) := by
      intro x hx
      exact (h x (Set.Icc_subset_uIcc hx)).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ f (Set.Ioo a b) := by
      intro x hx
      have hxu : x ∈ Set.uIcc a b :=
        Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hx)
      exact (h x hxu).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hcslope⟩ := exists_deriv_eq_slope f hab hcont hdiff
    have hc0 : deriv f c = 0 := by
      have hcu : c ∈ Set.uIcc a b :=
        Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hc)
      exact (h c hcu).deriv
    rw [hc0] at hcslope
    have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    field_simp [hne] at hcslope
    linarith
  · simpa [hab]
  · have hcont : ContinuousOn f (Set.Icc b a) := by
      intro x hx
      have hxu : x ∈ Set.uIcc a b := by
        rw [Set.uIcc_comm]
        exact Set.Icc_subset_uIcc hx
      exact (h x hxu).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ f (Set.Ioo b a) := by
      intro x hx
      have hxu : x ∈ Set.uIcc a b := by
        rw [Set.uIcc_comm]
        exact Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hx)
      exact (h x hxu).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hcslope⟩ := exists_deriv_eq_slope f hab hcont hdiff
    have hc0 : deriv f c = 0 := by
      have hcu : c ∈ Set.uIcc a b := by
        rw [Set.uIcc_comm]
        exact Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hc)
      exact (h c hcu).deriv
    rw [hc0] at hcslope
    have hne : a - b ≠ 0 := sub_ne_zero.mpr hab.ne'
    field_simp [hne] at hcslope
    linarith

private theorem substitutionFacts (x : ℝ) (hx : x ∈ branch) :
    x = xOfZ (z x) ∧
    HasDerivAt xOfZ (-5 * z x ^ 4 / (z x ^ 5 - 1) ^ 2) (z x) ∧
    DifferentiableAt ℝ z x ∧
    originalIntegrand x = -5 * transformedIntegrand x := by
  have hx' : x ≠ -1 ∧ x ≠ 0 := hx
  have hroot : ∀ t : ℝ, fifthRoot t ^ 5 = t := by
    intro t
    rcases lt_trichotomy t 0 with ht | ht | ht
    · have hb : 0 < -t := neg_pos.mpr ht
      have hp : (Real.rpow (-t) (1 / 5 : ℝ)) ^ 5 = -t := by
        calc
          (Real.rpow (-t) (1 / 5 : ℝ)) ^ 5 =
              Real.rpow (Real.rpow (-t) (1 / 5 : ℝ)) (5 : ℝ) := by
                simpa only using
                  (Real.rpow_natCast
                    (Real.rpow (-t) (1 / 5 : ℝ)) 5).symm
          _ = Real.rpow (-t) ((1 / 5 : ℝ) * 5) := by
                exact (Real.rpow_mul (le_of_lt hb) _ _).symm
          _ = -t := by norm_num
      rw [fifthRoot, Real.sign_of_neg ht, abs_of_neg ht]
      calc
        (-1 * Real.rpow (-t) (1 / 5 : ℝ)) ^ 5 =
            -(Real.rpow (-t) (1 / 5 : ℝ) ^ 5) := by ring
        _ = t := by rw [hp]; ring
    · subst t
      simp [fifthRoot]
    · have hp : (Real.rpow t (1 / 5 : ℝ)) ^ 5 = t := by
        calc
          (Real.rpow t (1 / 5 : ℝ)) ^ 5 =
              Real.rpow (Real.rpow t (1 / 5 : ℝ)) (5 : ℝ) := by
                simpa only using
                  (Real.rpow_natCast
                    (Real.rpow t (1 / 5 : ℝ)) 5).symm
          _ = Real.rpow t ((1 / 5 : ℝ) * 5) := by
                exact (Real.rpow_mul (le_of_lt ht) _ _).symm
          _ = t := by norm_num
      simpa [fifthRoot, Real.sign_of_pos ht, abs_of_pos ht] using hp
  have hu : 1 + 1 / x ≠ 0 := by
    intro h
    apply hx'.1
    field_simp [hx'.2] at h
    linarith
  have hxz : x = xOfZ (z x) := by
    unfold xOfZ z
    rw [hroot]
    field_simp [hx'.2]
    <;> ring
  have hqeq : z x ^ 5 - 1 = 1 / x := by
    rw [z, hroot]
    ring
  have hq : z x ^ 5 - 1 ≠ 0 := by
    rw [hqeq]
    exact one_div_ne_zero hx'.2
  have hder : HasDerivAt xOfZ
      (-5 * z x ^ 4 / (z x ^ 5 - 1) ^ 2) (z x) := by
    have hp : HasDerivAt (fun y : ℝ => y ^ 5 - 1)
        (5 * z x ^ 4) (z x) := by
      convert ((hasDerivAt_id (z x)).pow 5).sub_const 1 using 1 <;> norm_num
    have hi : HasDerivAt (fun y : ℝ => 1 / (y ^ 5 - 1))
        ((0 * (z x ^ 5 - 1) - 1 * (5 * z x ^ 4)) /
          (z x ^ 5 - 1) ^ 2) (z x) :=
      (hasDerivAt_const (z x) (1 : ℝ)).div hp hq
    unfold xOfZ
    convert hi using 1 <;> ring
  have huDer : HasDerivAt (fun y : ℝ => 1 + 1 / y) (-1 / x ^ 2) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add
      ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx'.2) using 1 <;>
      simp [one_div] <;> ring
  have hdiff : DifferentiableAt ℝ z x := by
    rcases lt_trichotomy (1 + 1 / x) 0 with hneg | hzero | hpos
    · have hvpos : 0 < -(1 + 1 / x) := neg_pos.mpr hneg
      have hr := Real.hasDerivAt_rpow_const
        (p := (1 / 5 : ℝ)) (Or.inl hvpos.ne')
      have hc := hr.comp x huDer.neg
      have hzder := hc.neg
      have hevU : ∀ᶠ y in nhds x, 1 + 1 / y < 0 :=
        huDer.continuousAt.eventually (isOpen_Iio.mem_nhds hneg)
      have hevent :
          z =ᶠ[nhds x]
            (-(fun u : ℝ => Real.rpow u (1 / 5 : ℝ)) ∘
              (-fun y : ℝ => 1 + 1 / y)) := by
        filter_upwards [hevU] with y hy
        change fifthRoot (1 + 1 / y) =
          -Real.rpow (-(1 + 1 / y)) (1 / 5 : ℝ)
        rw [fifthRoot, Real.sign_of_neg hy, abs_of_neg hy]
        ring
      exact (hzder.congr_of_eventuallyEq hevent).differentiableAt
    · exact False.elim (hu hzero)
    · have hr := Real.hasDerivAt_rpow_const
        (p := (1 / 5 : ℝ)) (Or.inl hpos.ne')
      have hzder := hr.comp x huDer
      have hevU : ∀ᶠ y in nhds x, 0 < 1 + 1 / y :=
        huDer.continuousAt.eventually (isOpen_Ioi.mem_nhds hpos)
      have hevent :
          z =ᶠ[nhds x]
            ((fun u : ℝ => Real.rpow u (1 / 5 : ℝ)) ∘
              fun y : ℝ => 1 + 1 / y) := by
        filter_upwards [hevU] with y hy
        change fifthRoot (1 + 1 / y) =
          Real.rpow (1 + 1 / y) (1 / 5 : ℝ)
        rw [fifthRoot, Real.sign_of_pos hy, abs_of_pos hy]
        ring
      exact (hzder.congr_of_eventuallyEq hevent).differentiableAt
  have hz5 : z x ^ 5 = 1 + 1 / x := by
    rw [z, hroot]
  have hz0 : z x ≠ 0 := by
    intro hz
    apply hu
    rw [← hz5, hz]
    norm_num
  have hevent : (fun y : ℝ => y) =ᶠ[nhds x] (xOfZ ∘ z) := by
    filter_upwards [eventually_ne_nhds hx'.2] with y hy
    change y = xOfZ (z y)
    unfold xOfZ z
    rw [hroot]
    field_simp [hy]
    <;> ring
  have hcomp := hder.comp x hdiff.hasDerivAt
  have hidder : HasDerivAt (fun y : ℝ => y)
      ((-5 * z x ^ 4 / (z x ^ 5 - 1) ^ 2) * deriv z x) x :=
    hcomp.congr_of_eventuallyEq hevent
  have hchain : (-5 * z x ^ 4 / (z x ^ 5 - 1) ^ 2) * deriv z x = 1 :=
    hidder.unique (hasDerivAt_id x)
  have hchain' : -5 * z x ^ 4 * deriv z x = (z x ^ 5 - 1) ^ 2 := by
    field_simp [hq] at hchain
    nlinarith
  have hmul :
      -5 * z x ^ 4 * (z x ^ 5 - 1) * deriv z x =
        (z x ^ 5 - 1) ^ 3 := by
    calc
      -5 * z x ^ 4 * (z x ^ 5 - 1) * deriv z x =
          (z x ^ 5 - 1) * (-5 * z x ^ 4 * deriv z x) := by ring
      _ = (z x ^ 5 - 1) * (z x ^ 5 - 1) ^ 2 := by rw [hchain']
      _ = (z x ^ 5 - 1) ^ 3 := by ring
  have hxq : x * (z x ^ 5 - 1) = 1 := by
    rw [hqeq]
    field_simp [hx'.2]
  have hxcube : x ^ 3 * (z x ^ 5 - 1) ^ 3 = 1 := by
    calc
      x ^ 3 * (z x ^ 5 - 1) ^ 3 =
          (x * (z x ^ 5 - 1)) ^ 3 := by ring
      _ = 1 := by rw [hxq]; norm_num
  have hscale : originalIntegrand x = -5 * transformedIntegrand x := by
    change 1 / (x ^ 3 * z x) =
      -5 * (z x ^ 3 * (z x ^ 5 - 1) * deriv z x)
    calc
      1 / (x ^ 3 * z x) = (z x ^ 5 - 1) ^ 3 / z x := by
        apply (div_eq_div_iff
          (mul_ne_zero (pow_ne_zero 3 hx'.2) hz0) hz0).2
        calc
          1 * z x = (x ^ 3 * (z x ^ 5 - 1) ^ 3) * z x := by rw [hxcube]
          _ = (z x ^ 5 - 1) ^ 3 * (x ^ 3 * z x) := by ring
      _ = -5 * (z x ^ 3 * (z x ^ 5 - 1) * deriv z x) := by
        apply (div_eq_iff hz0).2
        calc
          (z x ^ 5 - 1) ^ 3 =
              -5 * z x ^ 4 * (z x ^ 5 - 1) * deriv z x := hmul.symm
          _ = (-5 * (z x ^ 3 * (z x ^ 5 - 1) * deriv z x)) * z x := by ring
  exact ⟨hxz, hder, hdiff, hscale⟩

theorem gap1 (x : ℝ) (hx : x ∈ branch) :
    originalIntegrand x = powerFormIntegrand x := by
  unfold originalIntegrand powerFormIntegrand
  ring
theorem gap2 (x : ℝ) (hx : x ∈ branch) :
    x = xOfZ (z x) := by
  exact (substitutionFacts x hx).1
theorem gap3 (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt xOfZ
      (-5 * z x ^ 4 / (z x ^ 5 - 1) ^ 2) (z x) := by
  exact (substitutionFacts x hx).2.1
theorem gap4 :
    AntiderivativesOn originalIntegrand = ScaledFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨fun y => (-1 / 5 : ℝ) * F y, ?_, ?_⟩
    · intro x hx
      have hder := (hF x hx).const_mul (-1 / 5 : ℝ)
      have hscale := (substitutionFacts x hx).2.2.2
      convert hder using 1
      linarith [hscale]
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hx' : x ≠ -1 ∧ x ≠ 0 := hx
    have heq : F =ᶠ[nhds x] fun y => (-5 : ℝ) * G y := by
      filter_upwards [eventually_ne_nhds hx'.1, eventually_ne_nhds hx'.2] with y hy1 hy0
      exact hFG y ⟨hy1, hy0⟩
    have hder := (hG x hx).const_mul (-5 : ℝ)
    have hscale := (substitutionFacts x hx).2.2.2
    have hder' : HasDerivAt (fun y => (-5 : ℝ) * G y) (originalIntegrand x) x := by
      rw [hscale]
      exact hder
    exact hder'.congr_of_eventuallyEq heq
theorem gap5 :
    ScaledFamily = BranchwisePrimitiveFamily := by
  rw [← gap4]
  ext F
  constructor
  · intro hF
    let H : ℝ → ℝ := fun y => F y - primitive y
    have hprim : ∀ x ∈ branch, HasDerivAt primitive (originalIntegrand x) x := by
      intro x hx
      have hz := (substitutionFacts x hx).2.2.1.hasDerivAt
      have hp9 := (hz.pow 9).const_mul (-5 / 9 : ℝ)
      have hp4 := (hz.pow 4).const_mul (5 / 4 : ℝ)
      have hp : HasDerivAt primitive (-5 * transformedIntegrand x) x := by
        convert hp9.add hp4 using 1 <;>
          simp only [transformedIntegrand] <;> ring
      convert hp using 1
      exact (substitutionFacts x hx).2.2.2
    refine ⟨H (-2), H (-1 / 2), H 1, ?_, ?_, ?_⟩
    · intro x hx
      have hseg : ∀ t ∈ Set.uIcc (-2 : ℝ) x, HasDerivAt H 0 t := by
        intro t ht
        have htlo : t < -1 := by
          rcases Set.mem_uIcc.mp ht with ht | ht
          · exact lt_of_le_of_lt ht.2 hx
          · exact lt_of_le_of_lt ht.2 (by norm_num)
        have htb : t ∈ branch := by
          change t ≠ -1 ∧ t ≠ 0
          constructor <;> linarith
        simpa [H] using (hF t htb).sub (hprim t htb)
      have hc := eq_of_hasDerivAt_zero_on_uIcc H (-2) x hseg
      dsimp [H] at hc ⊢
      linarith
    · intro x hx
      have hseg : ∀ t ∈ Set.uIcc (-1 / 2 : ℝ) x, HasDerivAt H 0 t := by
        intro t ht
        have htlo : -1 < t := by
          rcases Set.mem_uIcc.mp ht with ht | ht
          · exact lt_of_lt_of_le (by norm_num) ht.1
          · exact lt_of_lt_of_le hx.1 ht.1
        have hthi : t < 0 := by
          rcases Set.mem_uIcc.mp ht with ht | ht
          · exact lt_of_le_of_lt ht.2 hx.2
          · exact lt_of_le_of_lt ht.2 (by norm_num)
        have htb : t ∈ branch := by
          change t ≠ -1 ∧ t ≠ 0
          constructor <;> linarith
        simpa [H] using (hF t htb).sub (hprim t htb)
      have hc := eq_of_hasDerivAt_zero_on_uIcc H (-1 / 2) x hseg
      dsimp [H] at hc ⊢
      linarith
    · intro x hx
      have hseg : ∀ t ∈ Set.uIcc (1 : ℝ) x, HasDerivAt H 0 t := by
        intro t ht
        have htpos : 0 < t := by
          rcases Set.mem_uIcc.mp ht with ht | ht
          · exact lt_of_lt_of_le (by norm_num) ht.1
          · exact lt_of_lt_of_le hx ht.1
        have htb : t ∈ branch := by
          change t ≠ -1 ∧ t ≠ 0
          constructor <;> linarith
        simpa [H] using (hF t htb).sub (hprim t htb)
      have hc := eq_of_hasDerivAt_zero_on_uIcc H 1 x hseg
      dsimp [H] at hc ⊢
      linarith
  · rintro ⟨Cl, Cm, Cr, hl, hm, hr⟩
    intro x hx
    have hprim : HasDerivAt primitive (originalIntegrand x) x := by
      have hz := (substitutionFacts x hx).2.2.1.hasDerivAt
      have hp9 := (hz.pow 9).const_mul (-5 / 9 : ℝ)
      have hp4 := (hz.pow 4).const_mul (5 / 4 : ℝ)
      have hp : HasDerivAt primitive (-5 * transformedIntegrand x) x := by
        convert hp9.add hp4 using 1 <;>
          simp only [transformedIntegrand] <;> ring
      convert hp using 1
      exact (substitutionFacts x hx).2.2.2
    have hx' : x ≠ -1 ∧ x ≠ 0 := hx
    rcases lt_trichotomy x (-1) with hxl | hxe | hxr
    · have heq : F =ᶠ[nhds x] fun y => primitive y + Cl := by
        filter_upwards [eventually_lt_nhds hxl] with y hy
        exact hl y hy
      exact (hprim.add_const Cl).congr_of_eventuallyEq heq
    · exact False.elim (hx'.1 hxe)
    · rcases lt_trichotomy x 0 with hxm | hxe | hxp
      · have hmid : x ∈ middleBranch := ⟨hxr, hxm⟩
        have heq : F =ᶠ[nhds x] fun y => primitive y + Cm := by
          filter_upwards [eventually_gt_nhds hxr, eventually_lt_nhds hxm] with y hylo hyhi
          exact hm y ⟨hylo, hyhi⟩
        exact (hprim.add_const Cm).congr_of_eventuallyEq heq
      · exact False.elim (hx'.2 hxe)
      · have heq : F =ᶠ[nhds x] fun y => primitive y + Cr := by
          filter_upwards [eventually_gt_nhds hxp] with y hy
          exact hr y hy
        exact (hprim.add_const Cr).congr_of_eventuallyEq heq
theorem gap6 :
    AntiderivativesOn originalIntegrand =
      BranchwisePrimitiveFamily := by
  exact gap4.trans gap5
theorem gap7 (x : ℝ) (hx : x ∈ branch) :
    z x = fifthRoot (1 + 1 / x) := by
  rfl

end
end ProofGap.Exercise1988
