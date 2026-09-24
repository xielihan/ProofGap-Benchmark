import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1931

noncomputable section

def xOf (t : ℝ) := (t ^ 2 + 1) / (t ^ 2 - 1)
def parameterBranch : Set ℝ := {t | 1 < t}
def xBranch : Set ℝ := {x | 1 < x}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def radicalRatioAt (x : ℝ) :=
  (Real.sqrt (x + 1) - Real.sqrt (x - 1)) /
    (Real.sqrt (x + 1) + Real.sqrt (x - 1))
def rawParamIntegrand (t : ℝ) := radicalRatioAt (xOf t) * deriv xOf t
def normalizedParamIntegrand (t : ℝ) :=
  (Real.sqrt ((xOf t + 1) / (xOf t - 1)) - 1) /
    (Real.sqrt ((xOf t + 1) / (xOf t - 1)) + 1) * deriv xOf t
def rationalParamIntegrand (t : ℝ) := t / ((t - 1) * (t + 1) ^ 3)
def ScaledRationalFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn parameterBranch rationalParamIntegrand,
    ∀ t ∈ parameterBranch, F t = -4 * G t}
def partialFraction (t : ℝ) :=
  -2 / (t + 1) ^ 3 + 1 / (t + 1) ^ 2 +
    1 / (2 * (t + 1)) - 1 / (2 * (t - 1))
def parameterPrimitive (t : ℝ) :=
  1 / (t + 1) ^ 2 - 1 / (t + 1) +
    1 / 2 * Real.log |(t + 1) / (t - 1)|
def xSimplifiedIntegrand (x : ℝ) := x - Real.sqrt (x ^ 2 - 1)
def xPrimitive (x : ℝ) :=
  1 / 2 * x ^ 2 - 1 / 2 * x * Real.sqrt (x ^ 2 - 1) +
    1 / 2 * Real.log |x + Real.sqrt (x ^ 2 - 1)|

private theorem hasDerivAt_congr_on_Ioi
    (f g : ℝ → ℝ) (a x d : ℝ) (hx : a < x)
    (hfg : ∀ y, a < y → f y = g y) (hg : HasDerivAt g d x) :
    HasDerivAt f d x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact hfg y hy

private theorem hasDerivAt_xOf (t : ℝ) (ht : 1 < t) :
    HasDerivAt xOf (-4 * t / (t ^ 2 - 1) ^ 2) t := by
  have hd : t ^ 2 - 1 ≠ 0 := by
    have : 0 < t ^ 2 - 1 := by nlinarith
    exact ne_of_gt this
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * t) t := by
    convert (hasDerivAt_id t).pow 2 using 1 <;> norm_num
  unfold xOf
  convert (hsq.add_const 1).div (hsq.sub_const 1) hd using 1 <;>
    field_simp [hd] <;> ring

private theorem xOf_gt_one (t : ℝ) (ht : 1 < t) : 1 < xOf t := by
  have hd : 0 < t ^ 2 - 1 := by nlinarith
  unfold xOf
  apply (lt_div_iff₀ hd).2
  nlinarith

private theorem radical_eq_normalized (x : ℝ) (hx : 1 < x) :
    radicalRatioAt x =
      (Real.sqrt ((x + 1) / (x - 1)) - 1) /
        (Real.sqrt ((x + 1) / (x - 1)) + 1) := by
  let a := Real.sqrt (x + 1)
  let b := Real.sqrt (x - 1)
  let q := Real.sqrt ((x + 1) / (x - 1))
  have ha : 0 < a := Real.sqrt_pos.2 (by linarith)
  have hb : 0 < b := Real.sqrt_pos.2 (by linarith)
  have hq : 0 < q := Real.sqrt_pos.2
    (div_pos (by linarith) (by linarith))
  have ha2 : a ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = x - 1 := Real.sq_sqrt (by linarith)
  have hq2 : q ^ 2 = (x + 1) / (x - 1) :=
    Real.sq_sqrt (le_of_lt (div_pos (by linarith) (by linarith)))
  have hxm : x - 1 ≠ 0 := by linarith
  have hqb : q * b = a := by
    have hs : (q * b) ^ 2 = a ^ 2 := by
      rw [mul_pow, hq2, hb2, ha2]
      field_simp [hxm]
    nlinarith [mul_pos hq hb]
  change (a - b) / (a + b) = (q - 1) / (q + 1)
  field_simp [ne_of_gt (add_pos ha hb), ne_of_gt (by linarith : 0 < q + 1)]
  nlinarith

private theorem raw_eq_normalized (t : ℝ) (ht : 1 < t) :
    rawParamIntegrand t = normalizedParamIntegrand t := by
  unfold rawParamIntegrand normalizedParamIntegrand
  rw [radical_eq_normalized (xOf t) (xOf_gt_one t ht)]

private theorem xOf_ratio (t : ℝ) (ht : 1 < t) :
    (xOf t + 1) / (xOf t - 1) = t ^ 2 := by
  have hd : t ^ 2 - 1 ≠ 0 := by
    have : 0 < t ^ 2 - 1 := by nlinarith
    exact ne_of_gt this
  have hm : xOf t - 1 ≠ 0 := ne_of_gt (by linarith [xOf_gt_one t ht])
  unfold xOf at *
  field_simp [hd, hm]
  ring

private theorem normalized_eq_scaled (t : ℝ) (ht : 1 < t) :
    normalizedParamIntegrand t = -4 * rationalParamIntegrand t := by
  have hm : t - 1 ≠ 0 := by linarith
  have hp : t + 1 ≠ 0 := by linarith
  have hfac : t ^ 2 - 1 = (t - 1) * (t + 1) := by ring
  unfold normalizedParamIntegrand rationalParamIntegrand
  rw [xOf_ratio t ht, (hasDerivAt_xOf t ht).deriv]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (lt_trans (by norm_num) ht), hfac]
  field_simp [hm, hp]

private theorem partialFraction_eq_scaled (t : ℝ) (ht : 1 < t) :
    partialFraction t = -4 * rationalParamIntegrand t := by
  have hm : t - 1 ≠ 0 := by linarith
  have hp : t + 1 ≠ 0 := by linarith
  unfold partialFraction rationalParamIntegrand
  field_simp [hm, hp]
  ring

private theorem raw_eq_partialFraction (t : ℝ) (ht : 1 < t) :
    rawParamIntegrand t = partialFraction t := by
  rw [raw_eq_normalized t ht, normalized_eq_scaled t ht,
    partialFraction_eq_scaled t ht]

private theorem antiderivatives_eq_primitive_Ioi
    (a : ℝ) (f p : ℝ → ℝ)
    (hp : ∀ x, a < x → HasDerivAt p (f x) x) :
    AntiderivativesOn {x | a < x} f =
      PrimitiveFamilyOn {x | a < x} p := by
  ext F
  constructor
  · intro hF
    let b := a + 1
    let H := fun x => F x - p x
    have hb : a < b := by dsimp [b]; linarith
    have hH : ∀ x, a < x → HasDerivAt H 0 x := by
      intro x hx
      dsimp [H]
      convert (hF x hx).sub (hp x hx) using 1 <;> ring
    have hconst : ∀ x, a < x → H x = H b := by
      intro x hx
      by_cases hxb : x = b
      · simpa [hxb]
      rcases lt_or_gt_of_ne hxb with hlt | hgt
      · have hcont : ContinuousOn H (Set.Icc x b) := by
          intro y hy
          exact (hH y (by linarith [hy.1])).continuousAt.continuousWithinAt
        have hdiff : DifferentiableOn ℝ H (Set.Ioo x b) := by
          intro y hy
          exact (hH y (by linarith [hy.1])).differentiableAt.differentiableWithinAt
        rcases exists_deriv_eq_slope H hlt hcont hdiff with ⟨c, hc, hs⟩
        have hz : deriv H c = 0 := (hH c (by linarith [hc.1])).deriv
        rw [hz] at hs
        have hden : b - x ≠ 0 := by linarith
        field_simp [hden] at hs
        linarith
      · have hcont : ContinuousOn H (Set.Icc b x) := by
          intro y hy
          exact (hH y (by linarith [hy.1])).continuousAt.continuousWithinAt
        have hdiff : DifferentiableOn ℝ H (Set.Ioo b x) := by
          intro y hy
          exact (hH y (by linarith [hy.1])).differentiableAt.differentiableWithinAt
        rcases exists_deriv_eq_slope H hgt hcont hdiff with ⟨c, hc, hs⟩
        have hz : deriv H c = 0 := (hH c (by linarith [hc.1])).deriv
        rw [hz] at hs
        have hden : x - b ≠ 0 := by linarith
        field_simp [hden] at hs
        linarith
    refine ⟨H b, ?_⟩
    intro x hx
    have hc := hconst x hx
    dsimp [H] at hc ⊢
    linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    have hd : HasDerivAt (fun y => p y + C) (f x) x := (hp x hx).add_const C
    exact hasDerivAt_congr_on_Ioi F (fun y => p y + C) a x (f x) hx
      (fun y hy => hFC y hy) hd

private theorem parameterPrimitive_hasDerivAt (t : ℝ) (ht : 1 < t) :
    HasDerivAt parameterPrimitive (partialFraction t) t := by
  have hm : t - 1 ≠ 0 := by linarith
  have hp : t + 1 ≠ 0 := by linarith
  have hpow : (t + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hp
  have hplus : HasDerivAt (fun y : ℝ => y + 1) 1 t := by
    simpa using (hasDerivAt_id t).add_const 1
  have hminus : HasDerivAt (fun y : ℝ => y - 1) 1 t := by
    simpa using (hasDerivAt_id t).sub_const 1
  have hfirst : HasDerivAt (fun y : ℝ => 1 / (y + 1) ^ 2)
      (-2 / (t + 1) ^ 3) t := by
    convert (hasDerivAt_const t (1 : ℝ)).div (hplus.pow 2) hpow using 1 <;>
      simp [pow_two] <;> field_simp [hp] <;> ring
  have hsecond : HasDerivAt (fun y : ℝ => 1 / (y + 1))
      (-1 / (t + 1) ^ 2) t := by
    convert (hasDerivAt_const t (1 : ℝ)).div hplus hp using 1 <;>
      field_simp [hp] <;> ring
  have hratio : 0 < (t + 1) / (t - 1) := div_pos (by linarith) (by linarith)
  have hu : HasDerivAt (fun y => (y + 1) / (y - 1))
      (-2 / (t - 1) ^ 2) t := by
    convert hplus.div hminus hm using 1 <;>
      field_simp [hm] <;> ring
  have houter : HasDerivAt Real.log (((t + 1) / (t - 1))⁻¹)
      ((t + 1) / (t - 1)) :=
    Real.hasDerivAt_log (ne_of_gt hratio)
  have hlog : HasDerivAt (fun y => Real.log ((y + 1) / (y - 1)))
      ((-2 / (t - 1) ^ 2) / ((t + 1) / (t - 1))) t := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_comm] using
      houter.comp t hu
  have hlogabs : HasDerivAt (fun y => Real.log |(y + 1) / (y - 1)|)
      ((-2 / (t - 1) ^ 2) / ((t + 1) / (t - 1))) t :=
    hasDerivAt_congr_on_Ioi _ _ 1 t _ ht
      (fun y hy => by rw [abs_of_pos (div_pos (by linarith) (by linarith))]) hlog
  unfold parameterPrimitive partialFraction
  convert (hfirst.sub hsecond).add (hlogabs.const_mul (1 / 2)) using 1 <;>
    field_simp [hm, hp] <;> ring

private theorem sqrt_sq_sub_one_hasDerivAt (x : ℝ) (hx : 1 < x) :
    HasDerivAt (fun y => Real.sqrt (y ^ 2 - 1))
      (x / Real.sqrt (x ^ 2 - 1)) x := by
  have hr : 0 < x ^ 2 - 1 := by nlinarith
  have hq : Real.sqrt (x ^ 2 - 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr)
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> norm_num
  convert (Real.hasDerivAt_sqrt (ne_of_gt hr)).comp x (hsq.sub_const 1) using 1 <;>
    field_simp [hq] <;> ring

private theorem xPrimitive_hasDerivAt (x : ℝ) (hx : 1 < x) :
    HasDerivAt xPrimitive (xSimplifiedIntegrand x) x := by
  have hr : 0 < x ^ 2 - 1 := by nlinarith
  have hq : 0 < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.2 hr
  have hq0 : Real.sqrt (x ^ 2 - 1) ≠ 0 := ne_of_gt hq
  have hq2 : (Real.sqrt (x ^ 2 - 1)) ^ 2 = x ^ 2 - 1 :=
    Real.sq_sqrt (le_of_lt hr)
  have hsqrt := sqrt_sq_sub_one_hasDerivAt x hx
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hu : HasDerivAt (fun y => y + Real.sqrt (y ^ 2 - 1))
      (1 + x / Real.sqrt (x ^ 2 - 1)) x := hid.add hsqrt
  have hsum : 0 < x + Real.sqrt (x ^ 2 - 1) := by linarith
  have houter : HasDerivAt Real.log ((x + Real.sqrt (x ^ 2 - 1))⁻¹)
      (x + Real.sqrt (x ^ 2 - 1)) :=
    Real.hasDerivAt_log (ne_of_gt hsum)
  have hlog : HasDerivAt (fun y => Real.log (y + Real.sqrt (y ^ 2 - 1)))
      ((1 + x / Real.sqrt (x ^ 2 - 1)) /
        (x + Real.sqrt (x ^ 2 - 1))) x := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_comm] using
      houter.comp x hu
  have hlogabs : HasDerivAt
      (fun y => Real.log |y + Real.sqrt (y ^ 2 - 1)|)
      ((1 + x / Real.sqrt (x ^ 2 - 1)) /
        (x + Real.sqrt (x ^ 2 - 1))) x :=
    hasDerivAt_congr_on_Ioi _ _ 1 x _ hx
      (fun y hy => by
        rw [abs_of_pos]
        have hs : 0 ≤ Real.sqrt (y ^ 2 - 1) := Real.sqrt_nonneg _
        linarith) hlog
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> norm_num
  have hfirst : HasDerivAt (fun y : ℝ => (1 / 2) * y ^ 2) x x := by
    convert hsq.const_mul (1 / 2) using 1 <;> ring
  have hprod : HasDerivAt
      (fun y : ℝ => y * Real.sqrt (y ^ 2 - 1))
      (Real.sqrt (x ^ 2 - 1) + x * (x / Real.sqrt (x ^ 2 - 1))) x := by
    convert hid.mul hsqrt using 1 <;> ring
  have hmiddle : HasDerivAt
      (fun y : ℝ => -(1 / 2) * (y * Real.sqrt (y ^ 2 - 1)))
      (-(1 / 2) *
        (Real.sqrt (x ^ 2 - 1) + x * (x / Real.sqrt (x ^ 2 - 1)))) x :=
    hprod.const_mul (-(1 / 2))
  have hlast : HasDerivAt
      (fun y : ℝ => (1 / 2) * Real.log |y + Real.sqrt (y ^ 2 - 1)|)
      ((1 / 2) * ((1 + x / Real.sqrt (x ^ 2 - 1)) /
        (x + Real.sqrt (x ^ 2 - 1)))) x :=
    hlogabs.const_mul (1 / 2)
  have hlogder :
      ((1 + x / Real.sqrt (x ^ 2 - 1)) /
        (x + Real.sqrt (x ^ 2 - 1))) =
      1 / Real.sqrt (x ^ 2 - 1) := by
    field_simp [hq0, ne_of_gt hsum] <;> ring
  have htotal : HasDerivAt xPrimitive
      ((x + (-(1 / 2) *
        (Real.sqrt (x ^ 2 - 1) + x * (x / Real.sqrt (x ^ 2 - 1))))) +
        (1 / 2) * ((1 + x / Real.sqrt (x ^ 2 - 1)) /
          (x + Real.sqrt (x ^ 2 - 1)))) x := by
    unfold xPrimitive
    convert (hfirst.add hmiddle).add hlast using 1
    funext y
    simp only [Pi.add_apply]
    ring
  convert htotal using 1
  unfold xSimplifiedIntegrand
  rw [hlogder]
  field_simp [hq0]
  nlinarith [hq2]

private theorem radicalRatio_eq_simplified (x : ℝ) (hx : 1 < x) :
    radicalRatioAt x = xSimplifiedIntegrand x := by
  have ha : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.2 (by linarith)
  have hb : 0 < Real.sqrt (x - 1) := Real.sqrt_pos.2 (by linarith)
  have ha0 : 0 ≤ Real.sqrt (x + 1) := le_of_lt ha
  have hb0 : 0 ≤ Real.sqrt (x - 1) := le_of_lt hb
  have hc0 : 0 ≤ Real.sqrt (x ^ 2 - 1) := Real.sqrt_nonneg _
  have ha2 := Real.sq_sqrt (show 0 ≤ x + 1 by linarith)
  have hb2 := Real.sq_sqrt (show 0 ≤ x - 1 by linarith)
  have hc2 := Real.sq_sqrt (show 0 ≤ x ^ 2 - 1 by nlinarith)
  have hs : Real.sqrt (x + 1) + Real.sqrt (x - 1) ≠ 0 :=
    ne_of_gt (add_pos ha hb)
  have hab : Real.sqrt (x + 1) * Real.sqrt (x - 1) =
      Real.sqrt (x ^ 2 - 1) := by
    have hsq : (Real.sqrt (x + 1) * Real.sqrt (x - 1)) ^ 2 =
        (Real.sqrt (x ^ 2 - 1)) ^ 2 := by
      rw [mul_pow, ha2, hb2, hc2]
      ring
    nlinarith [mul_nonneg ha0 hb0]
  have hrat : radicalRatioAt x =
      (Real.sqrt (x + 1) - Real.sqrt (x - 1)) ^ 2 /
        (x + 1 - (x - 1)) := by
    unfold radicalRatioAt
    rw [show x + 1 - (x - 1) = 2 by ring]
    field_simp [hs]
    nlinarith
  rw [hrat]
  unfold xSimplifiedIntegrand
  rw [show x + 1 - (x - 1) = 2 by ring]
  nlinarith

theorem gap1 (t : ℝ) (ht : t ∈ parameterBranch) :
    xOf t = (t ^ 2 + 1) / (t ^ 2 - 1) := by
  rfl
theorem gap2 (t : ℝ) (ht : t ∈ parameterBranch) :
    HasDerivAt xOf (-4 * t / (t ^ 2 - 1) ^ 2) t := by
  change 1 < t at ht
  exact hasDerivAt_xOf t ht
theorem gap3 :
    AntiderivativesOn parameterBranch rawParamIntegrand =
      AntiderivativesOn parameterBranch normalizedParamIntegrand := by
  ext F
  constructor
  · intro hF
    intro t ht
    have hi := raw_eq_normalized t (by simpa [parameterBranch] using ht)
    simpa [hi] using hF t ht
  · intro hF
    intro t ht
    have hi := raw_eq_normalized t (by simpa [parameterBranch] using ht)
    simpa [hi] using hF t ht
theorem gap4 :
    AntiderivativesOn parameterBranch normalizedParamIntegrand =
      ScaledRationalFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨fun t => (-(1 : ℝ) / 4) * F t, ?_, ?_⟩
    · intro t ht
      have hi := normalized_eq_scaled t (by simpa [parameterBranch] using ht)
      convert (hF t ht).const_mul (-(1 : ℝ) / 4) using 1 <;>
        simp only [hi] <;> ring
    · intro t ht
      ring
  · rintro ⟨G, hG, hFG⟩
    intro t ht
    have ht' : 1 < t := by simpa [parameterBranch] using ht
    have hi := normalized_eq_scaled t ht'
    have hd : HasDerivAt (fun y => -4 * G y) (-4 * rationalParamIntegrand t) t :=
      (hG t ht).const_mul (-4)
    have hc : HasDerivAt F (-4 * rationalParamIntegrand t) t :=
      hasDerivAt_congr_on_Ioi F (fun y => -4 * G y) 1 t
        (-4 * rationalParamIntegrand t) ht'
        (fun y hy => hFG y (by simpa [parameterBranch] using hy)) hd
    simpa [hi] using hc
theorem gap5 :
    AntiderivativesOn parameterBranch rawParamIntegrand =
      ScaledRationalFamily := by
  exact Eq.trans gap3 gap4
theorem gap6 :
    AntiderivativesOn parameterBranch rawParamIntegrand =
      AntiderivativesOn parameterBranch partialFraction := by
  ext F
  constructor
  · intro hF t ht
    have hi := raw_eq_partialFraction t (by simpa [parameterBranch] using ht)
    simpa [hi] using hF t ht
  · intro hF t ht
    have hi := raw_eq_partialFraction t (by simpa [parameterBranch] using ht)
    simpa [hi] using hF t ht
theorem gap7 :
    AntiderivativesOn parameterBranch partialFraction =
      PrimitiveFamilyOn parameterBranch parameterPrimitive := by
  simpa [parameterBranch] using
    (antiderivatives_eq_primitive_Ioi (1 : ℝ) partialFraction parameterPrimitive
      parameterPrimitive_hasDerivAt)
theorem gap8 :
    AntiderivativesOn parameterBranch rawParamIntegrand =
      PrimitiveFamilyOn parameterBranch parameterPrimitive := by
  exact Eq.trans gap6 gap7
theorem gap9 :
    AntiderivativesOn xBranch radicalRatioAt =
      PrimitiveFamilyOn xBranch xPrimitive := by
  calc
    AntiderivativesOn xBranch radicalRatioAt =
        AntiderivativesOn xBranch xSimplifiedIntegrand := by
      ext F
      constructor
      · intro hF x hx
        simpa [radicalRatio_eq_simplified x (by simpa [xBranch] using hx)] using hF x hx
      · intro hF x hx
        simpa [radicalRatio_eq_simplified x (by simpa [xBranch] using hx)] using hF x hx
    _ = PrimitiveFamilyOn xBranch xPrimitive := by
      simpa [xBranch] using
        (antiderivatives_eq_primitive_Ioi (1 : ℝ) xSimplifiedIntegrand xPrimitive
          xPrimitive_hasDerivAt)
theorem gap10 (x : ℝ) (hx : x ∈ xBranch) :
    radicalRatioAt x =
      (Real.sqrt (x + 1) - Real.sqrt (x - 1)) ^ 2 /
        (x + 1 - (x - 1)) := by
  change 1 < x at hx
  have ha : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.2 (by linarith)
  have hb : 0 < Real.sqrt (x - 1) := Real.sqrt_pos.2 (by linarith)
  have ha2 := Real.sq_sqrt (show 0 ≤ x + 1 by linarith)
  have hb2 := Real.sq_sqrt (show 0 ≤ x - 1 by linarith)
  have hs : Real.sqrt (x + 1) + Real.sqrt (x - 1) ≠ 0 :=
    ne_of_gt (add_pos ha hb)
  unfold radicalRatioAt
  rw [show x + 1 - (x - 1) = 2 by ring]
  field_simp [hs]
  nlinarith
theorem gap11 (x : ℝ) (hx : x ∈ xBranch) :
    (Real.sqrt (x + 1) - Real.sqrt (x - 1)) ^ 2 /
        (x + 1 - (x - 1)) =
      x - Real.sqrt (x ^ 2 - 1) := by
  change 1 < x at hx
  have ha0 : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg _
  have hb0 : 0 ≤ Real.sqrt (x - 1) := Real.sqrt_nonneg _
  have hc0 : 0 ≤ Real.sqrt (x ^ 2 - 1) := Real.sqrt_nonneg _
  have ha2 := Real.sq_sqrt (show 0 ≤ x + 1 by linarith)
  have hb2 := Real.sq_sqrt (show 0 ≤ x - 1 by linarith)
  have hc2 := Real.sq_sqrt (show 0 ≤ x ^ 2 - 1 by nlinarith)
  have hab : Real.sqrt (x + 1) * Real.sqrt (x - 1) =
      Real.sqrt (x ^ 2 - 1) := by
    have hs : (Real.sqrt (x + 1) * Real.sqrt (x - 1)) ^ 2 =
        (Real.sqrt (x ^ 2 - 1)) ^ 2 := by
      rw [mul_pow, ha2, hb2, hc2]
      ring
    nlinarith [mul_nonneg ha0 hb0]
  rw [show x + 1 - (x - 1) = 2 by ring]
  nlinarith
theorem gap12 (x : ℝ) (hx : x ∈ xBranch) :
    radicalRatioAt x = xSimplifiedIntegrand x := by
  change 1 < x at hx
  exact radicalRatio_eq_simplified x hx
theorem gap13 :
    AntiderivativesOn xBranch radicalRatioAt =
      AntiderivativesOn xBranch xSimplifiedIntegrand := by
  ext F
  constructor
  · intro hF x hx
    have hi := gap12 x hx
    simpa [hi] using hF x hx
  · intro hF x hx
    have hi := gap12 x hx
    simpa [hi] using hF x hx
theorem gap14 :
    AntiderivativesOn xBranch xSimplifiedIntegrand =
      PrimitiveFamilyOn xBranch xPrimitive := by
  simpa [xBranch] using
    (antiderivatives_eq_primitive_Ioi (1 : ℝ) xSimplifiedIntegrand xPrimitive
      xPrimitive_hasDerivAt)
theorem gap15 :
    AntiderivativesOn xBranch radicalRatioAt =
      PrimitiveFamilyOn xBranch xPrimitive := by
  exact gap9

end
end ProofGap.Exercise1931
