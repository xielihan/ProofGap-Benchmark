import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise438

noncomputable section

def signedCbrt (x : ℝ) : ℝ :=
  if 0 ≤ x then Real.rpow x (1 / 3 : ℝ)
  else -Real.rpow (-x) (1 / 3 : ℝ)
def original (x : ℝ) : ℝ :=
  (Real.sqrt (1 - x) - 3) / (2 + signedCbrt x)
def rationalized (x : ℝ) : ℝ :=
  (-(8 + x) * (4 + signedCbrt (x ^ 2) - 2 * signedCbrt x)) /
    ((8 + x) * (Real.sqrt (1 - x) + 3))
def cancelled (x : ℝ) : ℝ :=
  -(4 + signedCbrt (x ^ 2) - 2 * signedCbrt x) /
    (Real.sqrt (1 - x) + 3)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

private lemma cube_strict {a b : ℝ} (h : a < b) : a ^ 3 < b ^ 3 := by
  have hs : 0 < (b - a) ^ 2 := pow_pos (sub_pos.mpr h) 2
  have hq : 0 < b ^ 2 + b * a + a ^ 2 := by
    nlinarith [sq_nonneg (a + b), hs]
  nlinarith [mul_pos (sub_pos.mpr h) hq]

private lemma cube_injective {a b : ℝ} (h : a ^ 3 = b ^ 3) : a = b := by
  by_contra hab
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact (ne_of_lt (cube_strict hlt)) h
  · exact (ne_of_gt (cube_strict hgt)) h

private lemma signedCbrt_cubed (x : ℝ) : signedCbrt x ^ 3 = x := by
  unfold signedCbrt
  split_ifs with hx
  · calc
      (Real.rpow x (1 / 3 : ℝ)) ^ 3 =
          Real.rpow (Real.rpow x (1 / 3 : ℝ)) (3 : ℝ) :=
        (Real.rpow_natCast _ 3).symm
      _ = Real.rpow x ((1 / 3 : ℝ) * 3) :=
        (Real.rpow_mul hx (1 / 3 : ℝ) 3).symm
      _ = x := by norm_num
  · have hx' : 0 ≤ -x := by linarith
    have hp : (Real.rpow (-x) (1 / 3 : ℝ)) ^ 3 = -x := by
      calc
        (Real.rpow (-x) (1 / 3 : ℝ)) ^ 3 =
            Real.rpow (Real.rpow (-x) (1 / 3 : ℝ)) (3 : ℝ) :=
          (Real.rpow_natCast _ 3).symm
        _ = Real.rpow (-x) ((1 / 3 : ℝ) * 3) :=
          (Real.rpow_mul hx' (1 / 3 : ℝ) 3).symm
        _ = -x := by norm_num
    nlinarith

private lemma signedCbrt_sq (x : ℝ) :
    signedCbrt (x ^ 2) = signedCbrt x ^ 2 := by
  apply cube_injective
  rw [signedCbrt_cubed]
  calc
    x ^ 2 = (signedCbrt x ^ 3) ^ 2 := by rw [signedCbrt_cubed]
    _ = (signedCbrt x ^ 2) ^ 3 := by ring

private lemma signedCbrt_continuousAt (a : ℝ) :
    ContinuousAt signedCbrt a := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hlo : (signedCbrt a - ε) ^ 3 < a := by
    calc
      (signedCbrt a - ε) ^ 3 < signedCbrt a ^ 3 :=
        cube_strict (sub_lt_self _ hε)
      _ = a := signedCbrt_cubed a
  have hhi : a < (signedCbrt a + ε) ^ 3 := by
    calc
      a = signedCbrt a ^ 3 := (signedCbrt_cubed a).symm
      _ < (signedCbrt a + ε) ^ 3 :=
        cube_strict (lt_add_of_pos_right _ hε)
  refine ⟨min (a - (signedCbrt a - ε) ^ 3)
      ((signedCbrt a + ε) ^ 3 - a), ?_, ?_⟩
  · exact lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi)
  · intro x hx
    rw [Real.dist_eq] at hx ⊢
    rw [abs_lt] at hx ⊢
    have hlcube :
        (signedCbrt a - ε) ^ 3 < signedCbrt x ^ 3 := by
      rw [signedCbrt_cubed]
      nlinarith [min_le_left
        (a - (signedCbrt a - ε) ^ 3)
        ((signedCbrt a + ε) ^ 3 - a)]
    have hucube :
        signedCbrt x ^ 3 < (signedCbrt a + ε) ^ 3 := by
      rw [signedCbrt_cubed]
      nlinarith [min_le_right
        (a - (signedCbrt a - ε) ^ 3)
        ((signedCbrt a + ε) ^ 3 - a)]
    constructor
    · have hlroot : signedCbrt a - ε < signedCbrt x := by
        by_contra hnot
        have hle : signedCbrt x ≤ signedCbrt a - ε := le_of_not_gt hnot
        rcases lt_or_eq_of_le hle with hlt | heq
        · have hc := cube_strict hlt
          linarith
        · rw [heq] at hlcube
          exact (lt_irrefl _ hlcube)
      linarith
    · have huroot : signedCbrt x < signedCbrt a + ε := by
        by_contra hnot
        have hle : signedCbrt a + ε ≤ signedCbrt x := le_of_not_gt hnot
        rcases lt_or_eq_of_le hle with hlt | heq
        · have hc := cube_strict hlt
          linarith
        · rw [← heq] at hucube
          exact (lt_irrefl _ hucube)
      linarith

private theorem hasLimitAtCongr {f g : ℝ → ℝ} {a L : ℝ}
    (hfg : f =ᶠ[nhdsWithin a ({a} : Set ℝ)ᶜ] g) :
    HasLimitAt f a L ↔ HasLimitAt g a L := by
  unfold HasLimitAt
  exact ⟨fun hf => hf.congr' hfg, fun hg => hg.congr' hfg.symm⟩

/-- Exercise 438, gap 1; use a signed real cube root near `x=-8`. -/
theorem gap1 : HasLimitAt original (-8) (-2) ↔
    HasLimitAt rationalized (-8) (-2) := by
  apply hasLimitAtCongr
  have hnear :
      ∀ᶠ x : ℝ in nhdsWithin (-8 : ℝ) ({-8} : Set ℝ)ᶜ,
        x ∈ Set.Ioo (-9 : ℝ) (-7 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds (by norm_num))
  filter_upwards [hnear, self_mem_nhdsWithin] with x hx hxmem
  have hxne : x ≠ -8 := by simpa using hxmem
  have harg : 0 ≤ 1 - x := by linarith [hx.2]
  have hsqrt : (Real.sqrt (1 - x)) ^ 2 = 1 - x :=
    Real.sq_sqrt harg
  have hcubed := signedCbrt_cubed x
  have hsq := signedCbrt_sq x
  have h8 : 8 + x ≠ 0 := by
    intro h
    apply hxne
    linarith
  have hcden : 2 + signedCbrt x ≠ 0 := by
    intro h
    have : signedCbrt x = -2 := by linarith
    rw [this] at hcubed
    norm_num at hcubed
    exact hxne hcubed.symm
  have hsden : Real.sqrt (1 - x) + 3 ≠ 0 := by positivity
  unfold original rationalized
  rw [hsq]
  apply (div_eq_div_iff hcden (mul_ne_zero h8 hsden)).2
  nlinarith [hcubed]

/-- Exercise 438, gap 2. -/
theorem gap2 : HasLimitAt original (-8) (-2) ↔
    HasLimitAt rationalized (-8) (-2) := by
  exact gap1

/-- Exercise 438, gap 3. -/
theorem gap3 : HasLimitAt rationalized (-8) (-2) ↔
    HasLimitAt cancelled (-8) (-2) := by
  apply hasLimitAtCongr
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxne : 8 + x ≠ 0 := by
    intro h
    have : x = -8 := by linarith
    exact (by simpa [this] using hx)
  unfold rationalized cancelled
  field_simp [hxne]

/-- Exercise 438, gap 4. -/
theorem gap4 : HasLimitAt cancelled (-8) (-2) := by
  have hm8 : signedCbrt (-8) = -2 := by
    apply cube_injective
    rw [signedCbrt_cubed]
    norm_num
  have h64 : signedCbrt 64 = 4 := by
    apply cube_injective
    rw [signedCbrt_cubed]
    norm_num
  have hx2 : ContinuousAt (fun x : ℝ => x ^ 2) (-8) :=
    continuousAt_id.pow 2
  have hc2 : ContinuousAt (fun x : ℝ => signedCbrt (x ^ 2)) (-8) := by
    have ht : Filter.Tendsto
        (signedCbrt ∘ fun x : ℝ => x ^ 2)
        (nhds (-8)) (nhds (signedCbrt ((-8 : ℝ) ^ 2))) :=
      Filter.Tendsto.comp
        (signedCbrt_continuousAt ((-8 : ℝ) ^ 2)) hx2
    simpa only [Function.comp_apply] using ht
  have hc : ContinuousAt (fun x : ℝ => signedCbrt x) (-8) :=
    signedCbrt_continuousAt (-8)
  have hnum : ContinuousAt
      (fun x : ℝ => -(4 + signedCbrt (x ^ 2) - 2 * signedCbrt x)) (-8) :=
    ((continuousAt_const.add hc2).sub
      (continuousAt_const.mul hc)).neg
  have harg : ContinuousAt (fun x : ℝ => 1 - x) (-8) :=
    continuousAt_const.sub continuousAt_id
  have hden : ContinuousAt
      (fun x : ℝ => Real.sqrt (1 - x) + 3) (-8) :=
    (Real.continuous_sqrt.continuousAt.comp harg).add continuousAt_const
  have hsqrt9 : Real.sqrt 9 = 3 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 9 by norm_num)
    have hn := Real.sqrt_nonneg (9 : ℝ)
    nlinarith
  have hdenne : Real.sqrt (1 - (-8 : ℝ)) + 3 ≠ 0 := by
    norm_num [hsqrt9]
  have hcont : ContinuousAt cancelled (-8) := by
    unfold cancelled
    exact hnum.div hden hdenne
  have hvalue : cancelled (-8) = -2 := by
    norm_num [cancelled, hm8, h64, hsqrt9]
  unfold HasLimitAt
  rw [← hvalue]
  exact hcont.tendsto.mono_left inf_le_left

/-- Exercise 438, gap 5. -/
theorem gap5 : HasLimitAt original (-8) (-2) := by
  exact gap1.mpr (gap3.mpr gap4)

end

end ProofGap.Exercise438
