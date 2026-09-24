import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise441

noncomputable section

def signedCbrt (x : ℝ) : ℝ :=
  if 0 ≤ x then Real.rpow x (1 / 3 : ℝ)
  else -Real.rpow (-x) (1 / 3 : ℝ)
def original (x : ℝ) : ℝ := (signedCbrt (x - 6) + 2) / (x ^ 3 + 8)
def cancelled (x : ℝ) : ℝ :=
  1 / ((x ^ 2 - 2 * x + 4) *
    (signedCbrt ((x - 6) ^ 2) - 2 * signedCbrt (x - 6) + 4))
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
    have hlroot : signedCbrt a - ε < signedCbrt x := by
      by_contra hnot
      have hle : signedCbrt x ≤ signedCbrt a - ε := le_of_not_gt hnot
      rcases lt_or_eq_of_le hle with hlt | heq
      · have hc := cube_strict hlt
        linarith
      · rw [heq] at hlcube
        exact (lt_irrefl _ hlcube)
    have huroot : signedCbrt x < signedCbrt a + ε := by
      by_contra hnot
      have hle : signedCbrt a + ε ≤ signedCbrt x := le_of_not_gt hnot
      rcases lt_or_eq_of_le hle with hlt | heq
      · have hc := cube_strict hlt
        linarith
      · rw [← heq] at hucube
        exact (lt_irrefl _ hucube)
    constructor <;> linarith

private theorem hasLimitAtCongr {f g : ℝ → ℝ} {a L : ℝ}
    (hfg : f =ᶠ[nhdsWithin a ({a} : Set ℝ)ᶜ] g) :
    HasLimitAt f a L ↔ HasLimitAt g a L := by
  unfold HasLimitAt
  exact ⟨fun hf => hf.congr' hfg, fun hg => hg.congr' hfg.symm⟩

/-- Exercise 441, gap 1; use the signed real cube root. -/
theorem gap1 : HasLimitAt original (-2) (1 / 144) ↔
    HasLimitAt cancelled (-2) (1 / 144) := by
  apply hasLimitAtCongr
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxne : x ≠ -2 := by simpa using hx
  let A : ℝ := signedCbrt (x - 6)
  have hA : A ^ 3 = x - 6 := by
    dsimp [A]
    exact signedCbrt_cubed (x - 6)
  have hsq : signedCbrt ((x - 6) ^ 2) = A ^ 2 := by
    dsimp [A]
    exact signedCbrt_sq (x - 6)
  have hxplus : x + 2 ≠ 0 := by
    intro h
    apply hxne
    linarith
  have hxpoly : x ^ 2 - 2 * x + 4 ≠ 0 := by
    apply ne_of_gt
    nlinarith [sq_nonneg (x - 1)]
  have hApoly : A ^ 2 - 2 * A + 4 ≠ 0 := by
    apply ne_of_gt
    nlinarith [sq_nonneg (A - 1)]
  have hxden : x ^ 3 + 8 ≠ 0 := by
    rw [show x ^ 3 + 8 = (x + 2) * (x ^ 2 - 2 * x + 4) by ring]
    exact mul_ne_zero hxplus hxpoly
  have hcancelden :
      (x ^ 2 - 2 * x + 4) *
          (signedCbrt ((x - 6) ^ 2) -
            2 * signedCbrt (x - 6) + 4) ≠ 0 := by
    rw [hsq]
    exact mul_ne_zero hxpoly hApoly
  have hcube :
      (A + 2) * (A ^ 2 - 2 * A + 4) = x + 2 := by
    calc
      (A + 2) * (A ^ 2 - 2 * A + 4) = A ^ 3 + 8 := by ring
      _ = x + 2 := by rw [hA]; ring
  unfold original cancelled
  change (A + 2) / (x ^ 3 + 8) =
    1 / ((x ^ 2 - 2 * x + 4) *
      (signedCbrt ((x - 6) ^ 2) - 2 * A + 4))
  rw [hsq]
  apply (div_eq_div_iff hxden (mul_ne_zero hxpoly hApoly)).2
  rw [show x ^ 3 + 8 = (x + 2) * (x ^ 2 - 2 * x + 4) by ring]
  calc
    (A + 2) * ((x ^ 2 - 2 * x + 4) * (A ^ 2 - 2 * A + 4)) =
        ((A + 2) * (A ^ 2 - 2 * A + 4)) *
          (x ^ 2 - 2 * x + 4) := by ring
    _ = (x + 2) * (x ^ 2 - 2 * x + 4) := by rw [hcube]
    _ = 1 * ((x + 2) * (x ^ 2 - 2 * x + 4)) := by ring

/-- Exercise 441, gap 2. -/
theorem gap2 : HasLimitAt original (-2) (1 / 144) ↔
    HasLimitAt cancelled (-2) (1 / 144) := by
  exact gap1

/-- Exercise 441, gap 3. -/
theorem gap3 : HasLimitAt cancelled (-2) (1 / 144) := by
  have hm8 : signedCbrt (-8) = -2 := by
    apply cube_injective
    rw [signedCbrt_cubed]
    norm_num
  have h64 : signedCbrt 64 = 4 := by
    apply cube_injective
    rw [signedCbrt_cubed]
    norm_num
  have hshift : ContinuousAt (fun x : ℝ => x - 6) (-2) :=
    continuousAt_id.sub continuousAt_const
  have hc : ContinuousAt (fun x : ℝ => signedCbrt (x - 6)) (-2) := by
    have ht : Filter.Tendsto
        (signedCbrt ∘ fun x : ℝ => x - 6)
        (nhds (-2)) (nhds (signedCbrt ((-2 : ℝ) - 6))) :=
      Filter.Tendsto.comp (signedCbrt_continuousAt ((-2 : ℝ) - 6)) hshift
    simpa only [Function.comp_apply] using ht
  have hsquare : ContinuousAt (fun x : ℝ => (x - 6) ^ 2) (-2) :=
    hshift.pow 2
  have hc2 :
      ContinuousAt (fun x : ℝ => signedCbrt ((x - 6) ^ 2)) (-2) := by
    have ht : Filter.Tendsto
        (signedCbrt ∘ fun x : ℝ => (x - 6) ^ 2)
        (nhds (-2)) (nhds (signedCbrt (((-2 : ℝ) - 6) ^ 2))) :=
      Filter.Tendsto.comp
        (signedCbrt_continuousAt (((-2 : ℝ) - 6) ^ 2)) hsquare
    simpa only [Function.comp_apply] using ht
  have hxpoly :
      ContinuousAt (fun x : ℝ => x ^ 2 - 2 * x + 4) (-2) :=
    ((continuousAt_id.pow 2).sub
      (continuousAt_const.mul continuousAt_id)).add continuousAt_const
  have hApoly : ContinuousAt
      (fun x : ℝ =>
        signedCbrt ((x - 6) ^ 2) - 2 * signedCbrt (x - 6) + 4) (-2) :=
    (hc2.sub (continuousAt_const.mul hc)).add continuousAt_const
  have hden := hxpoly.mul hApoly
  have hdenne :
      (((-2 : ℝ) ^ 2 - 2 * (-2) + 4) *
        (signedCbrt (((-2 : ℝ) - 6) ^ 2) -
          2 * signedCbrt ((-2) - 6) + 4)) ≠ 0 := by
    norm_num [hm8, h64]
  have hcont : ContinuousAt cancelled (-2) := by
    unfold cancelled
    exact continuousAt_const.div hden hdenne
  have hvalue : cancelled (-2) = (1 / 144 : ℝ) := by
    norm_num [cancelled, hm8, h64]
  unfold HasLimitAt
  rw [← hvalue]
  exact hcont.tendsto.mono_left inf_le_left

/-- Exercise 441, gap 4. -/
theorem gap4 : HasLimitAt original (-2) (1 / 144) := by
  exact gap1.mpr gap3

end

end ProofGap.Exercise441
