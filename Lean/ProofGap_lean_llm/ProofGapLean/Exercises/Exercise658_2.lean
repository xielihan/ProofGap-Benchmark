import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise658_2

noncomputable section

def target (x : ℝ) : ℝ := Real.sqrt ((1 + x) / (1 - x))
def model (x : ℝ) : ℝ :=
  Real.sqrt 2 * (1 / Real.sqrt (1 - x))

/-- Exercise 658_2, gap 1; restrict to `x<1`, where the radical factorization is valid. -/
private theorem equivalent_of_ratio_limit
    {l : Filter ℝ} {f g : ℝ → ℝ}
    (hg : ∀ᶠ x in l, g x ≠ 0)
    (hlim : Filter.Tendsto (fun x => f x / g x) l (nhds 1)) :
    Asymptotics.IsEquivalent l f g := by
  unfold Asymptotics.IsEquivalent
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hclose : ∀ᶠ x in l, f x / g x ∈ Metric.ball (1 : ℝ) c :=
    hlim.eventually (Metric.ball_mem_nhds (1 : ℝ) hc)
  filter_upwards [hg, hclose] with x hgx hx
  have hratio : ‖f x / g x - 1‖ < c := by
    simpa only [Metric.mem_ball, Real.dist_eq, Real.norm_eq_abs] using hx
  have hid : f x - g x = (f x / g x - 1) * g x := by
    calc
      f x - g x = f x / g x * g x - 1 * g x := by simp [hgx]
      _ = (f x / g x - 1) * g x := by rw [sub_mul]
  have hbound : ‖f x - g x‖ ≤ c * ‖g x‖ := by
    calc
      ‖f x - g x‖ = ‖f x / g x - 1‖ * ‖g x‖ := by rw [hid, norm_mul]
      _ ≤ c * ‖g x‖ :=
        mul_le_mul_of_nonneg_right (le_of_lt hratio) (norm_nonneg _)
  simpa using hbound

theorem gap1 (x : ℝ) (hx : -1 < x) (hx1 : x < 1) :
    target x / model x = Real.sqrt (1 + x) / Real.sqrt 2 := by
  have hxp : 0 ≤ 1 + x := by linarith
  have hxm : 0 < 1 - x := by linarith
  have hsqrt2 : Real.sqrt (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsqrtx : Real.sqrt (1 - x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hxm)
  unfold target model
  rw [Real.sqrt_div hxp]
  field_simp [hsqrt2, hsqrtx]

/-- Exercise 658_2, gap 2. -/
theorem gap2 :
    Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + x) / Real.sqrt 2)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 1) := by
  have hsqrt2 : Real.sqrt (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hcont :
      Continuous (fun x : ℝ => Real.sqrt (1 + x) / Real.sqrt 2) :=
    (Real.continuous_sqrt.comp (continuous_const.add continuous_id)).div_const _
  have ht :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + x) / Real.sqrt 2)
        (nhdsWithin 1 (Set.Iio 1))
        (nhds (Real.sqrt (1 + (1 : ℝ)) / Real.sqrt 2)) :=
    hcont.continuousAt.mono_left
      (show nhdsWithin (1 : ℝ) (Set.Iio 1) ≤ nhds 1 from inf_le_left)
  have hval : Real.sqrt (1 + (1 : ℝ)) / Real.sqrt 2 = 1 := by
    norm_num [hsqrt2]
  simpa only [hval] using ht

/-- Exercise 658_2, gap 3. -/
theorem gap3 :
    Filter.Tendsto (fun x : ℝ => target x / model x)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 1) := by
  refine gap2.congr' ?_
  have hnear0 : ∀ᶠ x in nhds (1 : ℝ), x ∈ Set.Ioi (-1) :=
    isOpen_Ioi.mem_nhds (by norm_num)
  have hnear :
      ∀ᶠ x in nhdsWithin (1 : ℝ) (Set.Iio 1), x ∈ Set.Ioi (-1) :=
    hnear0.filter_mono inf_le_left
  filter_upwards [hnear, self_mem_nhdsWithin] with x hx hx1
  exact (gap1 x hx hx1).symm

/-- Exercise 658_2, gap 4; make the one-sided domain explicit. -/
theorem gap4 :
    Asymptotics.IsEquivalent (nhdsWithin 1 (Set.Iio 1)) target model := by
  have hm :
      ∀ᶠ x in nhdsWithin (1 : ℝ) (Set.Iio 1), model x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    unfold model
    apply mul_ne_zero
    · exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    · exact div_ne_zero one_ne_zero
        (ne_of_gt (Real.sqrt_pos.2 (sub_pos.2 hx)))
  exact equivalent_of_ratio_limit hm gap3

/-- Exercise 658_2, gap 5; unpack the singleton coefficient/exponent pair. -/
theorem gap5 (C n : ℝ) (h : (C, n) = (Real.sqrt 2, 1 / 2)) :
    Asymptotics.IsEquivalent (nhdsWithin 1 (Set.Iio 1))
      target (fun x => C * Real.rpow (1 / (1 - x)) n) := by
  have hC : C = Real.sqrt 2 := congrArg Prod.fst h
  have hn : n = (1 / 2 : ℝ) := congrArg Prod.snd h
  subst C
  subst n
  have hg :
      ∀ᶠ x in nhdsWithin (1 : ℝ) (Set.Iio 1),
        Real.sqrt 2 * Real.rpow (1 / (1 - x)) (1 / 2) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    apply mul_ne_zero
    · exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    · exact ne_of_gt
        (Real.rpow_pos_of_pos (one_div_pos.2 (sub_pos.2 hx)) _)
  apply equivalent_of_ratio_limit hg
  refine gap3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hrpow :
      Real.rpow (1 / (1 - x)) (1 / 2) =
        1 / Real.sqrt (1 - x) := by
    change (1 / (1 - x)) ^ (1 / 2 : ℝ) = 1 / Real.sqrt (1 - x)
    calc
      (1 / (1 - x)) ^ (1 / 2 : ℝ) =
          Real.sqrt (1 / (1 - x)) := (Real.sqrt_eq_rpow _).symm
      _ = 1 / Real.sqrt (1 - x) := by
        rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
        norm_num
  change target x / model x =
    target x / (Real.sqrt 2 * Real.rpow (1 / (1 - x)) (1 / 2))
  unfold model
  rw [hrpow]

end

end ProofGap.Exercise658_2
