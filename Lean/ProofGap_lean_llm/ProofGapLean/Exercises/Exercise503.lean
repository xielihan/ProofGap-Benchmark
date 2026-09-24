import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise503

noncomputable section

def original (x : ℝ) : ℝ :=
  (1 - Real.sqrt (Real.cos x)) / (1 - Real.cos (Real.sqrt x))
def rationalized (x : ℝ) : ℝ :=
  (1 - Real.cos x) /
    (2 * Real.sin (Real.sqrt x / 2) ^ 2 * (1 + Real.sqrt (Real.cos x)))
def normalized (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (Real.sin (x / 2) / (x / 2)) ^ 2 *
    ((Real.sqrt x / 2) / Real.sin (Real.sqrt x / 2)) ^ 2 *
    (x / (1 + Real.sqrt (Real.cos x)))
def HasRightLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds L)

/-- Source: `proof_gap/exercise_503/1.txt`; use a right-hand limit because of `√x`. -/
private theorem one_sub_cos_eq_two_mul_sin_sq (t : ℝ) :
    1 - Real.cos t = 2 * Real.sin (t / 2) ^ 2 := by
  have ht : t / 2 + t / 2 = t := by ring
  calc
    1 - Real.cos t = 1 - Real.cos (t / 2 + t / 2) := by rw [ht]
    _ = 1 - (Real.cos (t / 2) * Real.cos (t / 2) -
        Real.sin (t / 2) * Real.sin (t / 2)) := by
      rw [Real.cos_add]
    _ = 2 * Real.sin (t / 2) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq (t / 2)]

private theorem tendsto_of_eventually_eq
    {f g : ℝ → ℝ} {l : Filter ℝ} {L : ℝ}
    (hfg : f =ᶠ[l] g)
    (hf : Filter.Tendsto f l (nhds L)) :
    Filter.Tendsto g l (nhds L) := by
  rw [Filter.tendsto_def] at hf ⊢
  intro s hs
  filter_upwards [hf s hs, hfg] with x hxs hx
  change f x ∈ s at hxs
  change g x ∈ s
  rw [← hx]
  exact hxs

private theorem tendsto_sin_div_self :
    Filter.Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 ({0}ᶜ)) (nhds 1) := by
  have hs : Filter.Tendsto Real.sinc
      (nhdsWithin 0 ({0}ᶜ)) (nhds 1) := by
    have hc : Filter.Tendsto Real.sinc (nhds 0) (nhds (Real.sinc 0)) :=
      Real.continuous_sinc.continuousAt
    simpa [Real.sinc] using hc.mono_left inf_le_left
  have heq : Real.sinc =ᶠ[nhdsWithin 0 ({0}ᶜ)]
      (fun x : ℝ => Real.sin x / x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    simp [Real.sinc, hx0]
  exact tendsto_of_eventually_eq heq hs

private theorem normalization_algebra
    (x q A B C : ℝ) (hq : q ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hsq : q ^ 2 = x) :
    (2 * A ^ 2) / (2 * B ^ 2 * C) =
      2 * ((1 / 2 : ℝ) * (A / (x / 2)) ^ 2 *
        ((q / 2) / B) ^ 2 * (x / C)) := by
  rw [← hsq]
  field_simp [hq, hB, hC]

private theorem eventually_original_eq_rationalized :
    original =ᶠ[nhdsWithin 0 (Set.Ioi 0)] rationalized := by
  have hsmall :
      ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
        x < min ((2 * Real.pi) ^ 2) (Real.pi / 2) :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (by
        apply lt_min
        · positivity
        · positivity))
  filter_upwards [self_mem_nhdsWithin, hsmall] with x hx hxl
  have hxq : x < (2 * Real.pi) ^ 2 :=
    lt_of_lt_of_le hxl (min_le_left _ _)
  have hxcos : x < Real.pi / 2 :=
    lt_of_lt_of_le hxl (min_le_right _ _)
  have hqpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hqsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
  have hqlt : Real.sqrt x < 2 * Real.pi := by
    nlinarith [Real.sqrt_nonneg x, Real.pi_pos]
  have hzpi : Real.sqrt x / 2 < Real.pi := by
    nlinarith
  have hsin : 0 < Real.sin (Real.sqrt x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) hzpi
  have hcos : 0 < Real.cos x := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_pos]
    · exact hxcos
  have hcos_sq : Real.sqrt (Real.cos x) ^ 2 = Real.cos x :=
    Real.sq_sqrt (le_of_lt hcos)
  have hrat :
      (1 - Real.sqrt (Real.cos x)) * (1 + Real.sqrt (Real.cos x)) =
        1 - Real.cos x := by
    nlinarith
  have hd : 2 * Real.sin (Real.sqrt x / 2) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt hsin))
  have hC : 1 + Real.sqrt (Real.cos x) ≠ 0 := by
    nlinarith [Real.sqrt_nonneg (Real.cos x)]
  unfold original rationalized
  rw [one_sub_cos_eq_two_mul_sin_sq (Real.sqrt x)]
  apply (div_eq_div_iff hd (mul_ne_zero hd hC)).2
  rw [← hrat]
  ring

private theorem eventually_rationalized_eq_two_normalized :
    rationalized =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun x => 2 * normalized x) := by
  have hsmall :
      ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
        x < (2 * Real.pi) ^ 2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by positivity))
  filter_upwards [self_mem_nhdsWithin, hsmall] with x hx hxl
  have hqpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hqsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
  have hqlt : Real.sqrt x < 2 * Real.pi := by
    nlinarith [Real.sqrt_nonneg x, Real.pi_pos]
  have hzpi : Real.sqrt x / 2 < Real.pi := by
    nlinarith
  have hsin : 0 < Real.sin (Real.sqrt x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) hzpi
  have hC : 1 + Real.sqrt (Real.cos x) ≠ 0 := by
    nlinarith [Real.sqrt_nonneg (Real.cos x)]
  unfold rationalized normalized
  rw [one_sub_cos_eq_two_mul_sin_sq x]
  simpa [mul_assoc] using
    normalization_algebra x (Real.sqrt x) (Real.sin (x / 2))
      (Real.sin (Real.sqrt x / 2)) (1 + Real.sqrt (Real.cos x))
      (ne_of_gt hqpos) (ne_of_gt hsin) hC hqsq

private theorem normalized_tendsto_zero :
    HasRightLimitAtZero normalized 0 := by
  unfold HasRightLimitAtZero
  have hid : Filter.Tendsto (fun x : ℝ => x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using (continuous_id.tendsto 0).mono_left inf_le_left
  have hhalf0 : Filter.Tendsto (fun x : ℝ => x / 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hc : Continuous (fun x : ℝ => x / 2) := continuous_id.div_const 2
    simpa using (hc.tendsto 0).mono_left inf_le_left
  have hhalf : Filter.Tendsto (fun x : ℝ => x / 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 ({0}ᶜ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hhalf0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using
      (div_ne_zero (ne_of_gt hx) (by norm_num : (2 : ℝ) ≠ 0))
  have hsinc : Filter.Tendsto
      (fun x : ℝ => Real.sin (x / 2) / (x / 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using tendsto_sin_div_self.comp hhalf
  have hsqrtHalf0 : Filter.Tendsto
      (fun x : ℝ => Real.sqrt x / 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hc : Continuous (fun x : ℝ => Real.sqrt x / 2) :=
      Real.continuous_sqrt.div_const 2
    simpa using (hc.tendsto 0).mono_left inf_le_left
  have hsqrtHalf : Filter.Tendsto
      (fun x : ℝ => Real.sqrt x / 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 ({0}ᶜ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hsqrtHalf0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using
      (div_ne_zero (ne_of_gt (Real.sqrt_pos.2 hx))
        (by norm_num : (2 : ℝ) ≠ 0))
  have hsqrtSinc : Filter.Tendsto
      (fun x : ℝ =>
        Real.sin (Real.sqrt x / 2) / (Real.sqrt x / 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using tendsto_sin_div_self.comp hsqrtHalf
  have hinvSinc : Filter.Tendsto
      (fun x : ℝ =>
        (Real.sqrt x / 2) / Real.sin (Real.sqrt x / 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa [inv_div] using
      hsqrtSinc.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hsqrtCos : Filter.Tendsto
      (fun x : ℝ => Real.sqrt (Real.cos x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hc : Continuous (fun x : ℝ => Real.sqrt (Real.cos x)) :=
      Real.continuous_sqrt.comp Real.continuous_cos
    simpa using (hc.tendsto 0).mono_left inf_le_left
  have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := tendsto_const_nhds
  have hden : Filter.Tendsto
      (fun x : ℝ => 1 + Real.sqrt (Real.cos x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 2) := by
    convert hone.add hsqrtCos using 1 <;> norm_num
  have hlast : Filter.Tendsto
      (fun x : ℝ => x / (1 + Real.sqrt (Real.cos x)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hid.div hden (by norm_num : (2 : ℝ) ≠ 0)
  have hconst : Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  unfold normalized
  convert (((hconst.mul (hsinc.pow 2)).mul (hinvSinc.pow 2)).mul hlast) using 1 <;>
    norm_num

private theorem rationalized_tendsto_zero :
    HasRightLimitAtZero rationalized 0 := by
  unfold HasRightLimitAtZero
  have hn : Filter.Tendsto normalized
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := normalized_tendsto_zero
  have hconst : Filter.Tendsto (fun _ : ℝ => (2 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 2) := tendsto_const_nhds
  have htwo : Filter.Tendsto (fun x : ℝ => 2 * normalized x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hconst.mul hn
  exact tendsto_of_eventually_eq
    eventually_rationalized_eq_two_normalized.symm htwo

private theorem original_tendsto_zero :
    HasRightLimitAtZero original 0 := by
  unfold HasRightLimitAtZero
  have hr : Filter.Tendsto rationalized
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := rationalized_tendsto_zero
  exact tendsto_of_eventually_eq
    eventually_original_eq_rationalized.symm hr

theorem gap1 (L : ℝ) :
    HasRightLimitAtZero original L ↔ HasRightLimitAtZero rationalized L := by
  unfold HasRightLimitAtZero
  constructor
  · intro h
    exact tendsto_of_eventually_eq eventually_original_eq_rationalized h
  · intro h
    exact tendsto_of_eventually_eq eventually_original_eq_rationalized.symm h

/-- Source: `proof_gap/exercise_503/2.txt`; use a right-hand limit because of `√x`. -/
theorem gap2 (L : ℝ) :
    HasRightLimitAtZero original L ↔ HasRightLimitAtZero normalized L := by
  constructor
  · intro h
    have hL : L = 0 := tendsto_nhds_unique h original_tendsto_zero
    subst L
    exact normalized_tendsto_zero
  · intro h
    have hL : L = 0 := tendsto_nhds_unique h normalized_tendsto_zero
    subst L
    exact original_tendsto_zero

/-- Source: `proof_gap/exercise_503/3.txt`; use a right-hand limit because of `√x`. -/
theorem gap3 : HasRightLimitAtZero normalized 0 := by
  exact normalized_tendsto_zero

/-- Source: `proof_gap/exercise_503/4.txt`; use a right-hand limit because of `√x`. -/
theorem gap4 : HasRightLimitAtZero original 0 := by
  exact original_tendsto_zero

end

end ProofGap.Exercise503
