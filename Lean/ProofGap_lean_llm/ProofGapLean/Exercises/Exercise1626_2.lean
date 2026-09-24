import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise1626_2

noncomputable section

def f (x : ℝ) := Real.tan x - x
def Approx (actual expected tolerance : ℝ) : Prop :=
  |actual - expected| < tolerance
def approximant : ℕ → ℝ
  | 1 => 7.7325
  | 2 => 7.7258
  | 3 => 7.7254
  | _ => 0
def SecondRoot (ξ : ℝ) : Prop :=
  ξ ∈ Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32) ∧ f ξ = 0
def ApproxRoot (sample tolerance : ℝ) : Prop :=
  ∃ ξ, SecondRoot ξ ∧ |sample - ξ| < tolerance

private lemma cos_ne_interval (x : ℝ)
    (hx : x ∈ Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32)) :
    Real.cos x ≠ 0 := by
  let y := x - 2 * Real.pi
  have hy0 : 0 < y := by
    dsimp [y]
    nlinarith [hx.1, Real.pi_pos]
  have hypi2 : y < Real.pi / 2 := by
    dsimp [y]
    nlinarith [hx.2, Real.pi_pos]
  have hcy : 0 < Real.cos y :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hypi2⟩
  have heq : Real.cos x = Real.cos y := by
    rw [show x = y + 2 * Real.pi by simp [y], Real.cos_add_two_pi]
  rw [heq]
  exact hcy.ne'

private lemma cos_ne_closed_interval (x : ℝ)
    (hx : x ∈ Set.Icc (39 * Real.pi / 16) (79 * Real.pi / 32)) :
    Real.cos x ≠ 0 := by
  let y := x - 2 * Real.pi
  have hy0 : 0 < y := by
    dsimp [y]
    nlinarith [hx.1, Real.pi_pos]
  have hypi2 : y < Real.pi / 2 := by
    dsimp [y]
    nlinarith [hx.2, Real.pi_pos]
  have hcy : 0 < Real.cos y :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hypi2⟩
  have heq : Real.cos x = Real.cos y := by
    rw [show x = y + 2 * Real.pi by simp [y], Real.cos_add_two_pi]
  rw [heq]
  exact hcy.ne'

private lemma tan_pos_interval (x : ℝ)
    (hx : x ∈ Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32)) :
    0 < Real.tan x := by
  let y := x - 2 * Real.pi
  have hy0 : 0 < y := by
    dsimp [y]
    nlinarith [hx.1, Real.pi_pos]
  have hypi2 : y < Real.pi / 2 := by
    dsimp [y]
    nlinarith [hx.2, Real.pi_pos]
  have hsy : 0 < Real.sin y :=
    Real.sin_pos_of_pos_of_lt_pi hy0 (lt_trans hypi2 (by nlinarith [Real.pi_pos]))
  have hcy : 0 < Real.cos y :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hypi2⟩
  rw [show x = y + 2 * Real.pi by simp [y], Real.tan_eq_sin_div_cos,
    Real.sin_add_two_pi, Real.cos_add_two_pi]
  positivity

private lemma tan_hasDerivAt (x : ℝ) (hx : Real.cos x ≠ 0) :
    HasDerivAt Real.tan (1 / (Real.cos x) ^ 2) x := by
  rw [show Real.tan = fun y => Real.sin y / Real.cos y by
    funext y; exact Real.tan_eq_sin_div_cos y]
  convert (Real.hasDerivAt_sin x).div (Real.hasDerivAt_cos x) hx using 1
  field_simp [hx]
  nlinarith [Real.sin_sq_add_cos_sq x]

private lemma deriv_f_eq_tan_sq (x : ℝ)
    (hx : x ∈ Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32)) :
    deriv f x = (Real.tan x) ^ 2 := by
  unfold f
  have hc := cos_ne_interval x hx
  have h := (tan_hasDerivAt x hc).sub (hasDerivAt_id x)
  calc
    deriv (fun y => Real.tan y - y) x = 1 / (Real.cos x) ^ 2 - 1 := by
      simpa [Pi.sub_apply, id] using h.deriv
    _ = (Real.tan x) ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp [hc]
      nlinarith [Real.sin_sq_add_cos_sq x]

private lemma sin_taylor_bound (x : ℝ) (hx : 0 < x) :
    |Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120)| ≤ x ^ 6 / 720 := by
  rcases taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.sin) (n := 5) hx Real.contDiff_sin.contDiffOn with
    ⟨c, hc, hrem⟩
  have hpoly :
      taylorWithinEval Real.sin 5 (Set.Icc 0 x) 0 x =
        x - x ^ 3 / 6 + x ^ 5 / 120 := by
    rw [taylor_within_apply]
    have h0 : (0 : ℝ) ∈ Set.Icc 0 x := ⟨le_rfl, hx.le⟩
    simp_rw [Real.iteratedDerivWithin_sin_Icc _ hx h0]
    norm_num [Finset.sum_range_succ, Real.iteratedDeriv_odd_sin]
    ring
  rw [hpoly] at hrem
  rw [hrem, abs_div, abs_mul]
  norm_num [sub_zero]
  have hcder : |Real.sin c| ≤ 1 := Real.abs_sin_le_one c
  rw [abs_of_pos hx]
  nlinarith [mul_le_mul_of_nonneg_right hcder (pow_nonneg hx.le 6)]

private lemma cos_taylor_bound (x : ℝ) (hx : 0 < x) :
    |Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)| ≤ x ^ 5 / 120 := by
  rcases taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.cos) (n := 4) hx Real.contDiff_cos.contDiffOn with
    ⟨c, hc, hrem⟩
  have hpoly :
      taylorWithinEval Real.cos 4 (Set.Icc 0 x) 0 x =
        1 - x ^ 2 / 2 + x ^ 4 / 24 := by
    rw [taylor_within_apply]
    have h0 : (0 : ℝ) ∈ Set.Icc 0 x := ⟨le_rfl, hx.le⟩
    simp_rw [Real.iteratedDerivWithin_cos_Icc _ hx h0]
    norm_num [Finset.sum_range_succ, Real.iteratedDeriv_odd_cos]
    ring
  rw [hpoly] at hrem
  rw [hrem, abs_div, abs_mul]
  norm_num [sub_zero]
  have hcder : |Real.sin c| ≤ 1 := Real.abs_sin_le_one c
  rw [abs_of_pos hx]
  nlinarith [mul_le_mul_of_nonneg_right hcder (pow_nonneg hx.le 5)]

private lemma tan_left_lt_six :
    Real.tan (39 * Real.pi / 16) < 6 := by
  rw [show 39 * Real.pi / 16 =
      ((Real.pi / 2 - Real.pi / 16) + Real.pi) + Real.pi by ring,
    Real.tan_add_pi, Real.tan_add_pi, Real.tan_pi_div_two_sub,
    Real.tan_eq_sin_div_cos, inv_div]
  have hz0 : 0 < Real.pi / 16 := by positivity
  have hz1 : Real.pi / 16 ≤ 1 := by nlinarith [Real.pi_lt_four]
  have hs := Real.sin_gt_sub_cube hz0 hz1
  have hp3 : Real.pi ^ 3 < (4 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ Real.pi_lt_four Real.pi_pos.le (by norm_num)
  have hs16 : 1 / 6 < Real.sin (Real.pi / 16) := by
    norm_num at hp3
    nlinarith [Real.pi_gt_three]
  have hcos := Real.cos_le_one (Real.pi / 16)
  have hsin0 : 0 < Real.sin (Real.pi / 16) := lt_trans (by norm_num) hs16
  apply (div_lt_iff₀ hsin0).2
  nlinarith

theorem gap1 : f (39 * Real.pi / 16) < 0 := by
  unfold f
  have hp := Real.pi_gt_three
  nlinarith [tan_left_lt_six]

private lemma tan_right_gt_eight :
    8 < Real.tan (79 * Real.pi / 32) := by
  rw [show 79 * Real.pi / 32 =
      ((Real.pi / 2 - Real.pi / 32) + Real.pi) + Real.pi by ring,
    Real.tan_add_pi, Real.tan_add_pi, Real.tan_pi_div_two_sub]
  have hz0 : 0 < Real.pi / 32 := by positivity
  have hz01 : Real.pi / 32 < 1 / 10 := by
    nlinarith [Real.pi_lt_d2]
  have hsin : Real.sin (Real.pi / 32) < 1 / 10 :=
    (Real.sin_lt hz0).trans hz01
  have hcoslb := Real.one_sub_sq_div_two_lt_cos
    (show Real.pi / 32 ≠ 0 by positivity)
  have hcos : 4 / 5 < Real.cos (Real.pi / 32) := by
    nlinarith [sq_nonneg (Real.pi / 32 - 1 / 10)]
  have htan0 : 0 < Real.tan (Real.pi / 32) := by
    rw [Real.tan_eq_sin_div_cos]
    have hs0 := Real.sin_pos_of_pos_of_lt_pi hz0
      (by nlinarith [Real.pi_pos])
    positivity
  have htan : Real.tan (Real.pi / 32) < 1 / 8 := by
    rw [Real.tan_eq_sin_div_cos]
    apply (div_lt_iff₀ (lt_trans (by norm_num) hcos)).2
    nlinarith
  rw [inv_eq_one_div]
  exact (lt_div_iff₀ htan0).2 (by nlinarith)
theorem gap2 : f (79 * Real.pi / 32) > 0 := by
  unfold f
  have hp := Real.pi_lt_d2
  nlinarith [tan_right_gt_eight]
theorem gap3 : ∃! ξ : ℝ, SecondRoot ξ := by
  let a := 39 * Real.pi / 16
  let b := 79 * Real.pi / 32
  have hab : a < b := by
    dsimp [a, b]
    nlinarith [Real.pi_pos]
  have hcont : ContinuousOn f (Set.Icc a b) := by
    unfold f
    apply ContinuousOn.sub
    · exact Real.continuousOn_tan.mono (by
        intro x hx
        exact cos_ne_closed_interval x hx)
    · exact continuousOn_id
  have hz : (0 : ℝ) ∈ Set.Icc (f a) (f b) := by
    dsimp [a, b]
    exact ⟨gap1.le, gap2.le⟩
  rcases intermediate_value_Icc hab.le hcont hz with ⟨ξ, hξ, hroot⟩
  have haξ : a < ξ := lt_of_le_of_ne hξ.1 (by
    intro ha
    subst ξ
    dsimp [a] at hroot
    linarith [gap1])
  have hξb : ξ < b := lt_of_le_of_ne hξ.2 (by
    intro hb
    subst ξ
    dsimp [b] at hroot
    linarith [gap2])
  have hmono : StrictMonoOn f (Set.Ioo a b) :=
    strictMonoOn_of_deriv_pos (convex_Ioo a b)
      (hcont.mono Set.Ioo_subset_Icc_self)
      (fun x hx => by
        have hx' : x ∈ Set.Ioo
            (39 * Real.pi / 16) (79 * Real.pi / 32) := by
          simpa [a, b] using interior_subset hx
        rw [deriv_f_eq_tan_sq x hx']
        exact sq_pos_of_pos (tan_pos_interval x hx'))
  refine ⟨ξ, ⟨⟨by simpa [a] using haξ, by simpa [b] using hξb⟩, hroot⟩, ?_⟩
  intro y hy
  have hy' : y ∈ Set.Ioo a b ∧ f y = 0 := by
    simpa [SecondRoot, a, b] using hy
  exact (hmono.injOn ⟨haξ, hξb⟩ hy'.1 (hroot.trans hy'.2.symm)).symm
theorem gap4 (x : ℝ)
    (hx : x ∈ Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32)) :
    deriv f x > 0 := by
  rw [deriv_f_eq_tan_sq x hx]
  exact sq_pos_of_pos (tan_pos_interval x hx)
theorem gap5 (x : ℝ)
    (hx : x ∈ Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32)) :
    deriv (deriv f) x > 0 := by
  have hlocal : deriv f =ᶠ[nhds x] fun y => (Real.tan y) ^ 2 := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact deriv_f_eq_tan_sq y hy
  rw [hlocal.deriv_eq]
  have hc := cos_ne_interval x hx
  have h := (tan_hasDerivAt x hc).pow 2
  have hd :
      deriv (fun y => (Real.tan y) ^ 2) x =
        2 * Real.tan x * (1 / (Real.cos x) ^ 2) := by
    convert h.deriv using 1 <;> ring
  rw [hd]
  have ht := tan_pos_interval x hx
  have hc2 : 0 < (Real.cos x) ^ 2 := sq_pos_of_ne_zero hc
  positivity
theorem gap6 : approximant 1 = 7.7325 := by rfl
theorem gap7 : approximant 2 = 7.7258 := by rfl
theorem gap8 : approximant 3 = 7.7254 := by rfl
set_option maxHeartbeats 2000000 in
private lemma gap9_certificate :
    Approx |f 7.7254| 0.0089 (1 / 10000) := by
  set_option maxHeartbeats 800000 in
    unfold Approx f
    let δ : ℝ := 5 * Real.pi / 2 - 7.7254
    have hδlo : (0.128581 : ℝ) < δ := by
      dsimp [δ]
      nlinarith [Real.pi_gt_d20]
    have hδhi : δ < (0.128582 : ℝ) := by
      dsimp [δ]
      nlinarith [Real.pi_lt_d20]
    have hδ0 : 0 < δ := lt_trans (by norm_num) hδlo
    have hδpi : δ < Real.pi := by
      nlinarith [hδhi, Real.pi_gt_three]
    have hs0 : 0 < Real.sin δ :=
      Real.sin_pos_of_pos_of_lt_pi hδ0 hδpi
    have hsin := sin_taylor_bound δ hδ0
    have hcos := cos_taylor_bound δ hδ0
    rw [abs_le] at hsin hcos
    have hlo (n : ℕ) (hn : n ≠ 0) :
        (0.128581 : ℝ) ^ n < δ ^ n :=
      pow_lt_pow_left₀ hδlo (by norm_num) hn
    have hhi (n : ℕ) (hn : n ≠ 0) :
        δ ^ n < (0.128582 : ℝ) ^ n :=
      pow_lt_pow_left₀ hδhi hδ0.le hn
    have hlo2 := hlo 2 (by norm_num)
    have hlo3 := hlo 3 (by norm_num)
    have hlo4 := hlo 4 (by norm_num)
    have hlo5 := hlo 5 (by norm_num)
    have hlo6 := hlo 6 (by norm_num)
    have hhi2 := hhi 2 (by norm_num)
    have hhi3 := hhi 3 (by norm_num)
    have hhi4 := hhi 4 (by norm_num)
    have hhi5 := hhi 5 (by norm_num)
    have hhi6 := hhi 6 (by norm_num)
    norm_num at hlo2 hlo3 hlo4 hlo5 hlo6 hhi2 hhi3 hhi4 hhi5 hhi6
    have hpolylo :
        (7.7342 : ℝ) *
            (δ - δ ^ 3 / 6 + δ ^ 5 / 120 + δ ^ 6 / 720) <
          1 - δ ^ 2 / 2 + δ ^ 4 / 24 - δ ^ 5 / 120 := by
      nlinarith
    have hpolyhi :
        1 - δ ^ 2 / 2 + δ ^ 4 / 24 + δ ^ 5 / 120 <
          (7.7344 : ℝ) *
            (δ - δ ^ 3 / 6 + δ ^ 5 / 120 - δ ^ 6 / 720) := by
      nlinarith
    have hsupper :
        Real.sin δ ≤ δ - δ ^ 3 / 6 + δ ^ 5 / 120 + δ ^ 6 / 720 := by
      linarith [hsin.2]
    have hslower :
        δ - δ ^ 3 / 6 + δ ^ 5 / 120 - δ ^ 6 / 720 ≤ Real.sin δ := by
      linarith [hsin.1]
    have hcupper :
        Real.cos δ ≤ 1 - δ ^ 2 / 2 + δ ^ 4 / 24 + δ ^ 5 / 120 := by
      linarith [hcos.2]
    have hclower :
        1 - δ ^ 2 / 2 + δ ^ 4 / 24 - δ ^ 5 / 120 ≤ Real.cos δ := by
      linarith [hcos.1]
    have hcotlo : (7.7342 : ℝ) < Real.cos δ / Real.sin δ := by
      rw [lt_div_iff₀ hs0]
      nlinarith
    have hcothi : Real.cos δ / Real.sin δ < (7.7344 : ℝ) := by
      rw [div_lt_iff₀ hs0]
      nlinarith
    have htan :
        Real.tan (7.7254 : ℝ) = Real.cos δ / Real.sin δ := by
      rw [show (7.7254 : ℝ) =
          ((Real.pi / 2 - δ) + Real.pi) + Real.pi by
        dsimp [δ]; ring,
        Real.tan_add_pi, Real.tan_add_pi, Real.tan_pi_div_two_sub,
        Real.tan_eq_sin_div_cos, inv_div]
    rw [htan]
    have hfpos : 0 < Real.cos δ / Real.sin δ - 7.7254 := by linarith
    rw [abs_of_pos hfpos, abs_lt]
    constructor <;> norm_num <;> linarith
theorem gap9 : Approx |f 7.7254| 0.0089 (1 / 10000) := by
  exact gap9_certificate
theorem gap10 :
    ∃ m : ℝ, m =
      sInf
        ((fun x : ℝ => |deriv f x|) ''
          Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32)) := by
  exact ⟨_, rfl⟩
theorem gap11 :
    sInf
        ((fun x : ℝ => |deriv f x|) ''
          Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32)) =
      (Real.tan (39 * Real.pi / 16)) ^ 2 := by
  let a : ℝ := 39 * Real.pi / 16
  let b : ℝ := 79 * Real.pi / 32
  let S : Set ℝ := (fun x : ℝ => |deriv f x|) '' Set.Ioo a b
  let L : ℝ := (Real.tan a) ^ 2
  have hab : a < b := by
    dsimp [a, b]
    nlinarith [Real.pi_pos]
  have hne : S.Nonempty := by
    let x := (a + b) / 2
    have hx : x ∈ Set.Ioo a b := by
      dsimp [x]
      constructor <;> linarith
    exact ⟨|deriv f x|, ⟨x, hx, rfl⟩⟩
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact abs_nonneg _
  have hlower : ∀ z ∈ S, L ≤ z := by
    rintro z ⟨x, hx, rfl⟩
    have hx' : x ∈ Set.Ioo
        (39 * Real.pi / 16) (79 * Real.pi / 32) := by
      simpa [a, b] using hx
    change L ≤ |deriv f x|
    rw [abs_of_pos (gap4 x hx'), deriv_f_eq_tan_sq x hx']
    let y := x - 2 * Real.pi
    have hy0 : 0 < y := by
      dsimp [y, a] at hx ⊢
      nlinarith [hx.1, Real.pi_pos]
    have hy2 : y < Real.pi / 2 := by
      dsimp [y, b] at hx ⊢
      nlinarith [hx.2, Real.pi_pos]
    have hybase : 7 * Real.pi / 16 < y := by
      dsimp [y, a] at hx ⊢
      nlinarith [hx.1, Real.pi_pos]
    have htan :
        Real.tan (7 * Real.pi / 16) < Real.tan y :=
      Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two
        (by positivity) hy2 hybase
    have ht0 : 0 < Real.tan (7 * Real.pi / 16) := by
      rw [Real.tan_eq_sin_div_cos]
      have hs : 0 < Real.sin (7 * Real.pi / 16) :=
        Real.sin_pos_of_pos_of_lt_pi (by positivity)
          (by nlinarith [Real.pi_pos])
      have hc : 0 < Real.cos (7 * Real.pi / 16) :=
        Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos],
          by nlinarith [Real.pi_pos]⟩
      positivity
    have hsq :
        (Real.tan (7 * Real.pi / 16)) ^ 2 <
          (Real.tan y) ^ 2 :=
      pow_lt_pow_left₀ htan ht0.le (by norm_num)
    have hta : Real.tan a = Real.tan (7 * Real.pi / 16) := by
      rw [show a = (7 * Real.pi / 16 + Real.pi) + Real.pi by
        dsimp [a]; ring, Real.tan_add_pi, Real.tan_add_pi]
    have htx : Real.tan x = Real.tan y := by
      rw [show x = y + Real.pi + Real.pi by simp [y]; ring,
        Real.tan_add_pi, Real.tan_add_pi]
    dsimp [L]
    rw [hta, htx]
    exact hsq.le
  have hminor : L ≤ sInf S := le_csInf hne hlower
  have hmajor : sInf S ≤ L := by
    by_contra hn
    have has : L < sInf S := lt_of_not_ge hn
    have hca : Real.cos a ≠ 0 := by
      apply cos_ne_closed_interval a
      simpa [a, b] using (show a ∈ Set.Icc a b from ⟨le_rfl, hab.le⟩)
    have hcont : ContinuousAt (fun x : ℝ => (Real.tan x) ^ 2) a :=
      (Real.continuousAt_tan.mpr hca).pow 2
    obtain ⟨δ, hδ, hclose⟩ :=
      (Metric.continuousAt_iff.mp hcont) (sInf S - L) (sub_pos.mpr has)
    let d : ℝ := min δ (b - a)
    have hd : 0 < d := lt_min hδ (sub_pos.mpr hab)
    let x : ℝ := a + d / 2
    have hx : x ∈ Set.Ioo a b := by
      dsimp [x]
      have hdb := min_le_right δ (b - a)
      constructor <;> nlinarith
    have hdist : dist x a < δ := by
      rw [Real.dist_eq]
      dsimp [x]
      rw [abs_of_nonneg (by linarith : 0 ≤ a + d / 2 - a)]
      have hdδ := min_le_left δ (b - a)
      nlinarith
    have hnear := hclose hdist
    have hx' : x ∈ Set.Ioo
        (39 * Real.pi / 16) (79 * Real.pi / 32) := by
      simpa [a, b] using hx
    have hmem : (Real.tan x) ^ 2 ∈ S := by
      refine ⟨x, hx, ?_⟩
      change |deriv f x| = (Real.tan x) ^ 2
      rw [abs_of_pos (gap4 x hx'), deriv_f_eq_tan_sq x hx']
    have hinf : sInf S ≤ (Real.tan x) ^ 2 := csInf_le hbdd hmem
    rw [Real.dist_eq] at hnear
    dsimp [L] at has hnear hinf ⊢
    rw [abs_lt] at hnear
    linarith
  change sInf S = L
  exact le_antisymm hmajor hminor
theorem gap12 : (Real.tan (39 * Real.pi / 16)) ^ 2 > 25 := by
  rw [show 39 * Real.pi / 16 =
      ((Real.pi / 2 - Real.pi / 16) + Real.pi) + Real.pi by ring,
    Real.tan_add_pi, Real.tan_add_pi, Real.tan_pi_div_two_sub,
    Real.tan_eq_sin_div_cos, Real.sin_pi_div_sixteen,
    Real.cos_pi_div_sixteen]
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2lt : Real.sqrt 2 < 2 := by nlinarith
  have hi : 24 / 13 < Real.sqrt (2 + Real.sqrt 2) := by
    have hbase : 0 ≤ 2 + Real.sqrt 2 := by positivity
    have hisq := Real.sq_sqrt hbase
    have hi0 : 0 ≤ Real.sqrt (2 + Real.sqrt 2) := Real.sqrt_nonneg _
    have hs2lb : 238 / 169 < Real.sqrt 2 := by nlinarith
    by_contra h
    have hle : Real.sqrt (2 + Real.sqrt 2) ≤ 24 / 13 := le_of_not_gt h
    have hmul1 := mul_le_mul_of_nonneg_left hle hi0
    have hmul2 := mul_le_mul_of_nonneg_right hle (by norm_num : (0 : ℝ) ≤ 24 / 13)
    nlinarith
  have hinnerlt : Real.sqrt (2 + Real.sqrt 2) < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    nlinarith
  have hsin : 0 < Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
    rw [Real.sqrt_pos]
    exact sub_pos.mpr hinnerlt
  have hcos : 0 < Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
    positivity
  field_simp
  nlinarith [Real.sq_sqrt (show 0 ≤ 2 + Real.sqrt (2 + Real.sqrt 2) by positivity),
    Real.sq_sqrt (show 0 ≤ 2 - Real.sqrt (2 + Real.sqrt 2) by
      exact (sub_pos.mpr hinnerlt).le)]
theorem gap13 :
    ∃ m : ℝ, m =
      sInf
        ((fun x : ℝ => |deriv f x|) ''
          Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32)) ∧
      m > 25 := by
  refine ⟨_, rfl, ?_⟩
  rw [gap11]
  exact gap12
theorem gap14 :
    ∃ ξ, SecondRoot ξ ∧
      |approximant 3 - ξ| ≤
        |f 7.7254| /
          sInf
            ((fun x : ℝ => |deriv f x|) ''
              Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32)) := by
  rcases gap3 with ⟨ξ, hξ, huniq⟩
  refine ⟨ξ, hξ, ?_⟩
  let S : Set ℝ :=
    (fun x : ℝ => |deriv f x|) ''
      Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32)
  let m : ℝ := sInf S
  have hmpos : 0 < m := by
    dsimp [m, S]
    rw [gap11]
    linarith [gap12]
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact abs_nonneg _
  have hm (x : ℝ)
      (hx : x ∈ Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32)) :
      m ≤ |deriv f x| := by
    exact csInf_le hbdd ⟨x, hx, rfl⟩
  have hsamp : (7.7254 : ℝ) ∈
      Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32) := by
    constructor
    · nlinarith [Real.pi_lt_d4]
    · nlinarith [Real.pi_gt_d4]
  rw [gap8]
  by_cases heq : (7.7254 : ℝ) = ξ
  · subst ξ
    have hnonneg : 0 ≤ |f 7.7254| / m :=
      div_nonneg (abs_nonneg _) hmpos.le
    simpa [m, S] using hnonneg
  rcases lt_or_gt_of_ne heq with hlt | hgt
  · have hcont : ContinuousOn f (Set.Icc (7.7254 : ℝ) ξ) := by
      intro x hx
      have hxI : x ∈
          Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32) :=
        ⟨lt_of_lt_of_le hsamp.1 hx.1, lt_of_le_of_lt hx.2 hξ.1.2⟩
      exact ((tan_hasDerivAt x (cos_ne_interval x hxI)).sub
        (hasDerivAt_id x)).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ f (Set.Ioo (7.7254 : ℝ) ξ) := by
      intro x hx
      have hxI : x ∈
          Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32) :=
        ⟨lt_trans hsamp.1 hx.1, lt_trans hx.2 hξ.1.2⟩
      exact ((tan_hasDerivAt x (cos_ne_interval x hxI)).sub
        (hasDerivAt_id x)).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hcder⟩ :=
      exists_deriv_eq_slope (f := f) hlt hcont hdiff
    have hcI : c ∈
        Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32) :=
      ⟨lt_trans hsamp.1 hc.1, lt_trans hc.2 hξ.1.2⟩
    have hmc := hm c hcI
    have hne : ξ - (7.7254 : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
    have he : f ξ - f 7.7254 = deriv f c * (ξ - 7.7254) := by
      rw [hcder]
      field_simp [hne]
    have habs : |f 7.7254| = |deriv f c| * |7.7254 - ξ| := by
      calc
        |f 7.7254| = |f ξ - f 7.7254| := by rw [hξ.2]; simp
        _ = |deriv f c| * |7.7254 - ξ| := by
          rw [he, abs_mul, abs_sub_comm]
    apply (le_div_iff₀ hmpos).2
    calc
      |7.7254 - ξ| * m ≤ |7.7254 - ξ| * |deriv f c| :=
        mul_le_mul_of_nonneg_left hmc (abs_nonneg _)
      _ = |f 7.7254| := by rw [mul_comm, ← habs]
  · have hcont : ContinuousOn f (Set.Icc ξ (7.7254 : ℝ)) := by
      intro x hx
      have hxI : x ∈
          Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32) :=
        ⟨lt_of_lt_of_le hξ.1.1 hx.1, lt_of_le_of_lt hx.2 hsamp.2⟩
      exact ((tan_hasDerivAt x (cos_ne_interval x hxI)).sub
        (hasDerivAt_id x)).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ f (Set.Ioo ξ (7.7254 : ℝ)) := by
      intro x hx
      have hxI : x ∈
          Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32) :=
        ⟨lt_trans hξ.1.1 hx.1, lt_trans hx.2 hsamp.2⟩
      exact ((tan_hasDerivAt x (cos_ne_interval x hxI)).sub
        (hasDerivAt_id x)).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hcder⟩ :=
      exists_deriv_eq_slope (f := f) hgt hcont hdiff
    have hcI : c ∈
        Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32) :=
      ⟨lt_trans hξ.1.1 hc.1, lt_trans hc.2 hsamp.2⟩
    have hmc := hm c hcI
    have hne : (7.7254 : ℝ) - ξ ≠ 0 := ne_of_gt (sub_pos.mpr hgt)
    have he : f 7.7254 - f ξ = deriv f c * (7.7254 - ξ) := by
      rw [hcder]
      field_simp [hne]
    have habs : |f 7.7254| = |deriv f c| * |7.7254 - ξ| := by
      calc
        |f 7.7254| = |f 7.7254 - f ξ| := by rw [hξ.2, sub_zero]
        _ = |deriv f c| * |7.7254 - ξ| := by rw [he, abs_mul]
    apply (le_div_iff₀ hmpos).2
    calc
      |7.7254 - ξ| * m ≤ |7.7254 - ξ| * |deriv f c| :=
        mul_le_mul_of_nonneg_left hmc (abs_nonneg _)
      _ = |f 7.7254| := by rw [mul_comm, ← habs]
theorem gap15 : |f 7.7254| / 25 < 0.001 := by
  have h := gap9
  rw [Approx, abs_lt] at h
  norm_num at h ⊢
  linarith
theorem gap16 : ApproxRoot (approximant 3) 0.001 := by
  rcases gap14 with ⟨ξ, hξ, hbound⟩
  refine ⟨ξ, hξ, ?_⟩
  let m : ℝ :=
    sInf
      ((fun x : ℝ => |deriv f x|) ''
        Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32))
  have hm : 25 < m := by
    dsimp [m]
    rw [gap11]
    exact gap12
  have hm0 : 0 < m := lt_trans (by norm_num) hm
  have hcomp : |f 7.7254| / m ≤ |f 7.7254| / 25 := by
    apply (div_le_iff₀ hm0).2
    have hn := abs_nonneg (f 7.7254)
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hm.le)]
  have hfine : |f 7.7254| / 25 < 0.0004 := by
    have h := gap9
    rw [Approx, abs_lt] at h
    norm_num at h ⊢
    linarith
  exact lt_of_le_of_lt hbound
    (lt_of_le_of_lt hcomp (lt_trans hfine (by norm_num)))
theorem gap17 : ApproxRoot 7.725 0.001 := by
  rcases gap14 with ⟨ξ, hξ, hbound⟩
  refine ⟨ξ, hξ, ?_⟩
  let m : ℝ :=
    sInf
      ((fun x : ℝ => |deriv f x|) ''
        Set.Ioo (39 * Real.pi / 16) (79 * Real.pi / 32))
  have hm : 25 < m := by
    dsimp [m]
    rw [gap11]
    exact gap12
  have hm0 : 0 < m := lt_trans (by norm_num) hm
  have hcomp : |f 7.7254| / m ≤ |f 7.7254| / 25 := by
    apply (div_le_iff₀ hm0).2
    have hn := abs_nonneg (f 7.7254)
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hm.le)]
  have hfine : |f 7.7254| / 25 < 0.0004 := by
    have h := gap9
    rw [Approx, abs_lt] at h
    norm_num at h ⊢
    linarith
  rw [gap8] at hbound
  have hroot : |7.7254 - ξ| < 0.0004 :=
    lt_of_le_of_lt hbound (lt_of_le_of_lt hcomp hfine)
  rw [show (7.725 : ℝ) - ξ =
      (7.725 - 7.7254) + (7.7254 - ξ) by ring]
  refine lt_of_le_of_lt (abs_add_le _ _) ?_
  norm_num
  linarith

end
end ProofGap.Exercise1626_2
