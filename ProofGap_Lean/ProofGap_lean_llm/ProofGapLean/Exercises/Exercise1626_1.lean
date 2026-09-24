import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise1626_1

noncomputable section

def f (x : ℝ) := Real.tan x - x
def sec (x : ℝ) := 1 / Real.cos x
def Approx (actual expected tolerance : ℝ) : Prop :=
  |actual - expected| < tolerance
def approximant : ℕ → ℝ
  | 1 => 4.4959
  | 2 => 4.4933
  | _ => 0
def FirstRoot (ξ : ℝ) : Prop :=
  ξ ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16) ∧ f ξ = 0
def ApproxRoot (sample tolerance : ℝ) : Prop :=
  ∃ ξ, FirstRoot ξ ∧ |sample - ξ| < tolerance

private lemma cos_ne_interval (x : ℝ)
    (hx : x ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16)) :
    Real.cos x ≠ 0 := by
  let y := x - Real.pi
  have hy0 : 0 < y := by dsimp [y]; nlinarith [hx.1, Real.pi_pos]
  have hypi2 : y < Real.pi / 2 := by dsimp [y]; nlinarith [hx.2, Real.pi_pos]
  have hcy : 0 < Real.cos y :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hypi2⟩
  have heq : Real.cos x = -Real.cos y := by
    rw [show x = y + Real.pi by simp [y], Real.cos_add_pi]
  rw [heq]
  exact neg_ne_zero.mpr hcy.ne'

private lemma tan_pos_interval (x : ℝ)
    (hx : x ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16)) :
    0 < Real.tan x := by
  let y := x - Real.pi
  have hy0 : 0 < y := by dsimp [y]; nlinarith [hx.1, Real.pi_pos]
  have hypi2 : y < Real.pi / 2 := by dsimp [y]; nlinarith [hx.2, Real.pi_pos]
  have hsy : 0 < Real.sin y :=
    Real.sin_pos_of_pos_of_lt_pi hy0 (lt_trans hypi2 (by nlinarith [Real.pi_pos]))
  have hcy : 0 < Real.cos y :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hypi2⟩
  rw [show x = y + Real.pi by simp [y], Real.tan_add_pi]
  rw [Real.tan_eq_sin_div_cos]
  positivity

private lemma tan_hasDerivAt (x : ℝ) (hx : Real.cos x ≠ 0) :
    HasDerivAt Real.tan (1 / (Real.cos x) ^ 2) x := by
  rw [show Real.tan = fun y => Real.sin y / Real.cos y by
    funext y; exact Real.tan_eq_sin_div_cos y]
  convert (Real.hasDerivAt_sin x).div (Real.hasDerivAt_cos x) hx using 1
  field_simp [hx]
  nlinarith [Real.sin_sq_add_cos_sq x]

private lemma sin_poly_bound (t : ℝ) (ht : |t| ≤ 1) :
    |Real.sin t -
        (t - t^3 / 6 + t^5 / 120 - t^7 / 5040 + t^9 / 362880 - t^11 / 39916800)| ≤
      |t|^12 * 3 := by
  let z : ℂ := Complex.I * t
  have hz : ‖z‖ = |t| := by simp [z, Real.norm_eq_abs]
  have hexp : Real.exp ‖z‖ < 3 := by
    calc
      Real.exp ‖z‖ = Real.exp |t| := by rw [hz]
      _ ≤ Real.exp 1 := Real.exp_monotone ht
      _ < 3 := Real.exp_one_lt_three
  have hexp_eq : Complex.exp z = Real.cos t + Real.sin t * Complex.I := by
    rw [show z = (t : ℂ) * Complex.I by simp [z, mul_comm], Complex.exp_mul_I]
    simp
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp z 12
  have him := Complex.abs_im_le_norm
    (Complex.exp z - ∑ m ∈ Finset.range 12, z ^ m / m.factorial)
  have hle :
      |(Complex.exp z - ∑ m ∈ Finset.range 12, z ^ m / m.factorial).im| ≤
        ‖z‖ ^ 12 * Real.exp ‖z‖ := him.trans h
  calc
    |Real.sin t -
        (t - t^3 / 6 + t^5 / 120 - t^7 / 5040 + t^9 / 362880 - t^11 / 39916800)|
        = |(Complex.exp z - ∑ m ∈ Finset.range 12, z ^ m / m.factorial).im| := by
          rw [hexp_eq]
          norm_num [z, Finset.sum_range_succ, pow_succ]
          simp only [Complex.sin_ofReal_re]
          ring
    _ ≤ ‖z‖ ^ 12 * Real.exp ‖z‖ := hle
    _ ≤ |t| ^ 12 * 3 := by
      rw [hz] at hexp ⊢
      gcongr

private lemma cos_poly_bound (t : ℝ) (ht : |t| ≤ 1) :
    |Real.cos t -
        (1 - t^2 / 2 + t^4 / 24 - t^6 / 720 + t^8 / 40320 - t^10 / 3628800)| ≤
      |t|^12 * 3 := by
  let z : ℂ := Complex.I * t
  have hz : ‖z‖ = |t| := by simp [z, Real.norm_eq_abs]
  have hexp : Real.exp ‖z‖ < 3 := by
    calc
      Real.exp ‖z‖ = Real.exp |t| := by rw [hz]
      _ ≤ Real.exp 1 := Real.exp_monotone ht
      _ < 3 := Real.exp_one_lt_three
  have hexp_eq : Complex.exp z = Real.cos t + Real.sin t * Complex.I := by
    rw [show z = (t : ℂ) * Complex.I by simp [z, mul_comm], Complex.exp_mul_I]
    simp
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp z 12
  have hre := Complex.abs_re_le_norm
    (Complex.exp z - ∑ m ∈ Finset.range 12, z ^ m / m.factorial)
  have hle :
      |(Complex.exp z - ∑ m ∈ Finset.range 12, z ^ m / m.factorial).re| ≤
        ‖z‖ ^ 12 * Real.exp ‖z‖ := hre.trans h
  calc
    |Real.cos t -
        (1 - t^2 / 2 + t^4 / 24 - t^6 / 720 + t^8 / 40320 - t^10 / 3628800)|
        = |(Complex.exp z - ∑ m ∈ Finset.range 12, z ^ m / m.factorial).re| := by
          rw [hexp_eq]
          norm_num [z, Finset.sum_range_succ, pow_succ]
          simp only [Complex.cos_ofReal_re]
          ring
    _ ≤ ‖z‖ ^ 12 * Real.exp ‖z‖ := hle
    _ ≤ |t| ^ 12 * 3 := by
      rw [hz] at hexp ⊢
      gcongr

private lemma sample_cot_bounds :
    let t : ℝ := 3 * Real.pi / 2 - 4.4933
    4.4910 < Real.cos t / Real.sin t ∧ Real.cos t / Real.sin t < 4.4912 := by
  dsimp only
  let t : ℝ := 3 * Real.pi / 2 - 4.4933
  have htL : (0.219088 : ℝ) < t := by
    dsimp [t]
    linarith [Real.pi_gt_d6]
  have htU : t < (0.21909 : ℝ) := by
    dsimp [t]
    linarith [Real.pi_lt_d6]
  have ht0 : 0 ≤ t := by linarith
  have htpos : 0 < t := by linarith
  have ht_abs : |t| ≤ 1 := by rw [abs_of_pos htpos]; linarith
  have hs := sin_poly_bound t ht_abs
  have hc := cos_poly_bound t ht_abs
  rw [abs_le] at hs hc
  rw [abs_of_pos htpos] at hs hc
  have hL (n : ℕ) : (0.219088 : ℝ)^n ≤ t^n :=
    pow_le_pow_left₀ (by norm_num) htL.le n
  have hU (n : ℕ) : t^n ≤ (0.21909 : ℝ)^n :=
    pow_le_pow_left₀ ht0 htU.le n
  have hL2 := hL 2; have hL3 := hL 3; have hL4 := hL 4
  have hL5 := hL 5; have hL6 := hL 6; have hL7 := hL 7
  have hL8 := hL 8; have hL9 := hL 9; have hL10 := hL 10
  have hL11 := hL 11; have hL12 := hL 12
  have hU2 := hU 2; have hU3 := hU 3; have hU4 := hU 4
  have hU5 := hU 5; have hU6 := hU 6; have hU7 := hU 7
  have hU8 := hU 8; have hU9 := hU 9; have hU10 := hU 10
  have hU11 := hU 11; have hU12 := hU 12
  norm_num at hL2 hL3 hL4 hL5 hL6 hL7 hL8 hL9 hL10 hL11 hL12
  norm_num at hU2 hU3 hU4 hU5 hU6 hU7 hU8 hU9 hU10 hU11 hU12
  have hsL : (0.217339 : ℝ) < Real.sin t := by linarith
  have hsU : Real.sin t < (0.217342 : ℝ) := by linarith
  have hcL : (0.9760955 : ℝ) < Real.cos t := by linarith
  have hcU : Real.cos t < (0.9760962 : ℝ) := by linarith
  change 4.4910 < Real.cos t / Real.sin t ∧ Real.cos t / Real.sin t < 4.4912
  constructor
  · rw [lt_div_iff₀ (lt_trans (by norm_num) hsL)]
    calc
      4.4910 * Real.sin t < 4.4910 * 0.217342 :=
        mul_lt_mul_of_pos_left hsU (by norm_num)
      _ < 0.9760955 := by norm_num
      _ < Real.cos t := hcL
  · rw [div_lt_iff₀ (lt_trans (by norm_num) hsL)]
    calc
      Real.cos t < 0.9760962 := hcU
      _ < 4.4912 * 0.217339 := by norm_num
      _ < 4.4912 * Real.sin t := mul_lt_mul_of_pos_left hsL (by norm_num)

private lemma tan_sample_bounds :
    4.4910 < Real.tan 4.4933 ∧ Real.tan 4.4933 < 4.4912 := by
  have h := sample_cot_bounds
  let t : ℝ := 3 * Real.pi / 2 - 4.4933
  change 4.4910 < Real.cos t / Real.sin t ∧ Real.cos t / Real.sin t < 4.4912 at h
  rw [show (4.4933 : ℝ) = Real.pi / 2 - t + Real.pi by simp [t]; ring,
    Real.tan_add_pi, Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub]
  exact h

private lemma cos_ne_closed (x : ℝ)
    (hx : x ∈ Set.Icc (4 * Real.pi / 3) (23 * Real.pi / 16)) :
    Real.cos x ≠ 0 := by
  let y := x - Real.pi
  have hy0 : 0 < y := by dsimp [y]; nlinarith [hx.1, Real.pi_pos]
  have hypi2 : y < Real.pi / 2 := by dsimp [y]; nlinarith [hx.2, Real.pi_pos]
  have hcy : 0 < Real.cos y :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hypi2⟩
  have heq : Real.cos x = -Real.cos y := by
    rw [show x = y + Real.pi by simp [y], Real.cos_add_pi]
  rw [heq]
  exact neg_ne_zero.mpr hcy.ne'

private lemma f_continuous_closed :
    ContinuousOn f (Set.Icc (4 * Real.pi / 3) (23 * Real.pi / 16)) := by
  apply ContinuousOn.sub
  · intro x hx
    exact (Real.continuousAt_tan.mpr (cos_ne_closed x hx)).continuousWithinAt
  · fun_prop

private lemma left_f_neg : f (4 * Real.pi / 3) < 0 := by
  rw [f, show 4 * Real.pi / 3 = Real.pi / 3 + Real.pi by ring,
    Real.tan_add_pi, Real.tan_pi_div_three]
  have hsqrt : Real.sqrt 3 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  nlinarith [Real.pi_gt_three]

private lemma right_f_pos : 0 < f (23 * Real.pi / 16) := by
  let t : ℝ := Real.pi / 16
  have ht0 : 0 < t := by dsimp [t]; positivity
  have htpi2 : t < Real.pi / 2 := by dsimp [t]; nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht0 (by nlinarith [Real.pi_pos])
  have hslt : Real.sin t < t := Real.sin_lt ht0
  have hclt : 1 - t^2 / 2 < Real.cos t :=
    Real.one_sub_sq_div_two_lt_cos ht0.ne'
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hrat : (23 * Real.pi / 16) * t < 1 - t^2 / 2 := by
    dsimp [t]
    nlinarith [sq_nonneg (Real.pi - 3.15)]
  have hmul : (23 * Real.pi / 16) * Real.sin t < Real.cos t := by
    calc
      (23 * Real.pi / 16) * Real.sin t < (23 * Real.pi / 16) * t :=
        mul_lt_mul_of_pos_left hslt (by positivity)
      _ < 1 - t^2 / 2 := hrat
      _ < Real.cos t := hclt
  have hcot : 23 * Real.pi / 16 < Real.cos t / Real.sin t := by
    rw [lt_div_iff₀ hsin]
    exact hmul
  rw [f, show 23 * Real.pi / 16 = Real.pi / 2 - t + Real.pi by simp [t]; ring,
    Real.tan_add_pi, Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub]
  rw [show Real.pi / 2 - t + Real.pi = 23 * Real.pi / 16 by simp [t]; ring]
  exact sub_pos.mpr hcot

private lemma tan_left_lt (x : ℝ)
    (hx : x ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16)) :
    Real.tan (4 * Real.pi / 3) < Real.tan x := by
  let y := x - Real.pi
  have hyU : y < Real.pi / 2 := by dsimp [y]; nlinarith [hx.2, Real.pi_pos]
  have hyL : Real.pi / 3 < y := by dsimp [y]; nlinarith [hx.1]
  rw [show 4 * Real.pi / 3 = Real.pi / 3 + Real.pi by ring,
    show x = y + Real.pi by simp [y], Real.tan_add_pi, Real.tan_add_pi]
  exact Real.tan_lt_tan_of_lt_of_lt_pi_div_two
    (by nlinarith [Real.pi_pos]) hyU hyL

private lemma tan_lt_of_mem {x y : ℝ}
    (hx : x ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16))
    (hy : y ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16))
    (hxy : x < y) : Real.tan x < Real.tan y := by
  let u := x - Real.pi
  let v := y - Real.pi
  have huL : -(Real.pi / 2) < u := by dsimp [u]; nlinarith [hx.1, Real.pi_pos]
  have hvU : v < Real.pi / 2 := by dsimp [v]; nlinarith [hy.2, Real.pi_pos]
  have huv : u < v := by dsimp [u, v]; linarith
  rw [show x = u + Real.pi by simp [u], show y = v + Real.pi by simp [v],
    Real.tan_add_pi, Real.tan_add_pi]
  exact Real.tan_lt_tan_of_lt_of_lt_pi_div_two huL hvU huv

private lemma sample_mem_interval :
    (4.4933 : ℝ) ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16) := by
  constructor
  · nlinarith [Real.pi_lt_d6]
  · nlinarith [Real.pi_gt_d6]

theorem gap1 (x : ℝ)
    (hx : x ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16)) :
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
theorem gap2 (x : ℝ)
    (hx : x ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16)) :
    (Real.tan x) ^ 2 > 0 := by
  exact sq_pos_of_pos (tan_pos_interval x hx)
theorem gap3 (x : ℝ)
    (hx : x ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16)) :
    deriv f x > 0 := by rw [gap1 x hx]; exact gap2 x hx

private lemma f_strictMono_closed :
    StrictMonoOn f (Set.Icc (4 * Real.pi / 3) (23 * Real.pi / 16)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) f_continuous_closed
  rw [interior_Icc]
  intro x hx
  exact gap3 x hx
theorem gap4 (x : ℝ)
    (hx : x ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16)) :
    deriv (deriv f) x = 2 * Real.tan x * (sec x) ^ 2 := by
  have hlocal : deriv f =ᶠ[nhds x] fun y => (Real.tan y) ^ 2 := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact gap1 y hy
  rw [hlocal.deriv_eq]
  have hc := cos_ne_interval x hx
  have h := (tan_hasDerivAt x hc).pow 2
  unfold sec
  convert h.deriv using 1 <;> ring
theorem gap5 (x : ℝ)
    (hx : x ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16)) :
    2 * Real.tan x * (sec x) ^ 2 > 0 := by
  have ht := tan_pos_interval x hx
  have hs : 0 < (sec x) ^ 2 := by
    apply sq_pos_of_ne_zero
    unfold sec
    exact one_div_ne_zero (cos_ne_interval x hx)
  positivity
theorem gap6 (x : ℝ)
    (hx : x ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16)) :
    deriv (deriv f) x > 0 := by rw [gap4 x hx]; exact gap5 x hx
theorem gap7 :
    f (4 * Real.pi / 3) * f (23 * Real.pi / 16) < 0 := by
  exact mul_neg_of_neg_of_pos left_f_neg right_f_pos
theorem gap8 : ∃! ξ : ℝ, FirstRoot ξ := by
  let a : ℝ := 4 * Real.pi / 3
  let b : ℝ := 23 * Real.pi / 16
  have hab : a ≤ b := by dsimp [a, b]; nlinarith [Real.pi_pos]
  have hleft : f a < 0 := by simpa [a] using left_f_neg
  have hright : 0 < f b := by simpa [b] using right_f_pos
  have hcont : ContinuousOn f (Set.Icc a b) := by
    simpa [a, b] using f_continuous_closed
  have hz : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨hleft.le, hright.le⟩
  rcases intermediate_value_Icc hab hcont hz with ⟨ξ, hξ, hzero⟩
  have hξopen : ξ ∈ Set.Ioo a b := by
    constructor
    · apply hξ.1.lt_of_ne
      intro heq
      subst ξ
      exact hleft.ne hzero
    · apply hξ.2.lt_of_ne
      intro heq
      subst ξ
      exact hright.ne' hzero
  refine ⟨ξ, ⟨by simpa [a, b] using hξopen, hzero⟩, ?_⟩
  intro y hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm := f_strictMono_closed ⟨hy.1.1.le, hy.1.2.le⟩
      (by simpa [a, b] using ⟨hξopen.1.le, hξopen.2.le⟩) hlt
    rw [hy.2, hzero] at hm
    exact lt_irrefl 0 hm
  · have hm := f_strictMono_closed
      (by simpa [a, b] using ⟨hξopen.1.le, hξopen.2.le⟩)
      ⟨hy.1.1.le, hy.1.2.le⟩ hgt
    rw [hzero, hy.2] at hm
    exact lt_irrefl 0 hm
theorem gap9 : approximant 1 = 4.4959 := by rfl
theorem gap10 : approximant 2 = 4.4933 := by rfl
theorem gap11 : Approx |f 4.4933| 0.0022 (1 / 10000) := by
  have ht := tan_sample_bounds
  have hf : (-0.0023 : ℝ) < f 4.4933 ∧ f 4.4933 < -0.0021 := by
    simp only [f]
    constructor <;> linarith [ht.1, ht.2]
  have hfneg : f 4.4933 < 0 := by linarith
  rw [Approx, abs_of_neg hfneg, abs_lt]
  constructor <;> linarith
theorem gap12 :
    ∃ m : ℝ, m =
      sInf
        ((fun x : ℝ => |deriv f x|) ''
          Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16)) := by
  exact ⟨_, rfl⟩
theorem gap13 :
    sInf
        ((fun x : ℝ => |deriv f x|) ''
          Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16)) =
      (Real.tan (4 * Real.pi / 3)) ^ 2 := by
  let a : ℝ := 4 * Real.pi / 3
  let b : ℝ := 23 * Real.pi / 16
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · let x : ℝ := (a + b) / 2
    have hx : x ∈ Set.Ioo a b := by
      dsimp [x, a, b]
      constructor <;> nlinarith [Real.pi_pos]
    exact ⟨|deriv f x|, ⟨x, hx, rfl⟩⟩
  · intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have htan := tan_left_lt x (by simpa [a, b] using hx)
    have htan0 : 0 ≤ Real.tan a := by
      dsimp [a]
      rw [show 4 * Real.pi / 3 = Real.pi / 3 + Real.pi by ring,
        Real.tan_add_pi, Real.tan_pi_div_three]
      positivity
    change Real.tan (4 * Real.pi / 3) ^ 2 ≤ |deriv f x|
    rw [gap1 x (by simpa [a, b] using hx),
      abs_of_pos (gap2 x (by simpa [a, b] using hx))]
    exact pow_le_pow_left₀ htan0 (by simpa [a] using htan.le) 2
  · intro w hw
    have hca : Real.cos a ≠ 0 := by
      apply cos_ne_closed
      dsimp [a, b]
      constructor
      · rfl
      · nlinarith [Real.pi_pos]
    have hcontg : ContinuousAt (fun x : ℝ => (Real.tan x)^2) a :=
      (Real.continuousAt_tan.mpr hca).pow 2
    have hev : ∀ᶠ x in nhds a, (Real.tan x)^2 < w :=
      hcontg.eventually (Iio_mem_nhds (by simpa [a] using hw))
    rw [Metric.eventually_nhds_iff] at hev
    rcases hev with ⟨ε, hε, hev⟩
    let d : ℝ := min (ε / 2) ((b - a) / 2)
    have hab : a < b := by dsimp [a, b]; nlinarith [Real.pi_pos]
    have hd : 0 < d := by
      dsimp [d]
      exact lt_min (half_pos hε) (half_pos (sub_pos.mpr hab))
    have hdε : d < ε := by
      have := min_le_left (ε / 2) ((b - a) / 2)
      dsimp [d]
      nlinarith
    have hdb : d < b - a := by
      have := min_le_right (ε / 2) ((b - a) / 2)
      dsimp [d]
      nlinarith
    let x : ℝ := a + d
    have hx : x ∈ Set.Ioo a b := by
      dsimp [x]
      constructor
      · linarith [hd]
      · linarith [hdb]
    have hdist : dist x a < ε := by
      rw [Real.dist_eq, abs_of_nonneg]
      · simpa [x] using hdε
      · dsimp [x]
        linarith
    have hgx : (Real.tan x)^2 < w := hev hdist
    refine ⟨|deriv f x|, ⟨x, hx, rfl⟩, ?_⟩
    rw [gap1 x (by simpa [a, b] using hx),
      abs_of_pos (gap2 x (by simpa [a, b] using hx))]
    exact hgx
theorem gap14 : (Real.tan (4 * Real.pi / 3)) ^ 2 = 3 := by
  rw [show 4 * Real.pi / 3 = Real.pi / 3 + Real.pi by ring,
    Real.tan_add_pi, Real.tan_pi_div_three, Real.sq_sqrt]
  norm_num
theorem gap15 : ∃ m : ℝ, m = 3 := by exact ⟨3, rfl⟩

private lemma deriv_ge_three (x : ℝ)
    (hx : x ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16)) :
    3 ≤ deriv f x := by
  rw [gap1 x hx]
  rw [← gap14]
  have htan := tan_left_lt x hx
  have htan0 : 0 ≤ Real.tan (4 * Real.pi / 3) := by
    rw [show 4 * Real.pi / 3 = Real.pi / 3 + Real.pi by ring,
      Real.tan_add_pi, Real.tan_pi_div_three]
    positivity
  exact pow_le_pow_left₀ htan0 htan.le 2
theorem gap16 :
    ∃ ξ, FirstRoot ξ ∧ |approximant 2 - ξ| ≤ |f 4.4933| / 3 := by
  rcases gap8 with ⟨ξ, hξ, hfξ⟩
  refine ⟨ξ, hξ, ?_⟩
  have hfzero : f ξ = 0 := hξ.2
  change |(4.4933 : ℝ) - ξ| ≤ |f 4.4933| / 3
  let s : ℝ := 4.4933
  change |s - ξ| ≤ |f s| / 3
  rcases lt_trichotomy s ξ with hsξ | rfl | hξs
  · have hcont : ContinuousOn f (Set.Icc s ξ) := by
      apply f_continuous_closed.mono
      intro y hy
      exact ⟨sample_mem_interval.1.le.trans hy.1,
        hy.2.trans hξ.1.2.le⟩
    have hdiff : DifferentiableOn ℝ f (Set.Ioo s ξ) := by
      intro y hy
      have hyg : y ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16) :=
        ⟨sample_mem_interval.1.trans hy.1, hy.2.trans hξ.1.2⟩
      exact ((Real.hasDerivAt_tan (cos_ne_closed y ⟨hyg.1.le, hyg.2.le⟩)).sub
        (hasDerivAt_id y)).differentiableAt.differentiableWithinAt
    rcases exists_deriv_eq_slope f hsξ hcont hdiff with ⟨c, hc, hslope⟩
    have hcg : c ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16) :=
      ⟨sample_mem_interval.1.trans hc.1, hc.2.trans hξ.1.2⟩
    have hd := deriv_ge_three c hcg
    have hden : ξ - s ≠ 0 := sub_ne_zero.mpr hsξ.ne'
    rw [eq_div_iff hden] at hslope
    have hfs : f s ≤ 0 := by nlinarith
    have hmul : 3 * (ξ - s) ≤ deriv f c * (ξ - s) :=
      mul_le_mul_of_nonneg_right hd (sub_nonneg.mpr hsξ.le)
    rw [abs_of_nonpos (sub_nonpos.mpr hsξ.le), abs_of_nonpos hfs]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith
  · rw [sub_self, abs_zero]
    apply div_nonneg
    · exact abs_nonneg _
    · norm_num
  · have hcont : ContinuousOn f (Set.Icc ξ s) := by
      apply f_continuous_closed.mono
      intro y hy
      exact ⟨hξ.1.1.le.trans hy.1,
        hy.2.trans sample_mem_interval.2.le⟩
    have hdiff : DifferentiableOn ℝ f (Set.Ioo ξ s) := by
      intro y hy
      have hyg : y ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16) :=
        ⟨hξ.1.1.trans hy.1, hy.2.trans sample_mem_interval.2⟩
      exact ((Real.hasDerivAt_tan (cos_ne_closed y ⟨hyg.1.le, hyg.2.le⟩)).sub
        (hasDerivAt_id y)).differentiableAt.differentiableWithinAt
    rcases exists_deriv_eq_slope f hξs hcont hdiff with ⟨c, hc, hslope⟩
    have hcg : c ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16) :=
      ⟨hξ.1.1.trans hc.1, hc.2.trans sample_mem_interval.2⟩
    have hd := deriv_ge_three c hcg
    have hden : s - ξ ≠ 0 := sub_ne_zero.mpr hξs.ne'
    rw [eq_div_iff hden] at hslope
    have hfs : 0 ≤ f s := by nlinarith
    have hmul : 3 * (s - ξ) ≤ deriv f c * (s - ξ) :=
      mul_le_mul_of_nonneg_right hd (sub_nonneg.mpr hξs.le)
    rw [abs_of_nonneg (sub_nonneg.mpr hξs.le), abs_of_nonneg hfs]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith
theorem gap17 : |f 4.4933| / 3 < 0.001 := by
  have h := gap11
  rw [Approx, abs_lt] at h
  norm_num at h ⊢
  linarith
theorem gap18 : ApproxRoot (approximant 2) 0.001 := by
  rcases gap16 with ⟨ξ, hξ, hbound⟩
  exact ⟨ξ, hξ, lt_of_le_of_lt hbound gap17⟩
theorem gap19 : ApproxRoot 4.493 0.001 := by
  rw [ApproxRoot]
  rcases gap8 with ⟨ξ, hξ, huniq⟩
  refine ⟨ξ, hξ, ?_⟩
  have ht := tan_sample_bounds
  have hf : (-0.0023 : ℝ) < f 4.4933 ∧ f 4.4933 < -0.0021 := by
    simp only [f]
    constructor <;> linarith [ht.1, ht.2]
  let s : ℝ := 4.4933
  have hsmem : s ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16) := by
    simpa [s] using sample_mem_interval
  have hsξ : s < ξ := by
    apply lt_of_not_ge
    intro h
    rcases h.eq_or_lt with heq | hlt
    · subst ξ
      have hz : f (4.4933 : ℝ) = 0 := by simpa [s] using hξ.2
      linarith [hf.2]
    · have hm := f_strictMono_closed
        ⟨hξ.1.1.le, hξ.1.2.le⟩ ⟨hsmem.1.le, hsmem.2.le⟩ hlt
      have hm' : f ξ < f (4.4933 : ℝ) := by simpa [s] using hm
      linarith [hξ.2, hf.2]
  have hcont : ContinuousOn f (Set.Icc s ξ) := by
    apply f_continuous_closed.mono
    intro y hy
    exact ⟨hsmem.1.le.trans hy.1, hy.2.trans hξ.1.2.le⟩
  have hdiff : DifferentiableOn ℝ f (Set.Ioo s ξ) := by
    intro y hy
    have hyg : y ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16) :=
      ⟨hsmem.1.trans hy.1, hy.2.trans hξ.1.2⟩
    exact ((Real.hasDerivAt_tan (cos_ne_closed y ⟨hyg.1.le, hyg.2.le⟩)).sub
      (hasDerivAt_id y)).differentiableAt.differentiableWithinAt
  rcases exists_deriv_eq_slope f hsξ hcont hdiff with ⟨c, hc, hslope⟩
  have hcmem : c ∈ Set.Ioo (4 * Real.pi / 3) (23 * Real.pi / 16) :=
    ⟨hsmem.1.trans hc.1, hc.2.trans hξ.1.2⟩
  have htanc : 4 < Real.tan c := by
    have hsc := tan_lt_of_mem hsmem hcmem hc.1
    have : 4 < Real.tan s := by
      simpa [s] using lt_trans (by norm_num : (4 : ℝ) < 4.4910) ht.1
    linarith
  have hd16 : 16 ≤ deriv f c := by
    rw [gap1 c hcmem]
    nlinarith
  have hden : ξ - s ≠ 0 := sub_ne_zero.mpr hsξ.ne'
  rw [eq_div_iff hden] at hslope
  have hmul : 16 * (ξ - s) ≤ deriv f c * (ξ - s) :=
    mul_le_mul_of_nonneg_right hd16 (sub_nonneg.mpr hsξ.le)
  have hfL : (-0.0023 : ℝ) < f s := by simpa [s] using hf.1
  have hupper : 16 * (ξ - s) < (0.0023 : ℝ) := by
    calc
      16 * (ξ - s) ≤ deriv f c * (ξ - s) := hmul
      _ = -f s := by rw [hslope, hξ.2]; ring
      _ < 0.0023 := by linarith
  have hroot : ξ - s < (0.0023 : ℝ) / 16 := by
    rw [div_eq_mul_inv]
    nlinarith
  rw [abs_of_neg]
  · dsimp [s] at hroot
    norm_num at hroot ⊢
    linarith
  · dsimp [s] at hsξ
    norm_num
    linarith

end
end ProofGap.Exercise1626_1
