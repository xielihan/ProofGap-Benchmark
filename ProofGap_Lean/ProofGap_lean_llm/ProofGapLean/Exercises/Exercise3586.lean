import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3586

noncomputable section

def sqrtOnePlus (t : ℝ) : ℝ :=
  Real.sqrt (1 + t)

def binomialTruncation3 (t : ℝ) : ℝ :=
  1 + (1 / 2 : ℝ) * t +
    (((1 / 2 : ℝ) * ((1 / 2 : ℝ) - 1)) / 2) * t ^ 2 +
    (((1 / 2 : ℝ) * ((1 / 2 : ℝ) - 1) * ((1 / 2 : ℝ) - 2)) / 6) *
      t ^ 3

def cubicApproximation (t : ℝ) : ℝ :=
  1 + (1 / 2 : ℝ) * t - (1 / 8 : ℝ) * t ^ 2 +
    (1 / 16 : ℝ) * t ^ 3

def AgreesToThirdOrder (g p : ℝ → ℝ) : Prop :=
  Asymptotics.IsLittleO (nhds 0)
    (fun t => g t - p t)
    (fun t : ℝ => t ^ 3)

def diskFunction (q : ℝ × ℝ) : ℝ :=
  Real.sqrt (1 - q.1 ^ 2 - q.2 ^ 2)

def radialQuartic (q : ℝ × ℝ) : ℝ :=
  1 - (1 / 2 : ℝ) * (q.1 ^ 2 + q.2 ^ 2) -
    (1 / 8 : ℝ) * (q.1 ^ 2 + q.2 ^ 2) ^ 2

def AgreesToFourthOrder (g p : (ℝ × ℝ) → ℝ) : Prop :=
  Asymptotics.IsLittleO (nhds (0, 0))
    (fun q => g q - p q)
    (fun q => ‖q‖ ^ 4)

private theorem sqrtOnePlus_cubic_error :
    Asymptotics.IsLittleO (nhds 0)
      (fun t => sqrtOnePlus t - cubicApproximation t)
      (fun t : ℝ => t ^ 3) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  change ∀ᶠ t in nhds 0,
    ‖sqrtOnePlus t - cubicApproximation t‖ ≤ c * ‖t ^ 3‖
  let δ : ℝ := min (1 / 2) (c / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℝ) hδ) ?_
  intro t ht
  have htδ : |t| < δ := by
    simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using ht
  have hδ_left : δ ≤ (1 / 2 : ℝ) := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_right : δ ≤ c / 2 := by
    dsimp [δ]
    exact min_le_right _ _
  have ht_half : |t| < (1 / 2 : ℝ) := lt_of_lt_of_le htδ hδ_left
  have ht_c : |t| < c := by
    have ht_right : |t| < c / 2 := lt_of_lt_of_le htδ hδ_right
    nlinarith
  have hrad : 0 ≤ 1 + t := by
    nlinarith [neg_abs_le t]
  let s : ℝ := Real.sqrt (1 + t)
  let u : ℝ := s - 1
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 1 + t := by
    dsimp [s]
    exact Real.sq_sqrt hrad
  have ht_factor : t = u * (s + 1) := by
    dsimp [u]
    nlinarith [hs_sq]
  have hsplus : 1 ≤ s + 1 := by
    linarith
  have hsplus0 : 0 ≤ s + 1 := by
    linarith
  have habs_factor : |t| = |u| * (s + 1) := by
    calc
      |t| = |u * (s + 1)| := congrArg abs ht_factor
      _ = |u| * |s + 1| := by rw [abs_mul]
      _ = |u| * (s + 1) := by rw [abs_of_nonneg hsplus0]
  have hu_le : |u| ≤ |t| := by
    calc
      |u| = |u| * 1 := by ring
      _ ≤ |u| * (s + 1) :=
        mul_le_mul_of_nonneg_left hsplus (abs_nonneg u)
      _ = |t| := habs_factor.symm
  have hu_half : |u| < (1 / 2 : ℝ) := lt_of_le_of_lt hu_le ht_half
  have hu_lower : -(1 / 2 : ℝ) < u := by
    nlinarith [neg_abs_le u]
  have hu_upper : u < (1 / 2 : ℝ) := by
    nlinarith [le_abs_self u]
  have hfactor :
      s - (1 + (1 / 2 : ℝ) * t - (1 / 8 : ℝ) * t ^ 2 +
        (1 / 16 : ℝ) * t ^ 3) =
        -(u ^ 4 * (10 + 6 * u + u ^ 2) / 16) := by
    rw [ht_factor]
    dsimp [u]
    ring
  have hprod :
      0 ≤ ((1 / 2 : ℝ) - u) * ((1 / 2 : ℝ) + u) := by
    exact mul_nonneg (by linarith) (by linarith)
  have hu_sq : u ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith [hprod]
  have hcoeff0 : 0 ≤ 10 + 6 * u + u ^ 2 := by
    nlinarith [sq_nonneg u]
  have hcoeff16 : 10 + 6 * u + u ^ 2 ≤ 16 := by
    nlinarith [hu_sq]
  have hrem_abs :
      |s - (1 + (1 / 2 : ℝ) * t - (1 / 8 : ℝ) * t ^ 2 +
        (1 / 16 : ℝ) * t ^ 3)| =
        |u| ^ 4 * (10 + 6 * u + u ^ 2) / 16 := by
    rw [hfactor, abs_neg, abs_div, abs_mul, abs_pow,
      abs_of_nonneg hcoeff0]
    norm_num
  have hbound :
      |s - (1 + (1 / 2 : ℝ) * t - (1 / 8 : ℝ) * t ^ 2 +
        (1 / 16 : ℝ) * t ^ 3)| ≤ c * |t ^ 3| := by
    calc
      |s - (1 + (1 / 2 : ℝ) * t - (1 / 8 : ℝ) * t ^ 2 +
        (1 / 16 : ℝ) * t ^ 3)| =
          |u| ^ 4 * (10 + 6 * u + u ^ 2) / 16 := hrem_abs
      _ ≤ |u| ^ 4 := by
        have hm := mul_le_mul_of_nonneg_left hcoeff16
          (pow_nonneg (abs_nonneg u) 4)
        nlinarith [hm]
      _ ≤ |t| ^ 4 := by
        gcongr
      _ = |t| * |t ^ 3| := by
        rw [abs_pow]
        ring
      _ ≤ c * |t ^ 3| :=
        mul_le_mul_of_nonneg_right (le_of_lt ht_c) (abs_nonneg (t ^ 3))
  simpa only [sqrtOnePlus, cubicApproximation, Real.norm_eq_abs, s] using hbound

private theorem sqrtOnePlus_quadratic_bound
    (a : ℝ) (ha0 : 0 ≤ a) (ha_small : a ≤ (1 / 8 : ℝ)) :
    |sqrtOnePlus (-a) -
      (1 - (1 / 2 : ℝ) * a - (1 / 8 : ℝ) * a ^ 2)| ≤ a ^ 3 := by
  have hrad : 0 ≤ 1 - a := by
    nlinarith
  let s : ℝ := Real.sqrt (1 - a)
  let u : ℝ := s - 1
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 1 - a := by
    dsimp [s]
    exact Real.sq_sqrt hrad
  have ht_factor : -a = u * (s + 1) := by
    dsimp [u]
    nlinarith [hs_sq]
  have hsplus : 1 ≤ s + 1 := by
    linarith
  have hsplus0 : 0 ≤ s + 1 := by
    linarith
  have habs_factor : a = |u| * (s + 1) := by
    calc
      a = |-a| := by rw [abs_neg, abs_of_nonneg ha0]
      _ = |u * (s + 1)| := congrArg abs ht_factor
      _ = |u| * |s + 1| := by rw [abs_mul]
      _ = |u| * (s + 1) := by rw [abs_of_nonneg hsplus0]
  have hu_le : |u| ≤ a := by
    calc
      |u| = |u| * 1 := by ring
      _ ≤ |u| * (s + 1) :=
        mul_le_mul_of_nonneg_left hsplus (abs_nonneg u)
      _ = a := habs_factor.symm
  have ha_factor : a = -(u * (s + 1)) := by
    nlinarith [ht_factor]
  have hfactor :
      s - (1 - (1 / 2 : ℝ) * a - (1 / 8 : ℝ) * a ^ 2) =
        u ^ 3 * (4 + u) / 8 := by
    rw [ha_factor]
    dsimp [u]
    ring
  have hcoeff0 : 0 ≤ 4 + u := by
    nlinarith [neg_abs_le u]
  have hcoeff8 : 4 + u ≤ 8 := by
    nlinarith [le_abs_self u]
  have hrem_abs :
      |s - (1 - (1 / 2 : ℝ) * a - (1 / 8 : ℝ) * a ^ 2)| =
        |u| ^ 3 * (4 + u) / 8 := by
    rw [hfactor, abs_div, abs_mul, abs_pow,
      abs_of_nonneg hcoeff0]
    norm_num
  have hbound :
      |s - (1 - (1 / 2 : ℝ) * a - (1 / 8 : ℝ) * a ^ 2)| ≤ a ^ 3 := by
    calc
      |s - (1 - (1 / 2 : ℝ) * a - (1 / 8 : ℝ) * a ^ 2)| =
          |u| ^ 3 * (4 + u) / 8 := hrem_abs
      _ ≤ |u| ^ 3 := by
        have hm := mul_le_mul_of_nonneg_left hcoeff8
          (pow_nonneg (abs_nonneg u) 3)
        nlinarith [hm]
      _ ≤ a ^ 3 := by
        gcongr
  simpa [sqrtOnePlus, s, sub_eq_add_neg] using hbound

private theorem pair_sq_le_two_norm_sq (q : ℝ × ℝ) :
    q.1 ^ 2 + q.2 ^ 2 ≤ 2 * ‖q‖ ^ 2 := by
  have hx_norm : ‖q.1‖ ≤ ‖q‖ := by
    change ‖q.1‖ ≤ max ‖q.1‖ ‖q.2‖
    exact le_max_left _ _
  have hy_norm : ‖q.2‖ ≤ ‖q‖ := by
    change ‖q.2‖ ≤ max ‖q.1‖ ‖q.2‖
    exact le_max_right _ _
  have hx : |q.1| ≤ ‖q‖ := by
    simpa [Real.norm_eq_abs] using hx_norm
  have hy : |q.2| ≤ ‖q‖ := by
    simpa [Real.norm_eq_abs] using hy_norm
  have hx2 : q.1 ^ 2 ≤ ‖q‖ ^ 2 := by
    rcases abs_le.mp hx with ⟨hxl, hxu⟩
    have hp : 0 ≤ (‖q‖ - q.1) * (‖q‖ + q.1) := by
      exact mul_nonneg (by linarith) (by linarith)
    nlinarith [hp]
  have hy2 : q.2 ^ 2 ≤ ‖q‖ ^ 2 := by
    rcases abs_le.mp hy with ⟨hyl, hyu⟩
    have hp : 0 ≤ (‖q‖ - q.2) * (‖q‖ + q.2) := by
      exact mul_nonneg (by linarith) (by linarith)
    nlinarith [hp]
  nlinarith [hx2, hy2]

private theorem radial_pointwise_sixth_order_bound
    (q : ℝ × ℝ) (hq : ‖q‖ ≤ (1 / 4 : ℝ)) :
    |sqrtOnePlus (-(q.1 ^ 2 + q.2 ^ 2)) - radialQuartic q| ≤
      8 * ‖q‖ ^ 6 := by
  let R : ℝ := ‖q‖
  let a : ℝ := q.1 ^ 2 + q.2 ^ 2
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact norm_nonneg _
  have hRquarter : R ≤ (1 / 4 : ℝ) := by
    simpa [R] using hq
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have haR : a ≤ 2 * R ^ 2 := by
    simpa [a, R] using pair_sq_le_two_norm_sq q
  have hR2quarter : R ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
    have hp :
        0 ≤ ((1 / 4 : ℝ) - R) * ((1 / 4 : ℝ) + R) := by
      exact mul_nonneg (by linarith) (by linarith)
    nlinarith [hp]
  have ha_small : a ≤ (1 / 8 : ℝ) := by
    nlinarith [haR, hR2quarter]
  have hbase :
      |sqrtOnePlus (-a) -
        (1 - (1 / 2 : ℝ) * a - (1 / 8 : ℝ) * a ^ 2)| ≤ a ^ 3 :=
    sqrtOnePlus_quadratic_bound a ha0 ha_small
  have hbound :
      |sqrtOnePlus (-(q.1 ^ 2 + q.2 ^ 2)) - radialQuartic q| ≤
        8 * R ^ 6 := by
    calc
      |sqrtOnePlus (-(q.1 ^ 2 + q.2 ^ 2)) - radialQuartic q| =
          |sqrtOnePlus (-a) -
            (1 - (1 / 2 : ℝ) * a - (1 / 8 : ℝ) * a ^ 2)| := by
              simp [radialQuartic, a]
      _ ≤ a ^ 3 := hbase
      _ ≤ (2 * R ^ 2) ^ 3 := by
        gcongr
      _ = 8 * R ^ 6 := by ring
  simpa [R] using hbound

private theorem radial_fourth_order_estimate :
    Asymptotics.IsLittleO (nhds ((0, 0) : ℝ × ℝ))
      (fun q => sqrtOnePlus (-(q.1 ^ 2 + q.2 ^ 2)) - radialQuartic q)
      (fun q : ℝ × ℝ => ‖q‖ ^ 4) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  change ∀ᶠ q in nhds ((0, 0) : ℝ × ℝ),
    ‖sqrtOnePlus (-(q.1 ^ 2 + q.2 ^ 2)) - radialQuartic q‖ ≤
      c * ‖(‖q‖ ^ 4 : ℝ)‖
  let δ : ℝ := min (1 / 4) (c / 8)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  refine Filter.mem_of_superset
    (Metric.ball_mem_nhds ((0, 0) : ℝ × ℝ) hδ) ?_
  intro q hq
  have hqdist : dist q ((0, 0) : ℝ × ℝ) < δ :=
    Metric.mem_ball.mp hq
  have hzero : ((0, 0) : ℝ × ℝ) = 0 := rfl
  rw [hzero, dist_zero_right] at hqdist
  let R : ℝ := ‖q‖
  have hRδ : R < δ := by
    simpa [R] using hqdist
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact norm_nonneg _
  have hδ_left : δ ≤ (1 / 4 : ℝ) := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_right : δ ≤ c / 8 := by
    dsimp [δ]
    exact min_le_right _ _
  have hRquarter : R < (1 / 4 : ℝ) :=
    lt_of_lt_of_le hRδ hδ_left
  have hR_c : 8 * R < c := by
    have hRright : R < c / 8 := lt_of_lt_of_le hRδ hδ_right
    nlinarith
  have hpoint :
      |sqrtOnePlus (-(q.1 ^ 2 + q.2 ^ 2)) - radialQuartic q| ≤
        8 * R ^ 6 := by
    simpa [R] using
      (radial_pointwise_sixth_order_bound q (le_of_lt hRquarter))
  have hRle1 : R ≤ 1 := by
    linarith
  have hR2leR : R ^ 2 ≤ R := by
    calc
      R ^ 2 = R * R := pow_two R
      _ ≤ R * 1 := mul_le_mul_of_nonneg_left hRle1 hR0
      _ = R := mul_one R
  have h8R2 : 8 * R ^ 2 ≤ c := by
    calc
      8 * R ^ 2 ≤ 8 * R :=
        mul_le_mul_of_nonneg_left hR2leR (by norm_num)
      _ ≤ c := le_of_lt hR_c
  have hcompare : 8 * R ^ 6 ≤ c * R ^ 4 := by
    have hm := mul_le_mul_of_nonneg_right h8R2
      (pow_nonneg hR0 4)
    calc
      8 * R ^ 6 = (8 * R ^ 2) * R ^ 4 := by ring
      _ ≤ c * R ^ 4 := hm
  have hbound :
      |sqrtOnePlus (-(q.1 ^ 2 + q.2 ^ 2)) - radialQuartic q| ≤
        c * R ^ 4 :=
    hpoint.trans hcompare
  simpa [Real.norm_eq_abs, R,
    abs_of_nonneg (pow_nonneg (norm_nonneg q) 4)] using hbound

theorem gap1 :
    AgreesToThirdOrder sqrtOnePlus binomialTruncation3 := by
  have hp : binomialTruncation3 = cubicApproximation := by
    funext t
    unfold binomialTruncation3 cubicApproximation
    ring
  unfold AgreesToThirdOrder
  rw [hp]
  exact sqrtOnePlus_cubic_error

theorem gap2 :
    AgreesToThirdOrder sqrtOnePlus cubicApproximation := by
  unfold AgreesToThirdOrder
  exact sqrtOnePlus_cubic_error

theorem gap3 :
    ∀ x y : ℝ, diskFunction (x, y) =
      Real.sqrt (1 - x ^ 2 - y ^ 2) := by
  intro x y
  rfl

theorem gap4 :
    ∀ x y : ℝ,
      Real.sqrt (1 - x ^ 2 - y ^ 2) =
        sqrtOnePlus (-(x ^ 2 + y ^ 2)) := by
  intro x y
  unfold sqrtOnePlus
  congr 1
  ring

theorem gap5 :
    AgreesToFourthOrder
      (fun q => sqrtOnePlus (-(q.1 ^ 2 + q.2 ^ 2)))
      radialQuartic := by
  unfold AgreesToFourthOrder
  exact radial_fourth_order_estimate

theorem gap6 :
    AgreesToFourthOrder diskFunction radialQuartic := by
  have hfun : diskFunction =
      (fun q : ℝ × ℝ => sqrtOnePlus (-(q.1 ^ 2 + q.2 ^ 2))) := by
    funext q
    calc
      diskFunction q = Real.sqrt (1 - q.1 ^ 2 - q.2 ^ 2) := by
        simpa using gap3 q.1 q.2
      _ = sqrtOnePlus (-(q.1 ^ 2 + q.2 ^ 2)) := gap4 q.1 q.2
  rw [hfun]
  exact gap5

end

end ProofGap.Exercise3586
