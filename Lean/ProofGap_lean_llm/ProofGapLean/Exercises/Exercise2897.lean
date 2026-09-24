import ProofGapLean.Prelude.Analysis
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2897

noncomputable section

open Filter
open scoped ENNReal Topology

def nthRootAbs (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.rpow |a n| (1 / (n : ℝ))

def SeriesConvergesAt (a : ℕ → ℝ) (x : ℝ) : Prop :=
  Summable (fun n : ℕ => a n * x ^ n)

def IsConvergenceRadius (a : ℕ → ℝ) (R : ℝ≥0∞) : Prop :=
  (∀ x : ℝ, ENNReal.ofReal |x| < R → SeriesConvergesAt a x) ∧
    (∀ x : ℝ, R < ENNReal.ofReal |x| → ¬ SeriesConvergesAt a x)

private theorem radius_lower_bound
    {c : ℕ → ℝ} {S R : ℝ≥0∞}
    (hS : ∀ x : ℝ, ENNReal.ofReal |x| < S → SeriesConvergesAt c x)
    (hR : IsConvergenceRadius c R) : S ≤ R := by
  by_contra h
  have hRS : R < S := lt_of_not_ge h
  obtain ⟨T, hRT, hTS⟩ := exists_between hRS
  have hTtop : T ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hTS le_top)
  let x : ℝ := T.toReal
  have hx : ENNReal.ofReal |x| = T := by
    simp [x, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hTtop]
  exact (hR.2 x (by simpa [hx] using hRT))
    (hS x (by simpa [hx] using hTS))

private theorem sum_radius_lower_bound
    (a b A : ℕ → ℝ) (R₁ R₂ Rₐ : ℝ≥0∞)
    (ha : IsConvergenceRadius a R₁)
    (hb : IsConvergenceRadius b R₂)
    (hA : ∀ n, A n = a n + b n)
    (hRA : IsConvergenceRadius A Rₐ) :
    min R₁ R₂ ≤ Rₐ := by
  refine radius_lower_bound (c := A) ?_ hRA
  intro x hx
  have hx1 : ENNReal.ofReal |x| < R₁ :=
    lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : ENNReal.ofReal |x| < R₂ :=
    lt_of_lt_of_le hx (min_le_right _ _)
  unfold SeriesConvergesAt at ⊢
  simpa only [hA, add_mul] using
    (ha.1 x hx1).add (hb.1 x hx2)

private theorem series_mul_factor
    (a b B : ℕ → ℝ) (hB : ∀ n, B n = a n * b n)
    {x y q : ℝ} (hq : |q| < 1)
    (hx : SeriesConvergesAt a x)
    (hy : SeriesConvergesAt b y) :
    SeriesConvergesAt B (q * (x * y)) := by
  unfold SeriesConvergesAt at hx hy ⊢
  have hax0 : Tendsto (fun n : ℕ => a n * x ^ n) atTop (𝓝 0) :=
    hx.tendsto_atTop_zero
  have hby0 : Tendsto (fun n : ℕ => b n * y ^ n) atTop (𝓝 0) :=
    hy.tendsto_atTop_zero
  have hax : ∀ᶠ n : ℕ in atTop, ‖a n * x ^ n‖ < 1 := by
    have h := hax0.eventually
      (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
    simpa only [Metric.mem_ball, dist_zero_right] using h
  have hby : ∀ᶠ n : ℕ in atTop, ‖b n * y ^ n‖ < 1 := by
    have h := hby0.eventually
      (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
    simpa only [Metric.mem_ball, dist_zero_right] using h
  have hgeomAbs : Summable (fun n : ℕ => |q| ^ n) :=
    summable_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs] using hq)
  have hgeom : Summable (fun n : ℕ => ‖q ^ n‖) := by
    simpa only [Real.norm_eq_abs, abs_pow] using hgeomAbs
  refine hgeom.of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hax, hby] with n han hbn
  calc
    ‖B n * (q * (x * y)) ^ n‖ =
        ‖a n * x ^ n‖ * ‖b n * y ^ n‖ * ‖q ^ n‖ := by
      rw [hB n]
      simp only [mul_pow, norm_mul]
      ring
    _ ≤ ‖q ^ n‖ := by
      have hab : ‖a n * x ^ n‖ * ‖b n * y ^ n‖ ≤ 1 * 1 :=
        mul_le_mul (le_of_lt han) (le_of_lt hbn) (norm_nonneg _) (by norm_num)
      simpa using mul_le_mul_of_nonneg_right hab (norm_nonneg (q ^ n))

private theorem finite_product_converges
    (a b B : ℕ → ℝ) (R₁ R₂ : ℝ≥0∞)
    (ha : IsConvergenceRadius a R₁)
    (hb : IsConvergenceRadius b R₂)
    (hB : ∀ n, B n = a n * b n)
    (hR₁0 : R₁ ≠ 0) (hR₂0 : R₂ ≠ 0)
    (hR₁top : R₁ ≠ ⊤) (hR₂top : R₂ ≠ ⊤) :
    ∀ z : ℝ, ENNReal.ofReal |z| < R₁ * R₂ →
      SeriesConvergesAt B z := by
  intro z hz
  have hr₁pos : 0 < R₁.toReal := ENNReal.toReal_pos hR₁0 hR₁top
  have hr₂pos : 0 < R₂.toReal := ENNReal.toReal_pos hR₂0 hR₂top
  have hzreal : |z| < R₁.toReal * R₂.toReal := by
    rw [← ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top hR₁top hR₂top)] at hz
    simpa using hz
  let x : ℝ := (|z| / R₂.toReal + R₁.toReal) / 2
  have hlow : |z| / R₂.toReal < R₁.toReal :=
    (div_lt_iff₀ hr₂pos).2 (by simpa [mul_comm] using hzreal)
  have hxpos : 0 < x := by
    dsimp [x]
    have hznonneg := abs_nonneg z
    positivity
  have hxl : |z| / R₂.toReal < x := by
    dsimp [x]
    linarith
  have hxr₁ : x < R₁.toReal := by
    dsimp [x]
    linarith
  have hxR : ENNReal.ofReal |x| < R₁ := by
    rw [← ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hR₁top]
    rw [ENNReal.toReal_ofReal (abs_nonneg x)]
    simpa [abs_of_pos hxpos] using hxr₁
  have hzxr₂ : |z| / x < R₂.toReal := by
    apply (div_lt_iff₀ hxpos).2
    have h := (div_lt_iff₀ hr₂pos).1 hxl
    simpa [mul_comm] using h
  let y : ℝ := (|z| / x + R₂.toReal) / 2
  have hypos : 0 < y := by
    dsimp [y]
    positivity
  have hyl : |z| / x < y := by
    dsimp [y]
    linarith
  have hyr₂ : y < R₂.toReal := by
    dsimp [y]
    linarith
  have hyR : ENNReal.ofReal |y| < R₂ := by
    rw [← ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hR₂top]
    rw [ENNReal.toReal_ofReal (abs_nonneg y)]
    simpa [abs_of_pos hypos] using hyr₂
  have hzxy : |z| < x * y := by
    simpa [mul_comm] using (div_lt_iff₀ hxpos).1 hyl
  let q : ℝ := z / (x * y)
  have hq : |q| < 1 := by
    dsimp [q]
    rw [abs_div, abs_of_pos (mul_pos hxpos hypos)]
    exact (div_lt_one (mul_pos hxpos hypos)).2 hzxy
  have hs := series_mul_factor a b B hB hq (ha.1 x hxR) (hb.1 y hyR)
  have hfactor : q * (x * y) = z := by
    dsimp [q]
    field_simp [ne_of_gt (mul_pos hxpos hypos)]
  simpa only [hfactor] using hs

private theorem entire_left_product
    (a b B : ℕ → ℝ) (R₂ : ℝ≥0∞)
    (ha : IsConvergenceRadius a ⊤)
    (hb : IsConvergenceRadius b R₂)
    (hB : ∀ n, B n = a n * b n)
    (hR₂0 : R₂ ≠ 0) (hR₂top : R₂ ≠ ⊤) :
    ∀ z : ℝ, ENNReal.ofReal |z| < (⊤ : ℝ≥0∞) →
      SeriesConvergesAt B z := by
  intro z hz
  have hr₂pos : 0 < R₂.toReal := ENNReal.toReal_pos hR₂0 hR₂top
  let y : ℝ := R₂.toReal / 2
  have hypos : 0 < y := by dsimp [y]; positivity
  have hyr₂ : y < R₂.toReal := by dsimp [y]; linarith
  have hyR : ENNReal.ofReal |y| < R₂ := by
    rw [← ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hR₂top]
    rw [ENNReal.toReal_ofReal (abs_nonneg y)]
    simpa [abs_of_pos hypos] using hyr₂
  let x : ℝ := |z| / y + 1
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hzxy : |z| < x * y := by
    apply (div_lt_iff₀ hypos).1
    dsimp [x]
    linarith
  let q : ℝ := z / (x * y)
  have hq : |q| < 1 := by
    dsimp [q]
    rw [abs_div, abs_of_pos (mul_pos hxpos hypos)]
    exact (div_lt_one (mul_pos hxpos hypos)).2 hzxy
  have hs := series_mul_factor a b B hB hq
    (ha.1 x (by simp)) (hb.1 y hyR)
  have hfactor : q * (x * y) = z := by
    dsimp [q]
    field_simp [ne_of_gt (mul_pos hxpos hypos)]
  simpa only [hfactor] using hs

private theorem entire_right_product
    (a b B : ℕ → ℝ) (R₁ : ℝ≥0∞)
    (ha : IsConvergenceRadius a R₁)
    (hb : IsConvergenceRadius b ⊤)
    (hB : ∀ n, B n = a n * b n)
    (hR₁0 : R₁ ≠ 0) (hR₁top : R₁ ≠ ⊤) :
    ∀ z : ℝ, ENNReal.ofReal |z| < (⊤ : ℝ≥0∞) →
      SeriesConvergesAt B z := by
  intro z hz
  have hr₁pos : 0 < R₁.toReal := ENNReal.toReal_pos hR₁0 hR₁top
  let x : ℝ := R₁.toReal / 2
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hxr₁ : x < R₁.toReal := by dsimp [x]; linarith
  have hxR : ENNReal.ofReal |x| < R₁ := by
    rw [← ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hR₁top]
    rw [ENNReal.toReal_ofReal (abs_nonneg x)]
    simpa [abs_of_pos hxpos] using hxr₁
  let y : ℝ := |z| / x + 1
  have hypos : 0 < y := by dsimp [y]; positivity
  have hdiv : |z| / x < y := by
    dsimp [y]
    linarith
  have hzxy : |z| < x * y := by
    simpa [mul_comm] using (div_lt_iff₀ hxpos).1 hdiv
  let q : ℝ := z / (x * y)
  have hq : |q| < 1 := by
    dsimp [q]
    rw [abs_div, abs_of_pos (mul_pos hxpos hypos)]
    exact (div_lt_one (mul_pos hxpos hypos)).2 hzxy
  have hs := series_mul_factor a b B hB hq
    (ha.1 x hxR) (hb.1 y (by simp))
  have hfactor : q * (x * y) = z := by
    dsimp [q]
    field_simp [ne_of_gt (mul_pos hxpos hypos)]
  simpa only [hfactor] using hs

private theorem finite_inv_product
    (R₁ R₂ : ℝ≥0∞)
    (hR₁0 : R₁ ≠ 0) (hR₂0 : R₂ ≠ 0)
    (hR₁top : R₁ ≠ ⊤) (hR₂top : R₂ ≠ ⊤) :
    R₁⁻¹ * R₂⁻¹ = (R₁ * R₂)⁻¹ := by
  refine (ENNReal.toReal_eq_toReal ?_ ?_).mp ?_
  · exact ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.2 hR₁0) (ENNReal.inv_ne_top.2 hR₂0)
  · exact ENNReal.inv_ne_top.2 (mul_ne_zero hR₁0 hR₂0)
  · simp [ENNReal.toReal_mul, mul_comm]

theorem gap1
    (a b A : ℕ → ℝ) (hA : ∀ n, A n = a n + b n) :
    ∀ n, 0 < n →
      nthRootAbs A n = Real.rpow |a n + b n| (1 / (n : ℝ)) := by
  intro n hn
  simp [nthRootAbs, hA n]

theorem gap2 (a b : ℕ → ℝ) :
    ∀ n, 0 < n →
      Real.rpow |a n + b n| (1 / (n : ℝ)) ≤
        Real.rpow (|a n| + |b n|) (1 / (n : ℝ)) := by
  intro n hn
  exact Real.rpow_le_rpow (abs_nonneg (a n + b n))
    (abs_add_le (a n) (b n)) (by positivity)

theorem gap3 (a b : ℕ → ℝ) :
    ∀ n, 0 < n →
      Real.rpow (|a n| + |b n|) (1 / (n : ℝ)) ≤
        Real.rpow (2 * max |a n| |b n|) (1 / (n : ℝ)) := by
  intro n hn
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  have ha : |a n| ≤ max |a n| |b n| := le_max_left _ _
  have hb : |b n| ≤ max |a n| |b n| := le_max_right _ _
  linarith

theorem gap4
    (a b A : ℕ → ℝ) (hA : ∀ n, A n = a n + b n) :
    ∀ n, 0 < n → nthRootAbs A n ≤
      Real.rpow (2 * max |a n| |b n|) (1 / (n : ℝ)) := by
  intro n hn
  rw [gap1 a b A hA n hn]
  exact (gap2 a b n hn).trans (gap3 a b n hn)

theorem gap5
    (a b A : ℕ → ℝ) (hA : ∀ n, A n = a n + b n) :
    ∀ n, 0 < n → nthRootAbs A n ≤
      Real.rpow 2 (1 / (n : ℝ)) *
        max (nthRootAbs a n) (nthRootAbs b n) := by
  intro n hn
  have hm : 0 ≤ max |a n| |b n| :=
    (abs_nonneg (a n)).trans (le_max_left _ _)
  have hmul :
      Real.rpow (2 * max |a n| |b n|) (1 / (n : ℝ)) =
        Real.rpow 2 (1 / (n : ℝ)) *
          Real.rpow (max |a n| |b n|) (1 / (n : ℝ)) := by
    exact Real.mul_rpow (by norm_num) hm
  have hmax :
      Real.rpow (max |a n| |b n|) (1 / (n : ℝ)) =
        max (nthRootAbs a n) (nthRootAbs b n) := by
    unfold nthRootAbs
    by_cases hab : |a n| ≤ |b n|
    · have hr :
          Real.rpow |a n| (1 / (n : ℝ)) ≤
            Real.rpow |b n| (1 / (n : ℝ)) :=
        Real.rpow_le_rpow (abs_nonneg _) hab (by positivity)
      rw [max_eq_right hab, max_eq_right hr]
    · have hba : |b n| ≤ |a n| := le_of_not_ge hab
      have hr :
          Real.rpow |b n| (1 / (n : ℝ)) ≤
            Real.rpow |a n| (1 / (n : ℝ)) :=
        Real.rpow_le_rpow (abs_nonneg _) hba (by positivity)
      rw [max_eq_left hba, max_eq_left hr]
  calc
    nthRootAbs A n ≤ Real.rpow (2 * max |a n| |b n|) (1 / (n : ℝ)) :=
      gap4 a b A hA n hn
    _ = Real.rpow 2 (1 / (n : ℝ)) *
        Real.rpow (max |a n| |b n|) (1 / (n : ℝ)) := hmul
    _ = Real.rpow 2 (1 / (n : ℝ)) *
        max (nthRootAbs a n) (nthRootAbs b n) := by rw [hmax]

theorem gap6 :
    Tendsto (fun n : ℕ => Real.rpow 2 (1 / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 1) := by
  have hzero :
      Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hconst :
      Continuous (fun _ : ℝ => Real.log (2 : ℝ)) :=
    continuous_const
  have hid : Continuous (fun t : ℝ => t) :=
    continuous_id
  have hlinear :
      Continuous (fun t : ℝ => Real.log (2 : ℝ) * t) :=
    hconst.mul hid
  have hlog :
      Tendsto
        (fun n : ℕ =>
          Real.log (2 : ℝ) * (1 / ((n + 1 : ℕ) : ℝ)))
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_apply, mul_zero] using
      (hlinear.tendsto (0 : ℝ)).comp hzero
  have hexp :
      Tendsto
        (fun n : ℕ =>
          Real.exp
            (Real.log (2 : ℝ) * (1 / ((n + 1 : ℕ) : ℝ))))
        atTop (𝓝 (Real.exp (0 : ℝ))) :=
    (Real.continuous_exp.tendsto (0 : ℝ)).comp hlog
  have hrpow (t : ℝ) :
      Real.rpow (2 : ℝ) t =
        Real.exp (Real.log (2 : ℝ) * t) := by
    exact Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) t
  simpa only [hrpow, Real.exp_zero] using hexp

theorem gap7
    (a b A : ℕ → ℝ) (R₁ R₂ Rₐ : ℝ≥0∞)
    (ha : IsConvergenceRadius a R₁)
    (hb : IsConvergenceRadius b R₂)
    (hA : ∀ n, A n = a n + b n)
    (hRA : IsConvergenceRadius A Rₐ) :
    1 / Rₐ ≤ max (1 / R₁) (1 / R₂) := by
  have hminbound : min R₁ R₂ ≤ Rₐ :=
    sum_radius_lower_bound a b A R₁ R₂ Rₐ ha hb hA hRA
  have hinv : Rₐ⁻¹ ≤ (min R₁ R₂)⁻¹ :=
    (ENNReal.inv_le_inv).2 hminbound
  by_cases h : R₁ ≤ R₂
  · have hi : R₂⁻¹ ≤ R₁⁻¹ := by
      rw [ENNReal.inv_le_inv]
      exact h
    have hmin : min R₁ R₂ = R₁ := min_eq_left h
    have hmax : max R₁⁻¹ R₂⁻¹ = R₁⁻¹ := max_eq_left hi
    have htarget : Rₐ⁻¹ ≤ max R₁⁻¹ R₂⁻¹ := by
      calc
        Rₐ⁻¹ ≤ (min R₁ R₂)⁻¹ := hinv
        _ = R₁⁻¹ := congrArg (fun t : ℝ≥0∞ => t⁻¹) hmin
        _ = max R₁⁻¹ R₂⁻¹ := hmax.symm
    simpa only [one_div] using htarget
  · have h' : R₂ ≤ R₁ := le_of_not_ge h
    have hi : R₁⁻¹ ≤ R₂⁻¹ := by
      rw [ENNReal.inv_le_inv]
      exact h'
    have hmin : min R₁ R₂ = R₂ := min_eq_right h'
    have hmax : max R₁⁻¹ R₂⁻¹ = R₂⁻¹ := max_eq_right hi
    have htarget : Rₐ⁻¹ ≤ max R₁⁻¹ R₂⁻¹ := by
      calc
        Rₐ⁻¹ ≤ (min R₁ R₂)⁻¹ := hinv
        _ = R₂⁻¹ := congrArg (fun t : ℝ≥0∞ => t⁻¹) hmin
        _ = max R₁⁻¹ R₂⁻¹ := hmax.symm
    simpa only [one_div] using htarget

theorem gap8
    (a b A : ℕ → ℝ) (R₁ R₂ Rₐ : ℝ≥0∞)
    (ha : IsConvergenceRadius a R₁)
    (hb : IsConvergenceRadius b R₂)
    (hA : ∀ n, A n = a n + b n)
    (hRA : IsConvergenceRadius A Rₐ) :
    min R₁ R₂ ≤ Rₐ := by
  exact sum_radius_lower_bound a b A R₁ R₂ Rₐ ha hb hA hRA

theorem gap9
    (a b B : ℕ → ℝ) (hB : ∀ n, B n = a n * b n) :
    ∀ n, 0 < n → nthRootAbs B n =
      Real.rpow |a n * b n| (1 / (n : ℝ)) := by
  intro n hn
  simp [nthRootAbs, hB n]

theorem gap10 (a b : ℕ → ℝ) :
    ∀ n, 0 < n → Real.rpow |a n * b n| (1 / (n : ℝ)) =
      nthRootAbs a n * nthRootAbs b n := by
  intro n hn
  unfold nthRootAbs
  rw [abs_mul]
  exact Real.mul_rpow (abs_nonneg (a n)) (abs_nonneg (b n))

theorem gap11
    (a b B : ℕ → ℝ) (hB : ∀ n, B n = a n * b n) :
    ∀ n, 0 < n →
      nthRootAbs B n = nthRootAbs a n * nthRootAbs b n := by
  intro n hn
  rw [gap9 a b B hB n hn]
  exact gap10 a b n hn

theorem gap12
    (a b B : ℕ → ℝ) (R₁ R₂ Rᵦ : ℝ≥0∞)
    (ha : IsConvergenceRadius a R₁)
    (hb : IsConvergenceRadius b R₂)
    (hB : ∀ n, B n = a n * b n)
    (hRB : IsConvergenceRadius B Rᵦ)
    (hR₁0 : R₁ ≠ 0) (hR₂0 : R₂ ≠ 0)
    (hR₁top : R₁ ≠ ⊤) (hR₂top : R₂ ≠ ⊤) :
    1 / Rᵦ ≤ (1 / R₁) * (1 / R₂) := by
  have hprod : R₁ * R₂ ≤ Rᵦ := by
    apply radius_lower_bound
    exact finite_product_converges a b B R₁ R₂ ha hb hB
      hR₁0 hR₂0 hR₁top hR₂top
    exact hRB
  have hinv : Rᵦ⁻¹ ≤ (R₁ * R₂)⁻¹ :=
    (ENNReal.inv_le_inv).2 hprod
  have hfinal : Rᵦ⁻¹ ≤ R₁⁻¹ * R₂⁻¹ :=
    hinv.trans_eq
      (finite_inv_product R₁ R₂ hR₁0 hR₂0 hR₁top hR₂top).symm
  simpa only [one_div] using hfinal

theorem gap13
    (R₁ R₂ : ℝ≥0∞)
    (hR₁0 : R₁ ≠ 0) (hR₂0 : R₂ ≠ 0)
    (hR₁top : R₁ ≠ ⊤) (hR₂top : R₂ ≠ ⊤) :
    (1 / R₁) * (1 / R₂) = 1 / (R₁ * R₂) := by
  simpa only [one_div] using
    finite_inv_product R₁ R₂ hR₁0 hR₂0 hR₁top hR₂top

theorem gap14
    (a b B : ℕ → ℝ) (R₁ R₂ Rᵦ : ℝ≥0∞)
    (ha : IsConvergenceRadius a R₁)
    (hb : IsConvergenceRadius b R₂)
    (hB : ∀ n, B n = a n * b n)
    (hRB : IsConvergenceRadius B Rᵦ)
    (hR₁0 : R₁ ≠ 0) (hR₂0 : R₂ ≠ 0)
    (hR₁top : R₁ ≠ ⊤) (hR₂top : R₂ ≠ ⊤) :
    1 / Rᵦ ≤ 1 / (R₁ * R₂) := by
  calc
    1 / Rᵦ ≤ (1 / R₁) * (1 / R₂) :=
      gap12 a b B R₁ R₂ Rᵦ ha hb hB hRB
        hR₁0 hR₂0 hR₁top hR₂top
    _ = 1 / (R₁ * R₂) :=
      gap13 R₁ R₂ hR₁0 hR₂0 hR₁top hR₂top

theorem gap15
    (a b B : ℕ → ℝ) (R₁ R₂ Rᵦ : ℝ≥0∞)
    (ha : IsConvergenceRadius a R₁)
    (hb : IsConvergenceRadius b R₂)
    (hB : ∀ n, B n = a n * b n)
    (hRB : IsConvergenceRadius B Rᵦ) :
    R₁ * R₂ ≤ Rᵦ := by
  by_cases hR₁0 : R₁ = 0
  · simp [hR₁0]
  by_cases hR₂0 : R₂ = 0
  · simp [hR₂0]
  by_cases hR₁top : R₁ = ⊤
  · have ha' : IsConvergenceRadius a ⊤ := by
      simpa [hR₁top] using ha
    by_cases hR₂top : R₂ = ⊤
    · have hb' : IsConvergenceRadius b ⊤ := by
        simpa [hR₂top] using hb
      have hall :
          ∀ z : ℝ, ENNReal.ofReal |z| < (⊤ : ℝ≥0∞) →
            SeriesConvergesAt B z := by
        intro z hz
        let y : ℝ := |z| + 1
        have hypos : 0 < y := by
          dsimp [y]
          positivity
        let q : ℝ := z / y
        have hq : |q| < 1 := by
          dsimp [q]
          rw [abs_div, abs_of_pos hypos]
          exact (div_lt_one hypos).2 (by dsimp [y]; linarith [abs_nonneg z])
        have hs := series_mul_factor a b B hB hq
          (ha'.1 1 (by simp)) (hb'.1 y (by simp))
        have hfactor : q * (1 * y) = z := by
          dsimp [q]
          field_simp [ne_of_gt hypos]
        simpa only [hfactor] using hs
      have htop : (⊤ : ℝ≥0∞) ≤ Rᵦ := radius_lower_bound hall hRB
      have hprod : R₁ * R₂ = ⊤ := by simp [hR₁top, hR₂top]
      rw [hprod]
      exact htop
    · have hall :=
        entire_left_product a b B R₂ ha' hb hB hR₂0 hR₂top
      have htop : (⊤ : ℝ≥0∞) ≤ Rᵦ := radius_lower_bound hall hRB
      have hprod : R₁ * R₂ = ⊤ := by simp [hR₁top, hR₂0]
      rw [hprod]
      exact htop
  · by_cases hR₂top : R₂ = ⊤
    · have hb' : IsConvergenceRadius b ⊤ := by
        simpa [hR₂top] using hb
      have hall :=
        entire_right_product a b B R₁ ha hb' hB hR₁0 hR₁top
      have htop : (⊤ : ℝ≥0∞) ≤ Rᵦ := radius_lower_bound hall hRB
      have hprod : R₁ * R₂ = ⊤ := by simp [hR₂top, hR₁0]
      rw [hprod]
      exact htop
    · apply radius_lower_bound
      exact finite_product_converges a b B R₁ R₂ ha hb hB
        hR₁0 hR₂0 hR₁top hR₂top
      exact hRB

end

end ProofGap.Exercise2897
