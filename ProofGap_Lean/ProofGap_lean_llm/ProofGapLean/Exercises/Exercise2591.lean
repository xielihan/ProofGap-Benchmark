import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise2591

noncomputable section

def nthRoot (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.rpow (a n) (1 / (n : ℝ))

def ratio (a : ℕ → ℝ) (n : ℕ) : ℝ := a (n + 1) / a n

def lambda (q q₁ : ℝ) : ℝ := (q₁ + q) / (2 * q₁)

private theorem normRatioDivPow
    (a : ℕ → ℝ) (hpos : ∀ n, 0 < a n) (b : ℝ) (hb : 0 < b) (n : ℕ) :
    ‖a (n + 1) / b ^ (n + 1)‖ / ‖a n / b ^ n‖ = ratio a n / b := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (div_pos (hpos _) (pow_pos hb _)),
    abs_of_pos (div_pos (hpos _) (pow_pos hb _))]
  unfold ratio
  field_simp
  ring

private theorem normPowDivRatio
    (a : ℕ → ℝ) (hpos : ∀ n, 0 < a n) (b : ℝ) (hb : 0 < b) (n : ℕ) :
    ‖b ^ (n + 1) / a (n + 1)‖ / ‖b ^ n / a n‖ = b / ratio a n := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (div_pos (pow_pos hb _) (hpos _)),
    abs_of_pos (div_pos (pow_pos hb _) (hpos _))]
  unfold ratio
  field_simp
  ring

theorem gap1
    (a : ℕ → ℝ) (q q₁ : ℝ)
    (hratio : Tendsto (ratio a) atTop (nhds q))
    (hpos : ∀ n, 0 < a n)
    (hq : 0 ≤ q)
    (hqq₁ : q₁ > q) :
    Tendsto (nthRoot a) atTop (nhds q) := by
  rw [tendsto_order]
  constructor
  · intro r hrq
    by_cases hr : r ≤ 0
    · filter_upwards with n
      exact hr.trans_lt (Real.rpow_pos_of_pos (hpos n) _)
    · have hrpos : 0 < r := lt_of_not_ge hr
      have hqpos : 0 < q := hrpos.trans hrq
      let f : ℕ → ℝ := fun n ↦ r ^ n / a n
      have hratiof : Tendsto (fun n ↦ ‖f (n + 1)‖ / ‖f n‖)
          atTop (nhds (r / q)) := by
        convert tendsto_const_nhds.div hratio hqpos.ne' using 1
        funext n
        exact normPowDivRatio a hpos r hrpos n
      have hsum : Summable f := summable_of_ratio_test_tendsto_lt_one
        ((div_lt_one hqpos).2 hrq)
        (Filter.Eventually.of_forall fun n ↦ div_ne_zero (pow_ne_zero n hrpos.ne')
          (hpos n).ne') hratiof
      have hevent : ∀ᶠ n in atTop, f n < 1 :=
        (tendsto_order.mp hsum.tendsto_atTop_zero).2 1 zero_lt_one
      filter_upwards [hevent, Filter.eventually_ge_atTop 1] with n hnsmall hn
      have hp : r ^ n < a n := (div_lt_one (hpos n)).mp hnsmall
      have hroot := Real.rpow_lt_rpow (pow_nonneg hrpos.le n) hp
        (show 0 < 1 / (n : ℝ) by positivity)
      rw [one_div, Real.pow_rpow_inv_natCast hrpos.le (by omega)] at hroot
      simpa [nthRoot, one_div] using hroot
  · intro b hqb
    have hb : 0 < b := hq.trans_lt hqb
    let f : ℕ → ℝ := fun n ↦ a n / b ^ n
    have hratiof : Tendsto (fun n ↦ ‖f (n + 1)‖ / ‖f n‖)
        atTop (nhds (q / b)) := by
      convert hratio.div_const b using 1
      funext n
      exact normRatioDivPow a hpos b hb n
    have hsum : Summable f := summable_of_ratio_test_tendsto_lt_one
      ((div_lt_one hb).2 hqb)
      (Filter.Eventually.of_forall fun n ↦ div_ne_zero (hpos n).ne' (pow_ne_zero n hb.ne'))
      hratiof
    have hevent : ∀ᶠ n in atTop, f n < 1 :=
      (tendsto_order.mp hsum.tendsto_atTop_zero).2 1 zero_lt_one
    filter_upwards [hevent, Filter.eventually_ge_atTop 1] with n hnsmall hn
    have hp : a n < b ^ n := (div_lt_one (pow_pos hb n)).mp hnsmall
    have hroot := Real.rpow_lt_rpow (hpos n).le hp
      (show 0 < 1 / (n : ℝ) by positivity)
    rw [one_div, Real.pow_rpow_inv_natCast hb.le (by omega)] at hroot
    simpa [nthRoot, one_div] using hroot

theorem gap2
    (q q₁ ε : ℝ)
    (hqq₁ : q₁ > q)
    (hε : ε = (q₁ - q) / 2) :
    ε > 0 := by
  rw [hε]
  linarith

theorem gap3
    (a : ℕ → ℝ) (q ε : ℝ)
    (hroot : Tendsto (nthRoot a) atTop (nhds q))
    (hε : ε > 0) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n ≥ n₀, |nthRoot a n - q| < ε := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hroot) ε hε
  refine ⟨max N 1, le_max_right _ _, fun n hn ↦ ?_⟩
  have := hN n (le_trans (le_max_left N 1) hn)
  simpa [Real.dist_eq] using this

theorem gap4
    (a : ℕ → ℝ) (q q₁ ε : ℝ)
    (hq : 0 ≤ q) (hqq₁ : q₁ > q)
    (hε : ε = (q₁ - q) / 2)
    (heventual : ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ n ≥ n₀, |nthRoot a n - q| < ε) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n ≥ n₀,
      nthRoot a n < q + ε ∧ q + ε = lambda q q₁ * q₁ := by
  obtain ⟨n₀, hn₀, heventual⟩ := heventual
  have hq₁ : 0 < q₁ := hq.trans_lt hqq₁
  have heq : q + ε = lambda q q₁ * q₁ := by
    rw [hε]
    unfold lambda
    field_simp
    ring
  refine ⟨n₀, hn₀, fun n hn ↦ ⟨?_, heq⟩⟩
  have habs := heventual n hn
  rw [abs_lt] at habs
  linarith

theorem gap5
    (q q₁ : ℝ) (hq : 0 ≤ q) (hqq₁ : q₁ > q) :
    |lambda q q₁| < 1 := by
  have hq₁ : 0 < q₁ := hq.trans_lt hqq₁
  have hlambda : 0 ≤ lambda q q₁ := by
    unfold lambda
    positivity
  rw [abs_of_nonneg hlambda]
  unfold lambda
  apply (div_lt_one (by positivity : 0 < 2 * q₁)).2
  linarith

theorem gap6
    (q q₁ : ℝ)
    (hlambda : |lambda q q₁| < 1) :
    (fun n : ℕ => (lambda q q₁) ^ n) =o[atTop]
      (fun _n : ℕ => (1 : ℝ)) := by
  simpa using (isLittleO_pow_pow_of_abs_lt_left
    (r₁ := lambda q q₁) (r₂ := (1 : ℝ)) (by simpa using hlambda))

theorem gap7
    (a : ℕ → ℝ) (q q₁ : ℝ)
    (hpos : ∀ n, 0 < a n)
    (heventual : ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n ≥ n₀,
      nthRoot a n < lambda q q₁ * q₁) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      a n ≤ (lambda q q₁) ^ n * q₁ ^ n := by
  obtain ⟨n₀, hn₀, heventual⟩ := heventual
  refine ⟨n₀, fun n hn ↦ ?_⟩
  have hnpos : 0 < n := by omega
  have hrootpos : 0 < nthRoot a n := Real.rpow_pos_of_pos (hpos n) _
  have hbasepos : 0 < lambda q q₁ * q₁ := hrootpos.trans (heventual n hn)
  have hp := Real.rpow_le_rpow hrootpos.le (heventual n hn).le
    (show (0 : ℝ) ≤ n by positivity)
  simpa [nthRoot, one_div, Real.rpow_natCast,
    Real.rpow_inv_natCast_pow (hpos n).le hnpos.ne', mul_pow] using hp

theorem gap8
    (q q₁ : ℝ)
    (hsmall : (fun n : ℕ => (lambda q q₁) ^ n) =o[atTop]
      (fun _n : ℕ => (1 : ℝ))) :
    (fun n : ℕ => (lambda q q₁) ^ n * q₁ ^ n) =o[atTop]
      (fun n : ℕ => q₁ ^ n) := by
  simpa using hsmall.mul_isBigO
    (Asymptotics.isBigO_refl (fun n : ℕ ↦ q₁ ^ n) atTop)

theorem gap9
    (a : ℕ → ℝ) (q q₁ : ℝ)
    (hpos : ∀ n, 0 < a n)
    (hbound : ∃ n₀ : ℕ, ∀ n ≥ n₀,
      a n ≤ (lambda q q₁) ^ n * q₁ ^ n)
    (henvelope : (fun n : ℕ => (lambda q q₁) ^ n * q₁ ^ n) =o[atTop]
      (fun n : ℕ => q₁ ^ n)) :
    a =o[atTop] (fun n : ℕ => q₁ ^ n) := by
  obtain ⟨n₀, hbound⟩ := hbound
  have hbig : a =O[atTop]
      (fun n : ℕ ↦ (lambda q q₁) ^ n * q₁ ^ n) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [Filter.eventually_atTop.2 ⟨n₀, hbound⟩] with n hn
    have henvpos : 0 < (lambda q q₁) ^ n * q₁ ^ n :=
      (hpos n).trans_le hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hpos n), abs_of_pos henvpos]
    simpa using hn
  exact hbig.trans_isLittleO henvelope

theorem gap10
    (a : ℕ → ℝ) (q₁ : ℝ)
    (hsmall : a =o[atTop] (fun n : ℕ => q₁ ^ n)) :
    a =o[atTop] (fun n : ℕ => q₁ ^ n) := hsmall

end

end ProofGap.Exercise2591
