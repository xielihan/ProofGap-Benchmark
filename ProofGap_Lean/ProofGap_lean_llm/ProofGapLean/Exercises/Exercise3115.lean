import ProofGapLean.Prelude.Analysis
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ProofGap.Exercise3115

noncomputable section

def multinomialRatio : ℝ :=
  (Nat.factorial 100 : ℝ) /
    ((Nat.factorial 20 : ℝ) * (Nat.factorial 30 : ℝ) *
      (Nat.factorial 50 : ℝ))

def decimalModel : ℝ :=
  (10 : ℝ) ^ 42 * 4.792

def LinearizedExp (A scale θ : ℝ) : Prop :=
  |A * Real.exp (θ / scale) - A * (1 + θ / scale)| ≤
    |A| * Real.exp (1 / scale) / (2 * scale ^ 2)

/-- Exercise 3115, gap 1; include the Stirling remainder bounds. -/
theorem gap1 :
    ∃ θ₁ θ₂ θ₃ θ₄ : ℝ,
      0 < θ₁ ∧ θ₁ < 1 ∧ 0 < θ₂ ∧ θ₂ < 1 ∧
      0 < θ₃ ∧ θ₃ < 1 ∧ 0 < θ₄ ∧ θ₄ < 1 ∧
      multinomialRatio =
        (Real.sqrt (2 * Real.pi * 100) * (100 : ℝ) ^ 100 *
            Real.exp (-100) * Real.exp (θ₁ / 1200)) /
          (Real.sqrt ((2 : ℝ) ^ 3 * Real.pi ^ 3 * 20 * 30 * 50) *
            (20 : ℝ) ^ 20 * (30 : ℝ) ^ 30 * (50 : ℝ) ^ 50 *
            Real.exp (-100) *
            Real.exp (θ₂ / 240 + θ₃ / 360 + θ₄ / 600)) := by
  let c : ℝ := 47 / 50
  let s : ℝ := c / 240 + c / 360 + c / 600
  let A : ℝ :=
    multinomialRatio * 20 * (20 : ℝ) ^ 20 * (30 : ℝ) ^ 30 *
      (50 : ℝ) ^ 50 / (100 : ℝ) ^ 100
  let K : ℝ :=
    (Real.sqrt (2 * Real.pi * 100) * (100 : ℝ) ^ 100 *
        Real.exp (-100)) /
      (Real.sqrt ((2 : ℝ) ^ 3 * Real.pi ^ 3 * 20 * 30 * 50) *
        (20 : ℝ) ^ 20 * (30 : ℝ) ^ 30 * (50 : ℝ) ^ 50 *
        Real.exp (-100) * Real.exp s)
  let q : ℝ := multinomialRatio / K
  have hsqrt :
      Real.sqrt ((2 : ℝ) ^ 3 * Real.pi ^ 3 * 20 * 30 * 50) =
        Real.sqrt (2 * Real.pi * 100) *
          (20 * Real.pi * Real.sqrt 3) := by
    have hsquare :
        (Real.sqrt ((2 : ℝ) ^ 3 * Real.pi ^ 3 * 20 * 30 * 50)) ^ 2 =
          (Real.sqrt (2 * Real.pi * 100) *
            (20 * Real.pi * Real.sqrt 3)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity :
            (0 : ℝ) ≤ (2 : ℝ) ^ 3 * Real.pi ^ 3 * 20 * 30 * 50)]
      rw [mul_pow]
      rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi * 100)]
      rw [mul_pow, mul_pow]
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    have hl :
        0 ≤ Real.sqrt ((2 : ℝ) ^ 3 * Real.pi ^ 3 * 20 * 30 * 50) :=
      Real.sqrt_nonneg _
    have hr :
        0 ≤ Real.sqrt (2 * Real.pi * 100) *
          (20 * Real.pi * Real.sqrt 3) := by positivity
    nlinarith
  have hbpos : 0 < Real.sqrt (2 * Real.pi * 100) := by positivity
  have hq_form : q = A * Real.pi * Real.sqrt 3 * Real.exp s := by
    dsimp [q, K, A]
    rw [hsqrt]
    field_simp [ne_of_gt hbpos, Real.exp_ne_zero]
    <;> ring
  have hApos : 0 < A := by
    dsimp [A, multinomialRatio]
    positivity
  have hpi_lower : (3141 : ℝ) / 1000 < Real.pi := by
    nlinarith [Real.pi_gt_d20]
  have hpi_upper : Real.pi < (3142 : ℝ) / 1000 := by
    nlinarith [Real.pi_lt_d20]
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_lower : (265 : ℝ) / 153 < Real.sqrt 3 := by
    have hrat : ((265 : ℝ) / 153) ^ 2 < 3 := by norm_num
    have hsqrt_nonneg := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  have hsqrt_upper : Real.sqrt 3 < (1351 : ℝ) / 780 := by
    have hrat : (3 : ℝ) < ((1351 : ℝ) / 780) ^ 2 := by norm_num
    have hsqrt_nonneg := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  have hs_nonneg : 0 ≤ s := by norm_num [s, c]
  have hs_lt_one : s < 1 := by norm_num [s, c]
  have hs_ne : s ≠ 0 := by
    have : 0 < s := by norm_num [s, c]
    exact ne_of_gt this
  have hexp_lower : 1 + s < Real.exp s := by
    simpa [add_comm] using Real.add_one_lt_exp hs_ne
  have hexp_upper : Real.exp s ≤ 1 / (1 - s) := by
    exact Real.exp_bound_div_one_sub_of_interval hs_nonneg hs_lt_one
  have hrational_lower :
      1 < A * ((3141 : ℝ) / 1000) * ((265 : ℝ) / 153) * (1 + s) := by
    dsimp [A, s, c, multinomialRatio]
    norm_num [Nat.factorial]
  have hrational_upper :
      A * ((3142 : ℝ) / 1000) * ((1351 : ℝ) / 780) *
          (1 / (1 - s)) <
        1 + (1 : ℝ) / 1200 := by
    dsimp [A, s, c, multinomialRatio]
    norm_num [Nat.factorial]
  have hq_lower : 1 < q := by
    rw [hq_form]
    calc
      1 < A * ((3141 : ℝ) / 1000) * ((265 : ℝ) / 153) * (1 + s) :=
        hrational_lower
      _ < A * Real.pi * Real.sqrt 3 * Real.exp s := by
        gcongr <;> norm_num [s, c] <;> positivity
  have hq_upper : q < Real.exp ((1 : ℝ) / 1200) := by
    rw [hq_form]
    calc
      A * Real.pi * Real.sqrt 3 * Real.exp s ≤
          A * ((3142 : ℝ) / 1000) * ((1351 : ℝ) / 780) *
            (1 / (1 - s)) := by
        gcongr <;> norm_num [s, c] <;> positivity
      _ < 1 + (1 : ℝ) / 1200 := hrational_upper
      _ < Real.exp ((1 : ℝ) / 1200) := by
        simpa [add_comm] using
          Real.add_one_lt_exp (show (1 : ℝ) / 1200 ≠ 0 by norm_num)
  have hK : 0 < K := by
    dsimp [K, s, c]
    positivity
  have hratio : 0 < multinomialRatio := by
    unfold multinomialRatio
    positivity
  have hq : 0 < q := lt_trans (by norm_num) hq_lower
  let θ₁ : ℝ := 1200 * Real.log q
  have hθ₁_pos : 0 < θ₁ := by
    dsimp [θ₁]
    have hlog : 0 < Real.log q := Real.log_pos hq_lower
    positivity
  have hθ₁_lt : θ₁ < 1 := by
    have hexp_log : Real.exp (Real.log q) = q := Real.exp_log hq
    have hlog : Real.log q < (1 : ℝ) / 1200 := by
      apply (Real.exp_lt_exp).mp
      simpa [hexp_log] using hq_upper
    dsimp [θ₁]
    nlinarith
  refine ⟨θ₁, c, c, c, hθ₁_pos, hθ₁_lt, ?_⟩
  have hc0 : 0 < c := by norm_num [c]
  have hc1 : c < 1 := by norm_num [c]
  refine ⟨hc0, hc1, hc0, hc1, hc0, hc1, ?_⟩
  have hexp : Real.exp (θ₁ / 1200) = q := by
    rw [show θ₁ / 1200 = Real.log q by dsimp [θ₁]; ring]
    exact Real.exp_log hq
  rw [hexp]
  dsimp [q, K, s]
  field_simp
  <;> ring

/-- Exercise 3115, gap 2; bind the effective error to its range. -/
theorem gap2 :
    ∃ θ : ℝ, |θ| < 1 ∧
      multinomialRatio = decimalModel * Real.exp (θ / 120) := by
  let q : ℝ := multinomialRatio / decimalModel
  have hmodel : 0 < decimalModel := by
    unfold decimalModel
    positivity
  have hratio : 0 < multinomialRatio := by
    unfold multinomialRatio
    positivity
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hq_lower : (120 : ℝ) / 121 < q := by
    dsimp [q, multinomialRatio, decimalModel]
    norm_num [Nat.factorial]
  have hq_upper : q < 1 := by
    dsimp [q, multinomialRatio, decimalModel]
    norm_num [Nat.factorial]
  have hexp_lower : Real.exp (-(1 : ℝ) / 120) < (120 : ℝ) / 121 := by
    have he : (121 : ℝ) / 120 < Real.exp ((1 : ℝ) / 120) := by
      have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) / 120 ≠ 0)
      norm_num at h ⊢
      linarith
    calc
      Real.exp (-(1 : ℝ) / 120) = 1 / Real.exp ((1 : ℝ) / 120) := by
        rw [show -(1 : ℝ) / 120 = -((1 : ℝ) / 120) by ring]
        simpa [one_div] using Real.exp_neg ((1 : ℝ) / 120)
      _ < 1 / ((121 : ℝ) / 120) :=
        one_div_lt_one_div_of_lt (by norm_num) he
      _ = (120 : ℝ) / 121 := by norm_num
  have hlog_lower : -(1 : ℝ) / 120 < Real.log q := by
    apply (Real.exp_lt_exp).mp
    rw [Real.exp_log hq]
    exact lt_trans hexp_lower hq_lower
  have hlog_upper : Real.log q < 0 := by
    apply (Real.exp_lt_exp).mp
    simpa [Real.exp_log hq] using hq_upper
  refine ⟨120 * Real.log q, ?_, ?_⟩
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 120),
      abs_of_neg hlog_upper]
    norm_num
    nlinarith
  · have hexp : Real.exp ((120 * Real.log q) / 120) = q := by
      rw [show (120 * Real.log q) / 120 = Real.log q by ring]
      exact Real.exp_log hq
    rw [hexp]
    dsimp [q]
    field_simp

/-- Exercise 3115, gap 3; make the first-order approximation quantitative. -/
theorem gap3 :
    ∀ θ : ℝ, |θ| < 1 →
      LinearizedExp decimalModel 120 θ := by
  intro θ hθ
  unfold LinearizedExp
  let x : ℝ := θ / 120
  have hx : |x| < (1 : ℝ) / 120 := by
    dsimp [x]
    rw [abs_div]
    norm_num
    exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 120)).2 hθ
  have htaylor :
      |Real.exp x - 1 - x| ≤
        Real.exp ((1 : ℝ) / 120) * x ^ 2 / 2 := by
    by_cases hx0 : x = 0
    · simp [hx0]
    · let r : ℝ := (Real.exp x - 1 - x) / x ^ 2
      let f : ℝ → ℝ := fun t => Real.exp t - 1 - t - r * t ^ 2
      let g : ℝ → ℝ := fun t => Real.exp t - 1 - 2 * r * t
      let g' : ℝ → ℝ := fun t => Real.exp t - 2 * r
      have hf0 : f 0 = 0 := by simp [f]
      have hfx : f x = 0 := by
        dsimp [f, r]
        field_simp [hx0]
        ring
      have hg0 : g 0 = 0 := by simp [g]
      have hfderiv (t : ℝ) : HasDerivAt f (g t) t := by
        dsimp [f, g]
        convert ((((Real.hasDerivAt_exp t).sub_const 1).sub
          (hasDerivAt_id t)).sub
          (((hasDerivAt_id t).pow 2).const_mul r)) using 1 <;>
            simp [id] <;> ring
      have hgderiv (t : ℝ) : HasDerivAt g (g' t) t := by
        dsimp [g, g']
        convert (((Real.hasDerivAt_exp t).sub_const 1).sub
          ((hasDerivAt_id t).const_mul (2 * r))) using 1 <;>
            simp [id] <;> ring
      have hfdiff : Differentiable ℝ f :=
        fun t => (hfderiv t).differentiableAt
      have hgdiff : Differentiable ℝ g :=
        fun t => (hgderiv t).differentiableAt
      have hr_eq : Real.exp x - 1 - x = r * x ^ 2 := by
        dsimp [r]
        field_simp [hx0]
      have hrema_nonneg : 0 ≤ Real.exp x - 1 - x := by
        nlinarith [Real.add_one_le_exp x]
      rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
      · obtain ⟨c, hc, hfc⟩ :=
          exists_deriv_eq_slope (f := f) hxneg
            hfdiff.continuous.continuousOn hfdiff.differentiableOn
        have hgc : g c = 0 := by
          calc
            g c = deriv f c := (hfderiv c).deriv.symm
            _ = (f 0 - f x) / (0 - x) := hfc
            _ = 0 := by simp [hf0, hfx]
        obtain ⟨d, hd, hgd⟩ :=
          exists_deriv_eq_slope (f := g) hc.2
            hgdiff.continuous.continuousOn hgdiff.differentiableOn
        have hg'd : g' d = 0 := by
          calc
            g' d = deriv g d := (hgderiv d).deriv.symm
            _ = (g 0 - g c) / (0 - c) := hgd
            _ = 0 := by simp [hg0, hgc]
        have hrval : r = Real.exp d / 2 := by
          dsimp [g'] at hg'd
          linarith
        have hd_bound : d ≤ (1 : ℝ) / 120 := by
          have : d < 0 := hd.2
          linarith
        rw [abs_of_nonneg hrema_nonneg, hr_eq, hrval]
        have he : Real.exp d ≤ Real.exp ((1 : ℝ) / 120) :=
          (Real.exp_le_exp).2 hd_bound
        nlinarith [mul_le_mul_of_nonneg_right he (sq_nonneg x)]
      · obtain ⟨c, hc, hfc⟩ :=
          exists_deriv_eq_slope (f := f) hxpos
            hfdiff.continuous.continuousOn hfdiff.differentiableOn
        have hgc : g c = 0 := by
          calc
            g c = deriv f c := (hfderiv c).deriv.symm
            _ = (f x - f 0) / (x - 0) := hfc
            _ = 0 := by simp [hf0, hfx]
        obtain ⟨d, hd, hgd⟩ :=
          exists_deriv_eq_slope (f := g) hc.1
            hgdiff.continuous.continuousOn hgdiff.differentiableOn
        have hg'd : g' d = 0 := by
          calc
            g' d = deriv g d := (hgderiv d).deriv.symm
            _ = (g c - g 0) / (c - 0) := hgd
            _ = 0 := by simp [hg0, hgc]
        have hrval : r = Real.exp d / 2 := by
          dsimp [g'] at hg'd
          linarith
        have hd_bound : d ≤ (1 : ℝ) / 120 := by
          have hdx : d < x := lt_trans hd.2 hc.2
          have hxa : x < (1 : ℝ) / 120 :=
            lt_of_le_of_lt (le_abs_self x) hx
          linarith
        rw [abs_of_nonneg hrema_nonneg, hr_eq, hrval]
        have he : Real.exp d ≤ Real.exp ((1 : ℝ) / 120) :=
          (Real.exp_le_exp).2 hd_bound
        nlinarith [mul_le_mul_of_nonneg_right he (sq_nonneg x)]
  calc
    |decimalModel * Real.exp (θ / 120) - decimalModel * (1 + θ / 120)| =
        |decimalModel| * |Real.exp x - 1 - x| := by
          dsimp [x]
          rw [← abs_mul]
          congr 1
          ring
    _ ≤ |decimalModel| *
        (Real.exp ((1 : ℝ) / 120) * x ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left htaylor (abs_nonneg decimalModel)
    _ ≤ |decimalModel| *
        (Real.exp ((1 : ℝ) / 120) * ((1 : ℝ) / 120) ^ 2 / 2) := by
      have hx2 : x ^ 2 ≤ ((1 : ℝ) / 120) ^ 2 := by
        have hdiff : 0 ≤ (1 : ℝ) / 120 - |x| :=
          sub_nonneg.mpr (le_of_lt hx)
        have hsum : 0 ≤ (1 : ℝ) / 120 + |x| :=
          add_nonneg (by norm_num) (abs_nonneg x)
        have hprod :
            0 ≤ ((1 : ℝ) / 120 - |x|) * ((1 : ℝ) / 120 + |x|) :=
          mul_nonneg hdiff hsum
        nlinarith [hprod, sq_abs x]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg decimalModel)
      refine (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 ?_
      exact mul_le_mul_of_nonneg_left hx2
        (le_of_lt (Real.exp_pos ((1 : ℝ) / 120)))
    _ = |decimalModel| * Real.exp (1 / 120) / (2 * 120 ^ 2) := by
      ring

/-- Exercise 3115, gap 4; retain one witness for value and approximation. -/
theorem gap4 :
    ∃ θ : ℝ,
      |θ| < 1 ∧
      multinomialRatio = decimalModel * Real.exp (θ / 120) ∧
      LinearizedExp decimalModel 120 θ := by
  obtain ⟨θ, hθ, hvalue⟩ := gap2
  exact ⟨θ, hθ, hvalue, gap3 θ hθ⟩

end

end ProofGap.Exercise3115
