import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise3028

noncomputable section

open Filter
open scoped BigOperators Topology

def term (x : ℝ) (n : ℕ) : ℝ :=
  ((n - 1).factorial : ℝ) ^ 2 / ((2 * n).factorial : ℝ) *
    (2 * x) ^ (2 * n)

def f (x : ℝ) : ℝ := ∑' n : ℕ, term x (n + 1)

def convergenceDomain : Set ℝ :=
  {x | Summable (fun n : ℕ => term x (n + 1))}

def ratioModel (x : ℝ) (n : ℕ) : ℝ :=
  let k := n + 1
  4 * (k : ℝ) ^ 2 * x ^ 2 /
    ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1))

private theorem term_ratio_eq_ratioModel (x : ℝ) (n : ℕ) :
    term x (n + 2) / term x (n + 1) = ratioModel x n := by
  by_cases hx : x = 0
  · subst x
    simp [term, ratioModel]
  unfold term ratioModel
  dsimp only
  simp only [Nat.add_sub_cancel]
  rw [show n + 2 - 1 = n + 1 by omega]
  rw [show 2 * (n + 2) = (2 * (n + 1) + 1) + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  rw [Nat.factorial_succ (2 * (n + 1))]
  push_cast
  have hfac : (((n.factorial : ℕ) : ℝ)) ≠ 0 := by positivity
  have h₁ : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  have h₂ : (2 * (n : ℝ) + 4) ≠ 0 := by positivity
  field_simp [hfac, h₁, h₂, hx]
  ring

private theorem ratioModel_tendsto (x : ℝ) :
    Tendsto (ratioModel x) atTop (𝓝 (x ^ 2)) := by
  have h₁ := tendsto_add_mul_div_add_mul_atTop_nhds
    (𝕜 := ℝ) 2 4 2 (d := 2) (by norm_num)
  have h₂ := tendsto_add_mul_div_add_mul_atTop_nhds
    (𝕜 := ℝ) 2 3 2 (d := 2) (by norm_num)
  have h := (h₁.mul h₂).const_mul (x ^ 2)
  convert h using 1
  · funext n
    unfold ratioModel
    dsimp only
    push_cast
    have hden₁ : 2 * (n : ℝ) + 4 ≠ 0 := by positivity
    have hden₂ : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp [hden₁, hden₂]
    ring
  · norm_num

theorem gap1 (x : ℝ) :
    Tendsto
        (fun n : ℕ => term x (n + 2) / term x (n + 1))
        atTop (𝓝 (x ^ 2)) ∧
      Tendsto (ratioModel x) atTop (𝓝 (x ^ 2)) := by
  constructor
  · convert ratioModel_tendsto x using 1
    funext n
    exact term_ratio_eq_ratioModel x n
  · exact ratioModel_tendsto x

theorem gap2 (x : ℝ) :
    Tendsto (ratioModel x) atTop (𝓝 (x ^ 2)) := by
  exact (gap1 x).2

theorem gap3 (x : ℝ) :
    Tendsto
      (fun n : ℕ => term x (n + 2) / term x (n + 1))
      atTop (𝓝 (x ^ 2)) := by
  exact (gap1 x).1

private theorem term_nonneg (x : ℝ) (n : ℕ) : 0 ≤ term x n := by
  unfold term
  rw [show 2 * n = n * 2 by omega, pow_mul]
  positivity

private theorem term_ne_zero_of_ne_zero (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    term x (n + 1) ≠ 0 := by
  unfold term
  apply mul_ne_zero
  · apply div_ne_zero <;> positivity
  · apply pow_ne_zero
    exact mul_ne_zero (by norm_num) hx

private theorem summable_term_of_abs_lt_one (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => term x (n + 1)) := by
  by_cases hx0 : x = 0
  · subst x
    simp [term]
  apply summable_of_ratio_test_tendsto_lt_one
      (show x ^ 2 < 1 by simpa using (sq_lt_sq₀ (abs_nonneg x) zero_le_one).2 hx)
  · exact Filter.Eventually.of_forall (term_ne_zero_of_ne_zero x hx0)
  · convert ratioModel_tendsto x using 1
    funext n
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (term_nonneg x (n + 2)),
      abs_of_nonneg (term_nonneg x (n + 1)),
      term_ratio_eq_ratioModel]

private theorem not_summable_term_of_one_lt_abs (x : ℝ) (hx : 1 < |x|) :
    ¬Summable (fun n : ℕ => term x (n + 1)) := by
  apply not_summable_of_ratio_test_tendsto_gt_one
      (show 1 < x ^ 2 by simpa using (sq_lt_sq₀ zero_le_one (abs_nonneg x)).2 hx)
  convert ratioModel_tendsto x using 1
  funext n
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (term_nonneg x (n + 2)),
    abs_of_nonneg (term_nonneg x (n + 1)),
    term_ratio_eq_ratioModel]

private def d1 (x : ℝ) (n : ℕ) : ℝ :=
  ((n.factorial : ℝ) ^ 2 / ((2 * (n + 1)).factorial : ℝ)) *
    (4 * ((n + 1 : ℕ) : ℝ)) * (2 * x) ^ (2 * n + 1)

private def d2 (x : ℝ) (n : ℕ) : ℝ :=
  ((n.factorial : ℝ) ^ 2 / ((2 * (n + 1)).factorial : ℝ)) *
    (8 * ((n + 1 : ℕ) : ℝ) * (2 * ((n + 1 : ℕ) : ℝ) - 1)) *
    (2 * x) ^ (2 * n)

private theorem hasDerivAt_term (x : ℝ) (n : ℕ) :
    HasDerivAt (fun y => term y (n + 1)) (d1 x n) x := by
  have hpow : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  unfold term d1
  simp only [Nat.add_sub_cancel]
  convert (((hasDerivAt_id x).const_mul 2).pow (2 * (n + 1))).const_mul
    (((n.factorial : ℝ) ^ 2) / ((2 * (n + 1)).factorial : ℝ)) using 1 <;>
    simp [id_eq, hpow] <;> push_cast <;> ring

private theorem hasDerivAt_d1 (x : ℝ) (n : ℕ) :
    HasDerivAt (fun y => d1 y n) (d2 x n) x := by
  have hpow : 2 * n + 1 - 1 = 2 * n := by omega
  unfold d1 d2
  convert (((hasDerivAt_id x).const_mul 2).pow (2 * n + 1)).const_mul
    ((((n.factorial : ℝ) ^ 2 / ((2 * (n + 1)).factorial : ℝ)) *
      (4 * ((n + 1 : ℕ) : ℝ)))) using 1 <;>
    simp [id_eq, hpow] <;> push_cast <;> ring

private theorem d1_ratio_eq (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    d1 x (n + 1) / d1 x n =
      ratioModel x n * ((n : ℝ) + 2) / ((n : ℝ) + 1) := by
  unfold d1 ratioModel
  dsimp only
  rw [show 2 * (n + 1 + 1) = (2 * (n + 1) + 1) + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ (2 * (n + 1))]
  push_cast
  have hfac : (((n.factorial : ℕ) : ℝ)) ≠ 0 := by positivity
  have h₁ : (n : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
  have h₃ : 2 * (n : ℝ) + 4 ≠ 0 := by positivity
  field_simp [hfac, h₁, h₂, h₃, hx]
  ring

private theorem d1_ne_zero_of_ne_zero (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    d1 x n ≠ 0 := by
  unfold d1
  apply mul_ne_zero (mul_ne_zero (div_ne_zero (by positivity) (by positivity))
    (by positivity))
  apply pow_ne_zero
  exact mul_ne_zero (by norm_num) hx

private theorem d2_eq_d1_mul (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    d2 x n = d1 x n * (2 * (n : ℝ) + 1) / x := by
  unfold d1 d2
  rw [pow_succ]
  push_cast
  field_simp [hx]
  ring

private theorem d2_ratio_eq (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    d2 x (n + 1) / d2 x n =
      ratioModel x n * ((n : ℝ) + 2) / ((n : ℝ) + 1) *
        (2 * (n : ℝ) + 3) / (2 * (n : ℝ) + 1) := by
  rw [d2_eq_d1_mul x hx (n + 1), d2_eq_d1_mul x hx n]
  have hd₁ := d1_ne_zero_of_ne_zero x hx n
  have hp : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  calc
    (d1 x (n + 1) * (2 * ((n + 1 : ℕ) : ℝ) + 1) / x) /
        (d1 x n * (2 * (n : ℝ) + 1) / x) =
      (d1 x (n + 1) / d1 x n) *
        (2 * (n : ℝ) + 3) / (2 * (n : ℝ) + 1) := by
          push_cast
          field_simp [hx, hd₁, hp]
          ring
    _ = ratioModel x n * ((n : ℝ) + 2) / ((n : ℝ) + 1) *
        (2 * (n : ℝ) + 3) / (2 * (n : ℝ) + 1) := by
      rw [d1_ratio_eq x hx n]

private theorem d1_ratio_tendsto (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => d1 x (n + 1) / d1 x n)
      atTop (𝓝 (x ^ 2)) := by
  have hlin := tendsto_add_mul_div_add_mul_atTop_nhds
    (𝕜 := ℝ) 2 1 1 (d := 1) (by norm_num)
  convert (ratioModel_tendsto x).mul hlin using 1
  · funext n
    rw [d1_ratio_eq x hx n]
    ring
  · norm_num

private theorem d2_ratio_tendsto (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => d2 x (n + 1) / d2 x n)
      atTop (𝓝 (x ^ 2)) := by
  have hlin₁ := tendsto_add_mul_div_add_mul_atTop_nhds
    (𝕜 := ℝ) 2 1 1 (d := 1) (by norm_num)
  have hlin₂ := tendsto_add_mul_div_add_mul_atTop_nhds
    (𝕜 := ℝ) 3 1 2 (d := 2) (by norm_num)
  convert ((ratioModel_tendsto x).mul hlin₁).mul hlin₂ using 1
  · funext n
    rw [d2_ratio_eq x hx n]
    ring
  · norm_num

private theorem d1_nonneg (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : 0 ≤ d1 x n := by
  unfold d1
  positivity

private theorem d2_nonneg (x : ℝ) (n : ℕ) : 0 ≤ d2 x n := by
  have hmid : 0 ≤ 2 * (((n + 1 : ℕ) : ℝ)) - 1 := by
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  unfold d2
  rw [show 2 * n = n * 2 by omega, pow_mul]
  positivity

private theorem summable_d1_of_pos_of_lt_one (x : ℝ) (hx0 : 0 < x)
    (hx1 : x < 1) : Summable (d1 x) := by
  apply summable_of_ratio_test_tendsto_lt_one
      (show x ^ 2 < 1 by nlinarith)
  · exact Filter.Eventually.of_forall fun n => by
      unfold d1
      apply mul_ne_zero (mul_ne_zero (div_ne_zero (by positivity) (by positivity))
        (by positivity))
      apply pow_ne_zero
      nlinarith
  · convert d1_ratio_tendsto x hx0.ne' using 1
    funext n
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (d1_nonneg x hx0.le (n + 1)),
      abs_of_nonneg (d1_nonneg x hx0.le n)]

private theorem summable_d2_of_pos_of_lt_one (x : ℝ) (hx0 : 0 < x)
    (hx1 : x < 1) : Summable (d2 x) := by
  apply summable_of_ratio_test_tendsto_lt_one
      (show x ^ 2 < 1 by nlinarith)
  · exact Filter.Eventually.of_forall fun n => by
      have hmid : 2 * (((n + 1 : ℕ) : ℝ)) - 1 ≠ 0 := by
        push_cast
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      unfold d2
      apply mul_ne_zero (mul_ne_zero (div_ne_zero (by positivity) (by positivity))
        (mul_ne_zero (mul_ne_zero (by norm_num) (by positivity)) hmid))
      apply pow_ne_zero
      nlinarith
  · convert d2_ratio_tendsto x hx0.ne' using 1
    funext n
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (d2_nonneg x (n + 1)),
      abs_of_nonneg (d2_nonneg x n)]

private theorem norm_d1_le (r y : ℝ) (hr : 0 < r)
    (hy : y ∈ Set.Ioo (-r) r) (n : ℕ) : ‖d1 y n‖ ≤ d1 r n := by
  have hay : |y| ≤ r := (abs_lt.mpr hy).le
  have hbase : |2 * y| ≤ 2 * r := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  unfold d1
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
    abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * (((n + 1 : ℕ) : ℝ)))]
  gcongr

private theorem norm_d2_le (r y : ℝ) (hr : 0 < r)
    (hy : y ∈ Set.Ioo (-r) r) (n : ℕ) : ‖d2 y n‖ ≤ d2 r n := by
  have hay : |y| ≤ r := (abs_lt.mpr hy).le
  have hbase : |2 * y| ≤ 2 * r := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  have hmid : 0 ≤ 2 * (((n + 1 : ℕ) : ℝ)) - 1 := by
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  unfold d2
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
    abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity)),
    abs_of_nonneg (mul_nonneg (by positivity) hmid)]
  gcongr

private theorem hasDerivAt_f_interior (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt f (∑' n : ℕ, d1 x n) x := by
  have hxabs : |x| < 1 := abs_lt.mpr hx
  obtain ⟨r, hxr, hr1⟩ := exists_between hxabs
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg x) hxr
  have hxrt : x ∈ Set.Ioo (-r) r := abs_lt.mp hxr
  have h0rt : (0 : ℝ) ∈ Set.Ioo (-r) r := by simpa using hr0
  have h := hasDerivAt_tsum_of_isPreconnected
    (summable_d1_of_pos_of_lt_one r hr0 hr1)
    isOpen_Ioo isPreconnected_Ioo
    (fun n y hy => hasDerivAt_term y n)
    (fun n y hy => norm_d1_le r y hr0 hy n)
    h0rt (by simp [term]) hxrt
  simpa [f] using h

private theorem hasDerivAt_d1_tsum_interior (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y => ∑' n : ℕ, d1 y n) (∑' n : ℕ, d2 x n) x := by
  have hxabs : |x| < 1 := abs_lt.mpr hx
  obtain ⟨r, hxr, hr1⟩ := exists_between hxabs
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg x) hxr
  have hxrt : x ∈ Set.Ioo (-r) r := abs_lt.mp hxr
  have h0rt : (0 : ℝ) ∈ Set.Ioo (-r) r := by simpa using hr0
  exact hasDerivAt_tsum_of_isPreconnected
    (summable_d2_of_pos_of_lt_one r hr0 hr1)
    isOpen_Ioo isPreconnected_Ioo
    (fun n y hy => hasDerivAt_d1 y n)
    (fun n y hy => norm_d2_le r y hr0 hy n)
    h0rt (by simp [d1]) hxrt

private theorem summable_d1_interior (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : Summable (d1 x) := by
  have hxabs : |x| < 1 := abs_lt.mpr hx
  obtain ⟨r, hxr, hr1⟩ := exists_between hxabs
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg x) hxr
  exact (summable_d1_of_pos_of_lt_one r hr0 hr1).of_norm_bounded
    (fun n => norm_d1_le r x hr0 (abs_lt.mp hxr) n)

private theorem summable_d2_interior (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : Summable (d2 x) := by
  have hxabs : |x| < 1 := abs_lt.mpr hx
  obtain ⟨r, hxr, hr1⟩ := exists_between hxabs
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg x) hxr
  exact (summable_d2_of_pos_of_lt_one r hr0 hr1).of_norm_bounded
    (fun n => norm_d2_le r x hr0 (abs_lt.mp hxr) n)

private theorem ode_term_identity (x : ℝ) (n : ℕ) :
    -x * d1 x n + (1 - x ^ 2) * d2 x n =
      d2 x n - d2 x (n + 1) := by
  unfold d1 d2
  rw [show 2 * (n + 1 + 1) = (2 * (n + 1) + 1) + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ (2 * (n + 1))]
  push_cast
  have hfac : (((n.factorial : ℕ) : ℝ)) ≠ 0 := by positivity
  have h₁ : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
  have h₂ : 2 * (n : ℝ) + 4 ≠ 0 := by positivity
  field_simp [hfac, h₁, h₂]
  ring

private theorem tsum_ode_identity (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    -x * (∑' n : ℕ, d1 x n) +
        (1 - x ^ 2) * (∑' n : ℕ, d2 x n) = 4 := by
  have hs1 := summable_d1_interior x hx
  have hs2 := summable_d2_interior x hx
  have hs2shift : Summable (fun n : ℕ => d2 x (n + 1)) :=
    (summable_nat_add_iff 1).2 hs2
  calc
    -x * (∑' n : ℕ, d1 x n) +
          (1 - x ^ 2) * (∑' n : ℕ, d2 x n) =
        ∑' n : ℕ, (-x * d1 x n + (1 - x ^ 2) * d2 x n) := by
      rw [← tsum_mul_left, ← tsum_mul_left]
      exact (((hs1.mul_left (-x)).hasSum.add
        (hs2.mul_left (1 - x ^ 2)).hasSum).tsum_eq).symm
    _ = ∑' n : ℕ, (d2 x n - d2 x (n + 1)) := by
      apply tsum_congr
      exact ode_term_identity x
    _ = (∑' n : ℕ, d2 x n) - ∑' n : ℕ, d2 x (n + 1) := by
      exact (hs2.hasSum.sub hs2shift.hasSum).tsum_eq
    _ = d2 x 0 := by
      have h := hs2.sum_add_tsum_nat_add 1
      simpa using sub_eq_iff_eq_add.mpr h.symm
    _ = 4 := by norm_num [d2]

private theorem deriv_f_eq_d1 (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv f x = ∑' n : ℕ, d1 x n :=
  (hasDerivAt_f_interior x hx).deriv

private theorem hasDerivAt_deriv_f_interior (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (deriv f) (∑' n : ℕ, d2 x n) x := by
  have heq : deriv f =ᶠ[𝓝 x] (fun y => ∑' n : ℕ, d1 y n) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact deriv_f_eq_d1 y hy
  exact (hasDerivAt_d1_tsum_interior x hx).congr_of_eventuallyEq heq

private theorem deriv_deriv_f_eq_d2 (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (deriv f) x = ∑' n : ℕ, d2 x n :=
  (hasDerivAt_deriv_f_interior x hx).deriv

private theorem ode_identity (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    -x * deriv f x + (1 - x ^ 2) * deriv (deriv f) x = 4 := by
  rw [deriv_f_eq_d1 x hx, deriv_deriv_f_eq_d2 x hx]
  exact tsum_ode_identity x hx

private theorem one_sub_sq_pos (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : 0 < 1 - x ^ 2 := by
  nlinarith [mul_pos (sub_pos.mpr hx.2) (by linarith [hx.1] : 0 < 1 + x)]

private theorem normalized_ode_identity (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    -(x / Real.sqrt (1 - x ^ 2)) * deriv f x +
        Real.sqrt (1 - x ^ 2) * deriv (deriv f) x =
      4 / Real.sqrt (1 - x ^ 2) := by
  have hq := one_sub_sq_pos x hx
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt hq.le
  have hode := ode_identity x hx
  field_simp [hs]
  rw [hs2]
  nlinarith

private def firstIntegral (x : ℝ) : ℝ :=
  Real.sqrt (1 - x ^ 2) * deriv f x - 4 * Real.arcsin x

private theorem hasDerivAt_firstIntegral (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt firstIntegral 0 x := by
  have hq := one_sub_sq_pos x hx
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hinner : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp <;> ring
  have hsqrt : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      (-x / Real.sqrt (1 - x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hinner using 1 <;>
      field_simp [hs] <;> ring
  have hasin := Real.hasDerivAt_arcsin (ne_of_gt hx.1) (ne_of_lt hx.2)
  unfold firstIntegral
  convert (hsqrt.mul (hasDerivAt_deriv_f_interior x hx)).sub
    (hasin.const_mul 4) using 1
  rw [← deriv_deriv_f_eq_d2 x hx]
  have hneg : -x / Real.sqrt (1 - x ^ 2) =
      -(x / Real.sqrt (1 - x ^ 2)) := by ring
  rw [hneg,
    normalized_ode_identity x hx]
  ring

private theorem firstIntegral_eq_zero (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : firstIntegral x = 0 := by
  have hdiff : DifferentiableOn ℝ firstIntegral (Set.Ioo (-1 : ℝ) 1) := by
    intro y hy
    exact (hasDerivAt_firstIntegral y hy).differentiableAt.differentiableWithinAt
  have hder : ∀ y ∈ Set.Ioo (-1 : ℝ) 1, deriv firstIntegral y = 0 := by
    intro y hy
    exact (hasDerivAt_firstIntegral y hy).deriv
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    hdiff hder hx (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)
  have hzero : firstIntegral 0 = 0 := by
    unfold firstIntegral
    rw [deriv_f_eq_d1 0 (by norm_num)]
    simp [d1]
  linarith

private theorem deriv_f_closed_form (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv f x = 4 * Real.arcsin x / Real.sqrt (1 - x ^ 2) := by
  have hq := one_sub_sq_pos x hx
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have h := firstIntegral_eq_zero x hx
  unfold firstIntegral at h
  apply (eq_div_iff hs).2
  linarith

private def secondIntegral (x : ℝ) : ℝ :=
  f x - 2 * Real.arcsin x ^ 2

private theorem hasDerivAt_secondIntegral (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt secondIntegral 0 x := by
  have hf := hasDerivAt_f_interior x hx
  have hasin := Real.hasDerivAt_arcsin (ne_of_gt hx.1) (ne_of_lt hx.2)
  unfold secondIntegral
  convert hf.sub ((hasin.pow 2).const_mul 2) using 1
  rw [← deriv_f_eq_d1 x hx, deriv_f_closed_form x hx]
  norm_num
  ring

private theorem f_eq_arcsin_sq_interior (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    f x = 2 * Real.arcsin x ^ 2 := by
  have hdiff : DifferentiableOn ℝ secondIntegral (Set.Ioo (-1 : ℝ) 1) := by
    intro y hy
    exact (hasDerivAt_secondIntegral y hy).differentiableAt.differentiableWithinAt
  have hder : ∀ y ∈ Set.Ioo (-1 : ℝ) 1, deriv secondIntegral y = 0 := by
    intro y hy
    exact (hasDerivAt_secondIntegral y hy).deriv
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    hdiff hder hx (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)
  have hzero : secondIntegral 0 = 0 := by
    unfold secondIntegral f
    simp [term]
  unfold secondIntegral at hconst hzero
  linarith

private theorem partial_sum_one_le (N : ℕ) :
    (∑ n ∈ Finset.range N, term 1 (n + 1)) ≤ Real.pi ^ 2 / 2 := by
  let S : ℝ → ℝ := fun r => ∑ n ∈ Finset.range N, term r (n + 1)
  have hcont : Continuous S := by
    dsimp [S, term]
    fun_prop
  have hlim : Tendsto S (𝓝[<] (1 : ℝ)) (𝓝 (S 1)) :=
    hcont.continuousAt.tendsto.mono_left inf_le_left
  change S 1 ≤ Real.pi ^ 2 / 2
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have hrabs : |r| < 1 := by rw [abs_of_pos hr.1]; exact hr.2
  have hs := summable_term_of_abs_lt_one r hrabs
  have hpartial : S r ≤ f r := by
    unfold S f
    exact hs.sum_le_tsum (Finset.range N) fun n hn => term_nonneg r (n + 1)
  rw [f_eq_arcsin_sq_interior r
    ⟨(by linarith [hr.1] : (-1 : ℝ) < r), hr.2⟩] at hpartial
  have hasin0 : 0 ≤ Real.arcsin r := Real.arcsin_nonneg.2 hr.1.le
  have hasinpi : Real.arcsin r ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two r
  have hsq : Real.arcsin r ^ 2 ≤ (Real.pi / 2) ^ 2 :=
    (sq_le_sq₀ hasin0 (by positivity)).2 hasinpi
  nlinarith

private theorem summable_term_one :
    Summable (fun n : ℕ => term 1 (n + 1)) := by
  apply summable_of_sum_range_le
  · intro n
    exact term_nonneg 1 (n + 1)
  · exact partial_sum_one_le

private theorem term_neg_one_eq_one (n : ℕ) :
    term (-1) (n + 1) = term 1 (n + 1) := by
  unfold term
  congr 1
  norm_num only [mul_neg, mul_one]
  rw [(even_two_mul (n + 1)).neg_pow]

private theorem summable_term_neg_one :
    Summable (fun n : ℕ => term (-1) (n + 1)) := by
  exact summable_term_one.congr fun n => (term_neg_one_eq_one n).symm

private theorem summable_term_iff_abs_le_one (x : ℝ) :
    Summable (fun n : ℕ => term x (n + 1)) ↔ |x| ≤ 1 := by
  constructor
  · intro hs
    exact le_of_not_gt fun hx => (not_summable_term_of_one_lt_abs x hx) hs
  · intro hx
    rcases hx.eq_or_lt with h | h
    · have habs : |x| = 1 := h
      rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp habs with hx1 | hx1
      · subst x
        exact summable_term_one
      · subst x
        exact summable_term_neg_one
    · exact summable_term_of_abs_lt_one x h

private theorem norm_term_le_one (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (n : ℕ) :
    ‖term x (n + 1)‖ ≤ term 1 (n + 1) := by
  have hxabs : |x| ≤ 1 := abs_le.mpr hx
  have hbase : |2 * x| ≤ (2 : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  unfold term
  simp only [Nat.add_sub_cancel]
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_pow,
    abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_pos (by positivity : (0 : ℝ) < (((2 * (n + 1)).factorial : ℕ) : ℝ))]
  norm_num only [mul_one]
  gcongr

private theorem continuousOn_f_closed : ContinuousOn f (Set.Icc (-1 : ℝ) 1) := by
  unfold f
  apply continuousOn_tsum
  · intro n
    unfold term
    fun_prop
  · exact summable_term_one
  · intro n x hx
    exact norm_term_le_one x hx n

private theorem f_eq_arcsin_sq_closed (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    f x = 2 * Real.arcsin x ^ 2 := by
  have heq : Set.EqOn f (fun y : ℝ => 2 * Real.arcsin y ^ 2)
      (Set.Ioo (-1 : ℝ) 1) := fun y hy => f_eq_arcsin_sq_interior y hy
  apply heq.of_subset_closure continuousOn_f_closed
    ((Real.continuous_arcsin.pow 2).const_mul 2).continuousOn
    Set.Ioo_subset_Icc_self _ hx
  rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]

theorem gap4 : convergenceDomain = Set.Icc (-1) 1 := by
  ext x
  simp [convergenceDomain, summable_term_iff_abs_le_one, abs_le]

theorem gap5 : ContinuousOn f (Set.Icc (-1) 1) := by
  exact continuousOn_f_closed

theorem gap6 (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv f x =
      ∑' n : ℕ,
        (((n : ℕ).factorial : ℝ) ^ 2 /
          ((2 * (n + 1)).factorial : ℝ)) *
          (4 * ((n + 1 : ℕ) : ℝ)) * (2 * x) ^ (2 * n + 1) := by
  simpa [d1] using deriv_f_eq_d1 x hx

theorem gap7 (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (deriv f) x =
      ∑' n : ℕ,
        (((n : ℕ).factorial : ℝ) ^ 2 /
          ((2 * (n + 1)).factorial : ℝ)) *
          (8 * ((n + 1 : ℕ) : ℝ) * (2 * ((n + 1 : ℕ) : ℝ) - 1)) *
          (2 * x) ^ (2 * n) := by
  simpa [d2] using deriv_deriv_f_eq_d2 x hx

theorem gap8 (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    -x * deriv f x + (1 - x ^ 2) * deriv (deriv f) x = 4 := by
  exact ode_identity x hx

theorem gap9 (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    -(x / Real.sqrt (1 - x ^ 2)) * deriv f x +
        Real.sqrt (1 - x ^ 2) * deriv (deriv f) x =
      4 / Real.sqrt (1 - x ^ 2) := by
  exact normalized_ode_identity x hx

theorem gap10 :
    ∃ C : ℝ, ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      Real.sqrt (1 - x ^ 2) * deriv f x =
        4 * Real.arcsin x + C := by
  refine ⟨0, ?_⟩
  intro x hx
  have h := firstIntegral_eq_zero x hx
  unfold firstIntegral at h
  linarith

theorem gap11 : deriv f 0 = 0 := by
  rw [deriv_f_eq_d1 0 (by norm_num)]
  simp [d1]

theorem gap12 (C : ℝ)
    (hC : ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      Real.sqrt (1 - x ^ 2) * deriv f x =
        4 * Real.arcsin x + C) :
    C = 0 := by
  have h := hC 0 (by norm_num)
  rw [deriv_f_eq_d1 0 (by norm_num)] at h
  simpa [d1] using h.symm

theorem gap13 (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv f x = 4 * Real.arcsin x / Real.sqrt (1 - x ^ 2) := by
  exact deriv_f_closed_form x hx

theorem gap14 :
    ∃ C₁ : ℝ, ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      f x = 2 * Real.arcsin x ^ 2 + C₁ := by
  exact ⟨0, fun x hx => by simpa using f_eq_arcsin_sq_closed x hx⟩

theorem gap15 : f 0 = 0 := by
  unfold f
  simp [term]

theorem gap16 (C₁ : ℝ)
    (hC₁ : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      f x = 2 * Real.arcsin x ^ 2 + C₁) :
    C₁ = 0 := by
  have h := hC₁ 0 (by norm_num)
  have hf0 : f 0 = 0 := by unfold f; simp [term]
  rw [hf0] at h
  simpa using h.symm

theorem gap17 (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    f x = 2 * Real.arcsin x ^ 2 := by
  exact f_eq_arcsin_sq_closed x hx

theorem gap18 (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (∑' n : ℕ, term x (n + 1)) = 2 * Real.arcsin x ^ 2 := by
  exact f_eq_arcsin_sq_closed x hx

end

end ProofGap.Exercise3028
