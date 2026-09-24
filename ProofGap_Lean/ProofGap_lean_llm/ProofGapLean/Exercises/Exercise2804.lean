import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2804

noncomputable section

open Filter
open scoped Interval Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) * x * (1 - x) ^ n

def badPoint (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

def epsilon0 : ℝ :=
  1 / (4 * Real.exp 1)

def PointwiseConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, Tendsto (fun n : ℕ => f n x) atTop (𝓝 (F x))

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

def integralSeq (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, term n x

def substitutedIntegralSeq (n : ℕ) : ℝ :=
  ∫ y in (0 : ℝ)..1, (n : ℝ) * (1 - y) * y ^ n

def antiderivativeBoundary (n : ℕ) : ℝ :=
  (n : ℝ) / ((n : ℝ) + 1) - (n : ℝ) / ((n : ℝ) + 2)

def rationalSeq (n : ℕ) : ℝ :=
  (n : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 2))

theorem gap1 :
    ∀ x : ℝ, x = 0 ∨ x = 1 → ∀ n : ℕ, term n x = 0 := by
  rintro x (rfl | rfl) n <;> cases n <;> simp [term]

theorem gap2 :
    ∀ x : ℝ, 0 < x → x < 1 →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 0) := by
  intro x hx0 hx1
  let q : ℝ := 1 - x
  let c : ℝ := -Real.log q
  have hq0 : 0 < q := by
    dsimp [q]
    linarith
  have hq1 : q < 1 := by
    dsimp [q]
    linarith
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq1
  have hc : 0 < c := by
    dsimp [c]
    linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have harg : Tendsto (fun n : ℕ => c * (n : ℝ)) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    have h := (tendsto_atTop.1 hnat) (b / c)
    filter_upwards [h] with n hn
    have hbc : b ≤ (n : ℝ) * c := (div_le_iff₀ hc).mp hn
    simpa [mul_comm] using hbc
  have hstd :
      Tendsto (fun t : ℝ => t ^ 1 * Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hcomp := hstd.comp harg
  have hconst :
      Tendsto (fun _ : ℕ => x / c) atTop (𝓝 (x / c)) :=
    tendsto_const_nhds
  have hscaled :
      Tendsto
        (fun n : ℕ =>
          (x / c) * ((c * (n : ℝ)) ^ 1 * Real.exp (-(c * (n : ℝ)))))
        atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using hconst.mul hcomp
  refine hscaled.congr' (Filter.Eventually.of_forall ?_)
  intro n
  have hpow : q ^ n = Real.exp (-(c * (n : ℝ))) := by
    calc
      q ^ n = (Real.exp (Real.log q)) ^ n := by rw [Real.exp_log hq0]
      _ = Real.exp ((n : ℝ) * Real.log q) := by
        rw [Real.exp_nat_mul]
      _ = Real.exp (-(c * (n : ℝ))) := by
        congr 1
        dsimp [c]
        ring
  rw [← hpow]
  dsimp [term, q]
  field_simp [ne_of_gt hc] <;> ring

theorem gap3 :
    PointwiseConvergesOn term (fun _ => 0) (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hzero | hx0
  · subst x
    have hfun : (fun n : ℕ => term n 0) = (fun _ : ℕ => (0 : ℝ)) := by
      funext n
      exact gap1 0 (Or.inl rfl) n
    rw [hfun]
    exact tendsto_const_nhds
  · rcases eq_or_lt_of_le hx.2 with hone | hx1
    · subst x
      have hfun : (fun n : ℕ => term n 1) = (fun _ : ℕ => (0 : ℝ)) := by
        funext n
        exact gap1 1 (Or.inr rfl) n
      rw [hfun]
      exact tendsto_const_nhds
    · exact gap2 x hx0 hx1

theorem gap4 :
    0 < epsilon0 := by
  unfold epsilon0
  positivity

theorem gap5 :
    epsilon0 < 1 / (2 * Real.exp 1) := by
  unfold epsilon0
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)

theorem gap6 :
    0 < 1 / (2 * Real.exp 1) := by
  positivity

theorem gap7 :
    ∀ n : ℕ,
      |term n (1 / ((n : ℝ) + 1))| =
        (n : ℝ) * (1 / ((n : ℝ) + 1)) *
          (1 - 1 / ((n : ℝ) + 1)) ^ n := by
  intro n
  rw [abs_of_nonneg]
  · rfl
  · have hn : 0 ≤ (n : ℝ) := by positivity
    have hd : 0 < (n : ℝ) + 1 := by positivity
    have hb : 0 ≤ 1 - 1 / ((n : ℝ) + 1) := by
      rw [sub_nonneg, div_le_one hd]
      norm_num
    exact mul_nonneg (mul_nonneg hn (le_of_lt (one_div_pos.mpr hd)))
      (pow_nonneg hb n)

theorem gap8 :
    ∀ n : ℕ,
      (n : ℝ) * (1 / ((n : ℝ) + 1)) *
          (1 - 1 / ((n : ℝ) + 1)) ^ n =
        ((n : ℝ) / ((n : ℝ) + 1)) ^ (n + 1) := by
  intro n
  have hd : (n : ℝ) + 1 ≠ 0 := by positivity
  have hbase :
      1 - 1 / ((n : ℝ) + 1) = (n : ℝ) / ((n : ℝ) + 1) := by
    field_simp [hd]
    ring
  rw [hbase, pow_succ]
  field_simp [hd]

theorem gap9 :
    Tendsto
      (fun n : ℕ => ((n : ℝ) / ((n : ℝ) + 1)) ^ (n + 1))
      atTop (𝓝 (Real.exp (-1))) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hn1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    have h := (tendsto_atTop.1 hnat) b
    filter_upwards [h] with n hn
    linarith
  have hi :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hn1
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hq :
      Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 1) := by
    have hsub :
        Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1))
          atTop (𝓝 1) := by
      simpa using hconst.sub hi
    refine hsub.congr' (Filter.Eventually.of_forall ?_)
    intro n
    have hd : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hd] <;> ring
  have hqne :
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) / ((n : ℝ) + 1) ≠ 1 := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hd : 0 < (n : ℝ) + 1 := by positivity
    exact ne_of_lt ((div_lt_one hd).2 (by linarith))
  have hqWithin :
      Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝[≠] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hq, ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hqne
  have hderiv : HasDerivAt Real.log 1 1 := by
    simpa using
      (Real.hasDerivAt_log (show (1 : ℝ) ≠ 0 by norm_num))
  have hslope :
      Tendsto (slope Real.log 1) (𝓝[≠] (1 : ℝ)) (𝓝 1) :=
    hasDerivAt_iff_tendsto_slope.mp hderiv
  have hneg :
      Tendsto
        (fun n : ℕ =>
          -(slope Real.log 1 ((n : ℝ) / ((n : ℝ) + 1))))
        atTop (𝓝 (-1)) := by
    simpa only [Function.comp_apply] using (hslope.comp hqWithin).neg
  have harg :
      Tendsto
        (fun n : ℕ =>
          ((n : ℝ) + 1) *
            Real.log ((n : ℝ) / ((n : ℝ) + 1)))
        atTop (𝓝 (-1)) := by
    refine hneg.congr' (Filter.Eventually.of_forall ?_)
    intro n
    have hd : (n : ℝ) + 1 ≠ 0 := by positivity
    have hlt : (n : ℝ) / ((n : ℝ) + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    have hne :
        (n : ℝ) / ((n : ℝ) + 1) - 1 ≠ 0 := by
      linarith
    have hne' :
        1 - (n : ℝ) / ((n : ℝ) + 1) ≠ 0 := by
      linarith
    simp only [slope, Real.log_one, smul_eq_mul]
    field_simp [hd, hne, hne'] <;> ring <;> simp
  have hexp :
      Tendsto
        (fun n : ℕ =>
          Real.exp
            (((n : ℝ) + 1) *
              Real.log ((n : ℝ) / ((n : ℝ) + 1))))
        atTop (𝓝 (Real.exp (-1))) := by
    simpa only [Function.comp_apply] using
      ((Real.hasDerivAt_exp (-1)).continuousAt.tendsto.comp harg)
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hqpos : 0 < (n : ℝ) / ((n : ℝ) + 1) :=
    div_pos hnpos (by positivity)
  symm
  calc
    ((n : ℝ) / ((n : ℝ) + 1)) ^ (n + 1) =
        (Real.exp
          (Real.log ((n : ℝ) / ((n : ℝ) + 1)))) ^ (n + 1) := by
      rw [Real.exp_log hqpos]
    _ = Real.exp
        (((n + 1 : ℕ) : ℝ) *
          Real.log ((n : ℝ) / ((n : ℝ) + 1))) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp
        (((n : ℝ) + 1) *
          Real.log ((n : ℝ) / ((n : ℝ) + 1))) := by
      norm_num only [Nat.cast_add, Nat.cast_one]

theorem gap10 :
    Tendsto (fun n : ℕ => |term n (badPoint n)|)
      atTop (𝓝 (Real.exp (-1))) := by
  simpa only [badPoint, gap7, gap8] using gap9

theorem gap11 :
    ∃ N : ℕ, ∀ n : ℕ, N < n →
      |term n (badPoint n)| > 1 / (2 * Real.exp 1) := by
  have hlim : 1 / (2 * Real.exp 1) < Real.exp (-1) := by
    rw [Real.exp_neg]
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    simpa only [one_div] using
      (one_div_lt_one_div_of_lt he (by nlinarith : Real.exp 1 < 2 * Real.exp 1))
  have hev : ∀ᶠ n : ℕ in atTop,
      1 / (2 * Real.exp 1) < |term n (badPoint n)| :=
    (tendsto_order.1 gap10).1 _ hlim
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  exact ⟨N, fun n hn => hN n (Nat.le_of_lt hn)⟩

theorem gap12 :
    1 / (2 * Real.exp 1) > epsilon0 := by
  exact gap5

theorem gap13 :
    ∃ N : ℕ, ∀ n : ℕ, N < n →
      |term n (badPoint n)| > epsilon0 := by
  rcases gap11 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hlarge := hN n hn
  have hcompare := gap12
  linarith

theorem gap14 :
    ¬ UniformlyConvergesOn term (fun _ => 0) (Set.Icc (0 : ℝ) 1) := by
  intro hunif
  rcases hunif epsilon0 gap4 with ⟨Nu, hNu⟩
  rcases gap13 with ⟨Nb, hNb⟩
  let n : ℕ := max Nu Nb + 1
  have hnu : Nu < n := by
    dsimp [n]
    omega
  have hnb : Nb < n := by
    dsimp [n]
    omega
  have hd : 0 < (n : ℝ) + 1 := by positivity
  have hx : badPoint n ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · unfold badPoint
      exact le_of_lt (one_div_pos.mpr hd)
    · unfold badPoint
      rw [div_le_one hd]
      norm_num
  have hu := hNu n hnu (badPoint n) hx
  have hb := hNb n hnb
  simp only [sub_zero] at hu
  linarith

theorem gap15 :
    (∫ _x in (0 : ℝ)..1, (0 : ℝ)) =
      ∫ _x in (0 : ℝ)..1, (0 : ℝ) := by
  rfl

theorem gap16 :
    (∫ _x in (0 : ℝ)..1, (0 : ℝ)) = 0 := by
  simp

theorem gap17 :
    (∫ _x in (0 : ℝ)..1, (0 : ℝ)) = 0 := by
  exact gap16

theorem gap18 :
    integralSeq =
      fun n : ℕ =>
        ∫ x in (0 : ℝ)..1, (n : ℝ) * x * (1 - x) ^ n := by
  rfl

theorem gap19 :
    integralSeq = substitutedIntegralSeq := by
  funext n
  simp only [integralSeq, substitutedIntegralSeq, term]
  have h := intervalIntegral.integral_comp_sub_left
    (f := fun y : ℝ => (n : ℝ) * (1 - y) * y ^ n)
    (a := (0 : ℝ)) (b := 1) (d := 1)
  convert h using 1 <;> norm_num <;> ring

theorem gap20 :
    substitutedIntegralSeq = antiderivativeBoundary := by
  funext n
  simp only [substitutedIntegralSeq, antiderivativeBoundary]
  have hpow (k : ℕ) :
      (∫ y : ℝ in (0 : ℝ)..1, y ^ k) =
        1 / ((k : ℝ) + 1) := by
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    have hF (y : ℝ) :
        HasDerivAt
          (fun z : ℝ =>
            (1 / ((k : ℝ) + 1)) * z ^ (k + 1))
          (y ^ k) y := by
      simpa [Nat.cast_add, hk, ← mul_assoc] using
        (((hasDerivAt_id y).pow (k + 1)).const_mul
          (1 / ((k : ℝ) + 1)))
    have hFTC :
        (∫ y : ℝ in (0 : ℝ)..1, y ^ k) =
          (1 / ((k : ℝ) + 1)) * (1 : ℝ) ^ (k + 1) -
            (1 / ((k : ℝ) + 1)) * (0 : ℝ) ^ (k + 1) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y _ => hF y)
        ((continuous_id.pow k).intervalIntegrable 0 1)
    simpa using hFTC
  have h1 : IntervalIntegrable (fun y : ℝ => (n : ℝ) * y ^ n)
      MeasureTheory.volume 0 1 := by
    exact (continuous_const.mul (continuous_id.pow n)).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun y : ℝ => (n : ℝ) * y ^ (n + 1))
      MeasureTheory.volume 0 1 := by
    exact (continuous_const.mul (continuous_id.pow (n + 1))).intervalIntegrable 0 1
  have hf :
      (fun y : ℝ => (n : ℝ) * (1 - y) * y ^ n) =
        fun y : ℝ => (n : ℝ) * y ^ n - (n : ℝ) * y ^ (n + 1) := by
    funext y
    rw [pow_succ]
    ring
  rw [hf, intervalIntegral.integral_sub h1 h2]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hpow n, hpow (n + 1)]
  have hcast : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  rw [hcast]
  have hd1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hd2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hd1, hd2] <;> ring

theorem gap21 :
    antiderivativeBoundary = rationalSeq := by
  funext n
  unfold antiderivativeBoundary rationalSeq
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h1, h2]
  ring

theorem gap22 :
    Tendsto rationalSeq atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hn1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    have h := (tendsto_atTop.1 hnat) b
    filter_upwards [h] with n hn
    linarith
  have hn2 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    have h := (tendsto_atTop.1 hnat) b
    filter_upwards [h] with n hn
    linarith
  have hi1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hn1
  have hi2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hn2
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hr : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 1) := by
    have h' :
        Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1))
          atTop (𝓝 1) := by
      simpa using hconst.sub hi1
    refine h'.congr' (Filter.Eventually.of_forall ?_)
    intro n
    have hd : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hd] <;> ring
  have hp :
      Tendsto
        (fun n : ℕ =>
          ((n : ℝ) / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 2)))
        atTop (𝓝 0) := by
    simpa using hr.mul hi2
  refine hp.congr' (Filter.Eventually.of_forall ?_)
  intro n
  unfold rationalSeq
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h1, h2]

theorem gap23 :
    Tendsto integralSeq atTop (𝓝 0) := by
  rw [gap19, gap20, gap21]
  exact gap22

theorem gap24 :
    PointwiseConvergesOn term (fun _ => 0) (Set.Icc (0 : ℝ) 1) ∧
      ¬ UniformlyConvergesOn term (fun _ => 0) (Set.Icc (0 : ℝ) 1) ∧
      Tendsto integralSeq atTop
        (𝓝 (∫ _x in (0 : ℝ)..1, (0 : ℝ))) := by
  refine ⟨gap3, gap14, ?_⟩
  rw [gap16]
  exact gap23

end

end ProofGap.Exercise2804
