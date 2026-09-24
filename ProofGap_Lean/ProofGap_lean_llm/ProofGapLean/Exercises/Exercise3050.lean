import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise3050

noncomputable section

open MeasureTheory
open scoped BigOperators

def f (a x : ℝ) : ℝ := 1 / (x + a)

def nthDeriv (g : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  (deriv^[n]) g

def ThetaAdmissible (ϑ : ℕ → ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 < ϑ n x ∧ ϑ n x < 1

def taylorPartial (a x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    (-1 : ℝ) ^ k * x ^ k / a ^ (k + 1)

def normalizedRemainder
    (a : ℝ) (ϑ : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (a / (a + ϑ n x * x)) ^ (n + 1)

def RemainderWitness
    (a : ℝ) (ϑ : ℕ → ℝ → ℝ) : Prop :=
  ThetaAdmissible ϑ ∧
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 ≤ x →
      f a x =
        taylorPartial a x n +
          (-1 : ℝ) ^ n * normalizedRemainder a ϑ n x *
            (x ^ n / a ^ (n + 1))

def moment (n : ℕ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ n

def weightedRemainderMoment
    (a : ℝ) (ϑ : ℕ → ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    Real.exp (-x) * normalizedRemainder a ϑ n x * x ^ n

def thetaFactor
    (a : ℝ) (ϑ : ℕ → ℝ → ℝ) (n : ℕ) : ℝ :=
  weightedRemainderMoment a ϑ n / (n.factorial : ℝ)

def targetIntegral (a : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) / (a + x)

def factorialPartial (a : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    (-1 : ℝ) ^ k * (k.factorial : ℝ) / a ^ (k + 1)

private theorem nthDeriv_formula_zpow (a y : ℝ) (n : ℕ) :
    nthDeriv (f a) n y =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) *
        (y + a) ^ (-1 - n : ℤ) := by
  unfold nthDeriv f
  simpa [one_div, add_comm] using
    congrFun (iter_deriv_inv_linear n (1 : ℝ) a) y

private theorem nthDeriv_formula (a y : ℝ) (n : ℕ)
    (hya : y + a ≠ 0) :
    nthDeriv (f a) n y =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) /
        (y + a) ^ (n + 1) := by
  rw [nthDeriv_formula_zpow]
  rw [show (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast]
  ring

private theorem taylor_exists (a x : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 1 ≤ n) (hx : 0 ≤ x) :
    ∃ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 ∧
      f a x =
        (∑ k ∈ Finset.range n,
          nthDeriv (f a) k 0 / (k.factorial : ℝ) * x ^ k) +
        nthDeriv (f a) n (θ * x) / (n.factorial : ℝ) * x ^ n := by
  by_cases hx0 : x = 0
  · subst x
    refine ⟨1 / 2, by norm_num, ?_⟩
    have hn0 : n ≠ 0 := by omega
    rw [zero_pow hn0, mul_zero, add_zero]
    rw [Finset.sum_eq_single 0]
    · simp [f, nthDeriv]
    · intro k hk hk0
      simp [hk0]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hf : ContDiffOn ℝ n (f a) (Set.Icc 0 x) := by
      have hlin : ContDiffOn ℝ n (fun y : ℝ => y + a) (Set.Icc 0 x) :=
        contDiffOn_id.add contDiffOn_const
      change ContDiffOn ℝ n (fun y : ℝ => 1 / (y + a)) (Set.Icc 0 x)
      simpa only [one_div] using hlin.inv (fun y hy => by
        have hy0 : 0 ≤ y := hy.1
        linarith)
    have hnsub : n - 1 + 1 = n := by omega
    have hf' : ContDiffOn ℝ (n - 1 + 1) (f a) (Set.Icc 0 x) := by
      have hlin : ContDiffOn ℝ (n - 1 + 1)
          (fun y : ℝ => y + a) (Set.Icc 0 x) :=
        contDiffOn_id.add contDiffOn_const
      change ContDiffOn ℝ (n - 1 + 1)
        (fun y : ℝ => 1 / (y + a)) (Set.Icc 0 x)
      simpa only [one_div] using hlin.inv (fun y hy => by
        have hy0 : 0 ≤ y := hy.1
        linarith)
    rcases taylor_mean_remainder_lagrange_iteratedDeriv
        (n := n - 1) hxpos hf' with
      ⟨c, hc, hrem⟩
    have heval :
        taylorWithinEval (f a) (n - 1) (Set.Icc 0 x) 0 x =
          ∑ k ∈ Finset.range n,
            nthDeriv (f a) k 0 / (k.factorial : ℝ) * x ^ k := by
      rw [taylor_within_apply]
      rw [hnsub]
      apply Finset.sum_congr rfl
      intro k hk
      rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc hxpos)
        (show ContDiffAt ℝ k (f a) 0 by
          have hlin : ContDiffAt ℝ k (fun y : ℝ => y + a) 0 :=
            contDiffAt_id.add contDiffAt_const
          change ContDiffAt ℝ k (fun y : ℝ => 1 / (y + a)) 0
          simpa only [one_div] using hlin.inv (by simpa using ha.ne'))
        ⟨le_rfl, hxpos.le⟩]
      rw [iteratedDeriv_eq_iterate]
      simp only [nthDeriv, smul_eq_mul]
      ring
    refine ⟨c / x, ⟨div_pos hc.1 hxpos,
      (div_lt_one hxpos).2 hc.2⟩, ?_⟩
    rw [heval] at hrem
    have hcx : c / x * x = c := by field_simp
    rw [hnsub, iteratedDeriv_eq_iterate] at hrem
    change f a x - _ = nthDeriv (f a) n c * (x - 0) ^ n /
      (n.factorial : ℝ) at hrem
    rw [hcx]
    rw [sub_zero] at hrem
    have hreorder : nthDeriv (f a) n c * x ^ n / (n.factorial : ℝ) =
        nthDeriv (f a) n c / (n.factorial : ℝ) * x ^ n := by ring
    rw [hreorder] at hrem
    linarith

private theorem taylor_explicit_exists (a x : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 1 ≤ n) (hx : 0 ≤ x) :
    ∃ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 ∧
      f a x = taylorPartial a x n +
        (-1 : ℝ) ^ n * x ^ n / (a + θ * x) ^ (n + 1) := by
  rcases taylor_exists a x ha n hn hx with ⟨θ, hθ, h⟩
  refine ⟨θ, hθ, ?_⟩
  rw [h]
  unfold taylorPartial
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have ha0 : (0 : ℝ) + a ≠ 0 := by positivity
    rw [nthDeriv_formula a 0 k ha0]
    have hkfac : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hkfac]
    ring
  · have hden : θ * x + a ≠ 0 := by
      have hnonneg : 0 ≤ θ * x := mul_nonneg hθ.1.le hx
      linarith
    rw [nthDeriv_formula a (θ * x) n hden]
    have hnfac : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have hden' : a + θ * x ≠ 0 := by simpa [add_comm] using hden
    field_simp [hnfac, hden, hden']
    ring

private theorem taylor_normalized_exists (a x : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 1 ≤ n) (hx : 0 ≤ x) :
    ∃ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 ∧
      f a x = taylorPartial a x n +
        (-1 : ℝ) ^ n * (a / (a + θ * x)) ^ (n + 1) *
          (x ^ n / a ^ (n + 1)) := by
  rcases taylor_explicit_exists a x ha n hn hx with ⟨θ, hθ, h⟩
  refine ⟨θ, hθ, ?_⟩
  rw [h]
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hden : a + θ * x ≠ 0 := by
    have hnonneg : 0 ≤ θ * x := mul_nonneg hθ.1.le hx
    linarith
  congr 1
  rw [div_pow]
  field_simp [ha0, hden]

private theorem normalized_pos (a x : ℝ) (ϑ : ℕ → ℝ → ℝ)
    (ha : 0 < a) (hϑ : ThetaAdmissible ϑ) (n : ℕ) (hx : 0 ≤ x) :
    0 < normalizedRemainder a ϑ n x := by
  have htheta := (hϑ n x hx).1
  have hden : 0 < a + ϑ n x * x := by positivity
  unfold normalizedRemainder
  positivity

private theorem normalized_lt_one (a x : ℝ) (ϑ : ℕ → ℝ → ℝ)
    (ha : 0 < a) (hϑ : ThetaAdmissible ϑ) (n : ℕ) (hx : 0 < x) :
    normalizedRemainder a ϑ n x < 1 := by
  have htheta := (hϑ n x hx.le).1
  have hden : 0 < a + ϑ n x * x := by positivity
  have hbase : 0 < a / (a + ϑ n x * x) := div_pos ha hden
  have hbase1 : a / (a + ϑ n x * x) < 1 := by
    apply (div_lt_one hden).2
    nlinarith [mul_pos htheta hx]
  unfold normalizedRemainder
  exact pow_lt_one₀ hbase.le hbase1 (by omega)

private theorem moment_eq_factorial (n : ℕ) :
    moment n = (n.factorial : ℝ) := by
  have hgamma := Real.Gamma_eq_integral
    (show (0 : ℝ) < (n : ℝ) + 1 by positivity)
  have hfac := Real.Gamma_nat_eq_factorial n
  unfold moment
  rw [← hfac, hgamma]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  congr 1
  rw [show (n : ℝ) + 1 - 1 = (n : ℝ) by ring]
  simpa only [Real.rpow_natCast]

private theorem moment_integrable (n : ℕ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ n) (Set.Ioi 0) := by
  have h := Real.GammaIntegral_convergent
    (show (0 : ℝ) < (n : ℝ) + 1 by positivity)
  apply h.congr_fun
  intro x hx
  rw [show (n : ℝ) + 1 - 1 = (n : ℝ) by ring]
  simpa only [Real.rpow_natCast]
  exact measurableSet_Ioi

private theorem weighted_lt_moment (a : ℝ) (ϑ : ℕ → ℝ → ℝ)
    (ha : 0 < a) (hϑ : ThetaAdmissible ϑ) (n : ℕ) :
    weightedRemainderMoment a ϑ n < moment n := by
  let base : ℝ → ℝ := fun x => Real.exp (-x) * x ^ n
  let w : ℝ → ℝ := fun x =>
    Real.exp (-x) * normalizedRemainder a ϑ n x * x ^ n
  have hbase : IntegrableOn base (Set.Ioi 0) := by
    simpa [base] using moment_integrable n
  by_cases hw : IntegrableOn w (Set.Ioi 0)
  · have hdiff : IntegrableOn (fun x => base x - w x) (Set.Ioi 0) :=
      hbase.sub hw
    have hpoint (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
        0 < base x - w x := by
      have hnorm0 := normalized_pos a x ϑ ha hϑ n hx.le
      have hnorm1 := normalized_lt_one a x ϑ ha hϑ n hx
      have hexp := Real.exp_pos (-x)
      have hxpow : 0 < x ^ n := pow_pos hx n
      dsimp [base, w]
      nlinarith [mul_pos hexp hxpow,
        mul_pos (mul_pos hexp hnorm0) hxpow]
    have hpos : 0 < ∫ x in Set.Ioi (0 : ℝ), (base x - w x) := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae]
      · have hsupp : Function.support (fun x => base x - w x) ∩ Set.Ioi 0 =
            Set.Ioi (0 : ℝ) := by
          rw [Set.inter_eq_right]
          intro x hx
          rw [Function.mem_support]
          exact ne_of_gt (hpoint x hx)
        rw [hsupp, Real.volume_Ioi, ← ENNReal.ofReal_zero]
        exact ENNReal.ofReal_lt_top
      · refine Filter.eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) ?_
        exact fun x hx => (hpoint x hx).le
      · exact hdiff
    rw [integral_sub hbase hw] at hpos
    change (∫ x in Set.Ioi (0 : ℝ), w x) <
      ∫ x in Set.Ioi (0 : ℝ), base x
    linarith
  · have hwzero : (∫ x in Set.Ioi (0 : ℝ), w x) = 0 :=
      integral_undef hw
    change (∫ x in Set.Ioi (0 : ℝ), w x) <
      ∫ x in Set.Ioi (0 : ℝ), base x
    rw [hwzero]
    have hm : 0 < moment n := by rw [moment_eq_factorial]; positivity
    simpa [weightedRemainderMoment, moment, w, base] using hm

private theorem f_exp_integrable (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * f a x) (Set.Ioi 0) := by
  have hmajor : IntegrableOn
      (fun x : ℝ => (1 / a) * Real.exp (-x)) (Set.Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).const_mul (1 / a)
  apply hmajor.mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := hx
    have hden : 0 < x + a := by linarith
    unfold f
    have h₁ : ContinuousAt (fun y : ℝ => Real.exp (-y)) x := by fun_prop
    have h₂ : ContinuousAt (fun y : ℝ => 1 / (y + a)) x := by
      fun_prop (disch := exact ne_of_gt hden)
    exact (h₁.mul h₂).continuousWithinAt
  · refine Filter.eventually_of_mem
      (self_mem_ae_restrict measurableSet_Ioi) ?_
    intro x hx
    have hxpos : 0 < x := hx
    have hexp : 0 < Real.exp (-x) := Real.exp_pos _
    have hden : 0 < x + a := by linarith
    have hdiv : Real.exp (-x) / (x + a) ≤ Real.exp (-x) / a :=
      (div_le_div_iff_of_pos_left hexp hden ha).2 (by linarith)
    simpa [f, Real.norm_eq_abs, abs_of_pos hexp, abs_of_pos ha,
      abs_of_pos hden, div_eq_mul_inv, mul_comm] using hdiv

private theorem taylor_exp_integrable (a : ℝ) (n : ℕ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-x) * taylorPartial a x n)
      (Set.Ioi 0) := by
  let g : ℕ → ℝ → ℝ := fun k x =>
    ((-1 : ℝ) ^ k / a ^ (k + 1)) * (Real.exp (-x) * x ^ k)
  have hg : IntegrableOn (fun x => ∑ k ∈ Finset.range n, g k x)
      (Set.Ioi 0) := by
    apply integrable_finset_sum
    intro k hk
    exact (moment_integrable k).const_mul _
  apply hg.congr_fun
  · intro x hx
    unfold taylorPartial g
    change (∑ k ∈ Finset.range n,
        (-1 : ℝ) ^ k / a ^ (k + 1) * (Real.exp (-x) * x ^ k)) =
      Real.exp (-x) *
        (∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * x ^ k / a ^ (k + 1))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  · exact measurableSet_Ioi

private theorem weighted_integrable_of_witness
    (a : ℝ) (ϑ : ℕ → ℝ → ℝ) (ha : 0 < a)
    (hϑ : RemainderWitness a ϑ) (n : ℕ) (hn : 1 ≤ n) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-x) * normalizedRemainder a ϑ n x * x ^ n)
      (Set.Ioi 0) := by
  let rhs : ℝ → ℝ := fun x =>
    ((-1 : ℝ) ^ n * a ^ (n + 1)) *
      (Real.exp (-x) * f a x - Real.exp (-x) * taylorPartial a x n)
  have hrhs : IntegrableOn rhs (Set.Ioi 0) := by
    exact ((f_exp_integrable a ha).sub (taylor_exp_integrable a n)).const_mul _
  apply hrhs.congr_fun
  · intro x hx
    have hw := hϑ.2 n hn x hx.le
    have ha0 : a ≠ 0 := ne_of_gt ha
    dsimp [rhs]
    rw [hw]
    field_simp [ha0]
    ring_nf
    rw [pow_mul]
    have hs : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
      rw [← sq_abs]
      simp
    rw [hs]
    ring
  · exact measurableSet_Ioi

private theorem weighted_pos_of_witness
    (a : ℝ) (ϑ : ℕ → ℝ → ℝ) (ha : 0 < a)
    (hϑ : RemainderWitness a ϑ) (n : ℕ) (hn : 1 ≤ n) :
    0 < weightedRemainderMoment a ϑ n := by
  have hint := weighted_integrable_of_witness a ϑ ha hϑ n hn
  unfold weightedRemainderMoment
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have hsupp : Function.support (fun x : ℝ =>
        Real.exp (-x) * normalizedRemainder a ϑ n x * x ^ n) ∩
        Set.Ioi 0 = Set.Ioi (0 : ℝ) := by
      rw [Set.inter_eq_right]
      intro x hx
      rw [Function.mem_support]
      exact mul_ne_zero
        (mul_ne_zero (Real.exp_ne_zero _)
          (ne_of_gt (normalized_pos a x ϑ ha hϑ.1 n hx.le)))
        (pow_ne_zero _ (ne_of_gt hx))
    rw [hsupp, Real.volume_Ioi, ← ENNReal.ofReal_zero]
    exact ENNReal.ofReal_lt_top
  · refine Filter.eventually_of_mem
      (self_mem_ae_restrict measurableSet_Ioi) ?_
    intro x hx
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos _).le
        (normalized_pos a x ϑ ha hϑ.1 n hx.le).le)
      (pow_nonneg hx.le n)
  · exact hint

private theorem target_eq_f_exp (a : ℝ) :
    targetIntegral a =
      ∫ x in Set.Ioi (0 : ℝ), f a x * Real.exp (-x) := by
  unfold targetIntegral f
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [div_eq_mul_inv]
  rw [add_comm x a]
  ring

private def momentRange (a : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k / a ^ (k + 1) * moment k

private theorem momentRange_eq_Icc (a : ℝ) (n : ℕ) :
    momentRange a n =
      ∑ k ∈ Finset.Icc 1 n,
        (-1 : ℝ) ^ (k - 1) / a ^ k * moment (k - 1) := by
  induction n with
  | zero => simp [momentRange]
  | succ n ih =>
      rw [momentRange, Finset.sum_range_succ]
      change momentRange a n + _ = _
      rw [ih]
      have hs : Finset.Icc 1 (n + 1) =
          insert (n + 1) (Finset.Icc 1 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hs, Finset.sum_insert]
      · simp only [Nat.add_sub_cancel]
        ring
      · simp

private theorem integral_taylorPartial (a : ℝ) (n : ℕ) :
    (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-x) * taylorPartial a x n) = momentRange a n := by
  unfold taylorPartial momentRange
  have heq : (fun x : ℝ => Real.exp (-x) *
        (∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * x ^ k / a ^ (k + 1))) =
      (fun x : ℝ => ∑ k ∈ Finset.range n,
        (-1 : ℝ) ^ k / a ^ (k + 1) * (Real.exp (-x) * x ^ k)) := by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [heq]
  rw [integral_finset_sum _ (fun k hk =>
    (moment_integrable k).const_mul ((-1 : ℝ) ^ k / a ^ (k + 1)))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul]
  rfl

private theorem target_expansion (a : ℝ) (ϑ : ℕ → ℝ → ℝ)
    (ha : 0 < a) (hϑ : RemainderWitness a ϑ)
    (n : ℕ) (hn : 1 ≤ n) :
    targetIntegral a =
      (∑ k ∈ Finset.Icc 1 n,
        (-1 : ℝ) ^ (k - 1) / a ^ k * moment (k - 1)) +
      (-1 : ℝ) ^ n / a ^ (n + 1) *
        weightedRemainderMoment a ϑ n := by
  let p : ℝ → ℝ := fun x => Real.exp (-x) * taylorPartial a x n
  let r : ℝ → ℝ := fun x =>
    Real.exp (-x) * normalizedRemainder a ϑ n x * x ^ n
  let c : ℝ := (-1 : ℝ) ^ n / a ^ (n + 1)
  have hp : IntegrableOn p (Set.Ioi 0) := by
    simpa [p] using taylor_exp_integrable a n
  have hr : IntegrableOn r (Set.Ioi 0) := by
    simpa [r] using weighted_integrable_of_witness a ϑ ha hϑ n hn
  have hcr : IntegrableOn (fun x => c * r x) (Set.Ioi 0) :=
    hr.const_mul c
  have heq : Set.EqOn (fun x => Real.exp (-x) * f a x)
      (fun x => p x + c * r x) (Set.Ioi 0) := by
    intro x hx
    have hw := hϑ.2 n hn x hx.le
    have ha0 : a ≠ 0 := ne_of_gt ha
    dsimp [p, r, c]
    rw [hw]
    field_simp [ha0]
  calc
    targetIntegral a =
        ∫ x in Set.Ioi (0 : ℝ), f a x * Real.exp (-x) :=
      target_eq_f_exp a
    _ = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * f a x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      ring
    _ = ∫ x in Set.Ioi (0 : ℝ), (p x + c * r x) := by
      exact setIntegral_congr_fun measurableSet_Ioi heq
    _ = (∫ x in Set.Ioi (0 : ℝ), p x) +
          ∫ x in Set.Ioi (0 : ℝ), c * r x := by
      exact integral_add hp hcr
    _ = momentRange a n + c * weightedRemainderMoment a ϑ n := by
      rw [integral_const_mul]
      simp only [p, r, weightedRemainderMoment, integral_taylorPartial]
    _ = _ := by
      rw [momentRange_eq_Icc]

private theorem momentRange_eq_factorialPartial (a : ℝ) (n : ℕ) :
    momentRange a n = factorialPartial a n := by
  unfold momentRange factorialPartial
  apply Finset.sum_congr rfl
  intro k hk
  rw [moment_eq_factorial]
  ring

private theorem weighted_eq_theta_mul_factorial
    (a : ℝ) (ϑ : ℕ → ℝ → ℝ) (n : ℕ) :
    weightedRemainderMoment a ϑ n =
      thetaFactor a ϑ n * (n.factorial : ℝ) := by
  unfold thetaFactor
  have hfac : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hfac]

private theorem target_factorial_expansion
    (a : ℝ) (ϑ : ℕ → ℝ → ℝ) (ha : 0 < a)
    (hϑ : RemainderWitness a ϑ) (n : ℕ) (hn : 1 ≤ n) :
    targetIntegral a = factorialPartial a n +
      (-1 : ℝ) ^ n * (n.factorial : ℝ) / a ^ (n + 1) *
        thetaFactor a ϑ n := by
  rw [target_expansion a ϑ ha hϑ n hn]
  rw [← momentRange_eq_Icc, momentRange_eq_factorialPartial]
  rw [weighted_eq_theta_mul_factorial]
  ring

private theorem thetaFactor_pos_of_witness
    (a : ℝ) (ϑ : ℕ → ℝ → ℝ) (ha : 0 < a)
    (hϑ : RemainderWitness a ϑ) (n : ℕ) (hn : 1 ≤ n) :
    0 < thetaFactor a ϑ n := by
  unfold thetaFactor
  exact div_pos (weighted_pos_of_witness a ϑ ha hϑ n hn) (by positivity)

private theorem thetaFactor_lt_one_of_witness
    (a : ℝ) (ϑ : ℕ → ℝ → ℝ) (ha : 0 < a)
    (hϑ : RemainderWitness a ϑ) (n : ℕ) :
    thetaFactor a ϑ n < 1 := by
  unfold thetaFactor
  apply (div_lt_one (by positivity : (0 : ℝ) < (n.factorial : ℝ))).2
  have hlt := weighted_lt_moment a ϑ ha hϑ.1 n
  rw [moment_eq_factorial] at hlt
  exact hlt

private theorem hundred_pow_inv_eq_ten_zpow (k : ℕ) :
    1 / (100 : ℝ) ^ (k + 1) =
      (10 : ℝ) ^ (-(2 : ℤ) * (k + 1 : ℤ)) := by
  calc
    1 / (100 : ℝ) ^ (k + 1) =
        ((10 : ℝ) ^ (2 * (k + 1)))⁻¹ := by
      congr 1
      norm_num [pow_mul]
    _ = (10 : ℝ) ^ (-((2 * (k + 1) : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_natCast]
    _ = (10 : ℝ) ^ (-(2 : ℤ) * (k + 1 : ℤ)) := by
      congr 1

private noncomputable def chosenTheta (a : ℝ) (ha : 0 < a) :
    ℕ → ℝ → ℝ := fun n x =>
  if h : 1 ≤ n ∧ 0 ≤ x then
    Classical.choose (taylor_normalized_exists a x ha n h.1 h.2)
  else 1 / 2

private theorem chosenTheta_spec (a x : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 1 ≤ n) (hx : 0 ≤ x) :
    chosenTheta a ha n x ∈ Set.Ioo (0 : ℝ) 1 ∧
      f a x = taylorPartial a x n +
        (-1 : ℝ) ^ n * normalizedRemainder a (chosenTheta a ha) n x *
          (x ^ n / a ^ (n + 1)) := by
  let h := taylor_normalized_exists a x ha n hn hx
  have hs := Classical.choose_spec h
  have hif : 1 ≤ n ∧ 0 ≤ x := ⟨hn, hx⟩
  simpa [chosenTheta, hif, normalizedRemainder] using hs

private theorem chosenTheta_witness (a : ℝ) (ha : 0 < a) :
    RemainderWitness a (chosenTheta a ha) := by
  constructor
  · intro n x hx
    by_cases hn : 1 ≤ n
    · exact (chosenTheta_spec a x ha n hn hx).1
    · have hn0 : n = 0 := by omega
      subst n
      simp [chosenTheta, hx]
      norm_num
  · intro n hn x hx
    exact (chosenTheta_spec a x ha n hn hx).2

private theorem target_hundred_expansion (ϑ : ℕ → ℝ → ℝ)
    (hϑ : RemainderWitness 100 ϑ) (n : ℕ) (hn : 1 ≤ n) :
    targetIntegral 100 =
      (∑ k ∈ Finset.range n,
        (-1 : ℝ) ^ k * (k.factorial : ℝ) *
          10 ^ (-(2 : ℤ) * (k + 1 : ℤ))) +
      (-1 : ℝ) ^ n * thetaFactor 100 ϑ n * (n.factorial : ℝ) *
        10 ^ (-(2 : ℤ) * (n + 1 : ℤ)) := by
  rw [target_factorial_expansion 100 ϑ (by norm_num) hϑ n hn]
  unfold factorialPartial
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [← hundred_pow_inv_eq_ten_zpow]
    ring
  · rw [← hundred_pow_inv_eq_ten_zpow]
    ring

private theorem error_bound_of_witness (ϑ : ℕ → ℝ → ℝ)
    (hϑ : RemainderWitness 100 ϑ) :
    |thetaFactor 100 ϑ 2 * (2 : ℝ) * 10 ^ (-(6 : ℤ))| <
      2 * 10 ^ (-(6 : ℤ)) := by
  have ht0 := thetaFactor_pos_of_witness 100 ϑ (by norm_num) hϑ 2 (by norm_num)
  have ht1 := thetaFactor_lt_one_of_witness 100 ϑ (by norm_num) hϑ 2
  have hz : 0 < (10 : ℝ) ^ (-(6 : ℤ)) := zpow_pos (by norm_num) _
  rw [abs_of_pos (mul_pos (mul_pos ht0 (by norm_num)) hz)]
  have htwo : thetaFactor 100 ϑ 2 * 2 < 2 := by nlinarith
  exact mul_lt_mul_of_pos_right htwo hz

private theorem target_hundred_numerical_bound :
    |targetIntegral 100 - 0.01 + 0.0001| ≤ 0.000002 := by
  let ϑ := chosenTheta 100 (by norm_num)
  have hw : RemainderWitness 100 ϑ := chosenTheta_witness 100 (by norm_num)
  have hform := target_factorial_expansion 100 ϑ (by norm_num) hw 2 (by norm_num)
  have ht0 := thetaFactor_pos_of_witness 100 ϑ (by norm_num) hw 2 (by norm_num)
  have ht1 := thetaFactor_lt_one_of_witness 100 ϑ (by norm_num) hw 2
  have hpartial : factorialPartial 100 2 = (99 / 10000 : ℝ) := by
    norm_num [factorialPartial, Finset.sum_range_succ]
  have herr : targetIntegral 100 - 0.01 + 0.0001 =
      thetaFactor 100 ϑ 2 * 2 / (100 : ℝ) ^ 3 := by
    rw [hpartial] at hform
    norm_num at hform
    rw [hform]
    ring
  rw [herr, abs_of_pos (by positivity)]
  calc
    thetaFactor 100 ϑ 2 * 2 / (100 : ℝ) ^ 3 ≤
        2 / (100 : ℝ) ^ 3 := by
      apply (div_le_div_iff_of_pos_right (by positivity)).2
      nlinarith
    _ = 0.000002 := by norm_num

theorem gap1 (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) :
    f a x = 1 / (x + a) := by
  rfl

theorem gap2 (a x : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 1 ≤ n) (hx : 0 ≤ x) :
    ∃ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 ∧
      1 / (x + a) =
        (∑ k ∈ Finset.range n,
          nthDeriv (f a) k 0 / (k.factorial : ℝ) * x ^ k) +
        nthDeriv (f a) n (θ * x) / (n.factorial : ℝ) * x ^ n := by
  simpa [f] using taylor_exists a x ha n hn hx

theorem gap3 (a x : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 1 ≤ n) (hx : 0 ≤ x) :
    ∃ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 ∧
      f a x =
        (∑ k ∈ Finset.range n,
          nthDeriv (f a) k 0 / (k.factorial : ℝ) * x ^ k) +
        nthDeriv (f a) n (θ * x) / (n.factorial : ℝ) * x ^ n := by
  exact taylor_exists a x ha n hn hx

theorem gap4 (a x : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 1 ≤ n) (hx : 0 ≤ x) :
    ∃ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 ∧
      f a x =
        taylorPartial a x n +
          (-1 : ℝ) ^ n * x ^ n / (a + θ * x) ^ (n + 1) := by
  exact taylor_explicit_exists a x ha n hn hx

theorem gap5 (a x : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 1 ≤ n) (hx : 0 ≤ x) :
    ∃ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 ∧
      f a x =
        taylorPartial a x n +
          (-1 : ℝ) ^ n * (a / (a + θ * x)) ^ (n + 1) *
            (x ^ n / a ^ (n + 1)) := by
  exact taylor_normalized_exists a x ha n hn hx

theorem gap6 (a x : ℝ) (ϑ : ℕ → ℝ → ℝ)
    (ha : 0 < a) (hϑ : ThetaAdmissible ϑ)
    (n : ℕ) (hx : 0 ≤ x) :
    0 < normalizedRemainder a ϑ n x := by
  exact normalized_pos a x ϑ ha hϑ n hx

theorem gap7 (a x : ℝ) (ϑ : ℕ → ℝ → ℝ)
    (ha : 0 < a) (hϑ : ThetaAdmissible ϑ)
    (n : ℕ) (hx : 0 < x) :
    normalizedRemainder a ϑ n x < 1 := by
  exact normalized_lt_one a x ϑ ha hϑ n hx

theorem gap8 (x : ℝ) (hx : 0 ≤ x) : (0 : ℝ) < 1 := by
  norm_num

theorem gap9 (n : ℕ) :
    moment n = (n.factorial : ℝ) := by
  exact moment_eq_factorial n

theorem gap10 (a : ℝ) (ϑ : ℕ → ℝ → ℝ)
    (ha : 0 < a) (hϑ : RemainderWitness a ϑ)
    (n : ℕ) (hn : 1 ≤ n) :
    0 < weightedRemainderMoment a ϑ n := by
  exact weighted_pos_of_witness a ϑ ha hϑ n hn

theorem gap11 (a : ℝ) (ϑ : ℕ → ℝ → ℝ)
    (ha : 0 < a) (hϑ : ThetaAdmissible ϑ) (n : ℕ) :
    weightedRemainderMoment a ϑ n < moment n := by
  exact weighted_lt_moment a ϑ ha hϑ n

theorem gap12 (n : ℕ) :
    moment n = (n.factorial : ℝ) := by
  exact moment_eq_factorial n

theorem gap13 (n : ℕ) : (0 : ℝ) < (n.factorial : ℝ) := by
  positivity

theorem gap14 (a : ℝ) (ϑ : ℕ → ℝ → ℝ)
    (ha : 0 < a) (hϑ : RemainderWitness a ϑ)
    (n : ℕ) (hn : 1 ≤ n) :
    weightedRemainderMoment a ϑ n =
      thetaFactor a ϑ n * (n.factorial : ℝ) ∧
    0 < thetaFactor a ϑ n ∧ thetaFactor a ϑ n < 1 := by
  exact ⟨weighted_eq_theta_mul_factorial a ϑ n,
    thetaFactor_pos_of_witness a ϑ ha hϑ n hn,
    thetaFactor_lt_one_of_witness a ϑ ha hϑ n⟩

theorem gap15 (a : ℝ) (ha : 0 < a) :
    targetIntegral a =
      ∫ x in Set.Ioi (0 : ℝ), f a x * Real.exp (-x) := by
  exact target_eq_f_exp a

theorem gap16 (a : ℝ) (ϑ : ℕ → ℝ → ℝ)
    (ha : 0 < a) (hϑ : RemainderWitness a ϑ)
    (n : ℕ) (hn : 1 ≤ n) :
    targetIntegral a =
      (∑ k ∈ Finset.Icc 1 n,
        (-1 : ℝ) ^ (k - 1) / a ^ k * moment (k - 1)) +
      (-1 : ℝ) ^ n / a ^ (n + 1) *
        weightedRemainderMoment a ϑ n := by
  exact target_expansion a ϑ ha hϑ n hn

theorem gap17 (a : ℝ) (ϑ : ℕ → ℝ → ℝ)
    (ha : 0 < a) (hϑ : RemainderWitness a ϑ)
    (n : ℕ) (hn : 1 ≤ n) :
    targetIntegral a =
      factorialPartial a n +
        (-1 : ℝ) ^ n * (n.factorial : ℝ) / a ^ (n + 1) *
          thetaFactor a ϑ n := by
  exact target_factorial_expansion a ϑ ha hϑ n hn

theorem gap18 (a : ℝ) (ϑ : ℕ → ℝ → ℝ)
    (ha : a = 100) (hϑ : RemainderWitness 100 ϑ)
    (n : ℕ) (hn : 1 ≤ n) :
    targetIntegral 100 =
      (∑ k ∈ Finset.range n,
        (-1 : ℝ) ^ k * (k.factorial : ℝ) * 10 ^ (-(2 : ℤ) * (k + 1 : ℤ))) +
      (-1 : ℝ) ^ n * thetaFactor 100 ϑ n * (n.factorial : ℝ) *
        10 ^ (-(2 : ℤ) * (n + 1 : ℤ)) := by
  exact target_hundred_expansion ϑ hϑ n hn

theorem gap19 (a : ℝ) (ϑ : ℕ → ℝ → ℝ)
    (ha : a = 100) (hϑ : RemainderWitness 100 ϑ) :
    ∃ Error : ℝ,
      Error = thetaFactor 100 ϑ 2 * (2 : ℝ) * 10 ^ (-(6 : ℤ)) := by
  exact ⟨_, rfl⟩

theorem gap20 (a : ℝ) (ϑ : ℕ → ℝ → ℝ)
    (ha : a = 100) (hϑ : RemainderWitness 100 ϑ) :
    ∃ Error : ℝ,
      Error = thetaFactor 100 ϑ 2 * (2 : ℝ) * 10 ^ (-(6 : ℤ)) ∧
      |Error| < 2 * 10 ^ (-(6 : ℤ)) := by
  refine ⟨thetaFactor 100 ϑ 2 * (2 : ℝ) * 10 ^ (-(6 : ℤ)), rfl, ?_⟩
  exact error_bound_of_witness ϑ hϑ

theorem gap21 :
    |targetIntegral 100 - 0.01 + 0.0001| ≤ 0.000002 := by
  exact target_hundred_numerical_bound

theorem gap22 (a : ℝ) (ϑ : ℕ → ℝ → ℝ)
    (ha : 0 < a) (hϑ : RemainderWitness a ϑ)
    (n : ℕ) (hn : 1 ≤ n) :
    targetIntegral a =
      factorialPartial a n +
        (-1 : ℝ) ^ n *
          (thetaFactor a ϑ n * (n.factorial : ℝ)) / a ^ (n + 1) := by
  rw [target_factorial_expansion a ϑ ha hϑ n hn]
  ring

end

end ProofGap.Exercise3050
