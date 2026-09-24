import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Order.Floor

namespace ProofGap.Exercise2899

noncomputable section

open Filter
open scoped BigOperators Topology

def centeredTerm (a : ℕ → ℝ) (x₀ x : ℝ) (n : ℕ) : ℝ :=
  a n * (x - x₀) ^ n

def derivativeSeriesTerm
    (a : ℕ → ℝ) (x₀ : ℝ) (m : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  let n : ℕ := m + k
  (Nat.factorial n : ℝ) / (Nat.factorial k : ℝ) *
    a n * (x - x₀) ^ k

def derivativeMajorantTerm
    (a : ℕ → ℝ) (m : ℕ) (L : ℝ) (k : ℕ) : ℝ :=
  let n : ℕ := m + k
  (Nat.factorial n : ℝ) / (Nat.factorial k : ℝ) *
    |a n| * L ^ k

def exponentialMajorantTerm (M L : ℝ) (k : ℕ) : ℝ :=
  M * L ^ k / (Nat.factorial k : ℝ)

def taylorTerm (f : ℝ → ℝ) (c x : ℝ) (k : ℕ) : ℝ :=
  iteratedDeriv k f c / (Nat.factorial k : ℝ) * (x - c) ^ k

def taylorRemainder (f : ℝ → ℝ) (n : ℕ) (c x : ℝ) : ℝ :=
  f x - ∑ k ∈ Finset.range (n + 1), taylorTerm f c x k

def EntireCoefficientBound (a : ℕ → ℝ) (M : ℝ) : Prop :=
  0 < M ∧ ∀ n : ℕ, |(Nat.factorial n : ℝ) * a n| < M

theorem gap1
    (a : ℕ → ℝ) (M : ℝ) (hM : EntireCoefficientBound a M) :
    ∀ n : ℕ, 0 < n → |a n| < M / (Nat.factorial n : ℝ) := by
  intro n hn
  have hfac : (0 : ℝ) < Nat.factorial n := by positivity
  apply (lt_div_iff₀ hfac).2
  have h := hM.2 n
  rw [abs_mul, abs_of_pos hfac] at h
  simpa [mul_comm] using h

theorem gap2
    (a : ℕ → ℝ) (x₀ M : ℝ) (hM : EntireCoefficientBound a M) :
    ∀ n : ℕ, ∀ x N : ℝ, 0 < N →
      x₀ ∈ Set.Icc (-N) N → x ∈ Set.Icc (-N) N →
        |a n * (x - x₀) ^ n| <
          M / (Nat.factorial n : ℝ) * (2 * N) ^ n := by
  intro n x N hN hx₀ hx
  have hfac : (0 : ℝ) < Nat.factorial n := by positivity
  have ha : |a n| < M / (Nat.factorial n : ℝ) := by
    apply (lt_div_iff₀ hfac).2
    have h := hM.2 n
    rw [abs_mul, abs_of_pos hfac] at h
    simpa [mul_comm] using h
  have hxabs : |x| ≤ N := (abs_le).2 hx
  have hx₀abs : |x₀| ≤ N := (abs_le).2 hx₀
  have hdist : |x - x₀| ≤ 2 * N := by
    calc
      |x - x₀| ≤ |x| + |x₀| := abs_sub x x₀
      _ ≤ N + N := add_le_add hxabs hx₀abs
      _ = 2 * N := by ring
  rw [abs_mul, abs_pow]
  have hpow : |x - x₀| ^ n ≤ (2 * N) ^ n :=
    pow_le_pow_left₀ (abs_nonneg _) hdist n
  have hmajor : 0 < (2 * N) ^ n := pow_pos (by positivity) n
  calc
    |a n| * |x - x₀| ^ n ≤ |a n| * (2 * N) ^ n :=
      mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    _ < (M / (Nat.factorial n : ℝ)) * (2 * N) ^ n :=
      mul_lt_mul_of_pos_right ha hmajor

theorem gap3 (x₀ M : ℝ) :
    ∀ N : ℝ, 0 ≤ N → x₀ ∈ Set.Icc (-N) N →
      Summable (fun n : ℕ =>
        M / (Nat.factorial n : ℝ) * (2 * N) ^ n) := by
  intro N hN hx₀
  have hs := (Real.summable_pow_div_factorial (2 * N)).mul_left M
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hs

theorem gap4
    (a : ℕ → ℝ) (f : ℝ → ℝ) (x₀ M : ℝ)
    (hf : ∀ x, f x = ∑' n, centeredTerm a x₀ x n)
    (hM : EntireCoefficientBound a M) :
    ∀ N : ℝ, 0 ≤ N →
      TendstoUniformlyOn
        (fun k x => ∑ n ∈ Finset.range k, centeredTerm a x₀ x n)
        f atTop (Set.Icc (-N) N) := by
  intro N hN
  let L := N + |x₀|
  have hL : 0 ≤ L := add_nonneg hN (abs_nonneg x₀)
  have hu : Summable (fun n : ℕ =>
      M / (Nat.factorial n : ℝ) * L ^ n) := by
    have hs := (Real.summable_pow_div_factorial L).mul_left M
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hs
  have hbound : ∀ n x, x ∈ Set.Icc (-N) N →
      ‖centeredTerm a x₀ x n‖ ≤
        M / (Nat.factorial n : ℝ) * L ^ n := by
    intro n x hx
    have hfac : (0 : ℝ) < Nat.factorial n := by positivity
    have ha : |a n| ≤ M / (Nat.factorial n : ℝ) := by
      apply (le_div_iff₀ hfac).2
      have h := (hM.2 n).le
      rw [abs_mul, abs_of_pos hfac] at h
      simpa [mul_comm] using h
    have hxabs : |x| ≤ N := (abs_le).2 hx
    have hdist : |x - x₀| ≤ L := by
      calc
        |x - x₀| ≤ |x| + |x₀| := by
          simpa [Real.norm_eq_abs] using norm_sub_le x x₀
        _ ≤ N + |x₀| := add_le_add hxabs le_rfl
        _ = L := rfl
    simp only [centeredTerm, norm_mul, Real.norm_eq_abs, norm_pow]
    have hcoef0 : 0 ≤ M / (Nat.factorial n : ℝ) :=
      div_nonneg hM.1.le hfac.le
    exact mul_le_mul ha (pow_le_pow_left₀ (abs_nonneg _) hdist n)
      (by positivity) hcoef0
  have hfun : f = fun x => ∑' n, centeredTerm a x₀ x n := funext hf
  rw [hfun]
  exact tendstoUniformlyOn_tsum_nat hu hbound

theorem gap5
    (a : ℕ → ℝ) (M : ℝ) (hM : EntireCoefficientBound a M) :
    ∀ x : ℝ, Summable (fun n : ℕ => a n * x ^ n) := by
  intro x
  have hmajor := (Real.summable_pow_div_factorial |x|).mul_left M
  have hnorm : Summable (fun n : ℕ => ‖a n * x ^ n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hmajor
    intro n
    have hfac : (0 : ℝ) < Nat.factorial n := by positivity
    have ha : |a n| < M / (Nat.factorial n : ℝ) := by
      apply (lt_div_iff₀ hfac).2
      have h := hM.2 n
      rw [abs_mul, abs_of_pos hfac] at h
      simpa [mul_comm] using h
    simp only [norm_mul, Real.norm_eq_abs, norm_pow]
    calc
      |a n| * |x| ^ n ≤ (M / (Nat.factorial n : ℝ)) * |x| ^ n :=
        mul_le_mul_of_nonneg_right ha.le (by positivity)
      _ = M * (|x| ^ n / (Nat.factorial n : ℝ)) := by ring
  exact hnorm.of_norm

private def coefficientFPowerSeries (a : ℕ → ℝ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ a

private theorem coefficientFPowerSeries_radius
    (a : ℕ → ℝ) (M : ℝ) (hM : EntireCoefficientBound a M) :
    (coefficientFPowerSeries a).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  have hs : Summable (fun n => ‖a n * (r : ℝ) ^ n‖) :=
    summable_norm_iff.mpr (gap5 a M hM (r : ℝ))
  simpa [coefficientFPowerSeries,
    FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
    NNReal.norm_eq] using hs

private theorem centered_hasFPowerSeriesOnBall
    (a : ℕ → ℝ) (x₀ M : ℝ) (hM : EntireCoefficientBound a M) :
    HasFPowerSeriesOnBall
      (fun x => ∑' n, centeredTerm a x₀ x n)
      (coefficientFPowerSeries a) x₀ ⊤ := by
  refine ⟨by rw [coefficientFPowerSeries_radius a M hM], by simp, ?_⟩
  intro x hx
  have hs := (gap5 a M hM x).hasSum
  convert hs using 1
  · funext n
    unfold coefficientFPowerSeries
    rw [FormalMultilinearSeries.ofScalars_apply_eq]
    simp [smul_eq_mul]
  · simp [centeredTerm]

private theorem function_hasFPowerSeriesOnBall
    (a : ℕ → ℝ) (f : ℝ → ℝ) (x₀ M : ℝ)
    (hf : ∀ x, f x = ∑' n, centeredTerm a x₀ x n)
    (hM : EntireCoefficientBound a M) :
    HasFPowerSeriesOnBall f (coefficientFPowerSeries a) x₀ ⊤ := by
  exact (centered_hasFPowerSeriesOnBall a x₀ M hM).congr
    (fun x hx => (hf x).symm)

private theorem coefficient_changeOriginSeries_apply
    (a : ℕ → ℝ) (y : ℝ) (m k : ℕ) :
    ((coefficientFPowerSeries a).changeOriginSeries m k (fun _ => y))
        (fun _ => 1) =
      (Nat.choose (m + k) k : ℝ) * a (m + k) * y ^ k := by
  unfold FormalMultilinearSeries.changeOriginSeries
  simp only [ContinuousMultilinearMap.sum_apply]
  rw [Finset.sum_eq_card_nsmul
    (b := a (m + k) * y ^ k)]
  · simp only [nsmul_eq_mul, Finset.card_univ]
    rw [Fintype.card_subtype, ← Finset.powerset_univ,
      ← Finset.powersetCard_eq_filter, Finset.card_powersetCard]
    simp only [Finset.card_univ, Fintype.card_fin]
    ring
  · intro i hi
    rw [FormalMultilinearSeries.changeOriginSeriesTerm_apply]
    unfold coefficientFPowerSeries
    simp [FormalMultilinearSeries.ofScalars, smul_eq_mul, List.prod_ofFn,
      Finset.prod_piecewise, i.prop]

private theorem coefficient_changeOrigin_apply
    (a : ℕ → ℝ) (M : ℝ) (hM : EntireCoefficientBound a M)
    (y : ℝ) (m : ℕ) :
    ((coefficientFPowerSeries a).changeOrigin y m) (fun _ => 1) =
      ∑' k : ℕ,
        (Nat.choose (m + k) k : ℝ) * a (m + k) * y ^ k := by
  unfold FormalMultilinearSeries.changeOrigin FormalMultilinearSeries.sum
  have hradius :
      ((coefficientFPowerSeries a).changeOriginSeries m).radius = ⊤ := by
    apply top_unique
    rw [← coefficientFPowerSeries_radius a M hM]
    exact (coefficientFPowerSeries a).le_changeOriginSeries_radius m
  have hs : Summable (fun n : ℕ =>
      ((coefficientFPowerSeries a).changeOriginSeries m n) fun _ => y) := by
    apply (coefficientFPowerSeries a).changeOriginSeries m |>.summable
    simp [hradius]
  rw [← (ContinuousMultilinearMap.hasSum_eval hs.hasSum
    (fun _ => 1)).tsum_eq]
  apply tsum_congr
  intro k
  exact coefficient_changeOriginSeries_apply a y m k

private theorem iteratedDeriv_eq_derivativeSeries
    (a : ℕ → ℝ) (f : ℝ → ℝ) (x₀ M : ℝ)
    (hf : ∀ x, f x = ∑' n, centeredTerm a x₀ x n)
    (hM : EntireCoefficientBound a M) (m : ℕ) (x : ℝ) :
    iteratedDeriv m f x = ∑' k, derivativeSeriesTerm a x₀ m x k := by
  have h := function_hasFPowerSeriesOnBall a f x₀ M hf hM
  have hc0 := h.changeOrigin (y := x - x₀) (by simp)
  have hc : HasFPowerSeriesOnBall f
      ((coefficientFPowerSeries a).changeOrigin (x - x₀)) x ⊤ := by
    simpa using hc0
  have hfact := hc.factorial_smul (1 : ℝ) m
  simp only [nsmul_eq_mul, smul_eq_mul,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one] at hfact
  rw [coefficient_changeOrigin_apply a M hM] at hfact
  calc
    iteratedDeriv m f x = (Nat.factorial m : ℝ) *
        ∑' k, (Nat.choose (m + k) k : ℝ) *
          a (m + k) * (x - x₀) ^ k := by
      simpa using hfact.symm
    _ = ∑' k, (Nat.factorial m : ℝ) *
        ((Nat.choose (m + k) k : ℝ) *
          a (m + k) * (x - x₀) ^ k) := by
      rw [tsum_mul_left]
    _ = ∑' k, derivativeSeriesTerm a x₀ m x k := by
      apply tsum_congr
      intro k
      have hnat := Nat.add_choose_mul_factorial_mul_factorial m k
      have hcoef :
          (Nat.factorial m : ℝ) * (Nat.choose (m + k) k : ℝ) =
            (Nat.factorial (m + k) : ℝ) / (Nat.factorial k : ℝ) := by
        apply (eq_div_iff (by positivity : (Nat.factorial k : ℝ) ≠ 0)).2
        norm_cast
        simpa [mul_assoc, mul_comm, mul_left_comm] using hnat
      unfold derivativeSeriesTerm
      dsimp
      calc
        (Nat.factorial m : ℝ) *
            ((Nat.choose (m + k) k : ℝ) *
              a (m + k) * (x - x₀) ^ k) =
            ((Nat.factorial m : ℝ) * (Nat.choose (m + k) k : ℝ)) *
              a (m + k) * (x - x₀) ^ k := by ring
        _ = (Nat.factorial (m + k) : ℝ) / (Nat.factorial k : ℝ) *
              a (m + k) * (x - x₀) ^ k := by rw [hcoef]

theorem gap6
    (a : ℕ → ℝ) (f : ℝ → ℝ) (x₀ M : ℝ)
    (hf : ∀ x, f x = ∑' n, centeredTerm a x₀ x n)
    (hM : EntireCoefficientBound a M) :
    ContDiff ℝ ⊤ f := by
  have h := function_hasFPowerSeriesOnBall a f x₀ M hf hM
  have ha : AnalyticOnNhd ℝ f Set.univ := by
    simpa using h.analyticOnNhd
  exact ha.contDiff

theorem gap7
    (a : ℕ → ℝ) (f : ℝ → ℝ) (x₀ M : ℝ)
    (hf : ∀ x, f x = ∑' n, centeredTerm a x₀ x n)
    (hM : EntireCoefficientBound a M) :
    ∀ m : ℕ, ∀ x : ℝ,
      iteratedDeriv m f x =
        ∑' k, derivativeSeriesTerm a x₀ m x k := by
  exact iteratedDeriv_eq_derivativeSeries a f x₀ M hf hM

theorem gap8 (x₀ : ℝ) :
    ∀ x c R : ℝ, 0 < R → |x - c| < R →
      |x - x₀| ≤ |x - c| + |c - x₀| := by
  intro x c R hR hx
  rw [show x - x₀ = (x - c) + (c - x₀) by ring]
  simpa [Real.norm_eq_abs] using norm_add_le (x - c) (c - x₀)

theorem gap9 (x₀ : ℝ) :
    ∀ x c R L : ℝ, L = R + |c - x₀| →
      0 < R → |x - c| < R →
        |x - c| + |c - x₀| < L := by
  intro x c R L hL hR hx
  rw [hL]
  linarith

theorem gap10 (x₀ : ℝ) :
    ∀ x c R L : ℝ, L = R + |c - x₀| →
      0 < R → |x - c| < R → |x - x₀| < L := by
  intro x c R L hL hR hx
  exact lt_of_le_of_lt (gap8 x₀ x c R hR hx)
    (gap9 x₀ x c R L hL hR hx)

private theorem derivativeMajorantTerm_le_expTerm
    (a : ℕ → ℝ) (M : ℝ) (hM : EntireCoefficientBound a M)
    (m : ℕ) (L : ℝ) (hL : 0 ≤ L) (k : ℕ) :
    derivativeMajorantTerm a m L k ≤
      M * (L ^ k / (Nat.factorial k : ℝ)) := by
  let n := m + k
  have hfacn : (0 : ℝ) < Nat.factorial n := by positivity
  have hcoef : (Nat.factorial n : ℝ) * |a n| ≤ M := by
    have h := (hM.2 n).le
    rw [abs_mul, abs_of_pos hfacn] at h
    exact h
  unfold derivativeMajorantTerm
  dsimp [n]
  calc
    (Nat.factorial n : ℝ) / (Nat.factorial k : ℝ) * |a n| * L ^ k =
        ((Nat.factorial n : ℝ) * |a n|) *
          (L ^ k / (Nat.factorial k : ℝ)) := by ring
    _ ≤ M * (L ^ k / (Nat.factorial k : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)

private theorem summable_derivativeMajorantTerm
    (a : ℕ → ℝ) (M : ℝ) (hM : EntireCoefficientBound a M)
    (m : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    Summable (derivativeMajorantTerm a m L) := by
  have hmajor := (Real.summable_pow_div_factorial L).mul_left M
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor
  · intro k
    unfold derivativeMajorantTerm
    dsimp
    positivity
  · exact derivativeMajorantTerm_le_expTerm a M hM m L hL

private theorem norm_derivativeSeriesTerm_le_majorant
    (a : ℕ → ℝ) (x₀ : ℝ) (m : ℕ) (x L : ℝ)
    (hx : |x - x₀| ≤ L) (k : ℕ) :
    ‖derivativeSeriesTerm a x₀ m x k‖ ≤
      derivativeMajorantTerm a m L k := by
  let n := m + k
  unfold derivativeSeriesTerm derivativeMajorantTerm
  dsimp [n]
  simp only [Real.norm_eq_abs, abs_mul, abs_pow]
  rw [abs_of_nonneg (by positivity :
    0 ≤ (Nat.factorial n : ℝ) / (Nat.factorial k : ℝ))]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg _) hx k) (by positivity)

theorem gap11
    (a : ℕ → ℝ) (f : ℝ → ℝ) (x₀ M : ℝ)
    (hf : ∀ x, f x = ∑' n, centeredTerm a x₀ x n)
    (hM : EntireCoefficientBound a M) :
    ∀ x c L : ℝ, |x - x₀| < L → ∀ m : ℕ,
      |iteratedDeriv m f x| ≤
        ∑' k, derivativeMajorantTerm a m L k := by
  intro x c L hx m
  have hL : 0 ≤ L := (abs_nonneg _).trans hx.le
  have hmajor := summable_derivativeMajorantTerm a M hM m L hL
  have hnorm : Summable (fun k => ‖derivativeSeriesTerm a x₀ m x k‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_ hmajor
    intro k
    exact norm_derivativeSeriesTerm_le_majorant a x₀ m x L hx.le k
  rw [gap7 a f x₀ M hf hM m x]
  calc
    |∑' k, derivativeSeriesTerm a x₀ m x k| ≤
        ∑' k, ‖derivativeSeriesTerm a x₀ m x k‖ := by
      simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k, derivativeMajorantTerm a m L k :=
      hnorm.tsum_mono hmajor
        (norm_derivativeSeriesTerm_le_majorant a x₀ m x L hx.le)

theorem gap12
    (a : ℕ → ℝ) (M : ℝ) (hM : EntireCoefficientBound a M) :
    ∀ m : ℕ, ∀ L : ℝ, 0 ≤ L →
      (∑' k, derivativeMajorantTerm a m L k) ≤
        M * (∑' s : ℕ, L ^ s / (Nat.factorial s : ℝ)) := by
  intro m L hL
  have hmajor := summable_derivativeMajorantTerm a M hM m L hL
  have hexp := (Real.summable_pow_div_factorial L).mul_left M
  calc
    (∑' k, derivativeMajorantTerm a m L k) ≤
        ∑' k, M * (L ^ k / (Nat.factorial k : ℝ)) :=
      hmajor.tsum_mono hexp
        (derivativeMajorantTerm_le_expTerm a M hM m L hL)
    _ = M * (∑' s : ℕ, L ^ s / (Nat.factorial s : ℝ)) := by
      rw [tsum_mul_left]

theorem gap13
    (a : ℕ → ℝ) (f : ℝ → ℝ) (x₀ M : ℝ)
    (hf : ∀ x, f x = ∑' n, centeredTerm a x₀ x n)
    (hM : EntireCoefficientBound a M) :
    ∀ x L : ℝ, |x - x₀| < L → 0 ≤ L → ∀ m : ℕ,
      |iteratedDeriv m f x| ≤
        M * (∑' s : ℕ, L ^ s / (Nat.factorial s : ℝ)) := by
  intro x L hx hL m
  exact (gap11 a f x₀ M hf hM x x L hx m).trans
    (gap12 a M hM m L hL)

theorem gap14
    (a : ℕ → ℝ) (f : ℝ → ℝ) (x₀ M : ℝ)
    (hf : ∀ x, f x = ∑' n, centeredTerm a x₀ x n)
    (hM : EntireCoefficientBound a M) :
    ∀ x L : ℝ, |x - x₀| < L → 0 ≤ L → ∀ m : ℕ,
      |iteratedDeriv m f x| ≤ M * Real.exp L := by
  intro x L hx hL m
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  exact gap13 a f x₀ M hf hM x L hx hL m

private theorem taylorTerm_hasSum
    (a : ℕ → ℝ) (f : ℝ → ℝ) (x₀ M : ℝ)
    (hf : ∀ x, f x = ∑' n, centeredTerm a x₀ x n)
    (hM : EntireCoefficientBound a M) (x c : ℝ) :
    HasSum (taylorTerm f c x) (f x) := by
  have h := function_hasFPowerSeriesOnBall a f x₀ M hf hM
  have hc0 := h.changeOrigin (y := c - x₀) (by simp)
  have hc : HasFPowerSeriesOnBall f
      ((coefficientFPowerSeries a).changeOrigin (c - x₀)) c ⊤ := by
    simpa using hc0
  have hs := hc.hasSum_iteratedFDeriv (y := x - c) (by simp)
  convert hs using 1
  · funext k
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      taylorTerm, smul_eq_mul]
    ring
  · ring_nf

theorem gap15
    (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f) :
    ∀ x c : ℝ, ∀ n : ℕ,
      ∃ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 ∧
        taylorRemainder f n c x =
          iteratedDeriv (n + 1) f (c + θ * (x - c)) /
              (Nat.factorial (n + 1) : ℝ) *
            (x - c) ^ (n + 1) := by
  intro x c n
  let d := x - c
  let g : ℝ → ℝ := fun t => f (c + d * t)
  have hg : ContDiff ℝ ⊤ g := by
    dsimp [g]
    fun_prop
  have hiter (k : ℕ) (t : ℝ) :
      iteratedDeriv k g t = d ^ k * iteratedDeriv k f (c + d * t) := by
    have hshift : ContDiff ℝ k (fun u : ℝ => f (c + u)) := by
      simpa [Function.comp_def] using
        (hf.of_le le_top).comp (contDiff_const.add contDiff_id)
    have h := congrFun (iteratedDeriv_comp_const_mul hshift d) t
    rw [iteratedDeriv_comp_const_add] at h
    simpa [g] using h
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) :=
    uniqueDiffOn_Icc zero_lt_one
  have hwithin (k : ℕ) :
      iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) 0 =
        iteratedDeriv k g 0 := by
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
      iteratedDeriv_eq_iteratedFDeriv,
      iteratedFDerivWithin_eq_iteratedFDeriv hu
        (hg.contDiffAt.of_le (by simp)) (by simp)]
  have hpoly :
      taylorWithinEval g n (Set.Icc (0 : ℝ) 1) 0 1 =
        ∑ k ∈ Finset.range (n + 1), taylorTerm f c x k := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hwithin k, hiter k 0]
    simp [taylorTerm, d, smul_eq_mul]
    ring
  obtain ⟨θ, hθ, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := n) zero_lt_one
      (hg.contDiffOn.of_le (by simp))
  refine ⟨θ, ⟨hθ.1.le, hθ.2.le⟩, ?_⟩
  unfold taylorRemainder
  rw [← hpoly]
  rw [hiter (n + 1) θ] at hrem
  have hg1 : g 1 = f x := by
    dsimp [g, d]
    congr 1
    ring
  rw [hg1] at hrem
  rw [hrem]
  dsimp [d]
  ring

theorem gap16
    (f : ℝ → ℝ) (M P : ℝ)
    (hf : ContDiff ℝ ⊤ f)
    (hderiv : ∀ m : ℕ, ∀ y : ℝ, |iteratedDeriv m f y| ≤ M * P) :
    ∀ x c R : ℝ, 0 ≤ M → 0 ≤ P → 0 < R → |x - c| < R →
      ∀ n : ℕ,
        |taylorRemainder f n c x| ≤
          M * P / (Nat.factorial (n + 1) : ℝ) * R ^ (n + 1) := by
  intro x c R hM hP hR hx n
  obtain ⟨θ, hθ, hrem⟩ := gap15 f hf x c n
  rw [hrem]
  have hfac : (0 : ℝ) < Nat.factorial (n + 1) := by positivity
  have hd := hderiv (n + 1) (c + θ * (x - c))
  have hpow : |x - c| ^ (n + 1) ≤ R ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg _) hx.le (n + 1)
  rw [abs_mul, abs_div, abs_pow, abs_of_pos hfac]
  exact mul_le_mul
    (div_le_div_of_nonneg_right hd hfac.le) hpow (by positivity)
    (div_nonneg (mul_nonneg hM hP) hfac.le)

theorem gap17 :
    ∀ R : ℝ, 0 ≤ R →
      Tendsto
        (fun n : ℕ => R ^ (n + 1) / (Nat.factorial (n + 1) : ℝ))
        atTop (𝓝 0) := by
  intro R hR
  exact (FloorSemiring.tendsto_pow_div_factorial_atTop R).comp
    (tendsto_add_atTop_nat 1)

theorem gap18
    (f : ℝ → ℝ) (M P : ℝ)
    (hrem :
      ∀ x c R : ℝ, 0 < R → |x - c| < R → ∀ n : ℕ,
        |taylorRemainder f n c x| ≤
          M * P / (Nat.factorial (n + 1) : ℝ) * R ^ (n + 1)) :
    ∀ x c R : ℝ, 0 < R → |x - c| < R →
      Tendsto (fun n => taylorRemainder f n c x) atTop (𝓝 0) := by
  intro x c R hR hx
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hu : Tendsto
      (fun n : ℕ => M * P *
        (R ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)))
      atTop (𝓝 0) := by
    simpa using (gap17 R hR.le).const_mul (M * P)
  apply squeeze_zero (fun n => norm_nonneg _) ?_ hu
  intro n
  calc
    ‖taylorRemainder f n c x‖ = |taylorRemainder f n c x| :=
      Real.norm_eq_abs _
    _ ≤ M * P / (Nat.factorial (n + 1) : ℝ) * R ^ (n + 1) :=
      hrem x c R hR hx n
    _ = M * P * (R ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) := by
      ring

theorem gap19
    (a : ℕ → ℝ) (f : ℝ → ℝ) (x₀ M : ℝ)
    (hf : ∀ x, f x = ∑' n, centeredTerm a x₀ x n)
    (hM : EntireCoefficientBound a M) :
    ∀ x c : ℝ, f x = ∑' k, taylorTerm f c x k := by
  intro x c
  exact (taylorTerm_hasSum a f x₀ M hf hM x c).tsum_eq.symm

theorem gap20
    (a : ℕ → ℝ) (f : ℝ → ℝ) (x₀ M : ℝ)
    (hf : ∀ x, f x = ∑' n, centeredTerm a x₀ x n)
    (hM : EntireCoefficientBound a M) :
    ContDiff ℝ ⊤ f := by
  exact gap6 a f x₀ M hf hM

theorem gap21
    (a : ℕ → ℝ) (f : ℝ → ℝ) (x₀ M : ℝ)
    (hf : ∀ x, f x = ∑' n, centeredTerm a x₀ x n)
    (hM : EntireCoefficientBound a M) :
    ∀ x c : ℝ, f x = ∑' n, taylorTerm f c x n := by
  exact gap19 a f x₀ M hf hM

theorem gap22
    (a : ℕ → ℝ) (f : ℝ → ℝ) (x₀ M : ℝ)
    (hf : ∀ x, f x = ∑' n, centeredTerm a x₀ x n)
    (hM : EntireCoefficientBound a M) :
    ContDiff ℝ ⊤ f ∧
      ∀ x c : ℝ, f x = ∑' n, taylorTerm f c x n := by
  exact ⟨gap20 a f x₀ M hf hM, gap21 a f x₀ M hf hM⟩

end

end ProofGap.Exercise2899
