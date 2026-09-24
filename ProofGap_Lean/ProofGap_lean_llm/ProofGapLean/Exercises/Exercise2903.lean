import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2903

noncomputable section

open scoped BigOperators Interval

def sincSeriesTerm (t : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * t ^ (2 * n) /
    (Nat.factorial (2 * n + 1) : ℝ)

def integratedSincTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n + 1) /
    ((Nat.factorial (2 * n + 1) : ℝ) * (2 * n + 1 : ℝ))

private theorem sincSeriesTerm_hasSum (t : ℝ) (ht : t ≠ 0) :
    HasSum (fun n => sincSeriesTerm t n) (Real.sin t / t) := by
  have hfun :
      (fun n : ℕ =>
        ((-1 : ℝ) ^ n * t ^ (2 * n + 1) /
          (Nat.factorial (2 * n + 1) : ℝ)) / t) =
        (fun n => sincSeriesTerm t n) := by
    funext n
    unfold sincSeriesTerm
    rw [pow_succ]
    field_simp [ht]
  simpa only [hfun] using (Real.hasSum_sin t).div_const t

private theorem integral_pow_even (x : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..x, t ^ (2 * n)) =
      x ^ (2 * n + 1) / (2 * n + 1 : ℝ) := by
  have hk : (2 * n + 1 : ℝ) ≠ 0 := by positivity
  have hderiv (t : ℝ) :
      HasDerivAt
        (fun y : ℝ => y ^ (2 * n + 1) / (2 * n + 1 : ℝ))
        (t ^ (2 * n)) t := by
    convert ((hasDerivAt_id t).pow (2 * n + 1)).div_const
      (2 * n + 1 : ℝ) using 1 <;>
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul,
          Nat.cast_ofNat, id_eq] <;>
        field_simp [hk] <;>
        ring_nf
  calc
    (∫ t in (0 : ℝ)..x, t ^ (2 * n)) =
        x ^ (2 * n + 1) / (2 * n + 1 : ℝ) -
          0 ^ (2 * n + 1) / (2 * n + 1 : ℝ) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hderiv t)
      exact (continuous_id.pow (2 * n)).intervalIntegrable (0 : ℝ) x
    _ = x ^ (2 * n + 1) / (2 * n + 1 : ℝ) := by
      norm_num

private theorem integral_sincSeriesTerm (x : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..x, sincSeriesTerm t n) = integratedSincTerm x n := by
  calc
    (∫ t in (0 : ℝ)..x, sincSeriesTerm t n) =
        ((-1 : ℝ) ^ n / (Nat.factorial (2 * n + 1) : ℝ)) *
          (∫ t in (0 : ℝ)..x, t ^ (2 * n)) := by
      have hfun :
          (fun t : ℝ => sincSeriesTerm t n) =
            (fun t : ℝ =>
              ((-1 : ℝ) ^ n /
                (Nat.factorial (2 * n + 1) : ℝ)) * t ^ (2 * n)) := by
        funext t
        unfold sincSeriesTerm
        ring
      rw [hfun, intervalIntegral.integral_const_mul]
    _ = ((-1 : ℝ) ^ n / (Nat.factorial (2 * n + 1) : ℝ)) *
        (x ^ (2 * n + 1) / (2 * n + 1 : ℝ)) := by
      rw [integral_pow_even]
    _ = integratedSincTerm x n := by
      have hfac : (Nat.factorial (2 * n + 1) : ℝ) ≠ 0 := by
        norm_num [Nat.factorial_ne_zero]
      have hk : (2 * n + 1 : ℝ) ≠ 0 := by positivity
      unfold integratedSincTerm
      field_simp [hfac, hk] <;> ring

private theorem norm_sincSeriesTerm (t : ℝ) (n : ℕ) :
    ‖sincSeriesTerm t n‖ =
      t ^ (2 * n) / (Nat.factorial (2 * n + 1) : ℝ) := by
  have hp : 0 ≤ t ^ (2 * n) := by
    rw [show 2 * n = n * 2 by omega, pow_mul]
    exact sq_nonneg (t ^ n)
  have hf : 0 ≤ (Nat.factorial (2 * n + 1) : ℝ) := Nat.cast_nonneg _
  have hsign : |(-1 : ℝ) ^ n| = 1 := by
    rw [abs_pow]
    norm_num
  rw [Real.norm_eq_abs]
  unfold sincSeriesTerm
  rw [abs_div, abs_mul, hsign, abs_of_nonneg hp, abs_of_nonneg hf, one_mul]

private theorem integral_norm_sincSeriesTerm (x : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..x, ‖sincSeriesTerm t n‖) =
      x ^ (2 * n + 1) /
        ((Nat.factorial (2 * n + 1) : ℝ) * (2 * n + 1 : ℝ)) := by
  calc
    (∫ t in (0 : ℝ)..x, ‖sincSeriesTerm t n‖) =
        (1 / (Nat.factorial (2 * n + 1) : ℝ)) *
          (∫ t in (0 : ℝ)..x, t ^ (2 * n)) := by
      have hfun :
          (fun t : ℝ => ‖sincSeriesTerm t n‖) =
            (fun t : ℝ =>
              (1 / (Nat.factorial (2 * n + 1) : ℝ)) * t ^ (2 * n)) := by
        funext t
        rw [norm_sincSeriesTerm]
        ring
      rw [hfun, intervalIntegral.integral_const_mul]
    _ = (1 / (Nat.factorial (2 * n + 1) : ℝ)) *
        (x ^ (2 * n + 1) / (2 * n + 1 : ℝ)) := by
      rw [integral_pow_even]
    _ = x ^ (2 * n + 1) /
        ((Nat.factorial (2 * n + 1) : ℝ) * (2 * n + 1 : ℝ)) := by
      have hfac : (Nat.factorial (2 * n + 1) : ℝ) ≠ 0 := by
        norm_num [Nat.factorial_ne_zero]
      have hk : (2 * n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hfac, hk] <;> ring

private theorem sincSeriesTerm_intervalIntegrable (x : ℝ) :
    ∀ n, IntervalIntegrable (fun t => sincSeriesTerm t n)
      MeasureTheory.volume 0 x := by
  intro n
  simpa [sincSeriesTerm] using
    ((continuous_const.mul (continuous_id.pow (2 * n))).div_const
      (Nat.factorial (2 * n + 1) : ℝ)).intervalIntegrable (0 : ℝ) x

private theorem summable_integral_norm_sincSeriesTerm (x : ℝ) :
    Summable (fun n => ∫ t in (0 : ℝ)..x, ‖sincSeriesTerm t n‖) := by
  have hs : Summable (fun n : ℕ =>
      |x| ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)) := by
    simpa [Real.norm_eq_abs, abs_div, abs_mul, abs_pow] using
      (Real.hasSum_sin |x|).summable.norm
  refine hs.of_norm_bounded ?_
  intro n
  rw [integral_norm_sincSeriesTerm]
  have hfac : 0 ≤ (Nat.factorial (2 * n + 1) : ℝ) := Nat.cast_nonneg _
  have hk : 0 ≤ (2 * n + 1 : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
    abs_of_nonneg hfac, abs_of_nonneg hk, div_mul_eq_div_div]
  apply div_le_self
  · positivity
  · norm_num

private theorem sinc_nnnorm_to_ofReal (r : ℝ) :
    (‖r‖₊ : ENNReal) = ENNReal.ofReal ‖r‖ := by
  change (↑‖r‖₊ : ENNReal) =
    (↑(Real.toNNReal ‖r‖) : ENNReal)
  congr 1
  apply Subtype.ext
  simp

private theorem intervalIntegral_tsum_of_le
    (f : ℕ → ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ∀ n, IntervalIntegrable (f n) MeasureTheory.volume a b)
    (hnorm : Summable (fun n => ∫ t in a..b, ‖f n t‖)) :
    (∫ t in a..b, ∑' n, f n t) = ∑' n, ∫ t in a..b, f n t := by
  have hfi : ∀ n, MeasureTheory.IntegrableOn (f n) (Set.Ioc a b)
      MeasureTheory.volume := by
    intro n
    exact (hf n).1
  have hs : Summable
      (fun n => ∫ t in Set.Ioc a b, ‖f n t‖ ∂MeasureTheory.volume) := by
    simpa only [intervalIntegral.integral_of_le hab] using hnorm
  have ha (n : ℕ) :
      0 ≤ ∫ t in Set.Ioc a b, ‖f n t‖ ∂MeasureTheory.volume := by
    exact MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  have ha_abs (n : ℕ) :
      0 ≤ ∫ t in Set.Ioc a b, |f n t| ∂MeasureTheory.volume := by
    simpa only [Real.norm_eq_abs] using ha n
  let A : ℕ → NNReal := fun n =>
    Real.toNNReal
      (∫ t in Set.Ioc a b, ‖f n t‖ ∂MeasureTheory.volume)
  have hA : Summable A := by
    rw [← NNReal.summable_coe]
    refine hs.congr ?_
    intro n
    simp [A, ha_abs n]
  have hlin (n : ℕ) :
      (∫⁻ t in Set.Ioc a b, ‖f n t‖₊ ∂MeasureTheory.volume) =
        (A n : ENNReal) := by
    have hnonneg :
        ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc a b)),
          0 ≤ ‖f n t‖ := by
      exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
    calc
      (∫⁻ t in Set.Ioc a b, ‖f n t‖₊ ∂MeasureTheory.volume) =
          ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ‖f n t‖
            ∂MeasureTheory.volume := by
        apply MeasureTheory.lintegral_congr
        exact fun t => sinc_nnnorm_to_ofReal (f n t)
      _ = ENNReal.ofReal
          (∫ t in Set.Ioc a b, ‖f n t‖ ∂MeasureTheory.volume) := by
        simpa using
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            (hfi n).norm hnonneg).symm
      _ = (A n : ENNReal) := by
        rfl
  have hsum_lintegral :
      (∑' n, ∫⁻ t in Set.Ioc a b, ‖f n t‖₊ ∂MeasureTheory.volume) =
        ∑' n, (A n : ENNReal) := by
    apply tsum_congr
    intro n
    exact hlin n
  have htop :
      (∑' n, ∫⁻ t in Set.Ioc a b, ‖f n t‖₊ ∂MeasureTheory.volume) ≠ ⊤ := by
    rw [hsum_lintegral]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hA
  calc
    (∫ t in a..b, ∑' n, f n t) =
        ∫ t in Set.Ioc a b, ∑' n, f n t ∂MeasureTheory.volume :=
      intervalIntegral.integral_of_le hab
    _ = ∑' n, ∫ t in Set.Ioc a b, f n t ∂MeasureTheory.volume :=
      MeasureTheory.integral_tsum
        (fun n => (hfi n).aestronglyMeasurable) htop
    _ = ∑' n, ∫ t in a..b, f n t := by
      apply tsum_congr
      intro n
      exact (intervalIntegral.integral_of_le hab).symm

private theorem intervalIntegral_tsum_sinc
    (x : ℝ)
    (hf : ∀ n, IntervalIntegrable (fun t => sincSeriesTerm t n)
      MeasureTheory.volume 0 x)
    (hnorm : Summable
      (fun n => ∫ t in (0 : ℝ)..x, ‖sincSeriesTerm t n‖)) :
    (∫ t in (0 : ℝ)..x, ∑' n, sincSeriesTerm t n) =
      ∑' n, ∫ t in (0 : ℝ)..x, sincSeriesTerm t n := by
  rcases le_total (0 : ℝ) x with hx | hx
  · exact intervalIntegral_tsum_of_le
      (fun n t => sincSeriesTerm t n) 0 x hx hf hnorm
  · have hf' : ∀ n, IntervalIntegrable (fun t => sincSeriesTerm t n)
        MeasureTheory.volume x 0 := by
      intro n
      exact (hf n).symm
    have hnorm' : Summable
        (fun n => ∫ t in x..(0 : ℝ), ‖sincSeriesTerm t n‖) := by
      refine hnorm.neg.congr ?_
      intro n
      have h := intervalIntegral.integral_symm
        (μ := MeasureTheory.volume)
        (f := fun t : ℝ => ‖sincSeriesTerm t n‖) x 0
      linarith
    have hsum := intervalIntegral_tsum_of_le
      (fun n t => sincSeriesTerm t n) x 0 hx hf' hnorm'
    have hsym (g : ℝ → ℝ) :
        -(∫ t in x..(0 : ℝ), g t) = ∫ t in (0 : ℝ)..x, g t := by
      have h := intervalIntegral.integral_symm
        (μ := MeasureTheory.volume) (f := g) x 0
      linarith
    calc
      (∫ t in (0 : ℝ)..x, ∑' n, sincSeriesTerm t n) =
          -(∫ t in x..(0 : ℝ), ∑' n, sincSeriesTerm t n) :=
        (hsym (fun t => ∑' n, sincSeriesTerm t n)).symm
      _ = -(∑' n, ∫ t in x..(0 : ℝ), sincSeriesTerm t n) :=
        congrArg (fun y : ℝ => -y) hsum
      _ = ∑' n, ∫ t in (0 : ℝ)..x, sincSeriesTerm t n := by
        rw [← tsum_neg]
        apply tsum_congr
        intro n
        exact hsym (fun t => sincSeriesTerm t n)

theorem gap1 :
    ∀ x : ℝ,
      (∫ t in (0 : ℝ)..x, Real.sin t / t) =
        ∫ t in (0 : ℝ)..x, ∑' n, sincSeriesTerm t n := by
  intro x
  have hne : ∀ᵐ t : ℝ ∂MeasureTheory.volume, t ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hne] with t ht
  intro _
  exact (sincSeriesTerm_hasSum t ht).tsum_eq.symm

theorem gap2 :
    ∀ x : ℝ,
      (∫ t in (0 : ℝ)..x, Real.sin t / t) =
        ∑' n, integratedSincTerm x n := by
  intro x
  rw [gap1 x]
  calc
    (∫ t in (0 : ℝ)..x, ∑' n, sincSeriesTerm t n) =
        ∑' n, ∫ t in (0 : ℝ)..x, sincSeriesTerm t n := by
      exact intervalIntegral_tsum_sinc x
        (sincSeriesTerm_intervalIntegrable x)
        (summable_integral_norm_sincSeriesTerm x)
    _ = ∑' n, integratedSincTerm x n := by
      apply tsum_congr
      intro n
      exact integral_sincSeriesTerm x n

end

end ProofGap.Exercise2903
