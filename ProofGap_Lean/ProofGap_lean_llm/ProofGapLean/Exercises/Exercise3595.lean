import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise3595

noncomputable section

abbrev Point2 := ℝ × ℝ

def function (q : Point2) : ℝ :=
  Real.exp q.1 * Real.sin q.2

def expSeries (x : ℝ) : ℝ :=
  ∑' m : ℕ, x ^ m / (Nat.factorial m : ℝ)

def sinSeries (y : ℝ) : ℝ :=
  ∑' n : ℕ,
    (-1 : ℝ) ^ n * y ^ (2 * n + 1) /
      (Nat.factorial (2 * n + 1) : ℝ)

def doubleSeriesTerm (q : Point2) (m n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (q.1 ^ m * q.2 ^ (2 * n + 1)) /
    ((Nat.factorial m : ℝ) * (Nat.factorial (2 * n + 1) : ℝ))

def doubleSeries (q : Point2) : ℝ :=
  ∑' m : ℕ, ∑' n : ℕ, doubleSeriesTerm q m n

private theorem cauSeq_tendsto_limit3595 (f : CauSeq ℂ norm) :
    Filter.Tendsto f Filter.atTop (nhds f.lim) := by
  refine tendsto_nhds.mpr ?_
  intro s hs hfs
  suffices ∃ a : ℕ, ∀ b : ℕ, b ≥ a → f b ∈ s by
    simpa using this
  let hexi := Metric.isOpen_iff.1 hs f.lim hfs
  let ε := Classical.choose hexi
  have hε := (Classical.choose_spec hexi).1
  have hεs := (Classical.choose_spec hexi).2
  let heq := Setoid.symm (CauSeq.equiv_lim f) ε hε
  let N := Classical.choose heq
  have hN := Classical.choose_spec heq
  exact ⟨N, fun b hb => hεs (by
    dsimp [Metric.ball]
    rw [dist_comm, dist_eq_norm]
    exact hN b hb)⟩

private theorem summable_complex_exp_term3595 (z : ℂ) :
    Summable (fun n : ℕ => z ^ n / (Nat.factorial n : ℂ)) := by
  apply Summable.of_norm
  simpa [norm_div, norm_pow, Complex.norm_natCast] using
    Real.summable_pow_div_factorial ‖z‖

private theorem complex_exp_eq_tsum3595 (z : ℂ) :
    Complex.exp z =
      ∑' n : ℕ, z ^ n / (Nat.factorial n : ℂ) := by
  have hc := cauSeq_tendsto_limit3595 (Complex.exp' z)
  have hexp :
      Filter.Tendsto
        (fun n : ℕ => ∑ m ∈ Finset.range n,
          z ^ m / (Nat.factorial m : ℂ))
        Filter.atTop (nhds (Complex.exp z)) := by
    simpa only [Complex.exp', Complex.exp] using hc
  exact tendsto_nhds_unique hexp
    (summable_complex_exp_term3595 z).hasSum.tendsto_sum_nat

private theorem real_exp_eq_tsum3595 (x : ℝ) :
    Real.exp x =
      ∑' n : ℕ, x ^ n / (Nat.factorial n : ℝ) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_exp, Complex.ofReal_tsum]
  simpa using complex_exp_eq_tsum3595 (x : ℂ)

private theorem complex_sin_eq_full_tsum3595 (y : ℝ) :
    Complex.sin (y : ℂ) =
      ∑' n : ℕ,
        (((-((y : ℂ) * Complex.I)) ^ n /
            (Nat.factorial n : ℂ) -
          (((y : ℂ) * Complex.I) ^ n /
            (Nat.factorial n : ℂ))) * Complex.I / 2) := by
  let a : ℕ → ℂ := fun n =>
    (-(y : ℂ) * Complex.I) ^ n / (Nat.factorial n : ℂ)
  let b : ℕ → ℂ := fun n =>
    ((y : ℂ) * Complex.I) ^ n / (Nat.factorial n : ℂ)
  have ha : Summable a := by
    simpa [a] using
      summable_complex_exp_term3595 (-(y : ℂ) * Complex.I)
  have hb : Summable b := by
    simpa [b] using
      summable_complex_exp_term3595 ((y : ℂ) * Complex.I)
  have hab := ha.sub hb
  rw [Complex.sin]
  rw [complex_exp_eq_tsum3595 (-(y : ℂ) * Complex.I),
    complex_exp_eq_tsum3595 ((y : ℂ) * Complex.I)]
  change ((∑' n, a n) - ∑' n, b n) * Complex.I / 2 = _
  rw [← ha.tsum_sub hb]
  rw [div_eq_mul_inv, ← hab.tsum_mul_right Complex.I]
  rw [← (hab.mul_right Complex.I).tsum_mul_right (2 : ℂ)⁻¹]
  apply tsum_congr
  intro n
  simp only [a, b]
  ring

private theorem real_sin_eq_tsum3595 (y : ℝ) :
    Real.sin y =
      ∑' n : ℕ,
        (-1 : ℝ) ^ n * y ^ (2 * n + 1) /
          (Nat.factorial (2 * n + 1) : ℝ) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sin, Complex.ofReal_tsum]
  let f : ℕ → ℂ := fun n =>
    (((-((y : ℂ) * Complex.I)) ^ n /
        (Nat.factorial n : ℂ) -
      (((y : ℂ) * Complex.I) ^ n /
        (Nat.factorial n : ℂ))) * Complex.I / 2)
  have ha :
      Summable (fun n : ℕ =>
        (-((y : ℂ) * Complex.I)) ^ n /
          (Nat.factorial n : ℂ)) :=
    summable_complex_exp_term3595 (-((y : ℂ) * Complex.I))
  have hb :
      Summable (fun n : ℕ =>
        ((y : ℂ) * Complex.I) ^ n /
          (Nat.factorial n : ℂ)) :=
    summable_complex_exp_term3595 ((y : ℂ) * Complex.I)
  have hf : Summable f := by
    have hsub := ha.sub hb
    have hmul := (hsub.mul_right Complex.I).mul_right (2 : ℂ)⁻¹
    simpa [f, div_eq_mul_inv, mul_assoc] using hmul
  have hfe : Summable (fun n : ℕ => f (2 * n)) := by
    exact hf.comp_injective (by
      intro a b hab
      omega)
  have hfo : Summable (fun n : ℕ => f (2 * n + 1)) := by
    exact hf.comp_injective (by
      intro a b hab
      exact Nat.mul_left_cancel (n := 2) (by decide)
        (Nat.add_right_cancel hab))
  have heven (n : ℕ) : f (2 * n) = 0 := by
    dsimp [f]
    rw [(even_two_mul n).neg_pow]
    ring
  have hodd (n : ℕ) :
      f (2 * n + 1) =
        (((-1 : ℝ) ^ n * y ^ (2 * n + 1) /
          (Nat.factorial (2 * n + 1) : ℝ) : ℝ) : ℂ) := by
    have hIpow :
        Complex.I ^ (2 * n) = (-1 : ℂ) ^ n := by
      rw [pow_mul, Complex.I_sq]
    dsimp [f]
    rw [(odd_two_mul_add_one n).neg_pow]
    simp only [pow_succ, mul_pow]
    rw [hIpow]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [complex_sin_eq_full_tsum3595]
  calc
    (∑' n : ℕ, f n) =
        (∑' n : ℕ, f (2 * n)) +
          ∑' n : ℕ, f (2 * n + 1) :=
      (tsum_even_add_odd hfe hfo).symm
    _ = ∑' n : ℕ, f (2 * n + 1) := by
      have hz : (∑' n : ℕ, f (2 * n)) = 0 := by
        calc
          (∑' n : ℕ, f (2 * n)) = ∑' _n : ℕ, (0 : ℂ) :=
            tsum_congr heven
          _ = 0 := tsum_zero
      rw [hz, zero_add]
    _ = ∑' n : ℕ,
        (((-1 : ℝ) ^ n * y ^ (2 * n + 1) /
          (Nat.factorial (2 * n + 1) : ℝ) : ℝ) : ℂ) :=
      tsum_congr hodd

private theorem summable_real_sin_term3595 (y : ℝ) :
    Summable (fun n : ℕ =>
      (-1 : ℝ) ^ n * y ^ (2 * n + 1) /
        (Nat.factorial (2 * n + 1) : ℝ)) := by
  apply Summable.of_norm
  have h :
      Summable (fun n : ℕ =>
        |y| ^ (2 * n + 1) /
          (Nat.factorial (2 * n + 1) : ℝ)) := by
    have hbase := Real.summable_pow_div_factorial |y|
    exact hbase.comp_injective (by
      intro a b hab
      exact Nat.mul_left_cancel (n := 2) (by decide)
        (Nat.add_right_cancel hab))
  simpa [Real.norm_eq_abs, abs_div, abs_mul, abs_pow] using h

theorem gap1 :
    ∀ x y : ℝ,
      function (x, y) = expSeries x * sinSeries y := by
  intro x y
  rw [function, expSeries, sinSeries, real_exp_eq_tsum3595,
    real_sin_eq_tsum3595]

theorem gap2 :
    ∀ x y : ℝ,
      function (x, y) = doubleSeries (x, y) := by
  intro x y
  rw [function, real_exp_eq_tsum3595, real_sin_eq_tsum3595]
  unfold doubleSeries
  let a : ℕ → ℝ := fun m =>
    x ^ m / (Nat.factorial m : ℝ)
  let b : ℕ → ℝ := fun n =>
    (-1 : ℝ) ^ n * y ^ (2 * n + 1) /
      (Nat.factorial (2 * n + 1) : ℝ)
  have ha : Summable a := by
    simpa [a] using Real.summable_pow_div_factorial x
  have hb : Summable b := by
    simpa [b] using summable_real_sin_term3595 y
  change (∑' m : ℕ, a m) * (∑' n : ℕ, b n) =
    ∑' m : ℕ, ∑' n : ℕ, doubleSeriesTerm (x, y) m n
  calc
    (∑' m : ℕ, a m) * (∑' n : ℕ, b n) =
        ∑' m : ℕ, a m * (∑' n : ℕ, b n) :=
      (ha.tsum_mul_right (∑' n : ℕ, b n)).symm
    _ = ∑' m : ℕ, ∑' n : ℕ, a m * b n := by
      apply tsum_congr
      intro m
      exact (hb.tsum_mul_left (a m)).symm
    _ = ∑' m : ℕ, ∑' n : ℕ, doubleSeriesTerm (x, y) m n := by
      apply tsum_congr
      intro m
      apply tsum_congr
      intro n
      dsimp [a, b, doubleSeriesTerm]
      ring

end

end ProofGap.Exercise3595
