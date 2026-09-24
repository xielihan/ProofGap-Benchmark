import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2871

noncomputable section

def oddProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (2 * k + 1 : ℕ)

def evenProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (2 * (k + 1) : ℕ)

def inverseSqrtTailTerm (t : ℝ) (n : ℕ) : ℝ :=
  let m := n + 1
  (-1 : ℝ) ^ m * oddProduct m / evenProduct m * t ^ (2 * m)

def inverseHyperbolicSineTailTerm (x : ℝ) (n : ℕ) : ℝ :=
  let m := n + 1
  (-1 : ℝ) ^ m * oddProduct m / evenProduct m *
    (x ^ (2 * m + 1) / (2 * m + 1))

private theorem oddProduct_succ (n : ℕ) :
    oddProduct (n + 1) = oddProduct n * ((2 * n + 1 : ℕ) : ℝ) := by
  simp [oddProduct, Finset.prod_range_succ]

private theorem evenProduct_succ (n : ℕ) :
    evenProduct (n + 1) = evenProduct n * ((2 * n + 2 : ℕ) : ℝ) := by
  simp only [evenProduct, Finset.prod_range_succ]
  push_cast
  ring

private theorem choose_neg_half_succ (n : ℕ) :
    Ring.choose (-1 / 2 : ℝ) (n + 1) =
      Ring.choose (-1 / 2 : ℝ) n *
        (-(((2 * n + 1 : ℕ) : ℝ)) / ((2 * n + 2 : ℕ) : ℝ)) := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul,
    descPochhammer_succ_right, Polynomial.smeval_mul,
    Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast]
  simp only [smul_eq_mul, pow_one, pow_zero, mul_one, nsmul_eq_mul,
    Nat.factorial_succ]
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hf, hn]
  push_cast
  ring

private theorem choose_neg_half_eq (n : ℕ) :
    Ring.choose (-1 / 2 : ℝ) n =
      (-1 : ℝ) ^ n * oddProduct n / evenProduct n := by
  induction n with
  | zero => simp [oddProduct, evenProduct]
  | succ n ih =>
      rw [choose_neg_half_succ, ih, oddProduct_succ, evenProduct_succ, pow_succ]
      have he : evenProduct n ≠ 0 := by
        unfold evenProduct
        positivity
      have hn : (((2 * n + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp [he, hn]

private def inverseSqrtSeriesTerm (t : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * oddProduct n / evenProduct n * t ^ (2 * n)

private theorem hasSum_inverseSqrtSeriesTerm (t : ℝ) (ht : |t| < 1) :
    HasSum (inverseSqrtSeriesTerm t) (1 / Real.sqrt (1 + t ^ 2)) := by
  have hmem : (t ^ 2 : ℝ) ∈ Metric.eball (0 : ℝ) 1 := by
    simp only [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one]
    rw [Real.dist_eq, sub_zero, abs_pow]
    nlinarith [abs_nonneg t]
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
      (a := (-1 / 2 : ℝ))).hasSum hmem
  convert h using 1
  · funext n
    rw [binomialSeries_apply, choose_neg_half_eq]
    simp only [smul_eq_mul, List.prod_ofFn, Fin.prod_const]
    unfold inverseSqrtSeriesTerm
    rw [pow_mul]
  · have hb : 0 ≤ 1 + t ^ 2 := by positivity
    simp only [zero_add]
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hb, ← Real.sqrt_eq_rpow]
    simp [one_div]

private theorem inverseSqrtTailTerm_eq (t : ℝ) (n : ℕ) :
    inverseSqrtTailTerm t n = inverseSqrtSeriesTerm t (n + 1) := by
  simp [inverseSqrtTailTerm, inverseSqrtSeriesTerm]

private theorem inverseSqrt_eq_one_add_tsum (t : ℝ) (ht : |t| < 1) :
    1 / Real.sqrt (1 + t ^ 2) = 1 + ∑' n, inverseSqrtTailTerm t n := by
  have hs := hasSum_inverseSqrtSeriesTerm t ht
  have hsplit := hs.summable.sum_add_tsum_nat_add 1
  calc
    1 / Real.sqrt (1 + t ^ 2) = ∑' n, inverseSqrtSeriesTerm t n :=
      hs.tsum_eq.symm
    _ = inverseSqrtSeriesTerm t 0 +
        ∑' n, inverseSqrtSeriesTerm t (n + 1) := by
      simpa using hsplit.symm
    _ = 1 + ∑' n, inverseSqrtTailTerm t n := by
      rw [tsum_congr (fun n => (inverseSqrtTailTerm_eq t n).symm)]
      simp [inverseSqrtSeriesTerm, oddProduct, evenProduct]

private theorem hasDerivAt_sqrt_one_add_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
  have hpos : 0 < 1 + x ^ 2 := by positivity
  convert ((Real.hasDerivAt_sqrt hpos.ne').comp x
    ((hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2))) using 1 <;>
    simp only [id_eq] <;> field_simp <;> ring

private theorem hasDerivAt_asinh_log (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.log (y + Real.sqrt (1 + y ^ 2)))
      (1 / Real.sqrt (1 + x ^ 2)) x := by
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have hsqrt := hasDerivAt_sqrt_one_add_sq x
  have hsqrtpos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hpos
  have hargpos : 0 < x + Real.sqrt (1 + x ^ 2) := by
    have hsqsqrt : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
      Real.sq_sqrt hpos.le
    nlinarith [Real.sqrt_nonneg (1 + x ^ 2)]
  have h := (Real.hasDerivAt_log hargpos.ne').comp x
    ((hasDerivAt_id x).add hsqrt)
  convert h using 1
  field_simp [hargpos.ne', hsqrtpos.ne']
  ring

private theorem oddProduct_nonneg (n : ℕ) : 0 ≤ oddProduct n := by
  unfold oddProduct
  positivity

private theorem evenProduct_pos (n : ℕ) : 0 < evenProduct n := by
  unfold evenProduct
  positivity

private theorem oddProduct_le_evenProduct (n : ℕ) : oddProduct n ≤ evenProduct n := by
  induction n with
  | zero => simp [oddProduct, evenProduct]
  | succ n ih =>
      rw [oddProduct_succ, evenProduct_succ]
      apply mul_le_mul ih
      · norm_num
      · positivity
      · exact (evenProduct_pos n).le

private theorem norm_inverseSqrtTailTerm_le (t : ℝ) (n : ℕ) :
    ‖inverseSqrtTailTerm t n‖ ≤ |t| ^ (2 * (n + 1)) := by
  unfold inverseSqrtTailTerm
  simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_neg, abs_one,
    one_pow]
  rw [abs_of_nonneg (oddProduct_nonneg (n + 1)),
    abs_of_pos (evenProduct_pos (n + 1))]
  simp only [one_mul]
  simpa using mul_le_mul_of_nonneg_right
    ((div_le_one (evenProduct_pos (n + 1))).2 (oddProduct_le_evenProduct (n + 1)))
    (pow_nonneg (abs_nonneg t) (2 * (n + 1)))

private def inverseSqrtTailContinuous (n : ℕ) : C(ℝ, ℝ) :=
  ⟨fun t => inverseSqrtTailTerm t n, by
    unfold inverseSqrtTailTerm
    fun_prop⟩

private theorem inverseSqrtTail_restrict_norm_le (x : ℝ) (n : ℕ) :
    ‖(inverseSqrtTailContinuous n).restrict
        (⟨Set.uIcc 0 x, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ ≤
      |x| ^ (2 * (n + 1)) := by
  apply (ContinuousMap.norm_le _ (pow_nonneg (abs_nonneg x) _)).2
  intro t
  have htx : |(t : ℝ)| ≤ |x| := by
    simpa [Real.dist_eq] using Real.dist_left_le_of_mem_uIcc t.property
  exact (norm_inverseSqrtTailTerm_le t n).trans
    (pow_le_pow_left₀ (abs_nonneg (t : ℝ)) htx _)

private theorem summable_inverseSqrtTail_restrict_norm (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ =>
      ‖(inverseSqrtTailContinuous n).restrict
        (⟨Set.uIcc 0 x, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖) := by
  have hq : ‖(|x| ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_pow, abs_abs]
    nlinarith [abs_nonneg x]
  have hg : Summable (fun n : ℕ => (|x| ^ 2) ^ n) :=
    summable_geometric_of_norm_lt_one hq
  have hg' : Summable (fun n : ℕ => |x| ^ (2 * (n + 1))) := by
    have hs := (summable_nat_add_iff 1).2 hg
    simpa [pow_mul] using hs
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => inverseSqrtTail_restrict_norm_le x n) hg'

private theorem hasDerivAt_inverseHyperbolicSineTailTerm (x : ℝ) (n : ℕ) :
    HasDerivAt (fun y => inverseHyperbolicSineTailTerm y n)
      (inverseSqrtTailTerm x n) x := by
  unfold inverseHyperbolicSineTailTerm inverseSqrtTailTerm
  let m := n + 1
  have hden : (((2 * m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have he : evenProduct m ≠ 0 := (evenProduct_pos m).ne'
  convert ((hasDerivAt_id x).pow (2 * m + 1)).const_mul
    (((-1 : ℝ) ^ m * oddProduct m / evenProduct m) /
      (((2 * m + 1 : ℕ) : ℝ))) using 1 <;>
    dsimp [m] <;> push_cast <;> field_simp [hden, he] <;> ring

private theorem integral_inverseSqrtTailTerm (x : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..x, inverseSqrtTailTerm t n) =
      inverseHyperbolicSineTailTerm x n := by
  have hcont : Continuous (fun t => inverseSqrtTailTerm t n) :=
    (inverseSqrtTailContinuous n).continuous
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := x)
    (fun t _ => hasDerivAt_inverseHyperbolicSineTailTerm t n)
    (hcont.intervalIntegrable 0 x)
  simpa [inverseHyperbolicSineTailTerm] using h

private theorem integral_one_add_inverseSqrtTail (x : ℝ) (hx : |x| < 1) :
    (∫ t in (0 : ℝ)..x, 1 + ∑' n, inverseSqrtTailTerm t n) =
      x + ∑' n, inverseHyperbolicSineTailTerm x n := by
  have hsumNorm := summable_inverseSqrtTail_restrict_norm x hx
  have hswap :=
    intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
      (a := (0 : ℝ)) (b := x) (f := inverseSqrtTailContinuous) hsumNorm
  have hswap' :
      (∑' n, ∫ t in (0 : ℝ)..x, inverseSqrtTailTerm t n) =
        ∫ t in (0 : ℝ)..x, ∑' n, inverseSqrtTailTerm t n := by
    simpa [inverseSqrtTailContinuous] using hswap
  have hcont : Continuous (fun t : ℝ => 1 / Real.sqrt (1 + t ^ 2)) := by
    exact continuous_const.div
      (Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2)))
      (fun t => ne_of_gt (Real.sqrt_pos.2 (by positivity)))
  have htailInt : IntervalIntegrable (fun t : ℝ => ∑' n, inverseSqrtTailTerm t n)
      MeasureTheory.volume 0 x := by
    have hbase : IntervalIntegrable
        (fun t : ℝ => 1 / Real.sqrt (1 + t ^ 2) - 1)
        MeasureTheory.volume 0 x :=
      (hcont.sub (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))).intervalIntegrable 0 x
    apply hbase.congr
    intro t ht
    have ht' : t ∈ Set.uIcc 0 x := Set.uIoc_subset_uIcc ht
    have htx : |t| ≤ |x| := by
      simpa [Real.dist_eq] using Real.dist_left_le_of_mem_uIcc ht'
    have heq := inverseSqrt_eq_one_add_tsum t (lt_of_le_of_lt htx hx)
    change 1 / Real.sqrt (1 + t ^ 2) - 1 = ∑' n, inverseSqrtTailTerm t n
    linarith
  rw [intervalIntegral.integral_add intervalIntegrable_const htailInt,
    intervalIntegral.integral_const, sub_zero, ← hswap']
  simp only [smul_eq_mul, mul_one]
  congr 1
  apply tsum_congr
  exact fun n => integral_inverseSqrtTailTerm x n

private theorem oddEvenRatio_sq_le (n : ℕ) :
    (oddProduct n / evenProduct n) ^ 2 ≤ 1 / (((n + 1 : ℕ) : ℝ)) := by
  induction n with
  | zero => simp [oddProduct, evenProduct]
  | succ n ih =>
      rw [oddProduct_succ, evenProduct_succ]
      have he : evenProduct n ≠ 0 := (evenProduct_pos n).ne'
      have hn1 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hn2 : (((n + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hfacDen : (((2 * n + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hsplit :
          (oddProduct n * (((2 * n + 1 : ℕ) : ℝ)) /
              (evenProduct n * (((2 * n + 2 : ℕ) : ℝ)))) ^ 2 =
            (oddProduct n / evenProduct n) ^ 2 *
              ((((2 * n + 1 : ℕ) : ℝ)) / (((2 * n + 2 : ℕ) : ℝ))) ^ 2 := by
        field_simp [he, hfacDen]
      rw [hsplit]
      have hfactor :
          ((((2 * n + 1 : ℕ) : ℝ)) / (((2 * n + 2 : ℕ) : ℝ))) ^ 2 ≤
            (((n + 1 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ)) := by
        rw [div_pow]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        push_cast
        nlinarith [sq_nonneg (n : ℝ)]
      calc
        (oddProduct n / evenProduct n) ^ 2 *
              ((((2 * n + 1 : ℕ) : ℝ)) / (((2 * n + 2 : ℕ) : ℝ))) ^ 2 ≤
            (1 / (((n + 1 : ℕ) : ℝ))) *
              ((((2 * n + 1 : ℕ) : ℝ)) / (((2 * n + 2 : ℕ) : ℝ))) ^ 2 :=
          mul_le_mul_of_nonneg_right ih (sq_nonneg _)
        _ ≤ (1 / (((n + 1 : ℕ) : ℝ))) *
              ((((n + 1 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hfactor (by positivity)
        _ = 1 / ((((n + 1) + 1 : ℕ) : ℝ)) := by
          field_simp [hn1, hn2]

private theorem oddEvenRatio_le_inv_sqrt (n : ℕ) :
    oddProduct n / evenProduct n ≤
      1 / Real.sqrt (((n + 1 : ℕ) : ℝ)) := by
  have hbase : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hsqrt : Real.sqrt (((n + 1 : ℕ) : ℝ)) ^ 2 = ((n + 1 : ℕ) : ℝ) :=
    Real.sq_sqrt hbase.le
  apply (sq_le_sq₀ (div_nonneg (oddProduct_nonneg n) (evenProduct_pos n).le)
    (by positivity)).mp
  have hright :
      (1 / Real.sqrt (((n + 1 : ℕ) : ℝ))) ^ 2 =
        1 / (((n + 1 : ℕ) : ℝ)) := by
    rw [div_pow, hsqrt]
    norm_num
  rw [hright]
  exact oddEvenRatio_sq_le n

private theorem norm_inverseHyperbolicSineTailTerm_le_pSeries
    (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) :
    ‖inverseHyperbolicSineTailTerm x n‖ ≤
      1 / |(n : ℝ) + 2| ^ (3 / 2 : ℝ) := by
  let m := n + 1
  have hN : (((m + 1 : ℕ) : ℝ)) = (n : ℝ) + 2 := by
    dsimp [m]
    push_cast
    ring
  have hNpos : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have hdenpos : 0 < 2 * (m : ℝ) + 1 := by positivity
  have hdenGe : (((m + 1 : ℕ) : ℝ)) ≤ 2 * (m : ℝ) + 1 := by
    push_cast
    nlinarith
  have hpow : |x| ^ (2 * m + 1) ≤ 1 :=
    pow_le_one₀ (abs_nonneg x) hx
  have hratio0 : 0 ≤ oddProduct m / evenProduct m :=
    div_nonneg (oddProduct_nonneg m) (evenProduct_pos m).le
  have hratio := oddEvenRatio_le_inv_sqrt m
  have hrpow :
      (((m + 1 : ℕ) : ℝ)) ^ (3 / 2 : ℝ) =
        (((m + 1 : ℕ) : ℝ)) * Real.sqrt (((m + 1 : ℕ) : ℝ)) := by
    calc
      (((m + 1 : ℕ) : ℝ)) ^ (3 / 2 : ℝ) =
          (((m + 1 : ℕ) : ℝ)) ^ (1 + 1 / 2 : ℝ) := by norm_num
      _ = (((m + 1 : ℕ) : ℝ)) ^ (1 : ℝ) *
          (((m + 1 : ℕ) : ℝ)) ^ (1 / 2 : ℝ) :=
        Real.rpow_add hNpos 1 (1 / 2)
      _ = (((m + 1 : ℕ) : ℝ)) * Real.sqrt (((m + 1 : ℕ) : ℝ)) := by
        rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  unfold inverseHyperbolicSineTailTerm
  change ‖(-1 : ℝ) ^ m * oddProduct m / evenProduct m *
    (x ^ (2 * m + 1) / (2 * (m : ℝ) + 1))‖ ≤
      1 / |(n : ℝ) + 2| ^ (3 / 2 : ℝ)
  simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_neg, abs_one,
    one_pow]
  rw [abs_of_nonneg (oddProduct_nonneg m), abs_of_pos (evenProduct_pos m),
    abs_of_pos hdenpos]
  simp only [one_mul]
  calc
    oddProduct m / evenProduct m *
          (|x| ^ (2 * m + 1) / (2 * (m : ℝ) + 1)) ≤
        (oddProduct m / evenProduct m) / (2 * (m : ℝ) + 1) := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hdenpos.le
      simpa using mul_le_mul_of_nonneg_left hpow hratio0
    _ ≤ (1 / Real.sqrt (((m + 1 : ℕ) : ℝ))) /
          (((m + 1 : ℕ) : ℝ)) :=
      div_le_div₀ (by positivity) hratio hNpos hdenGe
    _ = 1 / |(n : ℝ) + 2| ^ (3 / 2 : ℝ) := by
      rw [← hN, abs_of_pos hNpos, hrpow]
      field_simp [hNpos.ne', (Real.sqrt_pos.2 hNpos).ne']

private theorem inverseHyperbolicSineTailTerm_summable (x : ℝ) (hx : |x| ≤ 1) :
    Summable (inverseHyperbolicSineTailTerm x) := by
  have hp : Summable (fun n : ℕ => 1 / |(n : ℝ) + 2| ^ (3 / 2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 2 (3 / 2)).2 (by norm_num)
  exact Summable.of_norm_bounded hp
    (norm_inverseHyperbolicSineTailTerm_le_pSeries x hx)

private theorem inverseHyperbolicSineTailTerm_continuous (n : ℕ) :
    Continuous (fun x : ℝ => inverseHyperbolicSineTailTerm x n) := by
  unfold inverseHyperbolicSineTailTerm
  fun_prop

theorem gap1 :
    ∀ x : ℝ, Real.log (x + Real.sqrt (1 + x ^ 2)) =
      ∫ t in (0 : ℝ)..x, 1 / Real.sqrt (1 + t ^ 2) := by
  intro x
  have hcont : Continuous (fun t : ℝ => 1 / Real.sqrt (1 + t ^ 2)) := by
    exact continuous_const.div
      (Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2)))
      (fun t => ne_of_gt (Real.sqrt_pos.2 (by positivity)))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := x) (fun t _ => hasDerivAt_asinh_log t)
    (hcont.intervalIntegrable 0 x)
  simpa using h.symm

theorem gap2
    (hintegral :
      ∀ x : ℝ, Real.log (x + Real.sqrt (1 + x ^ 2)) =
        ∫ t in (0 : ℝ)..x, 1 / Real.sqrt (1 + t ^ 2)) :
    ∀ x : ℝ, |x| < 1 →
      (∫ t in (0 : ℝ)..x, 1 / Real.sqrt (1 + t ^ 2)) =
        ∫ t in (0 : ℝ)..x, 1 + ∑' n, inverseSqrtTailTerm t n := by
  intro x hx
  apply intervalIntegral.integral_congr
  intro t ht
  have htx : |t| ≤ |x| := by
    simpa [Real.dist_eq] using Real.dist_left_le_of_mem_uIcc ht
  exact inverseSqrt_eq_one_add_tsum t (lt_of_le_of_lt htx hx)

theorem gap3
    (hintegral :
      ∀ x : ℝ, Real.log (x + Real.sqrt (1 + x ^ 2)) =
        ∫ t in (0 : ℝ)..x, 1 / Real.sqrt (1 + t ^ 2))
    (hseriesIntegral :
      ∀ x : ℝ, |x| < 1 →
        (∫ t in (0 : ℝ)..x, 1 / Real.sqrt (1 + t ^ 2)) =
          ∫ t in (0 : ℝ)..x, 1 + ∑' n, inverseSqrtTailTerm t n) :
    ∀ x : ℝ, |x| < 1 →
      Real.log (x + Real.sqrt (1 + x ^ 2)) =
        ∫ t in (0 : ℝ)..x, 1 + ∑' n, inverseSqrtTailTerm t n := by
  intro x hx
  exact (hintegral x).trans (hseriesIntegral x hx)

theorem gap4
    (hexpandedIntegral :
      ∀ x : ℝ, |x| < 1 →
        Real.log (x + Real.sqrt (1 + x ^ 2)) =
          ∫ t in (0 : ℝ)..x, 1 + ∑' n, inverseSqrtTailTerm t n) :
    ∀ x : ℝ, |x| < 1 →
      Real.log (x + Real.sqrt (1 + x ^ 2)) =
        x + ∑' n, inverseHyperbolicSineTailTerm x n := by
  intro x hx
  exact (hexpandedIntegral x hx).trans (integral_one_add_inverseSqrtTail x hx)

theorem gap5
    (hinterior :
      ∀ x : ℝ, |x| < 1 →
        Real.log (x + Real.sqrt (1 + x ^ 2)) =
          x + ∑' n, inverseHyperbolicSineTailTerm x n) :
    ∀ x : ℝ, |x| ≤ 1 →
      Summable (inverseHyperbolicSineTailTerm x) := by
  intro x hx
  exact inverseHyperbolicSineTailTerm_summable x hx

theorem gap6
    (hinterior :
      ∀ x : ℝ, |x| < 1 →
        Real.log (x + Real.sqrt (1 + x ^ 2)) =
          x + ∑' n, inverseHyperbolicSineTailTerm x n)
    (hsummable :
      ∀ x : ℝ, |x| ≤ 1 →
        Summable (inverseHyperbolicSineTailTerm x)) :
    ∀ x : ℝ, |x| ≤ 1 →
      Real.log (x + Real.sqrt (1 + x ^ 2)) =
        x + ∑' n, inverseHyperbolicSineTailTerm x n := by
  have hp : Summable (fun n : ℕ => 1 / |(n : ℝ) + 2| ^ (3 / 2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 2 (3 / 2)).2 (by norm_num)
  have hseriesCont :
      ContinuousOn (fun x : ℝ => ∑' n, inverseHyperbolicSineTailTerm x n)
        (Set.Icc (-1 : ℝ) 1) := by
    apply continuousOn_tsum
    · intro n
      exact (inverseHyperbolicSineTailTerm_continuous n).continuousOn
    · exact hp
    · intro n x hx
      exact norm_inverseHyperbolicSineTailTerm_le_pSeries x (abs_le.mpr hx) n
  have hrightCont :
      ContinuousOn
        (fun x : ℝ => x + ∑' n, inverseHyperbolicSineTailTerm x n)
        (Set.Icc (-1 : ℝ) 1) :=
    continuousOn_id.add hseriesCont
  have hsqrtCont : Continuous (fun x : ℝ => Real.sqrt (1 + x ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))
  have hargCont : Continuous (fun x : ℝ => x + Real.sqrt (1 + x ^ 2)) :=
    continuous_id.add hsqrtCont
  have hargPos : ∀ x : ℝ, 0 < x + Real.sqrt (1 + x ^ 2) := by
    intro x
    have hsqrtSq : (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hsqrtNonneg := Real.sqrt_nonneg (1 + x ^ 2)
    nlinarith
  have hleftCont :
      Continuous (fun x : ℝ => Real.log (x + Real.sqrt (1 + x ^ 2))) :=
    hargCont.log (fun x => (hargPos x).ne')
  have heq :
      Set.EqOn
        (fun x : ℝ => Real.log (x + Real.sqrt (1 + x ^ 2)))
        (fun x : ℝ => x + ∑' n, inverseHyperbolicSineTailTerm x n)
        (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    exact hinterior x (abs_lt.mpr hx)
  have hclosure :
      Set.Icc (-1 : ℝ) 1 ⊆ closure (Set.Ioo (-1 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
  have hclosed := heq.of_subset_closure hleftCont.continuousOn hrightCont
    Set.Ioo_subset_Icc_self hclosure
  intro x hx
  exact hclosed (abs_le.mp hx)

end

end ProofGap.Exercise2871
