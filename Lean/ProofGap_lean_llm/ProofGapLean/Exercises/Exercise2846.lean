import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2846

noncomputable section

def cosineCompositionTerm (u x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * u ^ (2 * n) * Real.arcsin x ^ (2 * n) /
    (Nat.factorial (2 * n) : ℝ)

def cosineArcsineTerm (u x : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      -(u ^ 2 *
          (∏ k ∈ Finset.range n, (((2 * (k + 1) : ℕ) : ℝ) ^ 2 - u ^ 2)) /
          (Nat.factorial (2 * (n + 1)) : ℝ) *
        x ^ (2 * (n + 1)))

private theorem cosineArcsineTerm_succ (u x : ℝ) (n : ℕ) :
    cosineArcsineTerm u x (n + 1) =
      cosineArcsineTerm u x n *
        (((((2 * n : ℕ) : ℝ) ^ 2 - u ^ 2) * x ^ 2) /
          (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ))) := by
  cases n with
  | zero =>
      norm_num [cosineArcsineTerm]
      ring
  | succ n =>
      simp only [cosineArcsineTerm]
      rw [Finset.prod_range_succ]
      have hfac :
          ((Nat.factorial (2 * (n + 2)) : ℕ) : ℝ) =
            ((2 * n + 4 : ℕ) : ℝ) * ((2 * n + 3 : ℕ) : ℝ) *
              (Nat.factorial (2 * (n + 1)) : ℝ) := by
        rw [show 2 * (n + 2) = (2 * n + 3) + 1 by omega,
          Nat.factorial_succ,
          show 2 * n + 3 = (2 * n + 2) + 1 by omega,
          Nat.factorial_succ]
        push_cast
        ring
      rw [hfac]
      have hf : (Nat.factorial (2 * (n + 1)) : ℝ) ≠ 0 := by positivity
      field_simp [hf]
      push_cast
      ring

private def ratioFactor (u x : ℝ) (n : ℕ) : ℝ :=
  ((((2 * n : ℕ) : ℝ) ^ 2 - u ^ 2) * x ^ 2) /
    (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ))

private theorem ratioFactor_tendsto (u x : ℝ) :
    Filter.Tendsto (ratioFactor u x) Filter.atTop (nhds (x ^ 2)) := by
  have hidx : Filter.Tendsto (fun n : ℕ => 2 * n) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with n hn
    omega
  have hcast :
      Filter.Tendsto (fun n : ℕ => (((2 * n : ℕ) : ℝ))) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hidx
  have ha :
      Filter.Tendsto
        (fun n : ℕ =>
          (((2 * n : ℕ) : ℝ)) / (((2 * n : ℕ) : ℝ) + 2))
        Filter.atTop (nhds 1) := by
    convert (tendsto_natCast_div_add_atTop (𝕜 := ℝ) 2).comp hidx using 1
  have hb :
      Filter.Tendsto
        (fun n : ℕ =>
          (((2 * n : ℕ) : ℝ)) / (((2 * n : ℕ) : ℝ) + 1))
        Filter.atTop (nhds 1) := by
    convert (tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1).comp hidx using 1
  have hc2 :
      Filter.Tendsto (fun n : ℕ => (((2 * n : ℕ) : ℝ)) + 2)
        Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_add hcast tendsto_const_nhds
  have hc1 :
      Filter.Tendsto (fun n : ℕ => (((2 * n : ℕ) : ℝ)) + 1)
        Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_add hcast tendsto_const_nhds
  have hi2 :
      Filter.Tendsto (fun n : ℕ => 1 / ((((2 * n : ℕ) : ℝ)) + 2))
        Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hc2
  have hi1 :
      Filter.Tendsto (fun n : ℕ => 1 / ((((2 * n : ℕ) : ℝ)) + 1))
        Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hc1
  have hmain :=
    ((ha.mul hb).mul_const (x ^ 2)).sub
      ((tendsto_const_nhds (x := u ^ 2 * x ^ 2)).mul (hi2.mul hi1))
  convert hmain using 1
  · funext n
    unfold ratioFactor
    have h1 : (((2 * n : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (((2 * n : ℕ) : ℝ) + 2) ≠ 0 := by positivity
    push_cast
    field_simp [h1, h2]
  · ring

private theorem cosineArcsineTerm_summable (u x : ℝ) (hx : |x| < 1) :
    Summable (cosineArcsineTerm u x) := by
  have hx2 : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).2 hx
  obtain ⟨r, hxr, hr⟩ := exists_between hx2
  have hnorm :
      Filter.Tendsto (fun n : ℕ => ‖ratioFactor u x n‖)
        Filter.atTop (nhds (x ^ 2)) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)] using
      (ratioFactor_tendsto u x).norm
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ‖ratioFactor u x n‖ ≤ r :=
    hnorm.eventually_le_const hxr
  apply summable_of_ratio_norm_eventually_le hr
  filter_upwards [hev] with n hn
  rw [cosineArcsineTerm_succ]
  change
    ‖cosineArcsineTerm u x n * ratioFactor u x n‖ ≤
      r * ‖cosineArcsineTerm u x n‖
  rw [norm_mul, mul_comm r]
  exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)

private def arcCoeff (u : ℝ) (n : ℕ) : ℝ :=
  cosineArcsineTerm u 1 n

private def firstSeriesTerm (u x : ℝ) (n : ℕ) : ℝ :=
  (((2 * n : ℕ) : ℝ)) * arcCoeff u n * x ^ (2 * n - 1)

private def secondSeriesTerm (u x : ℝ) (n : ℕ) : ℝ :=
  (((2 * n : ℕ) : ℝ)) * (((2 * n - 1 : ℕ) : ℝ)) *
    arcCoeff u n * x ^ (2 * n - 2)

private theorem cosineArcsineTerm_eq (u x : ℝ) (n : ℕ) :
    cosineArcsineTerm u x n = arcCoeff u n * x ^ (2 * n) := by
  cases n with
  | zero => simp [cosineArcsineTerm, arcCoeff]
  | succ n =>
      simp only [cosineArcsineTerm, arcCoeff]
      ring

private theorem arcCoeff_succ (u : ℝ) (n : ℕ) :
    arcCoeff u (n + 1) = arcCoeff u n * ratioFactor u 1 n := by
  simpa [arcCoeff, ratioFactor] using cosineArcsineTerm_succ u 1 n

private theorem hasDerivAt_cosineArcsineTerm (u x : ℝ) (n : ℕ) :
    HasDerivAt (fun y => cosineArcsineTerm u y n)
      (firstSeriesTerm u x n) x := by
  rw [funext fun y => cosineArcsineTerm_eq u y n]
  simpa [firstSeriesTerm, mul_assoc, mul_comm, mul_left_comm] using
    ((hasDerivAt_id x).pow (2 * n)).const_mul (arcCoeff u n)

private theorem hasDerivAt_firstSeriesTerm (u x : ℝ) (n : ℕ) :
    HasDerivAt (fun y => firstSeriesTerm u y n)
      (secondSeriesTerm u x n) x := by
  unfold firstSeriesTerm secondSeriesTerm
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    ((hasDerivAt_id x).pow (2 * n - 1)).const_mul
      ((((2 * n : ℕ) : ℝ)) * arcCoeff u n)

private def firstRatio (u x : ℝ) (n : ℕ) : ℝ :=
  ratioFactor u x n * (((n + 1 : ℕ) : ℝ) / (n : ℝ))

private def secondRatio (u x : ℝ) (n : ℕ) : ℝ :=
  ratioFactor u x n *
    (((2 * n + 2 : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ)) *
    (((2 * n + 1 : ℕ) : ℝ) / ((2 * n - 1 : ℕ) : ℝ))

private theorem firstSeriesTerm_succ (u x : ℝ) (n : ℕ) (hn : n ≠ 0) :
    firstSeriesTerm u x (n + 1) =
      firstSeriesTerm u x n * firstRatio u x n := by
  unfold firstSeriesTerm firstRatio
  rw [arcCoeff_succ]
  have hpow : x ^ (2 * (n + 1) - 1) = x ^ (2 * n - 1) * x ^ 2 := by
    rw [show 2 * (n + 1) - 1 = (2 * n - 1) + 2 by omega, pow_add]
  rw [hpow]
  unfold ratioFactor
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have h1 : (((2 * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have h2 : (((2 * n + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hnR, h1, h2]
  push_cast
  ring

private theorem secondSeriesTerm_succ (u x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    secondSeriesTerm u x (n + 1) =
      secondSeriesTerm u x n * secondRatio u x n := by
  unfold secondSeriesTerm secondRatio
  rw [arcCoeff_succ]
  have hpow : x ^ (2 * (n + 1) - 2) = x ^ (2 * n - 2) * x ^ 2 := by
    rw [show 2 * (n + 1) - 2 = (2 * n - 2) + 2 by omega, pow_add]
  rw [hpow]
  unfold ratioFactor
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hnm : (((2 * n - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (by omega : 2 * n - 1 ≠ 0)
  have h1 : (((2 * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have h2 : (((2 * n + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hcast0 : (((2 * n - 1 : ℕ) : ℝ)) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
    push_cast
    ring
  have hcast1 : (((2 * (n + 1) - 1 : ℕ) : ℝ)) = 2 * (n : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * (n + 1))]
    push_cast
    ring
  rw [hcast0, hcast1]
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnmR : 2 * (n : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hn0, hnm, hnmR, h1, h2]
  push_cast
  ring

private theorem firstRatio_tendsto (u x : ℝ) :
    Filter.Tendsto (firstRatio u x) Filter.atTop (nhds (x ^ 2)) := by
  have hrat :
      Filter.Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) / (n : ℝ)))
        Filter.atTop (nhds 1) := by
    convert tendsto_add_mul_div_add_mul_atTop_nhds
      (𝕜 := ℝ) 1 0 1 (d := 1) one_ne_zero using 1
    · funext n
      push_cast
      ring
    · norm_num
  convert (ratioFactor_tendsto u x).mul hrat using 1 <;>
    simp [firstRatio, Nat.cast_add, Nat.cast_one]

private theorem secondRatio_tendsto (u x : ℝ) :
    Filter.Tendsto (secondRatio u x) Filter.atTop (nhds (x ^ 2)) := by
  have hrat1 :
      Filter.Tendsto
        (fun n : ℕ => (((2 * n + 2 : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ)))
        Filter.atTop (nhds 1) := by
    convert tendsto_add_mul_div_add_mul_atTop_nhds
      (𝕜 := ℝ) 2 0 2 (d := 2) (by norm_num) using 1
    · funext n
      push_cast
      ring
    · norm_num
  have hrat2 :
      Filter.Tendsto
        (fun n : ℕ => (((2 * n + 1 : ℕ) : ℝ) / ((2 * n - 1 : ℕ) : ℝ)))
        Filter.atTop (nhds 1) := by
    have h := tendsto_add_mul_div_add_mul_atTop_nhds
      (𝕜 := ℝ) 1 (-1) 2 (d := 2) (by norm_num)
    have heq :
        (fun n : ℕ => (1 + 2 * (n : ℝ)) / (-1 + 2 * (n : ℝ))) =ᶠ[Filter.atTop]
          (fun n : ℕ =>
            (((2 * n + 1 : ℕ) : ℝ) / ((2 * n - 1 : ℕ) : ℝ))) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
      push_cast
      ring
    exact Filter.Tendsto.congr' heq (by simpa using h)
  convert ((ratioFactor_tendsto u x).mul hrat1).mul hrat2 using 1 <;>
    simp [secondRatio, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

private theorem firstSeriesTerm_summable (u x : ℝ) (hx : |x| < 1) :
    Summable (firstSeriesTerm u x) := by
  have hx2 : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).2 hx
  obtain ⟨r, hxr, hr⟩ := exists_between hx2
  have hnorm :
      Filter.Tendsto (fun n : ℕ => ‖firstRatio u x n‖)
        Filter.atTop (nhds (x ^ 2)) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)] using
      (firstRatio_tendsto u x).norm
  have hev := hnorm.eventually_le_const hxr
  apply summable_of_ratio_norm_eventually_le hr
  filter_upwards [Filter.eventually_ge_atTop 1, hev] with n hn hratio
  rw [firstSeriesTerm_succ u x n (by omega), norm_mul, mul_comm r]
  exact mul_le_mul_of_nonneg_left hratio (norm_nonneg _)

private theorem secondSeriesTerm_summable (u x : ℝ) (hx : |x| < 1) :
    Summable (secondSeriesTerm u x) := by
  have hx2 : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).2 hx
  obtain ⟨r, hxr, hr⟩ := exists_between hx2
  have hnorm :
      Filter.Tendsto (fun n : ℕ => ‖secondRatio u x n‖)
        Filter.atTop (nhds (x ^ 2)) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)] using
      (secondRatio_tendsto u x).norm
  have hev := hnorm.eventually_le_const hxr
  apply summable_of_ratio_norm_eventually_le hr
  filter_upwards [Filter.eventually_ge_atTop 1, hev] with n hn hratio
  rw [secondSeriesTerm_succ u x n hn, norm_mul, mul_comm r]
  exact mul_le_mul_of_nonneg_left hratio (norm_nonneg _)

private def seriesValue (u x : ℝ) : ℝ :=
  ∑' n, cosineArcsineTerm u x n

private def seriesSlope (u x : ℝ) : ℝ :=
  ∑' n, firstSeriesTerm u x n

private def seriesAccel (u x : ℝ) : ℝ :=
  ∑' n, secondSeriesTerm u x n

private theorem firstSeriesTerm_norm_le (u R y : ℝ) (hR : 0 ≤ R)
    (hy : |y| ≤ R) (n : ℕ) :
    ‖firstSeriesTerm u y n‖ ≤ ‖firstSeriesTerm u R n‖ := by
  unfold firstSeriesTerm
  simp only [norm_mul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hR]
  gcongr

private theorem secondSeriesTerm_norm_le (u R y : ℝ) (hR : 0 ≤ R)
    (hy : |y| ≤ R) (n : ℕ) :
    ‖secondSeriesTerm u y n‖ ≤ ‖secondSeriesTerm u R n‖ := by
  unfold secondSeriesTerm
  simp only [norm_mul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hR]
  gcongr

private theorem hasDerivAt_seriesValue (u x : ℝ) (hx : |x| < 1) :
    HasDerivAt (seriesValue u) (seriesSlope u x) x := by
  obtain ⟨R, hxR, hR1⟩ := exists_between hx
  have hR : 0 < R := (abs_nonneg x).trans_lt hxR
  have hRabs : |R| < 1 := by simpa [abs_of_pos hR] using hR1
  have hu : Summable (fun n : ℕ => ‖firstSeriesTerm u R n‖) :=
    (firstSeriesTerm_summable u R hRabs).norm
  unfold seriesValue seriesSlope
  refine hasDerivAt_tsum_of_isPreconnected (α := ℕ) (𝕜 := ℝ) (F := ℝ)
    (g := fun n y => cosineArcsineTerm u y n)
    (g' := fun n y => firstSeriesTerm u y n)
    (t := Set.Ioo (-R) R) (y₀ := 0) (y := x) hu isOpen_Ioo
    isPreconnected_Ioo ?_ ?_ ?_ ?_ ?_
  · intro n y hy
    exact hasDerivAt_cosineArcsineTerm u y n
  · intro n y hy
    exact firstSeriesTerm_norm_le u R y hR.le (le_of_lt (abs_lt.mpr hy)) n
  · exact ⟨by linarith, hR⟩
  · exact cosineArcsineTerm_summable u 0 (by norm_num)
  · exact abs_lt.mp hxR

private theorem hasDerivAt_seriesSlope (u x : ℝ) (hx : |x| < 1) :
    HasDerivAt (seriesSlope u) (seriesAccel u x) x := by
  obtain ⟨R, hxR, hR1⟩ := exists_between hx
  have hR : 0 < R := (abs_nonneg x).trans_lt hxR
  have hRabs : |R| < 1 := by simpa [abs_of_pos hR] using hR1
  have hu : Summable (fun n : ℕ => ‖secondSeriesTerm u R n‖) :=
    (secondSeriesTerm_summable u R hRabs).norm
  unfold seriesSlope seriesAccel
  refine hasDerivAt_tsum_of_isPreconnected (α := ℕ) (𝕜 := ℝ) (F := ℝ)
    (g := fun n y => firstSeriesTerm u y n)
    (g' := fun n y => secondSeriesTerm u y n)
    (t := Set.Ioo (-R) R) (y₀ := 0) (y := x) hu isOpen_Ioo
    isPreconnected_Ioo ?_ ?_ ?_ ?_ ?_
  · intro n y hy
    exact hasDerivAt_firstSeriesTerm u y n
  · intro n y hy
    exact secondSeriesTerm_norm_le u R y hR.le (le_of_lt (abs_lt.mpr hy)) n
  · exact ⟨by linarith, hR⟩
  · exact firstSeriesTerm_summable u 0 (by norm_num)
  · exact abs_lt.mp hxR

private theorem series_ode_term (u x : ℝ) (n : ℕ) :
    secondSeriesTerm u x (n + 1) - x ^ 2 * secondSeriesTerm u x n -
        x * firstSeriesTerm u x n +
      u ^ 2 * cosineArcsineTerm u x n = 0 := by
  cases n with
  | zero =>
      norm_num [secondSeriesTerm, firstSeriesTerm, cosineArcsineTerm,
        arcCoeff, ratioFactor]
      ring
  | succ n =>
      rw [cosineArcsineTerm_eq]
      unfold secondSeriesTerm firstSeriesTerm
      rw [arcCoeff_succ u (n + 1)]
      unfold ratioFactor
      have he0 : 2 * (n + 1) - 2 = 2 * n := by omega
      have he1 : 2 * ((n + 1) + 1) - 2 = 2 * n + 2 := by omega
      have hd : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
      have hd1 : 2 * ((n + 1) + 1) - 1 = 2 * n + 3 := by omega
      have hc : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [he0, he1, hd, hd1, hc, pow_add]
      have h1 : (((2 * (n + 1) + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have h2 : (((2 * (n + 1) + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp [h1, h2]
      push_cast
      ring

private theorem series_ode (u x : ℝ) (hx : |x| < 1) :
    (1 - x ^ 2) * seriesAccel u x - x * seriesSlope u x +
        u ^ 2 * seriesValue u x = 0 := by
  have hs0 := cosineArcsineTerm_summable u x hx
  have hs1 := firstSeriesTerm_summable u x hx
  have hs2 := secondSeriesTerm_summable u x hx
  have hshift :
      (∑' n : ℕ, secondSeriesTerm u x (n + 1)) = seriesAccel u x := by
    have h := hs2.sum_add_tsum_nat_add 1
    simpa [seriesAccel, secondSeriesTerm] using h
  have hterms :
      (∑' n : ℕ, secondSeriesTerm u x (n + 1)) =
        ∑' n : ℕ, (
          x ^ 2 * secondSeriesTerm u x n + x * firstSeriesTerm u x n -
            u ^ 2 * cosineArcsineTerm u x n) := by
    apply tsum_congr
    intro n
    have h := series_ode_term u x n
    linarith
  have hsum :
      (∑' n : ℕ, (
          x ^ 2 * secondSeriesTerm u x n + x * firstSeriesTerm u x n -
            u ^ 2 * cosineArcsineTerm u x n)) =
        x ^ 2 * seriesAccel u x + x * seriesSlope u x -
          u ^ 2 * seriesValue u x := by
    rw [((hs2.mul_left (x ^ 2)).add (hs1.mul_left x)).tsum_sub
      (hs0.mul_left (u ^ 2)),
      (hs2.mul_left (x ^ 2)).tsum_add (hs1.mul_left x),
      hs2.tsum_mul_left, hs1.tsum_mul_left, hs0.tsum_mul_left]
    rfl
  rw [hshift, hsum] at hterms
  linarith

private def odeField (u t : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2, (t * z.2 - u ^ 2 * z.1) / (1 - t ^ 2))

private def seriesState (u x : ℝ) : ℝ × ℝ :=
  (seriesValue u x, seriesSlope u x)

private theorem hasDerivAt_seriesState (u x : ℝ) (hx : |x| < 1) :
    HasDerivAt (seriesState u) (odeField u x (seriesState u x)) x := by
  have hq : 1 - x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x, (sq_lt_one_iff_abs_lt_one x).2 hx]
  have hacc :
      seriesAccel u x =
        (x * seriesSlope u x - u ^ 2 * seriesValue u x) / (1 - x ^ 2) := by
    apply (eq_div_iff hq).2
    have h := series_ode u x hx
    ring_nf at h ⊢
    linarith
  have hpair :=
    (hasDerivAt_seriesValue u x hx).prodMk
      (hasDerivAt_seriesSlope u x hx)
  simpa [seriesState, odeField, hacc] using hpair

private def targetValue (u x : ℝ) : ℝ :=
  Real.cos (u * Real.arcsin x)

private def targetSlope (u x : ℝ) : ℝ :=
  -u / Real.sqrt (1 - x ^ 2) * Real.sin (u * Real.arcsin x)

private def targetState (u x : ℝ) : ℝ × ℝ :=
  (targetValue u x, targetSlope u x)

private theorem hasDerivAt_targetValue (u x : ℝ) (hx : |x| < 1) :
    HasDerivAt (targetValue u) (targetSlope u x) x := by
  have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have hi :=
    (Real.hasDerivAt_arcsin (ne_of_gt hxI.1) (ne_of_lt hxI.2)).const_mul u
  have hc := (Real.hasDerivAt_cos (u * Real.arcsin x)).comp x hi
  simpa [targetValue, targetSlope, Function.comp_apply, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using hc

private theorem hasDerivAt_targetSlope (u x : ℝ) (hx : |x| < 1) :
    HasDerivAt (targetSlope u)
      ((x * targetSlope u x - u ^ 2 * targetValue u x) / (1 - x ^ 2)) x := by
  have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hx
  have hq : 0 < 1 - x ^ 2 := by
    nlinarith [sq_nonneg x, (sq_lt_one_iff_abs_lt_one x).2 hx]
  have hqn : 1 - x ^ 2 ≠ 0 := ne_of_gt hq
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt hq.le
  have hpoly : HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp <;> ring
  have hsqrt := (Real.hasDerivAt_sqrt hqn).comp x hpoly
  have hi :=
    (Real.hasDerivAt_arcsin (ne_of_gt hxI.1) (ne_of_lt hxI.2)).const_mul u
  have hsin := (Real.hasDerivAt_sin (u * Real.arcsin x)).comp x hi
  have hraw := ((hasDerivAt_const x (-u)).div hsqrt hs).mul hsin
  have hraw' :
      HasDerivAt (targetSlope u)
        ((0 * Real.sqrt (1 - x ^ 2) -
              (-u) * (1 / (2 * Real.sqrt (1 - x ^ 2)) * (-2 * x))) /
            Real.sqrt (1 - x ^ 2) ^ 2 * Real.sin (u * Real.arcsin x) +
          (-u) / Real.sqrt (1 - x ^ 2) *
            (Real.cos (u * Real.arcsin x) *
              (u * (1 / Real.sqrt (1 - x ^ 2))))) x := by
    simpa only [targetSlope, Function.comp_apply] using hraw
  convert hraw' using 1
  · simp only [targetSlope, targetValue]
    field_simp [hs, hqn]
    rw [hs2]
    ring

private theorem hasDerivAt_targetState (u x : ℝ) (hx : |x| < 1) :
    HasDerivAt (targetState u) (odeField u x (targetState u x)) x := by
  have hpair :=
    (hasDerivAt_targetValue u x hx).prodMk (hasDerivAt_targetSlope u x hx)
  simpa [targetState, odeField] using hpair

private theorem exists_odeField_lipschitz (u R : ℝ) (hR : 0 < R) (hR1 : R < 1) :
    ∃ K : NNReal, ∀ t ∈ Set.Ioo (-R) R, LipschitzWith K (odeField u t) := by
  have hden : 0 < 1 - R ^ 2 := by nlinarith
  let C : NNReal :=
    ⟨(R + u ^ 2) / (1 - R ^ 2), div_nonneg (by positivity) hden.le⟩
  refine ⟨max 1 C, ?_⟩
  intro t ht
  have htSq : t ^ 2 < R ^ 2 := sq_lt_sq' ht.1 ht.2
  have hdenT : 0 < 1 - t ^ 2 := by nlinarith
  have hdenLe : 1 - R ^ 2 ≤ 1 - t ^ 2 := by nlinarith
  have hnum : |t| + u ^ 2 ≤ R + u ^ 2 := by
    have habs : |t| < R := abs_lt.mpr ht
    linarith
  have hnum0 : 0 ≤ |t| + u ^ 2 := by positivity
  have hcoefReal :
      ‖t / (1 - t ^ 2)‖ + ‖u ^ 2 / (1 - t ^ 2)‖ ≤
        (R + u ^ 2) / (1 - R ^ 2) := by
    simp only [norm_div, Real.norm_eq_abs]
    rw [abs_of_pos hdenT, abs_of_nonneg (sq_nonneg u)]
    calc
      |t| / (1 - t ^ 2) + u ^ 2 / (1 - t ^ 2) =
          (|t| + u ^ 2) / (1 - t ^ 2) := by ring
      _ ≤ (R + u ^ 2) / (1 - R ^ 2) :=
        div_le_div₀ (by positivity) hnum hden hdenLe
  have hcoef :
      ‖t / (1 - t ^ 2)‖₊ + ‖u ^ 2 / (1 - t ^ 2)‖₊ ≤ C := by
    apply NNReal.coe_le_coe.mp
    simpa [C] using hcoefReal
  have ha :
      LipschitzWith ‖t / (1 - t ^ 2)‖₊
        (fun z : ℝ × ℝ => (t / (1 - t ^ 2)) * z.2) := by
    convert (lipschitzWith_smul (t / (1 - t ^ 2))).comp
      (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × ℝ → ℝ)) using 1 <;>
      simp [Function.comp_def, smul_eq_mul]
  have hb :
      LipschitzWith ‖u ^ 2 / (1 - t ^ 2)‖₊
        (fun z : ℝ × ℝ => (u ^ 2 / (1 - t ^ 2)) * z.1) := by
    convert (lipschitzWith_smul (u ^ 2 / (1 - t ^ 2))).comp
      (LipschitzWith.prod_fst : LipschitzWith 1 (Prod.fst : ℝ × ℝ → ℝ)) using 1 <;>
      simp [Function.comp_def, smul_eq_mul]
  have hsecond :
      LipschitzWith
        (‖t / (1 - t ^ 2)‖₊ + ‖u ^ 2 / (1 - t ^ 2)‖₊)
        (fun z : ℝ × ℝ => (t * z.2 - u ^ 2 * z.1) / (1 - t ^ 2)) := by
    convert ha.sub hb using 1
    funext z
    field_simp [ne_of_gt hdenT]
  have hfield :
      LipschitzWith
        (max 1 (‖t / (1 - t ^ 2)‖₊ + ‖u ^ 2 / (1 - t ^ 2)‖₊))
        (odeField u t) := by
    simpa [odeField] using
      (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × ℝ → ℝ)).prodMk
        hsecond
  exact hfield.weaken (max_le_max le_rfl hcoef)

private theorem seriesValue_zero (u : ℝ) : seriesValue u 0 = 1 := by
  have h := (cosineArcsineTerm_summable u 0 (by norm_num)).sum_add_tsum_nat_add 1
  simpa [seriesValue, cosineArcsineTerm] using h.symm

private theorem seriesSlope_zero (u : ℝ) : seriesSlope u 0 = 0 := by
  unfold seriesSlope
  calc
    (∑' n : ℕ, firstSeriesTerm u 0 n) = ∑' _n : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro n
      cases n with
      | zero => simp [firstSeriesTerm]
      | succ n =>
          unfold firstSeriesTerm
          rw [zero_pow (by omega : 2 * (n + 1) - 1 ≠ 0)]
          ring
    _ = 0 := tsum_zero

private theorem seriesState_zero_eq_targetState (u : ℝ) :
    seriesState u 0 = targetState u 0 := by
  ext <;>
    simp [seriesState, targetState, seriesValue_zero, seriesSlope_zero,
      targetValue, targetSlope]

private theorem targetValue_eq_seriesValue (u x : ℝ) (hx : |x| < 1) :
    targetValue u x = seriesValue u x := by
  obtain ⟨R, hxR, hR1⟩ := exists_between hx
  have hR : 0 < R := (abs_nonneg x).trans_lt hxR
  obtain ⟨K, hK⟩ := exists_odeField_lipschitz u R hR hR1
  have hstates : Set.EqOn (seriesState u) (targetState u) (Set.Ioo (-R) R) := by
    apply ODE_solution_unique_of_mem_Ioo
      (v := odeField u) (s := fun _ => Set.univ) (K := K) (t₀ := 0)
    · intro t ht
      exact (hK t ht).lipschitzOnWith
    · exact ⟨by linarith, hR⟩
    · intro t ht
      have ht1 : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2.trans hR1⟩
      exact ⟨hasDerivAt_seriesState u t (abs_lt.mpr ht1), Set.mem_univ _⟩
    · intro t ht
      have ht1 : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2.trans hR1⟩
      exact ⟨hasDerivAt_targetState u t (abs_lt.mpr ht1), Set.mem_univ _⟩
    · exact seriesState_zero_eq_targetState u
  have hstate := hstates (abs_lt.mp hxR)
  exact (congrArg Prod.fst hstate).symm

theorem gap1
    (f : ℝ → ℝ) (u : ℝ) (hf : ∀ x, f x = Real.cos (u * Real.arcsin x)) :
    ∀ x, f x = ∑' n, cosineCompositionTerm u x n := by
  intro x
  rw [hf, Real.cos_eq_tsum]
  apply tsum_congr
  intro n
  unfold cosineCompositionTerm
  rw [mul_pow]
  ring

theorem gap2
    (f : ℝ → ℝ) (u : ℝ) (hf : ∀ x, f x = Real.cos (u * Real.arcsin x))
    (hcosine : ∀ x, f x = ∑' n, cosineCompositionTerm u x n) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      (∑' n, cosineCompositionTerm u x n) =
        ∑' n, cosineArcsineTerm u x n := by
  intro x hx
  calc
    (∑' n, cosineCompositionTerm u x n) = f x := (hcosine x).symm
    _ = targetValue u x := by simpa [targetValue] using hf x
    _ = seriesValue u x := targetValue_eq_seriesValue u x (abs_lt.mpr hx)
    _ = ∑' n, cosineArcsineTerm u x n := rfl

theorem gap3
    (f : ℝ → ℝ) (u : ℝ) (hf : ∀ x, f x = Real.cos (u * Real.arcsin x))
    (hcosine : ∀ x, f x = ∑' n, cosineCompositionTerm u x n)
    (htransform :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        (∑' n, cosineCompositionTerm u x n) =
          ∑' n, cosineArcsineTerm u x n) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1, f x = ∑' n, cosineArcsineTerm u x n := by
  intro x hx
  exact (hcosine x).trans (htransform x hx)

theorem gap4
    (f : ℝ → ℝ) (u : ℝ) (hf : ∀ x, f x = Real.cos (u * Real.arcsin x))
    (hcosine : ∀ x, f x = ∑' n, cosineCompositionTerm u x n)
    (htransform :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        (∑' n, cosineCompositionTerm u x n) =
          ∑' n, cosineArcsineTerm u x n)
    (hfseries :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, f x = ∑' n, cosineArcsineTerm u x n) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1, Summable (cosineArcsineTerm u x) := by
  intro x hx
  exact cosineArcsineTerm_summable u x (abs_lt.mpr hx)

end

end ProofGap.Exercise2846
