import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise463

noncomputable section

def pow13 (x : ℝ) : ℝ := Real.rpow x (1 / 3 : ℝ)
def pow23 (x : ℝ) : ℝ := Real.rpow x (2 / 3 : ℝ)
def pow43 (x : ℝ) : ℝ := Real.rpow x (4 / 3 : ℝ)
def original (x : ℝ) : ℝ := pow13 x * (pow23 (x + 1) - pow23 (x - 1))
def denominator (x : ℝ) : ℝ :=
  pow43 (x + 1) + pow23 (x ^ 2 - 1) + pow43 (x - 1)
def rationalized (x : ℝ) : ℝ :=
  original x * denominator x / denominator x
def normalized (x : ℝ) : ℝ :=
  4 / (pow43 (1 + 1 / x) + pow23 (1 - 1 / x ^ 2) + pow43 (1 - 1 / x))
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Exercise 463, gap 1; make the rationalizing factor explicit. -/
private theorem rpow_nat_eq_explicit (x : ℝ) (n : ℕ) :
    Real.rpow x (n : ℝ) = x ^ n := by
  change x ^ (n : ℝ) = x ^ n
  exact Real.rpow_natCast x n

private theorem rpow_rpow_mul_explicit
    (x a b : ℝ) (hx : 0 ≤ x) :
    Real.rpow (Real.rpow x a) b = Real.rpow x (a * b) := by
  change (x ^ a) ^ b = x ^ (a * b)
  rw [← Real.rpow_mul hx]

private theorem mul_rpow_explicit
    (x y a : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.rpow (x * y) a = Real.rpow x a * Real.rpow y a := by
  change (x * y) ^ a = x ^ a * y ^ a
  rw [Real.mul_rpow hx hy]

private theorem rpow_add_explicit
    (x a b : ℝ) (hx : 0 < x) :
    Real.rpow x a * Real.rpow x b = Real.rpow x (a + b) := by
  change x ^ a * x ^ b = x ^ (a + b)
  rw [← Real.rpow_add hx]

private theorem rpow_one_explicit (x : ℝ) : Real.rpow x (1 : ℝ) = x := by
  simpa using rpow_nat_eq_explicit x 1

private theorem rpow_def_of_pos_explicit
    (x p : ℝ) (hx : 0 < x) :
    Real.rpow x p = Real.exp (Real.log x * p) := by
  change x ^ p = Real.exp (Real.log x * p)
  rw [Real.rpow_def_of_pos hx]

private theorem rpow_two_thirds_sq (y : ℝ) (hy : 0 ≤ y) :
    (Real.rpow y (2 / 3 : ℝ)) ^ 2 = Real.rpow y (4 / 3 : ℝ) := by
  calc
    (Real.rpow y (2 / 3 : ℝ)) ^ 2 =
        Real.rpow (Real.rpow y (2 / 3 : ℝ)) (2 : ℝ) :=
      (rpow_nat_eq_explicit (Real.rpow y (2 / 3 : ℝ)) 2).symm
    _ = Real.rpow y ((2 / 3 : ℝ) * 2) :=
      rpow_rpow_mul_explicit y (2 / 3 : ℝ) 2 hy
    _ = Real.rpow y (4 / 3 : ℝ) := by norm_num

private theorem rpow_two_thirds_cube (y : ℝ) (hy : 0 ≤ y) :
    (Real.rpow y (2 / 3 : ℝ)) ^ 3 = y ^ 2 := by
  calc
    (Real.rpow y (2 / 3 : ℝ)) ^ 3 =
        Real.rpow (Real.rpow y (2 / 3 : ℝ)) (3 : ℝ) :=
      (rpow_nat_eq_explicit (Real.rpow y (2 / 3 : ℝ)) 3).symm
    _ = Real.rpow y ((2 / 3 : ℝ) * 3) :=
      rpow_rpow_mul_explicit y (2 / 3 : ℝ) 3 hy
    _ = Real.rpow y (2 : ℝ) := by norm_num
    _ = y ^ 2 := rpow_nat_eq_explicit y 2

private theorem rationalized_eq_normalized_of_one_lt (x : ℝ) (hx : 1 < x) :
    rationalized x = normalized x := by
  have hx0 : 0 < x := by linarith
  have hxp1 : 0 < x + 1 := by linarith
  have hxm1 : 0 < x - 1 := by linarith
  have hxsq : 1 < x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
  have hplusNorm : 0 < 1 + 1 / x := by positivity
  have hminusNorm : 0 < 1 - 1 / x := by
    apply sub_pos.mpr
    rw [div_lt_iff₀ hx0]
    simpa using hx
  have hmiddleNorm : 0 < 1 - 1 / x ^ 2 := by
    apply sub_pos.mpr
    rw [div_lt_iff₀ (by positivity : 0 < x ^ 2)]
    simpa using hxsq
  have hplusSq : (pow23 (x + 1)) ^ 2 = pow43 (x + 1) := by
    unfold pow23 pow43
    exact rpow_two_thirds_sq _ hxp1.le
  have hminusSq : (pow23 (x - 1)) ^ 2 = pow43 (x - 1) := by
    unfold pow23 pow43
    exact rpow_two_thirds_sq _ hxm1.le
  have hplusCube : (pow23 (x + 1)) ^ 3 = (x + 1) ^ 2 := by
    unfold pow23
    exact rpow_two_thirds_cube _ hxp1.le
  have hminusCube : (pow23 (x - 1)) ^ 3 = (x - 1) ^ 2 := by
    unfold pow23
    exact rpow_two_thirds_cube _ hxm1.le
  have hmiddle : pow23 (x ^ 2 - 1) = pow23 (x + 1) * pow23 (x - 1) := by
    unfold pow23
    rw [show x ^ 2 - 1 = (x + 1) * (x - 1) by ring]
    exact mul_rpow_explicit _ _ _ hxp1.le hxm1.le
  have hnum : original x * denominator x = 4 * pow43 x := by
    unfold original denominator
    rw [hmiddle, ← hplusSq, ← hminusSq]
    calc
      pow13 x * (pow23 (x + 1) - pow23 (x - 1)) *
          ((pow23 (x + 1)) ^ 2 +
            pow23 (x + 1) * pow23 (x - 1) +
            (pow23 (x - 1)) ^ 2) =
          pow13 x * ((pow23 (x + 1)) ^ 3 - (pow23 (x - 1)) ^ 3) := by ring
      _ = pow13 x * ((x + 1) ^ 2 - (x - 1) ^ 2) := by
        rw [hplusCube, hminusCube]
      _ = pow13 x * (4 * x) := by ring
      _ = 4 * pow43 x := by
        unfold pow13 pow43
        calc
          Real.rpow x (1 / 3 : ℝ) * (4 * x) =
              4 * (Real.rpow x (1 / 3 : ℝ) * Real.rpow x (1 : ℝ)) := by
                rw [rpow_one_explicit]
                ring
          _ = 4 * Real.rpow x ((1 / 3 : ℝ) + 1) := by
                rw [rpow_add_explicit x (1 / 3 : ℝ) 1 hx0]
          _ = 4 * Real.rpow x (4 / 3 : ℝ) := by norm_num
  have hplusScale :
      pow43 (x + 1) = pow43 x * pow43 (1 + 1 / x) := by
    unfold pow43
    rw [show x + 1 = x * (1 + 1 / x) by field_simp [ne_of_gt hx0]]
    exact mul_rpow_explicit _ _ _ hx0.le hplusNorm.le
  have hminusScale :
      pow43 (x - 1) = pow43 x * pow43 (1 - 1 / x) := by
    unfold pow43
    rw [show x - 1 = x * (1 - 1 / x) by field_simp [ne_of_gt hx0]]
    exact mul_rpow_explicit _ _ _ hx0.le hminusNorm.le
  have hxSqRpow :
      Real.rpow (x ^ 2) (2 / 3 : ℝ) = Real.rpow x (4 / 3 : ℝ) := by
    rw [show x ^ 2 = x * x by ring]
    calc
      Real.rpow (x * x) (2 / 3 : ℝ) =
          Real.rpow x (2 / 3 : ℝ) * Real.rpow x (2 / 3 : ℝ) :=
        mul_rpow_explicit _ _ _ hx0.le hx0.le
      _ = (Real.rpow x (2 / 3 : ℝ)) ^ 2 := by ring
      _ = Real.rpow x (4 / 3 : ℝ) := rpow_two_thirds_sq x hx0.le
  have hmiddleScale :
      pow23 (x ^ 2 - 1) = pow43 x * pow23 (1 - 1 / x ^ 2) := by
    unfold pow23 pow43
    rw [show x ^ 2 - 1 = x ^ 2 * (1 - 1 / x ^ 2) by
      field_simp [ne_of_gt hx0]
      <;> ring]
    calc
      Real.rpow (x ^ 2 * (1 - 1 / x ^ 2)) (2 / 3 : ℝ) =
          Real.rpow (x ^ 2) (2 / 3 : ℝ) *
            Real.rpow (1 - 1 / x ^ 2) (2 / 3 : ℝ) :=
        mul_rpow_explicit _ _ _ (sq_nonneg x) hmiddleNorm.le
      _ = Real.rpow x (4 / 3 : ℝ) *
            Real.rpow (1 - 1 / x ^ 2) (2 / 3 : ℝ) := by rw [hxSqRpow]
  have hden : denominator x =
      pow43 x *
        (pow43 (1 + 1 / x) + pow23 (1 - 1 / x ^ 2) + pow43 (1 - 1 / x)) := by
    unfold denominator
    rw [hplusScale, hmiddleScale, hminusScale]
    ring
  have hx43 : pow43 x ≠ 0 := by
    apply ne_of_gt
    unfold pow43
    exact Real.rpow_pos_of_pos hx0 _
  have hd :
      pow43 (1 + 1 / x) + pow23 (1 - 1 / x ^ 2) + pow43 (1 - 1 / x) ≠ 0 := by
    apply ne_of_gt
    unfold pow43 pow23
    exact add_pos
      (add_pos
        (Real.rpow_pos_of_pos hplusNorm _)
        (Real.rpow_pos_of_pos hmiddleNorm _))
      (Real.rpow_pos_of_pos hminusNorm _)
  unfold rationalized normalized
  rw [hnum, hden]
  field_simp [hx43, hd]

private theorem tendsto_rpow_const_one_atTop
    (p : ℝ) {f : ℝ → ℝ}
    (hf : Filter.Tendsto f Filter.atTop (nhds 1))
    (hpos : ∀ᶠ x in Filter.atTop, 0 < f x) :
    Filter.Tendsto (fun x => Real.rpow (f x) p) Filter.atTop (nhds 1) := by
  have hlog : Filter.Tendsto (fun x => Real.log (f x)) Filter.atTop (nhds 0) := by
    have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hf
    simpa using h
  have hp : Filter.Tendsto (fun _ : ℝ => p) Filter.atTop (nhds p) :=
    tendsto_const_nhds
  have hmul : Filter.Tendsto
      (fun x => Real.log (f x) * p) Filter.atTop (nhds 0) := by
    simpa using hlog.mul hp
  have hexp : Filter.Tendsto
      (fun x => Real.exp (Real.log (f x) * p)) Filter.atTop (nhds 1) := by
    simpa using Real.continuous_exp.continuousAt.tendsto.comp hmul
  apply hexp.congr'
  filter_upwards [hpos] with x hx
  exact (rpow_def_of_pos_explicit (f x) p hx).symm

theorem gap1 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity rationalized L := by
  unfold HasLimitAtPosInfinity
  apply Filter.tendsto_congr'
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  have hxp1 : 0 < x + 1 := by linarith
  have hxm1 : 0 ≤ x - 1 := by linarith
  have hxsqm1 : 0 ≤ x ^ 2 - 1 := by
    nlinarith [sq_nonneg (x - 1)]
  have hden : 0 < denominator x := by
    unfold denominator pow43 pow23
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg
        (Real.rpow_pos_of_pos hxp1 _)
        (Real.rpow_nonneg hxsqm1 _))
      (Real.rpow_nonneg hxm1 _)
  simp [rationalized, ne_of_gt hden]

/-- Exercise 463, gap 2; normalize by powers of `x`. -/
theorem gap2 (L : ℝ) :
    HasLimitAtPosInfinity rationalized L ↔ HasLimitAtPosInfinity normalized L := by
  unfold HasLimitAtPosInfinity
  apply Filter.tendsto_congr'
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  exact rationalized_eq_normalized_of_one_lt x (by linarith)

/-- Exercise 463, gap 3. -/
theorem gap3 : HasLimitAtPosInfinity normalized (4 / 3) := by
  unfold HasLimitAtPosInfinity normalized pow43 pow23
  have hinv : Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
  have hinv2 : Filter.Tendsto (fun x : ℝ => 1 / x ^ 2) Filter.atTop (nhds 0) := by
    simpa [one_div, inv_pow] using hinv.pow 2
  have hplus : Filter.Tendsto (fun x : ℝ => 1 + 1 / x) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hinv
  have hmiddle : Filter.Tendsto (fun x : ℝ => 1 - 1 / x ^ 2) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hinv2
  have hminus : Filter.Tendsto (fun x : ℝ => 1 - 1 / x) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hinv
  have hplusPos : ∀ᶠ x : ℝ in Filter.atTop, 0 < 1 + 1 / x := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hi : 0 < 1 / x := one_div_pos.mpr hx0
    linarith
  have hmiddlePos : ∀ᶠ x : ℝ in Filter.atTop, 0 < 1 - 1 / x ^ 2 := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hxsq : 1 < x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
    apply sub_pos.mpr
    rw [div_lt_iff₀ (by positivity : 0 < x ^ 2)]
    simpa using hxsq
  have hminusPos : ∀ᶠ x : ℝ in Filter.atTop, 0 < 1 - 1 / x := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hx1 : 1 < x := by linarith
    apply sub_pos.mpr
    rw [div_lt_iff₀ hx0]
    simpa using hx1
  have hp43a := tendsto_rpow_const_one_atTop (4 / 3 : ℝ) hplus hplusPos
  have hp23 := tendsto_rpow_const_one_atTop (2 / 3 : ℝ) hmiddle hmiddlePos
  have hp43b := tendsto_rpow_const_one_atTop (4 / 3 : ℝ) hminus hminusPos
  have hden : Filter.Tendsto
      (fun x : ℝ =>
        Real.rpow (1 + 1 / x) (4 / 3 : ℝ) +
          Real.rpow (1 - 1 / x ^ 2) (2 / 3 : ℝ) +
          Real.rpow (1 - 1 / x) (4 / 3 : ℝ))
      Filter.atTop (nhds 3) := by
    convert (hp43a.add hp23).add hp43b using 1 <;> norm_num
  convert (tendsto_const_nhds.div hden (by norm_num : (3 : ℝ) ≠ 0)) using 1 <;> norm_num

end

end ProofGap.Exercise463
