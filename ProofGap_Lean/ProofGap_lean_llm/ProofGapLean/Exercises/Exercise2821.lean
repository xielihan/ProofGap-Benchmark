import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2821

noncomputable section

open Filter
open scoped BigOperators Topology

def firstCoefficient (a : ℝ) (n : ℕ) : ℝ :=
  a ^ n / n

def secondCoefficient (b : ℝ) (n : ℕ) : ℝ :=
  b ^ n / (n : ℝ) ^ 2

def coefficient (a b : ℝ) (n : ℕ) : ℝ :=
  firstCoefficient a n + secondCoefficient b n

def powerTerm (a b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  coefficient a b n * x ^ n

def SeriesConvergesAt (a b x : ℝ) : Prop :=
  Summable (fun k : ℕ => powerTerm a b (k + 1) x)
    (SummationFilter.conditional ℕ)

def radius (a b : ℝ) : ℝ :=
  min (1 / a) (1 / b)

def HasConvergenceRadius (c : ℕ → ℝ) (r : ℝ) : Prop :=
  (∀ x : ℝ, |x| < r → Summable (fun k : ℕ => c (k + 1) * x ^ (k + 1))) ∧
    (∀ x : ℝ, r < |x| →
      ¬ Summable (fun k : ℕ => c (k + 1) * x ^ (k + 1)))

def ConditionallySummable (u : ℕ → ℝ) : Prop :=
  Summable u (SummationFilter.conditional ℕ) ∧
    ¬ Summable (fun n => |u n|)

def alternatingHarmonic (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / n

def alternatingSquare (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (n : ℝ) ^ 2

def leftSmallTerm (a b : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (a / b) ^ n / n

def leftSecondTerm (a b : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (b / a) ^ n / (n : ℝ) ^ 2

private theorem succ_ratio_tendsto_one :
    Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ))
      atTop (𝓝 1) := by
  have hcast : Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hrecip : Tendsto
      (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  have hlim : Tendsto
      (fun n : ℕ => 1 - 1 / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hrecip
  apply hlim.congr'
  filter_upwards with n
  have hn : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  field_simp [hn.ne']
  norm_num [Nat.cast_add, Nat.cast_one]
  <;> ring

private theorem leftSmall_abs_summable (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Summable (fun k : ℕ => |leftSmallTerm a b (k + 1)|) := by
  have hb : 0 < b := ha.trans hab
  have hq0 : 0 < a / b := div_pos ha hb
  have hq1 : a / b < 1 := (div_lt_one hb).2 hab
  have hgeo : Summable (fun k : ℕ => (a / b) ^ (k + 1)) := by
    have h := summable_geometric_of_norm_lt_one
      (show ‖a / b‖ < 1 by
        simpa [Real.norm_eq_abs, abs_div, abs_of_pos ha, abs_of_pos hb] using hq1)
    simpa [pow_succ, mul_comm] using h.mul_left (a / b)
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hgeo
  unfold leftSmallTerm
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    abs_pow, abs_of_pos hq0]
  rw [abs_of_pos (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) by positivity)]
  simp only [one_mul]
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
  exact div_le_self (pow_nonneg hq0.le _) hk

private theorem alternatingSquare_abs_summable :
    Summable (fun k : ℕ => |alternatingSquare (k + 1)|) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).2 hbase
  exact hshift.congr (fun k => by
    unfold alternatingSquare
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_nonneg (sq_nonneg (((k + 1 : ℕ) : ℝ)))] )

private theorem leftSecond_abs_summable (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    Summable (fun k : ℕ => |leftSecondTerm a b (k + 1)|) := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hq0 : 0 ≤ b / a := (div_pos hb ha).le
  have hq1 : b / a ≤ 1 := (div_le_one ha).2 hba
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).2 hbase
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hshift
  unfold leftSecondTerm
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    abs_pow, abs_of_nonneg hq0,
    abs_of_nonneg (sq_nonneg (((k + 1 : ℕ) : ℝ)))]
  simp only [one_mul]
  exact div_le_div_of_nonneg_right (pow_le_one₀ hq0 hq1)
    (sq_nonneg (((k + 1 : ℕ) : ℝ)))

private theorem summable_conditional_iff {u : ℕ → ℝ} :
    Summable u (SummationFilter.conditional ℕ) ↔
      ∃ l : ℝ,
        Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, u k) atTop (𝓝 l) := by
  simp only [Summable, HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff]
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l, by simpa [Function.comp_def] using hl⟩
  · rintro ⟨l, hl⟩
    exact ⟨l, by simpa [Function.comp_def] using hl⟩

private theorem tendsto_zero_of_summable_conditional {u : ℕ → ℝ}
    (hu : Summable u (SummationFilter.conditional ℕ)) :
    Tendsto u atTop (𝓝 0) := by
  rcases summable_conditional_iff.mp hu with ⟨l, hl⟩
  have hdiff := (hl.comp (tendsto_add_atTop_nat 1)).sub hl
  simpa [Finset.sum_range_succ] using hdiff

private theorem alternatingHarmonic_conditional_summable :
    Summable (fun k : ℕ => alternatingHarmonic (k + 1))
      (SummationFilter.conditional ℕ) := by
  have hanti : Antitone (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))) := by
    intro m n hmn
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hzero : Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  obtain ⟨l, hl⟩ := hanti.tendsto_alternating_series_of_tendsto_zero hzero
  apply summable_conditional_iff.mpr
  refine ⟨-l, ?_⟩
  convert hl.neg using 1
  · funext n
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    unfold alternatingHarmonic
    rw [pow_succ]
    ring

private theorem alternatingHarmonic_not_summable :
    ¬ Summable (fun k : ℕ => alternatingHarmonic (k + 1)) := by
  intro hs
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).1
  exact hs.abs.congr (fun k => by
    unfold alternatingHarmonic
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_pos (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) by positivity)])

private theorem harmonic_not_conditional_summable :
    ¬ Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ)))
      (SummationFilter.conditional ℕ) := by
  intro hs
  rcases summable_conditional_iff.mp hs with ⟨l, hl⟩
  have htop : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, 1 / (((k + 1 : ℕ) : ℝ)))
      atTop atTop := by
    simpa using Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨n, hn, hn'⟩ :=
    ((tendsto_atTop.1 htop (l + 1)).and
      (hl.eventually_lt_const (lt_add_one l))).exists
  linarith

private theorem tendsto_geometric_div_nat_pow_atTop (q : ℝ) (m : ℕ)
    (hq : 1 < q) :
    Tendsto
      (fun n : ℕ => q ^ (n + 1) / (((n + 1 : ℕ) : ℝ) ^ m))
      atTop atTop := by
  have hzero : Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ m) / q ^ (n + 1))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using
      (tendsto_pow_const_div_const_pow_of_one_lt m hq).comp
        (tendsto_add_atTop_nat 1)
  have hpositive : Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ m) / q ^ (n + 1))
      atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hzero, ?_⟩
    exact Filter.Eventually.of_forall (fun n =>
      div_pos
        (pow_pos (show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) by positivity) _)
        (pow_pos (show (0 : ℝ) < q by linarith) _))
  apply hpositive.inv_tendsto_nhdsGT_zero.congr'
  exact Filter.Eventually.of_forall (fun n => by
    simp only [Pi.inv_apply, inv_div])

private theorem not_seriesConvergesAt_of_one_lt_b_mul_abs
    (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hq : 1 < b * |x|) :
    ¬ SeriesConvergesAt a b x := by
  intro hs
  have hzero : Tendsto
      (fun k : ℕ => |powerTerm a b (k + 1) x|) atTop (𝓝 0) := by
    simpa using (tendsto_zero_of_summable_conditional hs).abs
  have hdom := tendsto_geometric_div_nat_pow_atTop (b * |x|) 2 hq
  have hle : ∀ k : ℕ,
      (b * |x|) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) ^ 2) ≤
        |powerTerm a b (k + 1) x| := by
    intro k
    have hfirst : 0 ≤ firstCoefficient a (k + 1) := by
      unfold firstCoefficient
      positivity
    have hsecond : 0 ≤ secondCoefficient b (k + 1) := by
      unfold secondCoefficient
      positivity
    have hcoeff : 0 ≤ coefficient a b (k + 1) := by
      unfold coefficient
      linarith
    calc
      (b * |x|) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) ^ 2) =
          secondCoefficient b (k + 1) * |x| ^ (k + 1) := by
            unfold secondCoefficient
            rw [mul_pow]
            ring
      _ ≤ coefficient a b (k + 1) * |x| ^ (k + 1) := by
            apply mul_le_mul_of_nonneg_right
            · unfold coefficient
              linarith
            · positivity
      _ = |powerTerm a b (k + 1) x| := by
            unfold powerTerm
            rw [abs_mul, abs_pow, abs_of_nonneg hcoeff]
  have htop : Tendsto
      (fun k : ℕ => |powerTerm a b (k + 1) x|) atTop atTop :=
    tendsto_atTop_mono' atTop (Filter.Eventually.of_forall hle) hdom
  obtain ⟨k, hk, hk'⟩ :=
    ((tendsto_atTop.1 htop 1).and
      (hzero.eventually_lt_const zero_lt_one)).exists
  linarith

private theorem not_seriesConvergesAt_of_one_lt_a_mul_abs
    (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hq : 1 < a * |x|) :
    ¬ SeriesConvergesAt a b x := by
  intro hs
  have hzero : Tendsto
      (fun k : ℕ => |powerTerm a b (k + 1) x|) atTop (𝓝 0) := by
    simpa using (tendsto_zero_of_summable_conditional hs).abs
  have hdom : Tendsto
      (fun k : ℕ => (a * |x|) ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
      atTop atTop := by
    simpa using tendsto_geometric_div_nat_pow_atTop (a * |x|) 1 hq
  have hle : ∀ k : ℕ,
      (a * |x|) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) ≤
        |powerTerm a b (k + 1) x| := by
    intro k
    have hfirst : 0 ≤ firstCoefficient a (k + 1) := by
      unfold firstCoefficient
      positivity
    have hsecond : 0 ≤ secondCoefficient b (k + 1) := by
      unfold secondCoefficient
      positivity
    have hcoeff : 0 ≤ coefficient a b (k + 1) := by
      unfold coefficient
      linarith
    calc
      (a * |x|) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) =
          firstCoefficient a (k + 1) * |x| ^ (k + 1) := by
            unfold firstCoefficient
            rw [mul_pow]
            ring
      _ ≤ coefficient a b (k + 1) * |x| ^ (k + 1) := by
            apply mul_le_mul_of_nonneg_right
            · unfold coefficient
              linarith
            · positivity
      _ = |powerTerm a b (k + 1) x| := by
            unfold powerTerm
            rw [abs_mul, abs_pow, abs_of_nonneg hcoeff]
  have htop : Tendsto
      (fun k : ℕ => |powerTerm a b (k + 1) x|) atTop atTop :=
    tendsto_atTop_mono' atTop (Filter.Eventually.of_forall hle) hdom
  obtain ⟨k, hk, hk'⟩ :=
    ((tendsto_atTop.1 htop 1).and
      (hzero.eventually_lt_const zero_lt_one)).exists
  linarith

theorem gap1 :
    ∀ a : ℝ, 0 < a →
      HasConvergenceRadius (firstCoefficient a) (1 / a) := by
  intro a ha
  constructor
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp [firstCoefficient]
    · let u : ℕ → ℝ := fun k => firstCoefficient a (k + 1) * x ^ (k + 1)
      have hune : ∀ k : ℕ, u k ≠ 0 := by
        intro k
        unfold u firstCoefficient
        exact mul_ne_zero (div_ne_zero (pow_ne_zero _ ha.ne') (by positivity))
          (pow_ne_zero _ hx0)
      have hratioEq :
          (fun n : ℕ => ‖u (n + 1)‖ / ‖u n‖) =
            fun n : ℕ => a * |x| *
              (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) := by
        funext n
        unfold u firstCoefficient
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_div, abs_div, abs_pow, abs_pow, abs_pow, abs_pow,
          abs_of_pos ha]
        simp only [show n + 1 + 1 = n + 2 by omega]
        rw [abs_of_pos (show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) by positivity),
          abs_of_pos (show (0 : ℝ) < ((n + 2 : ℕ) : ℝ) by positivity)]
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
        field_simp [ha.ne', abs_ne_zero.mpr hx0]
        <;> ring
      have hratio : Tendsto (fun n : ℕ => ‖u (n + 1)‖ / ‖u n‖)
          atTop (𝓝 (a * |x|)) := by
        rw [hratioEq]
        simpa using tendsto_const_nhds.mul succ_ratio_tendsto_one
      have hlt : a * |x| < 1 := by
        calc
          a * |x| < a * (1 / a) := mul_lt_mul_of_pos_left hx ha
          _ = 1 := by field_simp [ha.ne']
      change Summable u
      exact summable_of_ratio_test_tendsto_lt_one hlt
        (Filter.Eventually.of_forall hune) hratio
  · intro x hx hs
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      have : 0 < 1 / a := one_div_pos.mpr ha
      simpa using this.trans hx
    let u : ℕ → ℝ := fun k => firstCoefficient a (k + 1) * x ^ (k + 1)
    have hratioEq :
        (fun n : ℕ => ‖u (n + 1)‖ / ‖u n‖) =
          fun n : ℕ => a * |x| *
            (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) := by
      funext n
      unfold u firstCoefficient
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_div, abs_div, abs_pow, abs_pow, abs_pow, abs_pow,
        abs_of_pos ha]
      rw [abs_of_pos (show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) by positivity),
        abs_of_pos (show (0 : ℝ) < ((n + 2 : ℕ) : ℝ) by positivity)]
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
      field_simp [ha.ne', abs_ne_zero.mpr hx0]
      <;> ring
    have hratio : Tendsto (fun n : ℕ => ‖u (n + 1)‖ / ‖u n‖)
        atTop (𝓝 (a * |x|)) := by
      rw [hratioEq]
      simpa using tendsto_const_nhds.mul succ_ratio_tendsto_one
    have hgt : 1 < a * |x| := by
      calc
        1 = a * (1 / a) := by field_simp [ha.ne']
        _ < a * |x| := mul_lt_mul_of_pos_left hx ha
    exact (not_summable_of_ratio_test_tendsto_gt_one hgt hratio) hs

theorem gap2 :
    ∀ b : ℝ, 0 < b →
      HasConvergenceRadius (secondCoefficient b) (1 / b) := by
  intro b hb
  have hsq : Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) ^ 2)
      atTop (𝓝 1) := by simpa using succ_ratio_tendsto_one.pow 2
  have ratioLimit (x : ℝ) (hx0 : x ≠ 0) :
      Tendsto
        (fun n : ℕ =>
          ‖secondCoefficient b (n + 2) * x ^ (n + 2)‖ /
            ‖secondCoefficient b (n + 1) * x ^ (n + 1)‖)
        atTop (𝓝 (b * |x|)) := by
    have heq :
        (fun n : ℕ =>
          ‖secondCoefficient b (n + 2) * x ^ (n + 2)‖ /
            ‖secondCoefficient b (n + 1) * x ^ (n + 1)‖) =
          fun n : ℕ => b * |x| *
            ((((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) ^ 2) := by
      funext n
      unfold secondCoefficient
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_div, abs_div, abs_pow, abs_pow, abs_pow, abs_pow,
        abs_of_pos hb]
      rw [abs_of_pos (show (0 : ℝ) < ((n + 2 : ℕ) : ℝ) by positivity),
        abs_of_nonneg (sq_nonneg (((n + 1 : ℕ) : ℝ))), abs_pow]
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
      field_simp [hb.ne', abs_ne_zero.mpr hx0]
      <;> ring
    rw [heq]
    simpa using tendsto_const_nhds.mul hsq
  constructor
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp [secondCoefficient]
    · have hlt : b * |x| < 1 := by
        calc
          b * |x| < b * (1 / b) := mul_lt_mul_of_pos_left hx hb
          _ = 1 := by field_simp [hb.ne']
      exact summable_of_ratio_test_tendsto_lt_one hlt
        (Filter.Eventually.of_forall (fun n => by
          exact mul_ne_zero
            (div_ne_zero (pow_ne_zero _ hb.ne') (by positivity))
            (pow_ne_zero _ hx0)))
        (by simpa [Nat.add_assoc] using ratioLimit x hx0)
  · intro x hx hs
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      have : 0 < 1 / b := one_div_pos.mpr hb
      simpa using this.trans hx
    have hgt : 1 < b * |x| := by
      calc
        1 = b * (1 / b) := by field_simp [hb.ne']
        _ < b * |x| := mul_lt_mul_of_pos_left hx hb
    exact (not_summable_of_ratio_test_tendsto_gt_one hgt
      (by simpa [Nat.add_assoc] using ratioLimit x hx0)) hs

theorem gap3 :
    ∀ (a b : ℝ), 0 < a → 0 < b →
      radius a b = min (1 / a) (1 / b) := by
  intro a b ha hb
  rfl

theorem gap4 :
    ∀ (a b x : ℝ), 0 < a → 0 < b → |x| < radius a b →
      SeriesConvergesAt a b x := by
  intro a b x ha hb hx
  have h1 := (gap1 a ha).1 x (lt_of_lt_of_le hx (min_le_left _ _))
  have h2 := (gap2 b hb).1 x (lt_of_lt_of_le hx (min_le_right _ _))
  unfold SeriesConvergesAt
  exact ((h1.add h2).congr (fun k => by
    unfold powerTerm coefficient
    ring)).mono_filter (SummationFilter.conditional ℕ).le_atTop

theorem gap5 :
    ∀ (a b : ℝ), 0 < a → a < b →
      (∑' k : ℕ, powerTerm a b (k + 1) (-1 / b)) =
        (∑' k : ℕ, leftSmallTerm a b (k + 1)) +
          ∑' k : ℕ, alternatingSquare (k + 1) := by
  intro a b ha hab
  have hb : 0 < b := ha.trans hab
  have hleft := (leftSmall_abs_summable a b ha hab).of_abs
  have hsquare := alternatingSquare_abs_summable.of_abs
  rw [← hleft.tsum_add hsquare]
  apply tsum_congr
  intro k
  unfold powerTerm coefficient firstCoefficient secondCoefficient
  unfold leftSmallTerm alternatingSquare
  rw [add_mul]
  simp_rw [div_pow]
  congr 1 <;>
    field_simp [ha.ne', hb.ne', pow_ne_zero _ hb.ne'] <;> ring

theorem gap6 :
    ∀ (a b : ℝ), 0 < a → a < b →
      Tendsto
        (fun n : ℕ =>
          |leftSmallTerm a b (n + 2) / leftSmallTerm a b (n + 1)|)
        atTop (𝓝 (a / b)) := by
  intro a b ha hab
  have hb : 0 < b := ha.trans hab
  have hq : 0 < a / b := div_pos ha hb
  have heq :
      (fun n : ℕ =>
        |leftSmallTerm a b (n + 2) / leftSmallTerm a b (n + 1)|) =
        fun n : ℕ => (a / b) *
          (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) := by
    funext n
    unfold leftSmallTerm
    rw [abs_div, abs_div, abs_div, abs_mul, abs_mul,
      abs_pow, abs_pow, abs_pow, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_pos hq]
    rw [abs_of_pos (show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) by positivity),
      abs_of_pos (show (0 : ℝ) < ((n + 2 : ℕ) : ℝ) by positivity)]
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
    field_simp [hq.ne']
    <;> ring
  rw [heq]
  simpa using tendsto_const_nhds.mul succ_ratio_tendsto_one

theorem gap7 :
    ∀ (a b : ℝ), 0 < a → a < b → a / b < 1 := by
  intro a b ha hab
  exact (div_lt_one (ha.trans hab)).2 hab

theorem gap8 :
    ∀ (a b : ℝ), 0 < a → a < b →
      Tendsto
        (fun n : ℕ =>
          |leftSmallTerm a b (n + 2) / leftSmallTerm a b (n + 1)|)
        atTop (𝓝 (a / b)) ∧ a / b < 1 := by
  intro a b ha hab
  exact ⟨gap6 a b ha hab, gap7 a b ha hab⟩

theorem gap9 :
    ∀ (a b : ℝ), 0 < a → a < b →
      Summable (fun k : ℕ => |leftSmallTerm a b (k + 1)|) := by
  exact leftSmall_abs_summable

theorem gap10 :
    Summable (fun k : ℕ => |alternatingSquare (k + 1)|) := by
  exact alternatingSquare_abs_summable

theorem gap11 :
    ∀ (a b : ℝ), 0 < a → a < b →
      Summable (fun k : ℕ =>
        |powerTerm a b (k + 1) (-1 / b)|) := by
  intro a b ha hab
  have hb : 0 < b := ha.trans hab
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    ((leftSmall_abs_summable a b ha hab).add alternatingSquare_abs_summable)
  have heq : powerTerm a b (k + 1) (-1 / b) =
      leftSmallTerm a b (k + 1) + alternatingSquare (k + 1) := by
    unfold powerTerm coefficient firstCoefficient secondCoefficient
    unfold leftSmallTerm alternatingSquare
    rw [add_mul]
    simp_rw [div_pow]
    congr 1 <;>
      field_simp [ha.ne', hb.ne', pow_ne_zero _ hb.ne'] <;> ring
  rw [heq]
  exact abs_add_le _ _

theorem gap12 :
    ∀ (a b : ℝ), 0 < b → b ≤ a →
      (∑'[SummationFilter.conditional ℕ] k : ℕ,
        powerTerm a b (k + 1) (-1 / a)) =
        (∑'[SummationFilter.conditional ℕ] k : ℕ,
          alternatingHarmonic (k + 1)) +
          ∑'[SummationFilter.conditional ℕ] k : ℕ,
            leftSecondTerm a b (k + 1) := by
  intro a b hb hba
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hharm := alternatingHarmonic_conditional_summable
  have hsecond :=
    (leftSecond_abs_summable a b hb hba).of_abs.mono_filter
      (SummationFilter.conditional ℕ).le_atTop
  rw [← hharm.tsum_add hsecond]
  apply tsum_congr
  intro k
  unfold powerTerm coefficient firstCoefficient secondCoefficient
  unfold alternatingHarmonic leftSecondTerm
  rw [add_mul]
  simp_rw [div_pow]
  congr 1 <;>
    field_simp [ha.ne', hb.ne', pow_ne_zero _ ha.ne'] <;> ring

theorem gap13 :
    ConditionallySummable
      (fun k : ℕ => alternatingHarmonic (k + 1)) := by
  constructor
  · exact alternatingHarmonic_conditional_summable
  · intro habs
    exact alternatingHarmonic_not_summable habs.of_abs

theorem gap14 :
    ∀ (a b : ℝ), 0 < b → b ≤ a →
      Summable (fun k : ℕ => leftSecondTerm a b (k + 1)) := by
  intro a b hb hba
  exact (leftSecond_abs_summable a b hb hba).of_abs

theorem gap15 :
    ∀ (a b : ℝ), 0 < b → b ≤ a →
      ConditionallySummable
        (fun k : ℕ => powerTerm a b (k + 1) (-1 / a)) := by
  intro a b hb hba
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hharmC := alternatingHarmonic_conditional_summable
  have hsecondU := (leftSecond_abs_summable a b hb hba).of_abs
  have hsecondC := hsecondU.mono_filter (SummationFilter.conditional ℕ).le_atTop
  have heq : ∀ k : ℕ,
      powerTerm a b (k + 1) (-1 / a) =
        alternatingHarmonic (k + 1) + leftSecondTerm a b (k + 1) := by
    intro k
    unfold powerTerm coefficient firstCoefficient secondCoefficient
    unfold alternatingHarmonic leftSecondTerm
    rw [add_mul]
    simp_rw [div_pow]
    congr 1 <;>
      field_simp [ha.ne', hb.ne', pow_ne_zero _ ha.ne'] <;> ring
  constructor
  · exact (hharmC.add hsecondC).congr (fun k => (heq k).symm)
  · intro habs
    have hpowerU := habs.of_abs
    apply alternatingHarmonic_not_summable
    exact (hpowerU.sub hsecondU).congr (fun k => by
      rw [heq]
      ring)

theorem gap16 :
    ∀ (a b : ℝ), 0 < a → a < b →
      (∑' k : ℕ, powerTerm a b (k + 1) (1 / b)) =
        (∑' k : ℕ, (a / b) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) +
          ∑' k : ℕ, 1 / (((k + 1 : ℕ) : ℝ) ^ 2) := by
  intro a b ha hab
  have hb : 0 < b := ha.trans hab
  have hfirst : Summable
      (fun k : ℕ => (a / b) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
    exact (leftSmall_abs_summable a b ha hab).congr (fun k => by
      unfold leftSmallTerm
      rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        abs_pow, abs_of_pos (div_pos ha hb)]
      rw [abs_of_pos (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) by positivity)]
      simp only [one_mul])
  have hsecond : Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : (1 : ℕ) < 2)
    exact (summable_nat_add_iff 1).2 h
  rw [← hfirst.tsum_add hsecond]
  apply tsum_congr
  intro k
  unfold powerTerm coefficient firstCoefficient secondCoefficient
  rw [add_mul]
  simp_rw [div_pow]
  field_simp [ha.ne', hb.ne', pow_ne_zero _ hb.ne']
  <;> ring

theorem gap17 :
    ∀ (a b : ℝ), 0 < a → a < b →
      Summable (fun k : ℕ =>
        |powerTerm a b (k + 1) (1 / b)|) := by
  intro a b ha hab
  have hb : 0 < b := ha.trans hab
  have hfirst : Summable
      (fun k : ℕ => (a / b) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
    exact (leftSmall_abs_summable a b ha hab).congr (fun k => by
      unfold leftSmallTerm
      rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        abs_pow, abs_of_pos (div_pos ha hb)]
      rw [abs_of_pos (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) by positivity)]
      simp only [one_mul])
  have hsecond : Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : (1 : ℕ) < 2)
    exact (summable_nat_add_iff 1).2 h
  exact (hfirst.add hsecond).congr (fun k => by
    have h1 : 0 ≤ (a / b) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by positivity
    have h2 : 0 ≤ 1 / (((k + 1 : ℕ) : ℝ) ^ 2) := by positivity
    have heq : powerTerm a b (k + 1) (1 / b) =
        (a / b) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) +
          1 / (((k + 1 : ℕ) : ℝ) ^ 2) := by
      unfold powerTerm coefficient firstCoefficient secondCoefficient
      rw [add_mul]
      simp_rw [div_pow]
      field_simp [ha.ne', hb.ne', pow_ne_zero _ hb.ne']
      <;> ring
    rw [heq, abs_of_nonneg (add_nonneg h1 h2)])

theorem gap18 :
    ∀ (a b : ℝ), 0 < b → b ≤ a →
      (fun k : ℕ => powerTerm a b (k + 1) (1 / a)) =
        fun k : ℕ =>
          1 / (((k + 1 : ℕ) : ℝ)) +
            (b / a) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) ^ 2) := by
  intro a b hb hba
  have ha : 0 < a := lt_of_lt_of_le hb hba
  funext k
  unfold powerTerm coefficient firstCoefficient secondCoefficient
  rw [add_mul]
  simp_rw [div_pow]
  field_simp [ha.ne', hb.ne', pow_ne_zero _ ha.ne']
  <;> ring

theorem gap19 :
    ¬ Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ)))
      (SummationFilter.conditional ℕ) := by
  exact harmonic_not_conditional_summable

theorem gap20 :
    ∀ (a b : ℝ), 0 < b → b ≤ a →
      ¬ SeriesConvergesAt a b (1 / a) := by
  intro a b hb hba hs
  have heq := gap18 a b hb hba
  unfold SeriesConvergesAt at hs
  rw [heq] at hs
  have hsecondU : Summable
      (fun k : ℕ => (b / a) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
    exact (leftSecond_abs_summable a b hb hba).congr (fun k => by
      have ha : 0 < a := lt_of_lt_of_le hb hba
      unfold leftSecondTerm
      rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        abs_pow, abs_of_pos (div_pos hb ha),
        abs_of_nonneg (sq_nonneg (((k + 1 : ℕ) : ℝ)))]
      simp only [one_mul])
  have hsecondC := hsecondU.mono_filter (SummationFilter.conditional ℕ).le_atTop
  apply gap19
  exact (hs.sub hsecondC).congr (fun k => by ring)

theorem gap21 :
    ∀ (a b x : ℝ), 0 < a → 0 < b →
      (x ∈
          {y : ℝ |
            (a < b ∧ -1 / b ≤ y ∧ y ≤ 1 / b) ∨
            (b ≤ a ∧ -1 / a ≤ y ∧ y < 1 / a)} ↔
        SeriesConvergesAt a b x) := by
  intro a b x ha hb
  constructor
  · rintro (hcase | hcase)
    · rcases hcase with ⟨hab, hxlo, hxhi⟩
      by_cases hlo : x = -1 / b
      · subst x
        exact (gap11 a b ha hab).of_abs.mono_filter
          (SummationFilter.conditional ℕ).le_atTop
      by_cases hhi : x = 1 / b
      · subst x
        exact (gap17 a b ha hab).of_abs.mono_filter
          (SummationFilter.conditional ℕ).le_atTop
      have hinv : 1 / b < 1 / a := one_div_lt_one_div_of_lt ha hab
      have hr : radius a b = 1 / b := by
        unfold radius
        exact min_eq_right hinv.le
      apply gap4 a b x ha hb
      rw [hr]
      have hxlo' : -(1 / b) ≤ x := by
        simpa [div_eq_mul_inv] using hxlo
      have hlo' : x ≠ -(1 / b) := by
        simpa [div_eq_mul_inv] using hlo
      exact abs_lt.2 ⟨lt_of_le_of_ne hxlo' (Ne.symm hlo'),
        lt_of_le_of_ne hxhi hhi⟩
    · rcases hcase with ⟨hba, hxlo, hxhi⟩
      by_cases hlo : x = -1 / a
      · subst x
        exact (gap15 a b hb hba).1
      have hinv : 1 / a ≤ 1 / b := one_div_le_one_div_of_le hb hba
      have hr : radius a b = 1 / a := by
        unfold radius
        exact min_eq_left hinv
      apply gap4 a b x ha hb
      rw [hr]
      have hxlo' : -(1 / a) ≤ x := by
        simpa [div_eq_mul_inv] using hxlo
      have hlo' : x ≠ -(1 / a) := by
        simpa [div_eq_mul_inv] using hlo
      exact abs_lt.2 ⟨lt_of_le_of_ne hxlo' (Ne.symm hlo'), hxhi⟩
  · intro hs
    rcases lt_or_ge a b with hab | hba
    · left
      refine ⟨hab, ?_, ?_⟩
      · by_contra h
        have hxlt : x < -1 / b := lt_of_not_ge h
        have hxlt' : x < -(1 / b) := by
          simpa [div_eq_mul_inv] using hxlt
        have hxneg : x < 0 := by
          exact hxlt'.trans (neg_neg_of_pos (one_div_pos.mpr hb))
        have habs : 1 / b < |x| := by
          rw [abs_of_neg hxneg]
          simpa using neg_lt_neg hxlt'
        have hq : 1 < b * |x| := by
          calc
            1 = b * (1 / b) := by field_simp [hb.ne']
            _ < b * |x| := mul_lt_mul_of_pos_left habs hb
        exact (not_seriesConvergesAt_of_one_lt_b_mul_abs a b x ha hb hq) hs
      · by_contra h
        have hxgt : 1 / b < x := lt_of_not_ge h
        have habs : 1 / b < |x| := hxgt.trans_le (le_abs_self x)
        have hq : 1 < b * |x| := by
          calc
            1 = b * (1 / b) := by field_simp [hb.ne']
            _ < b * |x| := mul_lt_mul_of_pos_left habs hb
        exact (not_seriesConvergesAt_of_one_lt_b_mul_abs a b x ha hb hq) hs
    · right
      refine ⟨hba, ?_, ?_⟩
      · by_contra h
        have hxlt : x < -1 / a := lt_of_not_ge h
        have hxlt' : x < -(1 / a) := by
          simpa [div_eq_mul_inv] using hxlt
        have hxneg : x < 0 := by
          exact hxlt'.trans (neg_neg_of_pos (one_div_pos.mpr ha))
        have habs : 1 / a < |x| := by
          rw [abs_of_neg hxneg]
          simpa using neg_lt_neg hxlt'
        have hq : 1 < a * |x| := by
          calc
            1 = a * (1 / a) := by field_simp [ha.ne']
            _ < a * |x| := mul_lt_mul_of_pos_left habs ha
        exact (not_seriesConvergesAt_of_one_lt_a_mul_abs a b x ha hb hq) hs
      · by_contra h
        have hxge : 1 / a ≤ x := le_of_not_gt h
        rcases hxge.eq_or_lt with hxeq | hxgt
        · subst x
          exact (gap20 a b hb hba) hs
        · have habs : 1 / a < |x| := hxgt.trans_le (le_abs_self x)
          have hq : 1 < a * |x| := by
            calc
              1 = a * (1 / a) := by field_simp [ha.ne']
              _ < a * |x| := mul_lt_mul_of_pos_left habs ha
          exact (not_seriesConvergesAt_of_one_lt_a_mul_abs a b x ha hb hq) hs

end

end ProofGap.Exercise2821
