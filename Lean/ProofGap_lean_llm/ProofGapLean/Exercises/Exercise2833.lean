import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2833

noncomputable section

open Filter
open scoped BigOperators Topology

def coefficient (n : ℕ) : ℝ :=
  1 / (2 * (n : ℝ) + 1)

def ratio (x : ℝ) : ℝ :=
  (1 - x) / (1 + x)

def term (n : ℕ) (x : ℝ) : ℝ :=
  coefficient n * ratio x ^ n

def SeriesConvergesAt (x : ℝ) : Prop :=
  x ≠ -1 ∧ Summable (fun n : ℕ => term n x)

theorem gap1 :
    Tendsto
      (fun n : ℕ => |coefficient n / coefficient (n + 1)|)
      atTop (𝓝 1) := by
  have hden :
      Tendsto (fun n : ℕ => 2 * (n : ℝ) + 1) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have hzero :
      Tendsto (fun n : ℕ => (2 : ℝ) / (2 * (n : ℝ) + 1))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hlim :
      Tendsto (fun n : ℕ => 1 + (2 : ℝ) / (2 * (n : ℝ) + 1))
        atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hzero
  rw [show
      (fun n : ℕ => |coefficient n / coefficient (n + 1)|) =
        (fun n : ℕ => 1 + (2 : ℝ) / (2 * (n : ℝ) + 1)) by
    funext n
    have hn : 0 < 2 * (n : ℝ) + 1 := by positivity
    have hn1 : 0 < 2 * ((n + 1 : ℕ) : ℝ) + 1 := by positivity
    rw [coefficient, coefficient, abs_of_pos (by positivity)]
    field_simp [hn.ne', hn1.ne']
    norm_num [Nat.cast_add]
    ring]
  exact hlim

theorem gap2 :
    ∀ x : ℝ, x ≠ -1 → (|ratio x| < 1 ↔ 0 < x) := by
  intro x hx
  have hd : 1 + x ≠ 0 := by
    intro h
    apply hx
    linarith
  constructor
  · intro hratio
    rw [ratio, abs_div, div_lt_one (abs_pos.mpr hd)] at hratio
    nlinarith [sq_abs (1 - x), sq_abs (1 + x),
      abs_nonneg (1 - x), abs_nonneg (1 + x)]
  · intro hxpos
    rw [ratio, abs_div, div_lt_one (abs_pos.mpr hd)]
    nlinarith [sq_abs (1 - x), sq_abs (1 + x),
      abs_nonneg (1 - x), abs_nonneg (1 + x)]

theorem gap3 :
    ∀ x : ℝ, |ratio x| < 1 →
      Summable (fun n : ℕ => |term n x|) := by
  intro x hx
  have hgeom : Summable (fun n : ℕ => |ratio x| ^ n) := by
    apply summable_geometric_of_norm_lt_one
    simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg (ratio x))] using hx
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) ?_ hgeom
  intro n
  have hc0 : 0 ≤ coefficient n := by
    unfold coefficient
    positivity
  have hc1 : coefficient n ≤ 1 := by
    unfold coefficient
    apply (div_le_one (by positivity)).2
    have hn : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  rw [term, abs_mul, abs_pow, abs_of_nonneg hc0]
  calc
    coefficient n * |ratio x| ^ n ≤ 1 * |ratio x| ^ n :=
      mul_le_mul_of_nonneg_right hc1 (pow_nonneg (abs_nonneg _) n)
    _ = |ratio x| ^ n := one_mul _

theorem gap4 :
    ∀ x : ℝ, x < 0 → ¬ SeriesConvergesAt x := by
  intro x hx hseries
  rcases hseries with ⟨hxne, hsum⟩
  have hd : 1 + x ≠ 0 := by
    intro h
    apply hxne
    linarith
  have hr : 1 < |ratio x| := by
    rw [ratio, abs_div, one_lt_div (abs_pos.mpr hd)]
    nlinarith [sq_abs (1 - x), sq_abs (1 + x),
      abs_nonneg (1 - x), abs_nonneg (1 + x)]
  have hratio0 : ratio x ≠ 0 := by
    unfold ratio
    apply div_ne_zero
    · intro h
      linarith
    · exact hd
  have hc (n : ℕ) : coefficient n ≠ 0 := by
    unfold coefficient
    positivity
  have hlim :
      Tendsto
        (fun n : ℕ =>
          |ratio x| / |coefficient n / coefficient (n + 1)|)
        atTop (𝓝 |ratio x|) := by
    simpa using tendsto_const_nhds.div gap1 (by norm_num : (1 : ℝ) ≠ 0)
  have htermRatio :
      Tendsto
        (fun n : ℕ => ‖term (n + 1) x‖ / ‖term n x‖)
        atTop (𝓝 |ratio x|) := by
    rw [show
        (fun n : ℕ => ‖term (n + 1) x‖ / ‖term n x‖) =
          (fun n : ℕ =>
            |ratio x| / |coefficient n / coefficient (n + 1)|) by
      funext n
      rw [term, term, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_mul, abs_pow, abs_pow, abs_div, pow_succ]
      field_simp [abs_ne_zero.mpr (hc n), abs_ne_zero.mpr (hc (n + 1)),
        abs_ne_zero.mpr hratio0]
      ]
    exact hlim
  exact (not_summable_of_ratio_test_tendsto_gt_one hr htermRatio) hsum

theorem gap5 :
    ¬ Summable (fun n : ℕ => 1 / (2 * (n : ℝ) + 1)) := by
  intro hsum
  have hhalf :
      Summable (fun n : ℕ =>
        (1 / 2 : ℝ) * (1 / (((n + 1 : ℕ) : ℝ)))) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ hsum
    intro n
    have hn : 0 ≤ (n : ℝ) := by positivity
    have hsmall : 0 < 2 * (n : ℝ) + 1 := by positivity
    rw [show
        (1 / 2 : ℝ) * (1 / (((n + 1 : ℕ) : ℝ))) =
          1 / (2 * (((n + 1 : ℕ) : ℝ))) by
      field_simp]
    apply one_div_le_one_div_of_le hsmall
    norm_num [Nat.cast_add]
    nlinarith
  have hharm :
      Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))) := by
    convert hhalf.mul_left 2 using 1
    funext n
    ring
  apply Real.not_summable_one_div_natCast
  exact (summable_nat_add_iff 1).1 (by
    simpa only [Nat.cast_add, Nat.cast_one] using hharm)

theorem gap6 :
    ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) ↔ SeriesConvergesAt x := by
  intro x
  constructor
  · intro hx
    have hxpos : 0 < x := hx
    have hxne : x ≠ -1 := by linarith
    have hd : 1 + x ≠ 0 := by linarith
    have hratio : |ratio x| < 1 := by
      rw [ratio, abs_div, div_lt_one (abs_pos.mpr hd)]
      nlinarith [sq_abs (1 - x), sq_abs (1 + x),
        abs_nonneg (1 - x), abs_nonneg (1 + x)]
    have habs := gap3 x hratio
    refine ⟨hxne, ?_⟩
    have hnorm : Summable (fun n : ℕ => ‖term n x‖) := by
      simpa only [Real.norm_eq_abs] using habs
    exact hnorm.of_norm
  · intro hseries
    have hxle_or_pos : x ≤ 0 ∨ 0 < x := le_or_gt x 0
    rcases hxle_or_pos with hxle | hxpos
    · rcases lt_or_eq_of_le hxle with hxneg | rfl
      · exact False.elim ((gap4 x hxneg) hseries)
      · exfalso
        apply gap5
        simpa [SeriesConvergesAt, term, coefficient, ratio] using hseries
    · exact hxpos

end

end ProofGap.Exercise2833
