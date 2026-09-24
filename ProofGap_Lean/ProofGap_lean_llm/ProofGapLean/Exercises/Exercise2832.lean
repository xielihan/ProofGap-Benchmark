import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Instances.Real.Lemmas

namespace ProofGap.Exercise2832

noncomputable section

open Filter
open scoped BigOperators Topology

def rising (z : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (z + k)

def coefficient (α β γ : ℝ) (n : ℕ) : ℝ :=
  (rising α n * rising β n) /
    ((Nat.factorial n : ℝ) * rising γ n)

def powerTerm (α β γ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  coefficient α β γ n * x ^ n

def SeriesConvergesAt (α β γ x : ℝ) : Prop :=
  Summable (fun k : ℕ => powerTerm α β γ (k + 1) x)

def HasConvergenceRadiusOne (α β γ : ℝ) : Prop :=
  (∀ x : ℝ, |x| < 1 → SeriesConvergesAt α β γ x) ∧
    (∀ x : ℝ, 1 < |x| → ¬ SeriesConvergesAt α β γ x)

def delta (α β γ : ℝ) : ℝ :=
  γ - α - β

def ratioFormula (α β γ : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℝ) * (γ + n)) / ((α + n) * (β + n))

def raabeSeq (α β γ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) *
    (coefficient α β γ (n - 1) / coefficient α β γ n - 1)

def remainder (α β γ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 *
    (coefficient α β γ (n - 1) / coefficient α β γ n -
      1 - (delta α β γ + 1) / n)

private theorem rising_pos {z : ℝ} (hz : 0 < z) (n : ℕ) :
    0 < rising z n := by
  unfold rising
  apply Finset.prod_pos
  intro k hk
  positivity

private theorem coefficient_pos {α β γ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (n : ℕ) :
    0 < coefficient α β γ n := by
  unfold coefficient
  apply div_pos
  · exact mul_pos (rising_pos hα n) (rising_pos hβ n)
  · exact mul_pos (by exact_mod_cast Nat.factorial_pos n) (rising_pos hγ n)

private theorem coefficient_succ {α β γ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (n : ℕ) :
    coefficient α β γ (n + 1) =
      coefficient α β γ n *
        ((α + n) * (β + n) / ((n + 1 : ℝ) * (γ + n))) := by
  have hγn : γ + (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  simp only [coefficient, rising, Finset.prod_range_succ, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [hγn, hn1, ne_of_gt (rising_pos hγ n)] <;> ring

theorem gap1 :
    ∀ (α β γ : ℝ), 0 < α → 0 < β → 0 < γ →
      (fun n : ℕ =>
        |coefficient α β γ (n + 1) / coefficient α β γ (n + 2)|) =
          fun n : ℕ => ratioFormula α β γ (n + 1) := by
  intro α β γ hα hβ hγ
  funext n
  have hc := coefficient_succ hα hβ hγ (n + 1)
  rw [abs_of_pos (div_pos (coefficient_pos hα hβ hγ _)
    (coefficient_pos hα hβ hγ _))]
  rw [show n + 2 = (n + 1) + 1 by omega, hc]
  unfold ratioFormula
  have hc1 : coefficient α β γ (n + 1) ≠ 0 :=
    ne_of_gt (coefficient_pos hα hβ hγ _)
  have hαn : α + ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hβn : β + ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hγn : γ + ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hc1, hαn, hβn, hγn] <;> ring

theorem gap2 :
    ∀ (α β γ : ℝ), 0 < α → 0 < β → 0 < γ →
      Tendsto (ratioFormula α β γ) atTop (𝓝 1) := by
  intro α β γ hα hβ hγ
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hnum :
      Tendsto
        (fun n : ℕ => (1 + (n : ℝ)⁻¹) * (1 + γ * (n : ℝ)⁻¹))
        atTop (𝓝 1) := by
    simpa using
      ((tendsto_const_nhds (x := (1 : ℝ))).add hinv).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).add
          ((tendsto_const_nhds (x := γ)).mul hinv))
  have hden :
      Tendsto
        (fun n : ℕ =>
          (1 + α * (n : ℝ)⁻¹) * (1 + β * (n : ℝ)⁻¹))
        atTop (𝓝 1) := by
    simpa using
      ((tendsto_const_nhds (x := (1 : ℝ))).add
          ((tendsto_const_nhds (x := α)).mul hinv)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).add
          ((tendsto_const_nhds (x := β)).mul hinv))
  have hlim :
      Tendsto
        (fun n : ℕ =>
          ((1 + (n : ℝ)⁻¹) * (1 + γ * (n : ℝ)⁻¹)) /
            ((1 + α * (n : ℝ)⁻¹) * (1 + β * (n : ℝ)⁻¹)))
        atTop (𝓝 1) := by
    simpa using hnum.div hden one_ne_zero
  refine hlim.congr' (eventually_atTop.2 ?_)
  refine ⟨1, ?_⟩
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold ratioFormula
  field_simp [hn0] <;> ring

theorem gap3 :
    ∀ (α β γ : ℝ), 0 < α → 0 < β → 0 < γ →
      Tendsto
        (fun n : ℕ =>
          |coefficient α β γ (n + 1) / coefficient α β γ (n + 2)|)
        atTop (𝓝 1) := by
  intro α β γ hα hβ hγ
  rw [gap1 α β γ hα hβ hγ]
  exact (gap2 α β γ hα hβ hγ).comp (tendsto_add_atTop_nat 1)

private theorem powerTerm_ratio_tendsto (α β γ x : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hx : x ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        ‖powerTerm α β γ (n + 2) x‖ /
          ‖powerTerm α β γ (n + 1) x‖)
      atTop (𝓝 |x|) := by
  have hc := gap3 α β γ hα hβ hγ
  have hlim :
      Tendsto
        (fun n : ℕ =>
          |x| / |coefficient α β γ (n + 1) /
            coefficient α β γ (n + 2)|)
        atTop (𝓝 |x|) := by
    simpa using (tendsto_const_nhds.div hc one_ne_zero)
  refine hlim.congr' (Eventually.of_forall (fun n => ?_))
  change
    |x| / |coefficient α β γ (n + 1) /
        coefficient α β γ (n + 2)| =
      ‖powerTerm α β γ (n + 2) x‖ /
        ‖powerTerm α β γ (n + 1) x‖
  simp only [powerTerm, Real.norm_eq_abs, abs_mul, abs_pow]
  rw [abs_of_pos (coefficient_pos hα hβ hγ (n + 1)),
    abs_of_pos (coefficient_pos hα hβ hγ (n + 2)),
    abs_of_pos (div_pos (coefficient_pos hα hβ hγ (n + 1))
      (coefficient_pos hα hβ hγ (n + 2)))]
  field_simp [ne_of_gt (coefficient_pos hα hβ hγ (n + 1)),
    ne_of_gt (coefficient_pos hα hβ hγ (n + 2)),
    abs_ne_zero.mpr hx, pow_succ] <;> ring

theorem gap4 :
    ∀ (α β γ : ℝ), 0 < α → 0 < β → 0 < γ →
      HasConvergenceRadiusOne α β γ := by
  intro α β γ hα hβ hγ
  constructor
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp [SeriesConvergesAt, powerTerm]
    · have hratio :
          Tendsto
            (fun n : ℕ =>
              ‖powerTerm α β γ ((n + 1) + 1) x‖ /
                ‖powerTerm α β γ (n + 1) x‖)
            atTop (𝓝 |x|) := by
        simpa [Nat.add_assoc] using
          powerTerm_ratio_tendsto α β γ x hα hβ hγ hx0
      have hne :
          ∀ᶠ n : ℕ in atTop, powerTerm α β γ (n + 1) x ≠ 0 :=
        Eventually.of_forall (fun n =>
          mul_ne_zero (ne_of_gt (coefficient_pos hα hβ hγ _))
            (pow_ne_zero _ hx0))
      exact summable_of_ratio_test_tendsto_lt_one hx hne hratio
  · intro x hx hs
    have hx0 : x ≠ 0 :=
      abs_ne_zero.mp (ne_of_gt (lt_trans zero_lt_one hx))
    have hratio :
        Tendsto
          (fun n : ℕ =>
            ‖powerTerm α β γ ((n + 1) + 1) x‖ /
              ‖powerTerm α β γ (n + 1) x‖)
          atTop (𝓝 |x|) := by
      simpa [Nat.add_assoc] using
        powerTerm_ratio_tendsto α β γ x hα hβ hγ hx0
    exact (not_summable_of_ratio_test_tendsto_gt_one hx hratio) hs

theorem gap5 :
    ∀ (α β γ x : ℝ), 0 < α → 0 < β → 0 < γ → |x| < 1 →
      Summable (fun k : ℕ => |powerTerm α β γ (k + 1) x|) := by
  intro α β γ x hα hβ hγ hx
  exact ((gap4 α β γ hα hβ hγ).1 x hx).abs

theorem gap6 :
    ∀ (α β γ x : ℝ), 0 < α → 0 < β → 0 < γ → 1 < |x| →
      ¬ SeriesConvergesAt α β γ x := by
  intro α β γ x hα hβ hγ hx
  exact (gap4 α β γ hα hβ hγ).2 x hx

private theorem raabe_succ_eq (α β γ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (n : ℕ) :
    raabeSeq α β γ (n + 1) =
      (n + 1 : ℝ) * (ratioFormula α β γ n - 1) := by
  have hc := coefficient_succ hα hβ hγ n
  have hcn : coefficient α β γ n ≠ 0 :=
    ne_of_gt (coefficient_pos hα hβ hγ n)
  have hαn : α + (n : ℝ) ≠ 0 := by positivity
  have hβn : β + (n : ℝ) ≠ 0 := by positivity
  have hγn : γ + (n : ℝ) ≠ 0 := by positivity
  unfold raabeSeq ratioFormula
  rw [show n + 1 - 1 = n by omega, hc]
  push_cast
  field_simp [hcn, hαn, hβn, hγn] <;> ring

private theorem coefficient_pred_ratio (α β γ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (n : ℕ) (hn : 1 ≤ n) :
    coefficient α β γ (n - 1) / coefficient α β γ n =
      ((n : ℝ) * (γ + n - 1)) /
        ((α + n - 1) * (β + n - 1)) := by
  have hr := raabe_succ_eq α β γ hα hβ hγ (n - 1)
  rw [show n - 1 + 1 = n by omega] at hr
  unfold raabeSeq at hr
  rw [Nat.cast_sub hn] at hr
  norm_num at hr
  have hratio :
      coefficient α β γ (n - 1) / coefficient α β γ n =
        ratioFormula α β γ (n - 1) := by
    rcases hr with hratio | hnzero
    · exact hratio
    · norm_cast at hnzero
      omega
  rw [hratio]
  unfold ratioFormula
  rw [Nat.cast_sub hn]
  push_cast
  ring

theorem gap7 :
    ∀ (α β γ : ℝ), 0 < α → 0 < β → 0 < γ →
      Tendsto (fun n : ℕ => raabeSeq α β γ (n + 1))
        atTop (𝓝 (delta α β γ + 1)) := by
  intro α β γ hα hβ hγ
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hnum :
      Tendsto
        (fun n : ℕ =>
          (1 + (n : ℝ)⁻¹) *
            ((delta α β γ + 1) + (γ - α * β) * (n : ℝ)⁻¹))
        atTop (𝓝 (delta α β γ + 1)) := by
    simpa using
      ((tendsto_const_nhds (x := (1 : ℝ))).add hinv).mul
        ((tendsto_const_nhds (x := delta α β γ + 1)).add
          ((tendsto_const_nhds (x := γ - α * β)).mul hinv))
  have hden :
      Tendsto
        (fun n : ℕ =>
          (1 + α * (n : ℝ)⁻¹) * (1 + β * (n : ℝ)⁻¹))
        atTop (𝓝 1) := by
    simpa using
      ((tendsto_const_nhds (x := (1 : ℝ))).add
          ((tendsto_const_nhds (x := α)).mul hinv)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).add
          ((tendsto_const_nhds (x := β)).mul hinv))
  have hlim :
      Tendsto
        (fun n : ℕ =>
          ((1 + (n : ℝ)⁻¹) *
              ((delta α β γ + 1) + (γ - α * β) * (n : ℝ)⁻¹)) /
            ((1 + α * (n : ℝ)⁻¹) * (1 + β * (n : ℝ)⁻¹)))
        atTop (𝓝 (delta α β γ + 1)) := by
    simpa using hnum.div hden one_ne_zero
  refine hlim.congr' (eventually_atTop.2 ?_)
  refine ⟨1, ?_⟩
  intro n hn
  change _ = raabeSeq α β γ (n + 1)
  rw [raabe_succ_eq α β γ hα hβ hγ n]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold ratioFormula delta
  field_simp [hn0] <;> ring

theorem gap8 :
    ∀ (α β γ : ℝ), 0 < α → 0 < β → 0 < γ →
      ∃ L : ℝ, 0 ≤ L ∧
        ∀ n : ℕ, 1 ≤ n → |remainder α β γ n| ≤ L := by
  intro α β γ hα hβ hγ
  let d : ℝ := delta α β γ + 1
  let A : ℝ := (α - 1) * (β - 1)
  let C : ℝ := A + d * (α + β - 2)
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hnum :
      Tendsto (fun n : ℕ => -C - d * A * (n : ℝ)⁻¹)
        atTop (𝓝 (-C)) := by
    simpa using
      (tendsto_const_nhds (x := -C)).sub
        (((tendsto_const_nhds (x := d)).mul
          (tendsto_const_nhds (x := A))).mul hinv)
  have hden :
      Tendsto
        (fun n : ℕ =>
          (1 + (α - 1) * (n : ℝ)⁻¹) *
            (1 + (β - 1) * (n : ℝ)⁻¹))
        atTop (𝓝 1) := by
    simpa using
      ((tendsto_const_nhds (x := (1 : ℝ))).add
          ((tendsto_const_nhds (x := α - 1)).mul hinv)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).add
          ((tendsto_const_nhds (x := β - 1)).mul hinv))
  have hrat :
      Tendsto
        (fun n : ℕ =>
          (-C - d * A * (n : ℝ)⁻¹) /
            ((1 + (α - 1) * (n : ℝ)⁻¹) *
              (1 + (β - 1) * (n : ℝ)⁻¹)))
        atTop (𝓝 (-C)) := by
    simpa using hnum.div hden one_ne_zero
  have hrem : Tendsto (remainder α β γ) atTop (𝓝 (-C)) := by
    refine hrat.congr' (eventually_atTop.2 ?_)
    refine ⟨1, ?_⟩
    intro n hn
    change _ = remainder α β γ n
    unfold remainder
    rw [coefficient_pred_ratio α β γ hα hβ hγ n hn]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hαn : α + (n : ℝ) - 1 ≠ 0 := by nlinarith
    have hβn : β + (n : ℝ) - 1 ≠ 0 := by nlinarith
    have hden :
        (α + (n : ℝ) - 1) * (β + (n : ℝ) - 1) ≠ 0 :=
      mul_ne_zero hαn hβn
    have hαnorm : 1 + (α - 1) * (n : ℝ)⁻¹ ≠ 0 := by
      have heq :
          1 + (α - 1) * (n : ℝ)⁻¹ =
            (α + (n : ℝ) - 1) / (n : ℝ) := by
        field_simp [hn0] <;> ring
      rw [heq]
      exact div_ne_zero hαn hn0
    have hβnorm : 1 + (β - 1) * (n : ℝ)⁻¹ ≠ 0 := by
      have heq :
          1 + (β - 1) * (n : ℝ)⁻¹ =
            (β + (n : ℝ) - 1) / (n : ℝ) := by
        field_simp [hn0] <;> ring
      rw [heq]
      exact div_ne_zero hβn hn0
    have hfirst :
        (n : ℝ) * (γ + n - 1) /
              ((α + n - 1) * (β + n - 1)) - 1 =
          (d * (n : ℝ) - A) /
            ((α + n - 1) * (β + n - 1)) := by
      dsimp [d, A]
      unfold delta
      field_simp [hden] <;> ring
    have hsecond :
        (d * (n : ℝ) - A) /
              ((α + n - 1) * (β + n - 1)) - d / (n : ℝ) =
          (-C * (n : ℝ) - d * A) /
            ((n : ℝ) * ((α + n - 1) * (β + n - 1))) := by
      dsimp [C]
      field_simp [hn0, hden] <;> ring
    have hscaled :
        (n : ℝ) ^ 2 *
              ((-C * (n : ℝ) - d * A) /
                ((n : ℝ) * ((α + n - 1) * (β + n - 1)))) =
          (n : ℝ) * (-C * (n : ℝ) - d * A) /
            ((α + n - 1) * (β + n - 1)) := by
      field_simp [hn0, hden] <;> ring
    have hnormden :
        (1 + (α - 1) * (n : ℝ)⁻¹) *
            (1 + (β - 1) * (n : ℝ)⁻¹) =
          ((α + n - 1) * (β + n - 1)) / (n : ℝ) ^ 2 := by
      field_simp [hn0] <;> ring
    rw [hfirst, hsecond, hscaled, hnormden]
    field_simp [hn0, hden, hαnorm, hβnorm] <;> ring
  have hb := Metric.isBounded_range_of_tendsto (remainder α β γ) hrem
  rcases Metric.isBounded_range_iff.mp hb with ⟨B, hB⟩
  have hB0 : 0 ≤ B := by
    have := hB 0 0
    simpa using this
  refine ⟨B + |remainder α β γ 0|, add_nonneg hB0 (abs_nonneg _), ?_⟩
  intro n hn
  have hdist := hB n 0
  rw [Real.dist_eq] at hdist
  calc
    |remainder α β γ n| =
        |(remainder α β γ n - remainder α β γ 0) +
          remainder α β γ 0| := by ring
    _ ≤ |remainder α β γ n - remainder α β γ 0| +
        |remainder α β γ 0| := abs_add_le _ _
    _ ≤ B + |remainder α β γ 0| :=
      add_le_add hdist (le_refl _)

private theorem coefficient_ratio_remainder (α β γ : ℝ)
    (n : ℕ) (hn : 1 ≤ n) :
    coefficient α β γ (n - 1) / coefficient α β γ n =
      1 + (delta α β γ + 1) / (n : ℝ) +
        remainder α β γ n / (n : ℝ) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold remainder
  field_simp [hn0] <;> ring

theorem gap9 :
    ∀ (α β γ : ℝ), 0 < α → 0 < β → 0 < γ →
      0 < delta α β γ →
        Summable (fun k : ℕ => |coefficient α β γ (k + 1)|) := by
  intro α β γ hα hβ hγ hdelta
  let u : ℕ → ℝ := coefficient α β γ
  let d : ℝ := delta α β γ + 1
  let q : ℝ := (d + 1) / 2
  have hd1 : 1 < d := by dsimp [d]; linarith
  have hq1 : 1 < q := by dsimp [q]; linarith
  have heps : 0 < d - q := by dsimp [q]; linarith
  rcases gap8 α β γ hα hβ hγ with ⟨L, hL0, hL⟩
  obtain ⟨N₀ : ℕ, hN₀⟩ := exists_nat_ge (L / (d - q))
  let N : ℕ := max N₀ 1
  have hN1 : 1 ≤ N := by
    dsimp [N]
    exact le_max_right _ _
  have hratio : ∀ n : ℕ, N ≤ n →
      1 + q / (n : ℝ) ≤ u (n - 1) / u n := by
    intro n hn
    have hn1 : 1 ≤ n := hN1.trans hn
    have hnr : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    have hn0 : (n : ℝ) ≠ 0 := hnr.ne'
    have hn2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnr
    have hN₀n : (N₀ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (le_trans (le_max_left N₀ 1) hn)
    have hLn : L ≤ (n : ℝ) * (d - q) := by
      calc
        L = (L / (d - q)) * (d - q) := by
          field_simp [heps.ne']
        _ ≤ (n : ℝ) * (d - q) :=
          mul_le_mul_of_nonneg_right (hN₀.trans hN₀n) heps.le
    have hrem := hL n hn1
    have hremlo : -L ≤ remainder α β γ n := (abs_le.mp hrem).1
    rw [show u (n - 1) / u n =
      1 + d / (n : ℝ) + remainder α β γ n / (n : ℝ) ^ 2 by
        dsimp [u, d]
        exact coefficient_ratio_remainder α β γ n hn1]
    have hmul :
        (q / (n : ℝ)) * (n : ℝ) ^ 2 ≤
          (d / (n : ℝ) +
            remainder α β γ n / (n : ℝ) ^ 2) * (n : ℝ) ^ 2 := by
      field_simp [hn0]
      nlinarith
    have hcore := le_of_mul_le_mul_right hmul hn2
    linarith
  have hstep : ∀ n : ℕ, N ≤ n →
      (q - 1) * u n ≤
        (n : ℝ) * u (n - 1) - ((n : ℝ) + 1) * u n := by
    intro n hn
    have hn1 : 1 ≤ n := hN1.trans hn
    have hnr : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    have hn0 : (n : ℝ) ≠ 0 := hnr.ne'
    have hun : 0 < u n := by
      exact coefficient_pos hα hβ hγ n
    have hcross := (le_div_iff₀ hun).mp (hratio n hn)
    have hscaled := mul_le_mul_of_nonneg_left hcross hnr.le
    field_simp [hn0] at hscaled
    nlinarith
  let W : ℕ → ℝ := fun k =>
    (N + k : ℕ) * u (N + k - 1)
  have hstepW : ∀ k : ℕ,
      (q - 1) * u (N + k) ≤ W k - W (k + 1) := by
    intro k
    have hs := hstep (N + k) (Nat.le_add_right N k)
    dsimp [W]
    have hcast :
        ((N + (k + 1) : ℕ) : ℝ) = ((N + k : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    rw [hcast]
    exact hs
  have hbound : ∀ m : ℕ,
      (∑ k ∈ Finset.range m, u (N + k)) ≤ W 0 / (q - 1) := by
    intro m
    have hs :
        (∑ k ∈ Finset.range m, (q - 1) * u (N + k)) ≤
          ∑ k ∈ Finset.range m, (W k - W (k + 1)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hstepW k
    rw [← Finset.mul_sum, Finset.sum_range_sub'] at hs
    have hWm : 0 ≤ W m := by
      dsimp [W, u]
      exact mul_nonneg (by positivity) (coefficient_pos hα hβ hγ _).le
    have hmain :
        (q - 1) * (∑ k ∈ Finset.range m, u (N + k)) ≤ W 0 :=
      hs.trans (sub_le_self _ hWm)
    apply (le_div_iff₀ (by linarith : 0 < q - 1)).2
    simpa [mul_comm] using hmain
  have htail : Summable (fun k : ℕ => u (N + k)) :=
    summable_of_sum_range_le
      (fun k => (coefficient_pos hα hβ hγ _).le) hbound
  have hu : Summable u := by
    apply (summable_nat_add_iff N).mp
    simpa [Nat.add_comm] using htail
  have hshift : Summable (fun k : ℕ => u (k + 1)) :=
    (summable_nat_add_iff 1).mpr hu
  simpa [u, abs_of_pos (coefficient_pos hα hβ hγ _)] using hshift

theorem gap10 :
    ∀ (α β γ : ℝ), 0 < α → 0 < β → 0 < γ →
      delta α β γ ≤ 0 →
        ¬ Summable (fun k : ℕ => coefficient α β γ (k + 1)) := by
  intro α β γ hα hβ hγ hdelta hs
  let u : ℕ → ℝ := coefficient α β γ
  let d : ℝ := delta α β γ + 1
  have hd : d ≤ 1 := by dsimp [d]; linarith
  rcases gap8 α β γ hα hβ hγ with ⟨L, hL0, hL⟩
  obtain ⟨K : ℕ, hK⟩ := exists_nat_ge L
  have hratio : ∀ n : ℕ, K + 2 ≤ n →
      u (n - 1) / u n ≤
        1 + 1 / ((n : ℝ) - (K : ℝ) - 1) := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hnr : (0 : ℝ) < (n : ℝ) := by positivity
    have hn0 : (n : ℝ) ≠ 0 := hnr.ne'
    have hnK : (K : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hn
    have hspos : 0 < (n : ℝ) - (K : ℝ) - 1 := by linarith
    have hs0 : (n : ℝ) - (K : ℝ) - 1 ≠ 0 := hspos.ne'
    have hrem := hL n hn1
    have hremhi : remainder α β γ n ≤ L := (abs_le.mp hrem).2
    have hmain :
        d / (n : ℝ) + remainder α β γ n / (n : ℝ) ^ 2 ≤
          1 / (n : ℝ) + L / (n : ℝ) ^ 2 := by
      have hddiv : d / (n : ℝ) ≤ 1 / (n : ℝ) :=
        div_le_div_of_nonneg_right hd hnr.le
      have hrdiv :
          remainder α β γ n / (n : ℝ) ^ 2 ≤
            L / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hremhi (sq_nonneg _)
      linarith
    have hfrac :
        1 / (n : ℝ) + L / (n : ℝ) ^ 2 ≤
          1 / ((n : ℝ) - (K : ℝ) - 1) := by
      have heq :
          1 / (n : ℝ) + L / (n : ℝ) ^ 2 =
            ((n : ℝ) + L) / (n : ℝ) ^ 2 := by
        field_simp [hn0] <;> ring
      rw [heq]
      apply (div_le_iff₀ (sq_pos_of_pos hnr)).2
      rw [show
        1 / ((n : ℝ) - (K : ℝ) - 1) * (n : ℝ) ^ 2 =
          (n : ℝ) ^ 2 / ((n : ℝ) - (K : ℝ) - 1) by ring]
      apply (le_div_iff₀ hspos).2
      have hsle :
          (n : ℝ) - (K : ℝ) - 1 ≤ (n : ℝ) - L := by
        linarith
      have hsum0 : 0 ≤ (n : ℝ) + L := by positivity
      have hmul := mul_le_mul_of_nonneg_left hsle hsum0
      nlinarith [sq_nonneg L]
    rw [show u (n - 1) / u n =
      1 + d / (n : ℝ) + remainder α β γ n / (n : ℝ) ^ 2 by
        dsimp [u, d]
        exact coefficient_ratio_remainder α β γ n hn1]
    linarith
  have hweight : ∀ n : ℕ, K + 2 ≤ n →
      ((n : ℝ) - (K : ℝ) - 1) * u (n - 1) ≤
        ((n : ℝ) - (K : ℝ)) * u n := by
    intro n hn
    have hspos : 0 < (n : ℝ) - (K : ℝ) - 1 := by
      have : (K : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hs0 : (n : ℝ) - (K : ℝ) - 1 ≠ 0 := hspos.ne'
    have hun : 0 < u n := coefficient_pos hα hβ hγ n
    have hr := hratio n hn
    have hform :
        1 + 1 / ((n : ℝ) - (K : ℝ) - 1) =
          ((n : ℝ) - (K : ℝ)) /
            ((n : ℝ) - (K : ℝ) - 1) := by
      field_simp [hs0] <;> ring
    rw [hform] at hr
    have hcross := (div_le_iff₀ hun).mp hr
    calc
      ((n : ℝ) - (K : ℝ) - 1) * u (n - 1) ≤
          ((n : ℝ) - (K : ℝ) - 1) *
            (((n : ℝ) - (K : ℝ)) /
              ((n : ℝ) - (K : ℝ) - 1) * u n) :=
        mul_le_mul_of_nonneg_left hcross hspos.le
      _ = ((n : ℝ) - (K : ℝ)) * u n := by
        field_simp [hs0]
  have hweighted : ∀ j : ℕ,
      (2 : ℝ) * u (K + 2) ≤
        ((j : ℝ) + 2) * u (K + 2 + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hw := hweight (K + 2 + (j + 1)) (by omega)
        rw [show K + 2 + (j + 1) - 1 = K + 2 + j by omega] at hw
        push_cast at hw
        have hw' :
            ((j : ℝ) + 2) * u (K + 2 + j) ≤
              ((j : ℝ) + 3) * u (K + 2 + (j + 1)) := by
          convert hw using 1 <;> ring
        convert ih.trans hw' using 1 <;> push_cast <;> ring
  let C : ℝ := 2 * u (K + 2)
  have hC : 0 < C := by
    dsimp [C, u]
    exact mul_pos (by norm_num) (coefficient_pos hα hβ hγ _)
  have hlower : ∀ j : ℕ,
      C / ((j : ℝ) + 2) ≤ u (K + 2 + j) := by
    intro j
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 2)).2
    dsimp [C]
    simpa [mul_comm] using hweighted j
  have hu : Summable u := by
    apply (summable_nat_add_iff 1).mp
    simpa [u] using hs
  have hutail : Summable (fun j : ℕ => u (K + 2 + j)) := by
    have := (summable_nat_add_iff (K + 2)).mpr hu
    simpa [Nat.add_comm] using this
  have hscaled : Summable (fun j : ℕ => C / ((j : ℝ) + 2)) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hlower hutail
  have hharmtail : Summable (fun j : ℕ => 1 / ((j : ℝ) + 2)) := by
    refine (hscaled.mul_left (1 / C)).congr ?_
    intro j
    field_simp [hC.ne']
  have hharm : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    apply (summable_nat_add_iff 2).mp
    simpa [Nat.cast_add] using hharmtail
  exact Real.not_summable_one_div_natCast hharm

theorem gap11 :
    ∀ (α β γ : ℝ), 0 < α → 0 < β → 0 < γ →
      Tendsto (fun n : ℕ => raabeSeq α β γ (n + 1))
        atTop (𝓝 (delta α β γ + 1)) := by
  exact gap7

theorem gap12 :
    ∀ (α β γ : ℝ), 0 < α → 0 < β → 0 < γ →
      0 < delta α β γ →
        Summable (fun k : ℕ =>
          |(-1 : ℝ) ^ (k + 1) * coefficient α β γ (k + 1)|) := by
  intro α β γ hα hβ hγ hdelta
  simpa [abs_mul] using gap9 α β γ hα hβ hγ hdelta

theorem gap13 :
    ∀ (α β γ : ℝ), 0 < α → 0 < β → 0 < γ →
      -1 < delta α β γ →
        ∃ N : ℕ, ∀ n : ℕ, N < n →
          coefficient α β γ (n + 1) < coefficient α β γ n := by
  intro α β γ hα hβ hγ hdelta
  have hd : 0 < delta α β γ + 1 := by linarith
  have hlim := gap7 α β γ hα hβ hγ
  have hevent :
      ∀ᶠ n : ℕ in atTop, 0 < raabeSeq α β γ (n + 1) :=
    (tendsto_order.1 hlim).1 0 hd
  rcases eventually_atTop.1 hevent with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hr := hN n (Nat.le_of_lt hn)
  unfold raabeSeq at hr
  rw [show n + 1 - 1 = n by omega] at hr
  have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hratio :
      1 < coefficient α β γ n / coefficient α β γ (n + 1) := by
    nlinarith
  have hcross :=
    (lt_div_iff₀ (coefficient_pos hα hβ hγ (n + 1))).mp hratio
  simpa using hcross

theorem gap14 :
    ∀ (α β γ : ℝ), 0 < α → 0 < β → 0 < γ →
      -1 < delta α β γ →
        Tendsto (coefficient α β γ) atTop (𝓝 0) := by
  intro α β γ hα hβ hγ hdelta
  let u : ℕ → ℝ := coefficient α β γ
  let d : ℝ := delta α β γ + 1
  let q : ℝ := d / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hq : 0 < q := by dsimp [q]; linarith
  rcases gap13 α β γ hα hβ hγ hdelta with ⟨Ndec, hdec⟩
  have hanti : AntitoneOn u (Set.Ici (Ndec + 1)) := by
    apply antitoneOn_nat_Ici_of_succ_le
    intro n hn
    exact (hdec n (by omega)).le
  have hbelow : BddBelow (u '' Set.Ici (Ndec + 1)) := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨n, hn, rfl⟩
    exact (coefficient_pos hα hβ hγ n).le
  let ell : ℝ := sInf (u '' Set.Ici (Ndec + 1))
  have hlim : Tendsto u atTop (𝓝 ell) := by
    exact Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici hanti hbelow
  have hell0 : 0 ≤ ell := by
    exact ge_of_tendsto hlim
      (Eventually.of_forall fun n => (coefficient_pos hα hβ hγ n).le)
  have hell : ell = 0 := by
    by_contra hellne
    have hellpos : 0 < ell := lt_of_le_of_ne hell0 (Ne.symm hellne)
    have hRlim := gap7 α β γ hα hβ hγ
    have hReq : delta α β γ + 1 = d := by rfl
    rw [hReq] at hRlim
    have hRevent :
        ∀ᶠ n : ℕ in atTop, q < raabeSeq α β γ (n + 1) :=
      (tendsto_order.1 hRlim).1 q (by dsimp [q]; linarith)
    rcases eventually_atTop.1 hRevent with ⟨NR, hNR⟩
    have hlowevent :
        ∀ᶠ n : ℕ in atTop, ell / 2 < u n :=
      (tendsto_order.1 hlim).1 (ell / 2) (by linarith)
    rcases eventually_atTop.1 hlowevent with ⟨NL, hNL⟩
    let M : ℕ := max NR NL
    let c : ℝ := q * (ell / 2)
    have hc : 0 < c := by dsimp [c]; positivity
    let v : ℕ → ℝ := fun k => u (M + k)
    have hterm : ∀ k : ℕ,
        c * (1 / ((M + k + 1 : ℕ) : ℝ)) ≤ v k - v (k + 1) := by
      intro k
      let n : ℕ := M + k
      have hnR : NR ≤ n := by
        dsimp [n, M]
        exact le_trans (le_max_left _ _) (Nat.le_add_right _ _)
      have hnL : NL ≤ n + 1 := by
        dsimp [n, M]
        omega
      have hr := hNR n hnR
      have hlower := hNL (n + 1) hnL
      have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
      have hun : 0 < u (n + 1) := coefficient_pos hα hβ hγ _
      unfold raabeSeq at hr
      rw [show n + 1 - 1 = n by omega] at hr
      have hratio0 :
          q / ((n + 1 : ℕ) : ℝ) < u n / u (n + 1) - 1 := by
        apply (div_lt_iff₀ hnpos).2
        simpa [mul_comm] using hr
      have hratio :
          1 + q / ((n + 1 : ℕ) : ℝ) < u n / u (n + 1) := by
        linarith
      have hdiff0 := (lt_div_iff₀ hun).mp hratio
      have hdiff :
          q / ((n + 1 : ℕ) : ℝ) * u (n + 1) < u n - u (n + 1) := by
        nlinarith
      have hqu : q * (ell / 2) < q * u (n + 1) :=
        mul_lt_mul_of_pos_left hlower hq
      have hinvpos : 0 < 1 / ((n + 1 : ℕ) : ℝ) := one_div_pos.mpr hnpos
      have hcomp := mul_lt_mul_of_pos_right hqu hinvpos
      dsimp [n] at hcomp hdiff
      dsimp [c, v, n]
      have hleft :
          q * (ell / 2) * (1 / ((M + k + 1 : ℕ) : ℝ)) <
            q / ((M + k + 1 : ℕ) : ℝ) * u (M + k + 1) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcomp
      exact (hleft.trans hdiff).le
    have hbound : ∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          1 / ((M + k + 1 : ℕ) : ℝ)) ≤ v 0 / c := by
      intro m
      have hs :
          (∑ k ∈ Finset.range m,
              c * (1 / ((M + k + 1 : ℕ) : ℝ))) ≤
            ∑ k ∈ Finset.range m, (v k - v (k + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hterm k
      rw [← Finset.mul_sum, Finset.sum_range_sub'] at hs
      have hvnonneg : 0 ≤ v m := by
        dsimp [v, u]
        exact (coefficient_pos hα hβ hγ _).le
      have hmain :
          c * (∑ k ∈ Finset.range m,
            1 / ((M + k + 1 : ℕ) : ℝ)) ≤ v 0 :=
        hs.trans (sub_le_self _ hvnonneg)
      apply (le_div_iff₀ hc).2
      simpa [mul_comm] using hmain
    have htail : Summable (fun k : ℕ =>
        1 / ((M + k + 1 : ℕ) : ℝ)) :=
      summable_of_sum_range_le (fun k => by positivity) hbound
    have hharm : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
      apply (summable_nat_add_iff (M + 1)).mp
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
    exact Real.not_summable_one_div_natCast hharm
  simpa [u, hell] using hlim

theorem gap15 :
    ∀ (α β γ : ℝ), 0 < α → 0 < β → 0 < γ →
      delta α β γ ≤ -1 →
        ¬ SeriesConvergesAt α β γ (-1) := by
  intro α β γ hα hβ hγ hdelta hs
  have habs := hs.abs
  have hc : Summable (fun k : ℕ => coefficient α β γ (k + 1)) := by
    simpa [SeriesConvergesAt, powerTerm, abs_mul,
      abs_of_pos (coefficient_pos hα hβ hγ _)] using habs
  exact gap10 α β γ hα hβ hγ (by linarith) hc

theorem gap16 :
    ∀ (α β γ : ℝ), 0 < α → 0 < β → 0 < γ →
      -1 < delta α β γ →
        Tendsto (coefficient α β γ) atTop (𝓝 0) := by
  exact gap14

theorem gap17 :
    ∀ (α β γ : ℝ), 0 < α → 0 < β → 0 < γ →
      -1 < delta α β γ →
      Tendsto (coefficient α β γ) atTop (𝓝 0) := by
  exact gap14

private theorem seriesConverges_iff_tendsto_sum_range (u : ℕ → ℝ) :
    ProofGap.SeriesConverges u ↔
      ∃ l : ℝ,
        Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, u n) atTop (𝓝 l) := by
  unfold ProofGap.SeriesConverges Summable HasSum
  rw [SummationFilter.conditional_filter_eq_map_range]
  simp only [tendsto_map'_iff]
  constructor <;> rintro ⟨l, hl⟩
  · exact ⟨l, by simpa [Function.comp_def] using hl⟩
  · exact ⟨l, by simpa [Function.comp_def] using hl⟩

private theorem seriesConverges_of_summable {u : ℕ → ℝ} (hu : Summable u) :
    ProofGap.SeriesConverges u := by
  unfold ProofGap.SeriesConverges
  exact hu.mono_filter (SummationFilter.conditional ℕ).le_atTop

private theorem seriesConverges_tendsto_zero {u : ℕ → ℝ}
    (hu : ProofGap.SeriesConverges u) : Tendsto u atTop (𝓝 0) := by
  obtain ⟨l, hl⟩ := (seriesConverges_iff_tendsto_sum_range u).1 hu
  have hshift := hl.comp (tendsto_add_atTop_nat 1)
  have hsub := hshift.sub hl
  convert hsub using 1
  · funext n
    simp [Finset.sum_range_succ]
  · ring

private theorem summable_of_seriesConverges_of_nonneg {u : ℕ → ℝ}
    (hu : ProofGap.SeriesConverges u) (hu0 : ∀ n, 0 ≤ u n) : Summable u := by
  obtain ⟨l, hl⟩ := (seriesConverges_iff_tendsto_sum_range u).1 hu
  exact ⟨l, (hasSum_iff_tendsto_nat_of_nonneg hu0 l).2 hl⟩

private theorem seriesConverges_of_nat_add (u : ℕ → ℝ) (M : ℕ)
    (hu : ProofGap.SeriesConverges (fun n => u (n + M))) :
    ProofGap.SeriesConverges u := by
  obtain ⟨l, hl⟩ := (seriesConverges_iff_tendsto_sum_range _).1 hu
  apply (seriesConverges_iff_tendsto_sum_range u).2
  refine ⟨(∑ n ∈ Finset.range M, u n) + l, ?_⟩
  apply (tendsto_add_atTop_iff_nat M).1
  have hadd : Tendsto
      (fun n : ℕ =>
        (∑ k ∈ Finset.range M, u k) +
          ∑ k ∈ Finset.range n, u (k + M))
      atTop (𝓝 ((∑ k ∈ Finset.range M, u k) + l)) :=
    tendsto_const_nhds.add hl
  convert hadd using 1
  funext n
  rw [Nat.add_comm n M, Finset.sum_range_add]
  simp only [Nat.add_comm]

private theorem delta_gt_neg_one_of_coefficient_tendsto_zero
    (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hzero : Tendsto (coefficient α β γ) atTop (𝓝 0)) :
    -1 < delta α β γ := by
  by_contra hdelta
  have hd : delta α β γ + 1 ≤ 0 := by linarith
  rcases gap8 α β γ hα hβ hγ with ⟨L, hL0, hL⟩
  let w : ℕ → ℝ := fun n => L / (((n + 2 : ℕ) : ℝ) ^ 2)
  have hstep : ∀ n : ℕ,
      Real.log (coefficient α β γ (n + 1)) -
          Real.log (coefficient α β γ (n + 2)) ≤ w n := by
    intro n
    have hn : 1 ≤ n + 2 := by omega
    have hrem := hL (n + 2) hn
    have hratio :
        coefficient α β γ (n + 1) / coefficient α β γ (n + 2) ≤
          1 + L / (((n + 2 : ℕ) : ℝ) ^ 2) := by
      rw [show n + 1 = n + 2 - 1 by omega,
        coefficient_ratio_remainder α β γ (n + 2) hn]
      have hden : 0 ≤ (((n + 2 : ℕ) : ℝ) ^ 2) := sq_nonneg _
      have hdterm :
          (delta α β γ + 1) / (((n + 2 : ℕ) : ℝ)) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hd (by positivity)
      have hrterm :
          remainder α β γ (n + 2) / (((n + 2 : ℕ) : ℝ) ^ 2) ≤
            L / (((n + 2 : ℕ) : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right (abs_le.mp hrem).2 hden
      linarith
    calc
      Real.log (coefficient α β γ (n + 1)) -
          Real.log (coefficient α β γ (n + 2)) =
          Real.log (coefficient α β γ (n + 1) /
            coefficient α β γ (n + 2)) := by
        rw [Real.log_div
          (ne_of_gt (coefficient_pos hα hβ hγ _))
          (ne_of_gt (coefficient_pos hα hβ hγ _))]
      _ ≤ coefficient α β γ (n + 1) /
            coefficient α β γ (n + 2) - 1 :=
        Real.log_le_sub_one_of_pos
          (div_pos (coefficient_pos hα hβ hγ _)
            (coefficient_pos hα hβ hγ _))
      _ ≤ w n := by dsimp [w]; linarith
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hw : Summable w := by
    have hshift := (summable_nat_add_iff 2).mpr hbase
    have hmul := hshift.mul_left L
    simpa [w, Nat.cast_add, div_eq_mul_inv, mul_comm] using hmul
  have htel : ∀ m : ℕ,
      Real.log (coefficient α β γ 1) -
          Real.log (coefficient α β γ (m + 1)) ≤
        ∑ k ∈ Finset.range m, w k := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ]
        calc
          Real.log (coefficient α β γ 1) -
              Real.log (coefficient α β γ (m + 1 + 1)) =
              (Real.log (coefficient α β γ 1) -
                Real.log (coefficient α β γ (m + 1))) +
                (Real.log (coefficient α β γ (m + 1)) -
                  Real.log (coefficient α β γ (m + 2))) := by ring
          _ ≤ (∑ k ∈ Finset.range m, w k) + w m :=
            add_le_add ih (by simpa [Nat.add_assoc] using hstep m)
  let C : ℝ := Real.log (coefficient α β γ 1) - ∑' n, w n
  have hlower : ∀ m : ℕ, C ≤ Real.log (coefficient α β γ (m + 1)) := by
    intro m
    have hsum : (∑ k ∈ Finset.range m, w k) ≤ ∑' n, w n :=
      hw.sum_le_tsum (Finset.range m) (fun n hn => by
        dsimp [w]
        positivity)
    dsimp [C]
    linarith [htel m]
  have hzeroGT : Tendsto (coefficient α β γ) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hzero, Eventually.of_forall
      (fun n => coefficient_pos hα hβ hγ n)⟩
  have hlog : Tendsto
      (fun n : ℕ => Real.log (coefficient α β γ (n + 1)))
      atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hzeroGT |>.comp
      (tendsto_add_atTop_nat 1)
  have hevent := tendsto_atBot.1 hlog (C - 1)
  rcases hevent.exists with ⟨n, hn⟩
  linarith [hlower n]

private theorem not_seriesConverges_of_ratio_test_tendsto_gt_one
    {u : ℕ → ℝ} {l : ℝ} (hl : 1 < l) (hu0 : ∀ n, u n ≠ 0)
    (h : Tendsto (fun n => ‖u (n + 1)‖ / ‖u n‖) atTop (𝓝 l)) :
    ¬ ProofGap.SeriesConverges u := by
  intro hu
  obtain ⟨r, hr1, hrl⟩ := exists_between hl
  have hge : ∀ᶠ n in atTop, r * ‖u n‖ ≤ ‖u (n + 1)‖ := by
    filter_upwards [h.eventually_const_le hrl] with n hn
    rwa [← le_div_iff₀ (norm_pos_iff.mpr (hu0 n))]
  rw [eventually_atTop] at hge
  obtain ⟨N, hN⟩ := hge
  have hgrowth : Tendsto (fun n : ℕ => ‖u (n + N)‖) atTop atTop := by
    apply tendsto_atTop_of_geom_le
      (v := fun n : ℕ => ‖u (n + N)‖) (c := r)
      (by simpa using norm_pos_iff.mpr (hu0 N)) hr1
    intro n
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hN (n + N) (by omega)
  have hzero : Tendsto (fun n : ℕ => ‖u (n + N)‖) atTop (𝓝 0) := by
    simpa using
      ((seriesConverges_tendsto_zero hu).comp (tendsto_add_atTop_nat N)).norm
  exact not_tendsto_atTop_of_tendsto_nhds hzero hgrowth

theorem gap18 :
    ∀ (α β γ : ℝ), 0 < α → 0 < β → 0 < γ →
      -1 < delta α β γ →
        ProofGap.SeriesConverges
          (fun k : ℕ => powerTerm α β γ (k + 1) (-1)) := by
  intro α β γ hα hβ hγ hdelta
  obtain ⟨N, hdec⟩ := gap13 α β γ hα hβ hγ hdelta
  let M : ℕ := N + 1
  let a : ℕ → ℝ := fun k => coefficient α β γ (k + M)
  have haAnti : Antitone a := by
    apply antitone_nat_of_succ_le
    intro k
    dsimp [a, M]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (hdec (k + (N + 1)) (by omega)).le
  have ha0 : Tendsto a atTop (𝓝 0) := by
    exact (gap14 α β γ hα hβ hγ hdelta).comp
      (tendsto_add_atTop_nat M)
  obtain ⟨l, hl⟩ := haAnti.tendsto_alternating_series_of_tendsto_zero ha0
  have htail : ProofGap.SeriesConverges
      (fun k : ℕ => powerTerm α β γ (k + M) (-1)) := by
    apply (seriesConverges_iff_tendsto_sum_range _).2
    refine ⟨(-1 : ℝ) ^ M * l, ?_⟩
    have hmul := (tendsto_const_nhds (x := (-1 : ℝ) ^ M)).mul hl
    convert hmul using 1
    funext m
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [powerTerm, a]
    rw [show k + M = M + k by omega, pow_add]
    ring
  exact seriesConverges_of_nat_add
    (fun k : ℕ => powerTerm α β γ (k + 1) (-1)) (M - 1) (by
      simpa [M, Nat.add_assoc] using htail)

theorem gap19 :
    ∀ (α β γ : ℝ), 0 < α → 0 < β → 0 < γ →
      delta α β γ ≤ -1 →
        ¬ SeriesConvergesAt α β γ (-1) := by
  exact gap15

theorem gap20 :
    ∀ (α β γ x : ℝ), 0 < α → 0 < β → 0 < γ →
      (x ∈
          {y : ℝ |
            |y| < 1 ∨
            (y = 1 ∧ 0 < delta α β γ) ∨
            (y = -1 ∧ -1 < delta α β γ)} ↔
        ProofGap.SeriesConverges
          (fun k : ℕ => powerTerm α β γ (k + 1) x)) := by
  intro α β γ x hα hβ hγ
  constructor
  · rintro (hx | ⟨rfl, hdelta⟩ | ⟨rfl, hdelta⟩)
    · exact seriesConverges_of_summable
        ((gap4 α β γ hα hβ hγ).1 x hx)
    · apply seriesConverges_of_summable
      simpa [powerTerm, abs_of_pos (coefficient_pos hα hβ hγ _)] using
        gap9 α β γ hα hβ hγ hdelta
    · exact gap18 α β γ hα hβ hγ hdelta
  · intro hconv
    have habs : |x| ≤ 1 := by
      by_contra hnot
      have houtside : 1 < |x| := lt_of_not_ge hnot
      have hx0 : x ≠ 0 := abs_ne_zero.mp (ne_of_gt (zero_lt_one.trans houtside))
      have hratio : Tendsto
          (fun n : ℕ =>
            ‖powerTerm α β γ (n + 1 + 1) x‖ /
              ‖powerTerm α β γ (n + 1) x‖)
          atTop (𝓝 |x|) := by
        simpa [Nat.add_assoc] using
          powerTerm_ratio_tendsto α β γ x hα hβ hγ hx0
      have hne : ∀ n : ℕ, powerTerm α β γ (n + 1) x ≠ 0 := by
        intro n
        exact mul_ne_zero (ne_of_gt (coefficient_pos hα hβ hγ _))
          (pow_ne_zero _ hx0)
      exact (not_seriesConverges_of_ratio_test_tendsto_gt_one
        houtside hne hratio) hconv
    by_cases hinterior : |x| < 1
    · exact Or.inl hinterior
    · have habseq : |x| = 1 := le_antisymm habs (le_of_not_gt hinterior)
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habseq with hx | hx
      · subst x
        have hdelta : 0 < delta α β γ := by
          by_contra hnot
          have hcoeffConv : ProofGap.SeriesConverges
              (fun k : ℕ => coefficient α β γ (k + 1)) := by
            simpa [powerTerm] using hconv
          have hsum : Summable
              (fun k : ℕ => coefficient α β γ (k + 1)) :=
            summable_of_seriesConverges_of_nonneg hcoeffConv
              (fun k => (coefficient_pos hα hβ hγ _).le)
          exact gap10 α β γ hα hβ hγ (le_of_not_gt hnot) hsum
        exact Or.inr (Or.inl ⟨rfl, hdelta⟩)
      · subst x
        have htermZero := seriesConverges_tendsto_zero hconv
        have hshift : Tendsto
            (fun k : ℕ => coefficient α β γ (k + 1)) atTop (𝓝 0) := by
          have hnorm : Tendsto
              (fun k : ℕ => ‖powerTerm α β γ (k + 1) (-1)‖)
              atTop (𝓝 0) := by
            simpa using htermZero.norm
          convert hnorm using 1
          funext k
          rw [Real.norm_eq_abs]
          simp [powerTerm, abs_mul,
            abs_of_pos (coefficient_pos hα hβ hγ _)]
        have hzero : Tendsto (coefficient α β γ) atTop (𝓝 0) :=
          (tendsto_add_atTop_iff_nat 1).1 hshift
        exact Or.inr (Or.inr ⟨rfl,
          delta_gt_neg_one_of_coefficient_tendsto_zero
            α β γ hα hβ hγ hzero⟩)

end

end ProofGap.Exercise2832
